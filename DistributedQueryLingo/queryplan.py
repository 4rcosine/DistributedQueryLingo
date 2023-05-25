import problem_info
import os
import platform
import utils
import subprocess

class nodo_plan:
	"""Classe che rappresenta il nodo dell'albero della query"""
	#id = identificativo del nodo, serve per identificare il padre
	#tipo_op = operazione eseguita
	#set_attr = attributi coinvolti dall'operazione
	#set_oper = operandi coinvolti nell'operazione (per group by)
	#id_padre = identificativo del nodo padre
	#set_attrplain = set degli attributi che è necessario siano in chiaro per l'operazione
	#ordine = posizione del nodo (per quando ci sono più nodi su un solo livello, come nelle set operation)
	#profilo = profilo del nodo
	#candidati = set dei possibili assegnatari per il nodo
	#assegnatario = soggetto a cui è stato assegnato il nodo

	def __init__(self, tipo_op, dett_op, set_attributi, set_operandi, set_attrplain, id_padre, ordine):
		self.tipo_op = tipo_op
		self.dett_op = dett_op
		self.set_attr = utils.upper_set(set_attributi)
		self.set_oper = utils.upper_set(set_operandi)
		self.id_padre = id_padre.upper()
		self.set_attrplain = utils.upper_set(set_attrplain)
		self.ordine = ordine
		self.profilo = {}
		self.profilo["vp"] = set()
		self.profilo["ve"] = set()
		self.profilo["ip"] = set()
		self.profilo["ie"] = set()
		self.profilo["eq"] = []
		self.profilo["rn"] = dict()
		self.candidati = set()
		self.assegnatario = ""

	def get_profilo(self):
		return (self.profilo["vp"], self.profilo["ve"], self.profilo["ip"], self.profilo["ie"], self.profilo["eq"], self.candidati, self.assegnatario, self.tipo_op, self.set_attr, self.set_oper, self.dett_op)


class query_plan(object):
	"""Classe che rappresenta l'albero della query"""

	def __init__(self):
		self.lista_nodi = dict()
		self.soggetti = dict()
		self.op_cif_dec = list() #Operazioni di cifratura/decifratura iniettate nel secondo step

	def add_nodo(self, id, nodo):
		self.lista_nodi[id] = nodo

	def add_nodo(self, id, tipo_op, dett_op, set_attributi, set_operandi, set_attrplain, id_padre, ordine):
		nodo = nodo_plan(tipo_op=tipo_op, dett_op=dett_op, set_attributi=set_attributi, set_operandi=set_operandi, set_attrplain=set_attrplain, id_padre=str(id_padre), ordine=ordine)
		self.lista_nodi[id] = nodo

	def add_star_node(self):
		id_snode = "UNODE"
		root_node = utils.get_root_node(self)
		self.lista_nodi[root_node].id_padre = id_snode

		attrplain = []
		for attr in problem_info.attr_info:
			attrplain.append(attr["name"])

		nodo = nodo_plan(tipo_op="star", dett_op="", set_attributi=[], set_operandi=[], set_attrplain=attrplain, id_padre="0", ordine=0)
		self.lista_nodi[id_snode] = nodo
		
	def get_nodo(self, id):
		return self.lista_nodi[id]

	def get_num_nodi(self):
		return len(self.lista_nodi)

	def set_subj(self, soggetti):
		#Conversione delle liste in set
		for chiave, valore in soggetti.items():
			soggetti[chiave]["p"] = set(valore["p"])
			soggetti[chiave]["e"] = set(valore["e"])
			soggetti[chiave]["own"] = set(valore["own"])
		self.soggetti = soggetti

	def get_ocd(self):
		return self.op_cif_dec


	def pulisci_profili(self):
		#Candidati calcolati: sbianco tutto
		for id, nodo in self.lista_nodi.items():
			self.lista_nodi[id].profilo["vp"] = set()
			self.lista_nodi[id].profilo["ve"] = set()
			self.lista_nodi[id].profilo["ip"] = set()
			self.lista_nodi[id].profilo["ie"] = set()
			self.lista_nodi[id].profilo["eq"] = []
			self.lista_nodi[id].profilo["rn"] = {}

	#Funzione di ottenimento dei set degli attributi che devono essere cifrati con la stessa chiave
	def get_asc(self):

		id_primo_nodo = utils.get_root_node(self)

		ins_eq = self.lista_nodi[id_primo_nodo].profilo["eq"]
		
		lista_set_adc = list()
		set_attr_singoli = set()

		#Calcolo l'insieme degli attributi che da qualche parte deve essere cifrata
		set_adc = set()
		for ocd in self.op_cif_dec:
			if ocd["tipo_op"] == "C":
				set_adc.update(ocd["adc"])
			
		for subset in ins_eq:
			if subset.issubset(set_adc):
				lista_set_adc.append(subset)

		#Aggiungo gli attributi da cifrare singolarmente
		for ocd in self.op_cif_dec:
			if ocd["tipo_op"] == "C":
				#Per ogni singolo attributo da cifrare controllo se esso fa parte di un set di equivalenza, se no lo aggiungo come set singleton
				for adc in list(ocd["adc"]):
					found = False
					for subset in lista_set_adc:
						if adc in subset:
							found = True

					if not found:
						dummyset = set()
						dummyset.add(adc)
						lista_set_adc.append(dummyset)
		
		#Determino i possessori delle chiavi
		res = list()
		for kes in lista_set_adc:
			tmp = dict()
			tmp["kes"] = kes
			tmp["sogg"] = set()

			#Ciclo sui singoli attributi da cifrare, e ricerco nelle operazioni di cifratura gli id dei nodi dai quali reperirò i candidati a cui vanno assegnate le chiavi
			for adc in list(kes):
				for ocd in self.op_cif_dec:
					if adc in ocd["adc"]:
						tmp["sogg"].add(ocd["exec"])

			res.append(tmp)

		return res



	#I profili sono calcolati secondo una visita post-order
	def calc_cand_rec(self, id):

		#Uso una variabile temporanea per migliorare la leggibilità
		curr_n = self.lista_nodi[id]

		#Determino i figli del nodo corrente
		figli = []
		
		for indice, nodo_tmp in self.lista_nodi.items():
			if nodo_tmp.id_padre == id:
				figli.append(indice)

		if len(figli) > 0:
			#Lancio il esegui_step_rec ricorsivamente su tutti i figli
			for figlio in figli:
				self.calc_cand_rec(figlio)
			
				#Per tutti i figli, faccio l'union degli insiemi (escluso che per le join e prodotti cartesiani, il figlio sarà uno solo sempre)
				for i in {'vp', 've', 'ip', 'ie'}:
					self.lista_nodi[id].profilo[i].update(self.lista_nodi[figlio].profilo[i])

				if(len(self.lista_nodi[figlio].profilo["eq"]) > 0):
					for subset in self.lista_nodi[figlio].profilo["eq"]:
						self.lista_nodi[id].profilo["eq"].append(subset)

				self.lista_nodi[id].profilo["rn"].update(self.lista_nodi[figlio].profilo["rn"])
		
		#Bonifica attributi rinominati per i profili
		for pseudo, real in curr_n.profilo["rn"].items():
			if pseudo in curr_n.set_attr:
				self.lista_nodi[id].set_attr = curr_n.set_attr.difference(pseudo).union(real)

			if pseudo in curr_n.set_oper:
				self.lista_nodi[id].set_oper = curr_n.set_oper.difference(pseudo).union(real)

			if pseudo in curr_n.set_attrplain:
				self.lista_nodi[id].set_attrplain = curr_n.set_attrplain.difference(pseudo).union(real) 


		#Valutazione degli attributi che bisogna avere per forza decifrati per il nodo
		attr_da_decifrare = curr_n.profilo["ve"].intersection(curr_n.set_attrplain)
		if len(attr_da_decifrare) > 0:
			self.lista_nodi[id].profilo["ve"] = curr_n.profilo["ve"].difference(attr_da_decifrare)
			self.lista_nodi[id].profilo["vp"] = curr_n.profilo["vp"].union(attr_da_decifrare)

		#Determino il profilo del nodo corrente
		if curr_n.tipo_op == "base":
			#Mandata di calcolo set candidati: eseguo l'injection della cifratura, per calcolare i candidati possibili
			self.lista_nodi[id].profilo["ve"] = curr_n.set_attr

		elif curr_n.tipo_op == "proj":
			self.lista_nodi[id].profilo["vp"] = curr_n.profilo["vp"].intersection(curr_n.set_attr)
			self.lista_nodi[id].profilo["ve"] = curr_n.profilo["ve"].intersection(curr_n.set_attr)

		elif curr_n.tipo_op == "sel_val":
			self.lista_nodi[id].profilo["ip"] = curr_n.profilo["ip"].union(curr_n.profilo["vp"].intersection(curr_n.set_attr))
			self.lista_nodi[id].profilo["ie"] = curr_n.profilo["ie"].union(curr_n.profilo["ve"].intersection(curr_n.set_attr))

		elif curr_n.tipo_op == "sel_attr":
			self.lista_nodi[id].profilo["eq"].append(curr_n.set_attr)       #Qua viene aggiunto un set dentro al set → rappresentare il set di attributi come frozenset o come tupla

		elif curr_n.tipo_op == "join":
			self.lista_nodi[id].profilo["eq"].append(curr_n.set_attr)       #Discorso analogo per sel_attr

		elif curr_n.tipo_op == "gby":
			self.lista_nodi[id].profilo["vp"] = curr_n.profilo["vp"].intersection(curr_n.set_attr.union(curr_n.set_oper))
			self.lista_nodi[id].profilo["ve"] = curr_n.profilo["ve"].intersection(curr_n.set_attr.union(curr_n.set_oper))
			self.lista_nodi[id].profilo["ip"] = curr_n.profilo["ip"].union(curr_n.profilo["vp"].intersection(curr_n.set_attr))
			self.lista_nodi[id].profilo["ie"] = curr_n.profilo["ie"].union(curr_n.profilo["ve"].intersection(curr_n.set_attr))
		
		elif curr_n.tipo_op == "rename_p":
			self.lista_nodi[id].profilo["rn"][list(curr_n.set_oper)[0]] = list(curr_n.set_attr)[0]
			self.lista_nodi[id].profilo["vp"] = curr_n.profilo["vp"].difference(curr_n.set_attr).union(curr_n.set_oper)

		elif curr_n.tipo_op == "rename_e":
			self.lista_nodi[id].profilo["rn"][list(curr_n.set_oper)[0]] = list(curr_n.set_attr)[0]
			self.lista_nodi[id].profilo["ve"] = curr_n.profilo["ve"].difference(curr_n.set_attr).union(curr_n.set_oper)
		
		elif curr_n.tipo_op == "udf":
			self.lista_nodi[id].profilo["vp"] = curr_n.profilo["vp"].difference((curr_n.set_attr.difference(curr_n.set_oper)))
			self.lista_nodi[id].profilo["ve"] = curr_n.profilo["ve"].difference((curr_n.set_attr.difference(curr_n.set_oper)))
			self.lista_nodi[id].profilo["eq"].append(curr_n.set_attr)

		elif curr_n.tipo_op == "encr":
			self.lista_nodi[id].profilo["vp"] = curr_n.profilo["vp"].difference(curr_n.set_attr)
			self.lista_nodi[id].profilo["ve"] = curr_n.profilo["ve"].union(curr_n.set_attr)

		elif curr_n.tipo_op == "decr":
			self.lista_nodi[id].profilo["ve"] = curr_n.profilo["ve"].difference(curr_n.set_attr)
			self.lista_nodi[id].profilo["vp"] = curr_n.profilo["vp"].union(curr_n.set_attr)

		#Calcolo i candidati per il nodo
		if curr_n.tipo_op != 'base':

			if self.is_proj_after_base(id):
				#Per le proiezioni su tab base calcolo come unico candidato l'owner della tabella base
				for nodo_f in self.lista_nodi:
					if self.lista_nodi[nodo_f].id_padre == id:
						for subj, auth in self.soggetti.items():
							if self.lista_nodi[nodo_f].set_oper.issubset(auth["own"]):
								self.lista_nodi[id].candidati.add(subj)
								break
						break
			else:
				#Tabella non base: calcolo candidati
				for subj, auth in self.soggetti.items():
					#Controllo autorizzazione per il plain text
					aut_plain = (curr_n.profilo["vp"].union(curr_n.profilo["ip"])).issubset(auth["p"])
				
					#Controllo autorizzazione per il cifrato
					aut_encr = (curr_n.profilo["ve"].union(curr_n.profilo["ie"])).issubset(auth["p"].union(auth["e"]))

					aut_eq = True
					#Controllo autorizzazione per insiemi di equivalenza
					for subset in curr_n.profilo["eq"]:
						aut_eq = aut_eq and (subset.issubset(auth["p"]) or subset.issubset(auth["e"]))

					if aut_plain and aut_encr and aut_eq:
						self.lista_nodi[id].candidati.add(subj)
		else:
			#Tabella base: cerco l'owner
			for subj, auth in self.soggetti.items():
				if curr_n.set_oper.issubset(auth["own"]):
					self.lista_nodi[id].candidati.add(subj)
			
	#Funzione di calcolo assegnatario ed estensione del queryplan (integrazione Lingo)
	def assign_and_extend(self):
		f_handle = open('base_lingo.ltf',mode='r', encoding='utf-8')
		base_script = f_handle.read()
		f_handle.close()

		base_script = base_script.replace("§output_file§", "C:\\Users\\Giobberto\\source\\repos\\DistributedQueryUI\\DistributedQueryUI\\output_script.ltf")
		
		attr_list = ""
		attr_size = ""
		attr_enceff = ""

		server_list = ""
		server_compc = ""
		server_encrc = ""
		server_decrc = ""
		server_transfc = ""

		node_list = ""
		node_icard = ""
		node_ocard = ""
		node_opcost = ""
		node_nasize = ""

		star_nodes = ""
		base_nodes = ""
		base_proj_plain = ""
		base_impl = ""

		#Input attributi
		for attr in problem_info.attr_info:
			attr_list += attr["name"] + " "
			attr_size += attr["size"] + " "
			attr_enceff += attr["enceff"] + " "

		#Input soggetti
		for subj in problem_info.subj_info:
			server_list += subj["name"] + " "
			server_compc += subj["compcost"] + " "
			server_encrc += subj["encrcost"] + " "
			server_decrc += subj["decrcost"] + " "
			server_transfc += subj["transfcost"] + " "

		#Input nodi
		for node in problem_info.nodes_info:
			node_list += node["name"] + " "
			node_icard += node["icard"] + " "
			node_ocard += node["ocard"] + " "
			node_opcost += node["opcost"] + " "
			node_nasize += node["nasize"] + " "

		#Matrici autorizzazioni server per visibilità (in chiaro e in cifrato) su attributi
		auth_plain = ""
		auth_enc = ""

		for subj in problem_info.subj_info:
			subj_auth_p = ""
			subj_auth_e = ""

			for attr in problem_info.attr_info:
				#Metto 1 se l'attributo risulta nella lista degli attributi su cui il soggetto ha visibilità in plain
				subj_auth_p += "1 " if attr["name"] in self.soggetti[subj["name"]]["p"] else "0 "

				#Metto 1 se l'attributo risulta nella lista degli attributi su cui il soggetto ha visibilità in cifrato
				subj_auth_e += "1 " if attr["name"] in self.soggetti[subj["name"]]["e"] else "0 "

			auth_plain += subj_auth_p.strip() + "\n"
			auth_enc += subj_auth_e.strip() + "\n"

		#Matrice dei candidati
		candidates = ""

		for subj in problem_info.subj_info:
			cand_nodes = ""

			for node in problem_info.nodes_info:
				cand_nodes += "1 " if subj["name"] in self.lista_nodi[node["name"]].candidati else "0 "

			candidates += cand_nodes.strip() + "\n"

		#Matrici delle MRVs
		plain_view = ""
		encr_view = ""
		plain_impl = ""
		encr_impl = ""

		for attr in problem_info.attr_info:
			pv_row = ""
			ev_row = ""
			pi_row = ""
			ei_row = ""

			for node in problem_info.nodes_info:
				pv_row += "1 " if attr["name"] in self.lista_nodi[node["name"]].profilo["vp"] else "0 "
				ev_row += "1 " if attr["name"] in self.lista_nodi[node["name"]].profilo["ve"] else "0 "
				pi_row += "1 " if attr["name"] in self.lista_nodi[node["name"]].profilo["ip"] else "0 "
				ei_row += "1 " if attr["name"] in self.lista_nodi[node["name"]].profilo["ie"] else "0 "

			plain_view += pv_row.strip() + "\n"
			encr_view += ev_row.strip() + "\n"
			plain_impl += pi_row.strip() + "\n"
			encr_impl += ei_row.strip() + "\n"

		#Matrice che indica le relazioni di parentela tra nodi
		tree = ""

		for node_row in problem_info.nodes_info:
			par_row = ""
			for node_col in problem_info.nodes_info:
				par_row += "1 " if self.lista_nodi[node_col["name"]].id_padre == node_row["name"] else "0 "

			tree += par_row.strip() + "\n"

		#Matrice dei nodi che rendono impliciti gli attributi
		impl_nodes = ""
		
		for attr_row in problem_info.attr_info:
			impl_row = ""

			for node_col in problem_info.nodes_info:
				v_i = self.lista_nodi[node_col["name"]].profilo["ip"]
				e_i = self.lista_nodi[node_col["name"]].profilo["ie"]
				if attr_row["name"] in v_i.union(e_i):
					#Attributo presente negli impliciti, valuto se i figli hanno o meno gli attributi
					was_implicit = False
					for indice, nodo_tmp in self.lista_nodi.items():
						if nodo_tmp.id_padre == node_col["name"]:
							v_i_f = self.lista_nodi[indice].profilo["ip"]
							e_i_f = self.lista_nodi[indice].profilo["ie"]
							if attr_row["name"] in v_i_f.union(e_i_f):
								was_implicit = True
								break

					impl_row += "0 " if was_implicit else "1 "


				else:
					impl_row += "0 "

			impl_nodes += impl_row.strip() + "\n"


		#Matrice dei nodi che rendono equivalenti gli attributi
		eq_nodes = ""
		for attr_matr in problem_info.attr_info:
			for attr_row in problem_info.attr_info:
				eq_row = ""

				for node_col in problem_info.nodes_info:
					eq_set = self.lista_nodi[node_col["name"]].profilo["eq"]	#Lista di insiemi nel profilo del nodo
					attr_set = { attr_matr["name"], attr_row["name"]}							#Insieme di attr da trovare
					
					if attr_set in eq_set: 
						#Attributi presenti nel set eq, valuto se i figli hanno o meno gli attributi
						was_equal = False
						for indice, nodo_tmp in self.lista_nodi.items():
							if nodo_tmp.id_padre == node_col["name"]:
								eq_set_f = self.lista_nodi[indice].profilo["eq"]

								if attr_set in eq_set_f:
									was_equal = True
									break

						eq_row += "0 " if was_equal else "1 "


					else:
						eq_row += "0 "

				eq_nodes += eq_row.strip() + "\n"
		
		#Star nodes (nodi da dare agli utenti)
		star_nodes = ""
		idx_server_ut = 1
		idx_root = 1
		counter = 1
		
		for server in problem_info.subj_info:
			if server["name"] == "U":
				idx_server_ut = counter
				break;
			counter += 1

		counter = 1
		for node in problem_info.nodes_info:
			if node["name"] == "UNODE":
				idx_root = counter
				break
			counter += 1

		star_nodes += "ASSIGNEE( " + str(idx_server_ut) + "," + str(idx_root) + ") = 1;\n"

		#Tabelle base e relative proiezioni assegnate al proprietario
		idx_server = 1
		for server in problem_info.subj_info:

			idx_nodo = 1
			for node in problem_info.nodes_info:
				if (self.lista_nodi[node["name"]].tipo_op == "base" or self.is_proj_after_base(node["name"])) and server["name"] in self.lista_nodi[node["name"]].candidati:
					base_nodes += "ASSIGNEE( " + str(idx_server) + "," + str(idx_nodo) + ") = 1;\n"
				idx_nodo += 1
			idx_server += 1

		#Tutti gli attributi di relazioni base e proiezioni in plain text
		idx_attr = 1
		for attr in problem_info.attr_info:

			idx_nodo = 1
			for node in problem_info.nodes_info:
				
				if (self.lista_nodi[node["name"]].tipo_op == "base" or self.is_proj_after_base(node["name"])) and attr["name"] in self.lista_nodi[node["name"]].set_attr:
					base_proj_plain += "VP( " + str(idx_attr) + "," + str(idx_nodo) + ") = 1;\n"
				idx_nodo += 1
			idx_attr += 1
		
		#Vincolo per le relazioni base di non avere attributi impliciti
		idx_nodo = 1
		for node in problem_info.nodes_info:
			if self.lista_nodi[node["name"]].tipo_op == "base":
				base_impl += "\tIP( a, " + str(idx_nodo) + ") = 0;\n"
				base_impl += "\tIE( a, " + str(idx_nodo) + ") = 0;\n"
			idx_nodo += 1

		#Sostituisco tutto nel testo
		base_script = base_script.replace("§attr_list§", attr_list.strip())
		base_script = base_script.replace("§server_list§", server_list.strip())
		base_script = base_script.replace("§node_list§", node_list.strip())

		base_script = base_script.replace("§size§", attr_size.strip())
		base_script = base_script.replace("§enc_eff§", attr_enceff.strip())

		base_script = base_script.replace("§in_cards§", node_icard.strip())
		base_script = base_script.replace("§out_cards§", node_ocard.strip())

		base_script = base_script.replace("§comp_cost§", server_compc.strip())
		base_script = base_script.replace("§encr_cost§", server_encrc.strip())
		base_script = base_script.replace("§decr_cost§", server_decrc.strip())
		base_script = base_script.replace("§tr_cost§", server_transfc.strip())
		
		base_script = base_script.replace("§op_cost§", node_opcost.strip())
		base_script = base_script.replace("§na_size§", node_nasize.strip())
		
		#Matrici
		base_script = base_script.replace("§auth_plain§", auth_plain.strip())
		base_script = base_script.replace("§auth_encr§", auth_enc.strip())
		base_script = base_script.replace("§candidates§", candidates.strip())
		base_script = base_script.replace("§plain_view§", plain_view.strip())
		base_script = base_script.replace("§encr_view§", encr_view.strip())
		base_script = base_script.replace("§plain_impl§", plain_impl.strip())
		base_script = base_script.replace("§encr_impl§", encr_impl.strip())
		base_script = base_script.replace("§go_impl§", impl_nodes.strip())
		base_script = base_script.replace("§tree§", tree.strip())
		base_script = base_script.replace("§eq§", eq_nodes.strip())

		#Vincoli
		base_script = base_script.replace("§star_nodes§", star_nodes.strip())
		base_script = base_script.replace("§base_nodes§", base_nodes.strip())
		base_script = base_script.replace("§base_proj_plain§", base_proj_plain.strip())
		base_script = base_script.replace("§base_impl§", base_impl)
		
		#Scrivo il file da dare in input a lingo
		in_script = open("./input_script.ltf", "w")
		in_script.write(base_script)
		in_script.close()

		if os.path.exists("C:\\Users\\Giobberto\\source\\repos\\DistributedQueryUI\\DistributedQueryUI\\output_script.ltf"):
			os.remove("C:\\Users\\Giobberto\\source\\repos\\DistributedQueryUI\\DistributedQueryUI\\output_script.ltf")

		#Eseguo lingo con i parametri
		if platform.system() == "Darwin":
			os.system("open " + "")
		else:
			subprocess.Popen([utils.lingo_path, "C:\\Users\\Giobberto\\source\\repos\\DistributedQueryUI\\DistributedQueryUI\\input_script.ltf"]).wait()
		
		#Lettura dell'output da Lingo
		f_handle = open("C:\\Users\\Giobberto\\source\\repos\\DistributedQueryUI\\DistributedQueryUI\\output_script.ltf", "r")

		data_line = False
		output_data = []	#Lista di tre stringhe, una con gli assegnamenti, una con gli attributi in chiaro e una con gli attributi cifrati
		for line in f_handle:
			if data_line == True:
				output_data.append(line.strip())
				data_line = False

			elif "ASSIGNMENTS" in line or "VISIBLE PLAINTEXT" in line or "VISIBLE ENCRYPTED" in line:
				data_line = True
		f_handle.close()

		#Interpretazione dell'output di Lingo
		lingo_assign = output_data[0].split("#")
		lingo_assign.pop()
		for assignment in lingo_assign:
			assign_node = assignment.split("§")
			self.lista_nodi[assign_node[0]].assegnatario = assign_node[1]
		
		#Ripulisco i profili vp e ve di tutti i nodi, compilandoli con quello che mi da lingo
		for node in problem_info.nodes_info:
			self.lista_nodi[node["name"]].profilo["vp"] = set()
			self.lista_nodi[node["name"]].profilo["ve"] = set()
			self.lista_nodi[node["name"]].profilo["ip"] = set()
			self.lista_nodi[node["name"]].profilo["ie"] = set()

		lingo_vis_plain = output_data[1].split("#")
		lingo_vis_plain.pop()
		for attr_plain in lingo_vis_plain:
			ap_node = attr_plain.split("§")
			self.lista_nodi[ap_node[0]].profilo["vp"].add(ap_node[1])

		lingo_vis_encr = output_data[2].split("#")
		lingo_vis_encr.pop()
		for attr_encr in lingo_vis_encr:
			ae_node = attr_encr.split("§")
			self.lista_nodi[ae_node[0]].profilo["ve"].add(ae_node[1])

		#Per ogni nodo vado a vedere se devono essere effettuate cifrature o decifrature
		for node in problem_info.nodes_info:
			
			#Determino i figli del nodo corrente
			figli = []
		
			for indice, nodo_tmp in self.lista_nodi.items():
				if nodo_tmp.id_padre == node["name"]:
					figli.append(indice)

			if not len(figli):
				#Se siamo in tabella base e ci sono attributi da cifrare lo faccio qua direttamente
				attr_da_cifr = self.lista_nodi[node["name"]].profilo["ve"]

				if len(attr_da_cifr):
					self.op_cif_dec.append({ "padre" : self.lista_nodi[node["name"]].id_padre, "figlio" : node["name"], "tipo_op" : "C",  "adc" : attr_da_cifr, "exec" : self.lista_nodi[node["name"]].assegnatario})

			else:
				for figlio in figli:
					for i in {'ip', 'ie'}:
						self.lista_nodi[node["name"]].profilo[i].update(self.lista_nodi[figlio].profilo[i])

					#Operazioni cifratura
					ve_padre = self.lista_nodi[node["name"]].profilo["ve"]
					vp_figlio = self.lista_nodi[figlio].profilo["vp"]
					attr_da_cifr = ve_padre.intersection(vp_figlio)

					if len(attr_da_cifr):
						self.op_cif_dec.append({ "padre" : node["name"], "figlio" : figlio, "tipo_op" : "C",  "adc" : attr_da_cifr, "exec" : self.lista_nodi[figlio].assegnatario})

					#Operazioni decifratura
					vp_padre = self.lista_nodi[node["name"]].profilo["vp"]
					ve_figlio = self.lista_nodi[figlio].profilo["ve"]
					attr_da_dec = vp_padre.intersection(ve_figlio)

					if len(attr_da_dec):
						self.op_cif_dec.append({ "padre" : node["name"] , "figlio" : figlio, "tipo_op" : "D", "adc" : attr_da_dec, "exec" : self.lista_nodi[node["name"]].assegnatario})	

	#Funzione di calcolo dei profili a partire dagli assegnamenti di lingo
	def calc_impl_rec(self, id):
		#Uso una variabile temporanea per migliorare la leggibilità
		curr_n = self.lista_nodi[id]

		#Determino i figli del nodo corrente
		figli = []
		
		for indice, nodo_tmp in self.lista_nodi.items():
			if nodo_tmp.id_padre == id:
				figli.append(indice)

		if len(figli) > 0:
			#Lancio il calc_prof_rec ricorsivamente su tutti i figli
			for figlio in figli:
				self.calc_impl_rec(figlio)
			
				#Per tutti i figli, faccio l'union degli insiemi (escluso che per le join e prodotti cartesiani, il figlio sarà uno solo sempre)
				for i in {'ip', 'ie'}:
					self.lista_nodi[id].profilo[i].update(self.lista_nodi[figlio].profilo[i])

		if curr_n.tipo_op == "sel_val":
			self.lista_nodi[id].profilo["ip"] = curr_n.profilo["ip"].union(curr_n.profilo["vp"].intersection(curr_n.set_attr))
			self.lista_nodi[id].profilo["ie"] = curr_n.profilo["ie"].union(curr_n.profilo["ve"].intersection(curr_n.set_attr))

		elif curr_n.tipo_op == "gby":
			self.lista_nodi[id].profilo["ip"] = curr_n.profilo["ip"].union(curr_n.profilo["vp"].intersection(curr_n.set_attr))
			self.lista_nodi[id].profilo["ie"] = curr_n.profilo["ie"].union(curr_n.profilo["ve"].intersection(curr_n.set_attr))

		


	def sistema_set(self, id):
		#Mi ottengo la lista degli attributi in eq
		set_attr = set()
		for elem in self.lista_nodi[id].profilo["eq"]:
			set_attr.update(elem)

		#Creo un dizionario dove per ogni attributo in eq viene specificato il set collassato di appartenenza
		newEq = {}
		oldEq = {'dummy'}

		while oldEq != newEq:
			oldEq = newEq.copy()
			for attr in set_attr:
				newEq[attr] = set()
				for subset in self.lista_nodi[id].profilo["eq"]:
					if attr in subset:
						newEq[attr].update(subset)

		#Terminato il form che crea il dizionario ho un dizionario dove per ogni attributo in eq ho il relativo set collassato: creo una lista ignorando i doppioni
		self.lista_nodi[id].profilo["eq"] = []
		for key, sel in newEq.items():
			if sel not in self.lista_nodi[id].profilo["eq"]:
				self.lista_nodi[id].profilo["eq"].append(sel)

	def is_proj_after_base(self, id_nodo):
		#Determino i figli del nodo corrente

		if self.lista_nodi[id_nodo].tipo_op != 'proj':
			return False

		figli = []
		
		for indice, nodo_tmp in self.lista_nodi.items():
			if nodo_tmp.id_padre == id_nodo:
				figli.append(indice)

		return self.lista_nodi[figli[0]].tipo_op == "base"