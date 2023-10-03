#Modulo delle Utilities (funzioni ad uso comune)
import os
import sys
import platform
import problem_info
import queryplan

lingo_path = ""

ope_name = {
		"base" : "",
		"proj" : "projection",
		"sel_val" : "selection",
		"sel_attr" : "selection",
		"join" : "join",
		"gby" : "aggregation",
		"rename_p" : "rename",
		"rename_e" : "rename",
		"udf" : "user defined function",
		"encr" : "encryption",
		"decr" : "decryption",
		"star" : "result to user"
	}

def get_cur_dir():
	# determine if application is a script file or frozen exe
	if getattr(sys, 'frozen', False):
		application_path = os.path.dirname(sys.executable)
	elif __file__:
		application_path = os.path.dirname(__file__)

	return application_path

def upper_set(cset):
	dummy = set()

	for element in cset:
		dummy.add(element.upper())

	return dummy

def upper_list(clist):
	dummy = []

	for element in clist:
		dummy.append(element.upper())

	return dummy

def get_root_node(qp):
	id_primo_nodo = ""

	#Trovo l'ultimo nodo
	for indice, nodo in qp.lista_nodi.items():
		if qp.lista_nodi[indice].id_padre == "0":
			id_primo_nodo = indice

	return id_primo_nodo


def build_initial_json(lista_tab_json):
	#Per ogni tabella caricata...
	subj_json = dict()

	for json in lista_tab_json:
		
		#se nella lista soggetti non c'è l'owner lo aggiungo. Se c'è già lo imposto come owner
		if not json["owner"] in subj_json:
			subj_json[json["owner"]] = { "p" : [],  "e" : [], "own" : [json["name"].upper()], "pri" : -1}
		
		else:
			subj_json[json["owner"]]["own"].append(json["name"].upper())

		#Per ogni attribuito della tabella...
		for soggetto in json["permissions"]:

			if not soggetto in subj_json:
				subj_json[soggetto] = { "p" : [],  "e" : [], "own" : [], "pri" : -1}

			subj_json[soggetto]["p"] = list(upper_set(set(subj_json[soggetto]["p"] + json["permissions"][soggetto]["plain"])))
			subj_json[soggetto]["e"] = list(upper_set(set(subj_json[soggetto]["e"] + json["permissions"][soggetto]["encr"])))


		for sj in subj_json:
			if subj_json[sj]["p"] == [] and subj_json[sj]["e"] == []:
				subj_json[sj]["p"] = subj_json["any"]["p"]
				subj_json[sj]["e"] = subj_json["any"]["e"]

		#Controllo se l'user c'è. Se non c'è lo creo come utente che ha permesso di vedere tutti gli attributi in chiaro
		user_found = False
		for soggetto in subj_json:
			if soggetto == "U":
				user_found = True

		if not user_found:
			subj_json[soggetto]["p"] = list()

			for attr in problem_info.attr_info:
				subj_json[soggetto]["p"].append(attr["name"])
			
		if "any" in subj_json:
			del subj_json["any"]

	return subj_json

#Funzione per sviluppare le UDF in UDF + proiezione (fix per lingo)
def fix_udf(qp_dict):

	qp_dict_tmp = dict()

	for id, nodo in qp_dict.items():
		qp_dict_tmp[id] = nodo

	for node in qp_dict_tmp:

		if qp_dict_tmp[node]["op_type"] == "udf":
			#Aggiungo un nodo di tipo proiezione
			id_padre_udf = qp_dict_tmp[node]["parent_id"]
			qp_dict[node + "_PROJ"] = {
					"op_type": "proj",
					"op_detail": "",
					"set_attr": qp_dict_tmp[node]["set_oper"],
					"set_oper": [],
					"set_attrplain": [],
					"parent_id": id_padre_udf,
					"order": 0,
					"in_card": qp_dict_tmp[node]["out_card"],
					"out_card": qp_dict_tmp[node]["out_card"],
					"op_cost": 0,
					"na_size": 0
				}
			
			#print("in card proj: " + str(qp_dict[node + "_PROJ"]["in_card"]))
			#print("out card proj: " + str(qp_dict[node + "_PROJ"]["out_card"]))
			
			qp_dict[node]["set_oper"] = []
			qp_dict[node]["parent_id"] = id + "_PROJ"


def parseUint(str):
	try:
		return int(str)
	except:
		return -1

def draw_tree(qp, names_set, first):
	#Step 4: Generazione albero
	lista_ocd = qp.get_ocd()
	lista_asc = qp.get_asc()
	html_albero = ""
	html_ls_nodi = ""
	html_kes = ""

	stack_nodi = []
	stack_nodi.append(get_root_node(qp))
	nodi_ordinati = []

	#Ricalcolo il query plan creandone uno "temporaneo" mergiando i nodi UDF con le relative proiezioni
	qp_draw = queryplan.query_plan() 

	for indice, nodo_tmp in qp.lista_nodi.items():
		if nodo_tmp.tipo_op == "proj" and qp.is_proj_after_udf(indice):

			nodo_udf = dict()
			id_nodo_udf = ""

			for tmp_idx_figlio, tmp_nodo_figlio in qp.lista_nodi.items():
				if tmp_nodo_figlio.id_padre == indice:
					nodo_udf = tmp_nodo_figlio
					id_nodo_udf = tmp_idx_figlio

			dn = nodo_tmp.get()
			qp_draw.lista_nodi[id_nodo_udf] = queryplan.nodo_plan(dn[0], dn[1], dn[2], dn[3], dn[4], dn[5], dn[6], dn[7], dn[8], dn[9], dn[10], dn[11], dn[12], dn[13], dn[14])
			qp_draw.lista_nodi[id_nodo_udf].tipo_op = "udf"
			qp_draw.lista_nodi[id_nodo_udf].set_attr = nodo_udf.set_attr
			qp_draw.lista_nodi[id_nodo_udf].set_oper = nodo_tmp.set_attr


		elif nodo_tmp.tipo_op != "udf":
			dn = nodo_tmp.get()
			qp_draw.lista_nodi[indice] = queryplan.nodo_plan(dn[0], dn[1], dn[2], dn[3], dn[4], dn[5], dn[6], dn[7], dn[8], dn[9], dn[10], dn[11], dn[12], dn[13], dn[14])

			
			

	#Ordino i nodi
	while len(stack_nodi) > 0:
		curr_node = stack_nodi.pop(0)
		nodi_ordinati.append(curr_node)

		for indice, nodo_tmp in qp_draw.lista_nodi.items():
			if nodo_tmp.id_padre == curr_node:
				stack_nodi.append(indice)

	for node in nodi_ordinati:
	
		i = node
		html_ls_nodi += (", " if i != get_root_node(qp_draw) else "") + "node" + (i)

		html_nodo = ""
		nodo = qp_draw.get_nodo(i)
		vp, ve, ip, ie, eq, cand, assegn, operazione, attributi, operandi, dett_op = nodo.get_profilo()
		html_nodo += "node" + (i) + " = {\n"
		html_nodo += "parent: node" + nodo.id_padre + ", " if i != get_root_node(qp_draw) else ""
		html_nodo += "innerHTML : \""
	
		if not first:
			for ocd in lista_ocd:
				if i == ocd["figlio"] and ocd["tipo_op"] == "C":
					html_nodo += "<div class='box_up'><span class='enc'>" + ", ".join(list(ocd["adc"])) + "</span></div><br/>"
	
			html_nodo += "<div class='box_left'>"

			if operazione != "base" and not qp_draw.is_proj_after_base(i):
				cand_list = "<span class='as'>" + assegn + "</span>, "
				cand.remove(assegn)
				cand_list +=  ", ".join(list(cand))
				html_nodo += cand_list + "</div>"

			else:
				html_nodo += "<span class='as'>" + assegn + "</span></div>"

		html_nodo += "<div class='box_center " + (" leaf'" if operazione == "base" else "'") + "><p class='op'>"
		#Parti di output generate in base al tipo di operazione
		if operazione == "gby":
			html_nodo += dett_op + " on " + str(operandi).replace("'", "") + ", grouping"
		else:
			html_nodo += ope_name[operazione]

		if operazione == "star":
			html_nodo

		elif operazione != "base":
			html_nodo += " on " + str(attributi).replace("'", "")

		else:
			html_nodo += names_set[list(operandi)[0]] + " (" + ", ".join(list(attributi)) + ")"
	
		html_nodo += "</p></div>"
		
		if not first:
			html_nodo += "<div class='arrow_left'></div><div class='cont_right'><div class='box_right'>"
			html_nodo += "<i>v</i>: " + ", ".join(list(vp)) + (" <span class='enc_att'>" + ", ".join(list(ve)) + "</span>" if len(ve) > 0 else "") + "<br/>"
			html_nodo += "<i>i</i>: " + ", ".join(list(ip)) + (" <span class='enc_att'>" + ", ".join(list(ie)) + "</span>" if len(ie) > 0 else "") + "<br/>"
			html_nodo += "<i>eq</i>: "
			tmp_list = []
			for eq_set in list(eq):
				tmp_list.append("{" + ", ".join(eq_set) + "}")
			html_nodo += ",".join(tmp_list)
			html_nodo += "</div></div>"

			#Parti di output generate in base all'eventuale cifratura
			for ocd in lista_ocd:
				if i == ocd["padre"] and ocd["tipo_op"] == "D":
					html_nodo += "<br/><div class='box_down'><span class='enc'>" + ", ".join(ocd["adc"]) + "</span></div>"

		html_nodo += "\"\n};\n\n"
		html_albero += html_nodo

	if not first:
		html_kes += "<div class=\"kes_cont\" id=\"kes_separator\"><span class=\"kes\"><b>Key Encryption Sets</b><ul>"
		for asc in lista_asc:
			html_kes += "<li>" + str(asc["kes"]).replace("'", "") + " - Key to be given to " + str(asc["sogg"]).replace("'", "") + "</li>\n"
		html_kes += "</ul></span></div>"

	#Salvataggio dei dati nell'html finale
	f_base_html = open('./base_html/index.html',mode='r')
	base_html = f_base_html.read()
	f_base_html.close()

	end_html = base_html.replace("{{{nodes}}}", html_albero).replace("{{{n_list}}}", html_ls_nodi).replace("{{{kes}}}", html_kes)

	html_name = ""
	if first:
		html_name = "qp_init.html"

	else:
		html_name = "qp_end.html"

	print("\nWriting file...")
	out_html = open("./output/" + html_name, "w")
	out_html.write(end_html)
	out_html.close()
	
	out_path = os.path.abspath("./output")

	print("\nFile ready to be viewed on " + out_path + "\\" + html_name)


