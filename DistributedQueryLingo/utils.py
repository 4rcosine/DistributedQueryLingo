#Modulo delle Utilities (funzioni ad uso comune)
from email import utils
import os
import platform
import problem_info

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
			
		if "any" in subj_json:
			del subj_json["any"]

	return subj_json


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
	#Ordino i nodi
	while len(stack_nodi) > 0:
		curr_node = stack_nodi.pop(0)
		nodi_ordinati.append(curr_node)

		for indice, nodo_tmp in qp.lista_nodi.items():
			if nodo_tmp.id_padre == curr_node:
				stack_nodi.append(indice)

	for node in nodi_ordinati:
	
		i = node
		html_ls_nodi += (", " if i != get_root_node(qp) else "") + "node" + (i)

		html_nodo = ""
		nodo = qp.get_nodo(i)
		vp, ve, ip, ie, eq, cand, assegn, operazione, attributi, operandi, dett_op = nodo.get_profilo()
		html_nodo += "node" + (i) + " = {\n"
		html_nodo += "parent: node" + nodo.id_padre + ", " if i != get_root_node(qp) else ""
		html_nodo += "innerHTML : \""
	
		if not first:
			for ocd in lista_ocd:
				if i == ocd["figlio"] and ocd["tipo_op"] == "C":
					html_nodo += "<div class='box_up'><span class='enc'>" + ", ".join(list(ocd["adc"])) + "</span></div><br/>"
	
			html_nodo += "<div class='box_left'>"

			if operazione != "base" and not qp.is_proj_after_base(i):
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

	out_html = open("./output/" + html_name, "w")
	out_html.write(end_html)
	out_html.close()

	print("\nOpening file...")
	if platform.system() == "Darwin":
		os.system("open ./output/" + html_name)
	else:
		os.system("start ./output/" + html_name)


