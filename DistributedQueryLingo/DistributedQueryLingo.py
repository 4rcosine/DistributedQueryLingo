
import queryplan
import json
import utils
import sys
import os
import problem_info
import utils
import webbrowser

#Step 0: Inizializzazione
lista_tab_json = []
pri_dict = {}
names_set = dict()

print("--------------------------------------------")
print("    Secure Query Distribution Calculator    ")
print("--------------------------------------------")

#if not os.path.exists(utils.lingo_path):
#	print("An error occurred during the loading of the configuration: lingo executable not found at path '" + utils.lingo_path + "'")
#	input()
#	sys.exit(-1)

#Richiesta input
#print("The following configurations are available: ")
#configs = json.load(conf_json)
#k = 1
#for confs in configs:
#	print("\n\t" + str(k) + ") " + confs["conf_name"], end='')
#	k += 1
#
#scelta = 0
#while not (int(scelta) >= 1 and int(scelta) < k ):
#	scelta = utils.parseUint(input("\n\nPlease choose one configuration (type a number from 1 to " + str(k-1) + "): "))
#
#	if not (int(scelta) >= 1 and int(scelta) < k ):
#		print("Invalid option.")

curr_dir = utils.get_cur_dir()

conf_json = os.path.join(curr_dir, sys.argv[1]) if not os.path.isabs(sys.argv[1]) else sys.argv[1]

if not os.path.exists(conf_json):
	print("An error occurred during the loading of the configuration: configuration file not found at path '" + conf_json + "'")
	input()
	sys.exit(-1)

#Leggo i dati dalla configurazione
try:
	config = json.load(open(conf_json))
	print("\r\nConfgiuration loaded: " + config["conf_name"])
	#Per ogni tabella nelle configurazioni leggo relativi file descrittivi e di autorizzazioni
	for table in config["tables"]:
		f1 = open(table["table_file"])
		t_file = json.load(f1)
		a_file = json.load(open(table["auth_file"]))
		t_file["permissions"] = a_file["permissions"]
		lista_tab_json.append(t_file)
		names_set[t_file["name"].upper()] = t_file["fullName"].upper()

		#Per ogni attributo della tabella valorizzo le info inerenti all'attributo (nome, size, eff. cifr.)
		if(len(t_file["attributes"]) == len(t_file["attr_sizes"]) and len(t_file["attributes"]) == len(t_file["attr_enc_eff"])):
			for i in range(len(t_file["attributes"])):
				problem_info.add_attr_info(t_file["attributes"][i], t_file["attr_sizes"][i], t_file["attr_enc_eff"][i])

		else:
			raise Exception("Attribute info number mismatch")

	#Per ogni soggetto valorizzo le info inerenti
	si_dict = json.load(open(config["subject_file"]))
	user_found = False
	for subj in si_dict:
		problem_info.add_subj_info(subj, si_dict[subj]["comp_cost"], si_dict[subj]["encr_cost"], si_dict[subj]["decr_cost"], si_dict[subj]["transf_cost"])

		if subj == "U":
			user_found = True

	if not user_found:
		problem_info.add_subj_info("U", 999, 999, 999, 999)

	#Per ogni nodo valorizzo le info inerenti
	qp_dict = json.load(open(config["query_file"]))
	last_outcard = 0

	utils.fix_udf(qp_dict)

	for node in qp_dict:
		problem_info.add_node_info(node, qp_dict[node]["in_card"], qp_dict[node]["out_card"], qp_dict[node]["op_cost"], qp_dict[node]["na_size"])
		if qp_dict[node]["parent_id"] == "":
			last_outcard = qp_dict[node]["out_card"]

	problem_info.add_node_info("UNODE", last_outcard, 0, 0, 0)

except Exception as ex :
	print("An error occurred during the loading of the configuration. Most common errors are: \n- bad json format\n- files specified do not exist\n- attribute array and info arrays have different length (e.g. for a table 4 attributes are specified but enc. eff. is specified for only three of them)\n\nExiting the program")
	print(ex)
	sys.exit(-1)


subj_dict = utils.build_initial_json(lista_tab_json)

qp = queryplan.query_plan() 

for chiave, valore in qp_dict.items():
	qp.add_nodo(chiave, valore["op_type"], valore["op_detail"], set(valore["set_attr"]), set(valore["set_oper"]), set(valore["set_attrplain"]), valore["parent_id"], valore["order"])

qp.add_star_node()
qp.set_subj(subj_dict)

#Eventualmente disegno l'albero
#scelta = ""
#while scelta != "n" and scelta != "y":
#	scelta = input("Do you want to draw the initial query tree plan? [y/n]: ").lower()

#	if scelta != "n" and scelta != "y":
#		print("Invalid option.") 

#if scelta == "y":
utils.draw_tree(qp, names_set, True)

#Step 1: Calcolo dei candidati
id_primo_nodo = utils.get_root_node(qp)
qp.calc_cand_rec(id_primo_nodo)

#########################################################
#Step 3: Output
print("\n============================\n\tOUTPUT\n============================\n\n")
lista_ocd = qp.get_ocd()
lista_asc = qp.get_asc()

for node in problem_info.nodes_info:
	i = node["name"]
	nodo = qp.get_nodo(i)
	vp, ve, ip, ie, eq, cand, assegn, operazione, attributi, operandi, dett_op = nodo.get_profilo()
	print("Node: " + str(i))
	
	
	#Parti di output generate in base al tipo di operazione
	if operazione == "gby":
		print("-> Operation: " + dett_op + " on " + str(operandi).replace("'", "") + ", grouping", end='')
	else:
		print("-> Operation: " + utils.ope_name[operazione], end='')

	if operazione != "base":
		print(" on " + str(attributi).replace("'", ""), end='')

	else:
		print(" " + names_set[list(operandi)[0]], end='')
	
	print("")

	if operazione != "base" and not qp.is_proj_after_base(i):
		print("-> Candidates: " + str(cand).replace("'", ""))

	print("-> Assignee: " + assegn)
	#Parti di output generate in base all'eventuale cifratura
	for ocd in lista_ocd:
		if i == ocd["figlio"] and ocd["tipo_op"] == "C":
			print("-> Encryption of " + str(ocd["adc"]).replace("'", ""))

		if i == ocd["padre"] and ocd["tipo_op"] == "D":
			print("-> Decryption of " + str(ocd["adc"]).replace("'", ""))

	print("\n\tvp: " + str(list(vp)).replace("'", "") + "\n\tve: " + str(list(ve)).replace("'", "") + "\n\tip: " + str(list(ip)).replace("'", "") + "\n\tie: " + str(list(ie)).replace("'", "") + "\n\teq: " + str(list(eq)).replace("'", ""))

	print("\n=====================\n")
########################################################

#Step 2: Estensione queryplan
qp.assign_and_extend()

#Step 2: Ricalcolo degli attributi impliciti queryplan
qp.calc_impl_rec(id_primo_nodo)

#Step 3: Output
print("\n============================\n\tOUTPUT\n============================\n\n")
lista_ocd = qp.get_ocd()
lista_asc = qp.get_asc()

for node in problem_info.nodes_info:
	i = node["name"]
	nodo = qp.get_nodo(i)
	vp, ve, ip, ie, eq, cand, assegn, operazione, attributi, operandi, dett_op = nodo.get_profilo()
	print("Node: " + str(i))
	
	
	#Parti di output generate in base al tipo di operazione
	if operazione == "gby":
		print("-> Operation: " + dett_op + " on " + str(operandi).replace("'", "") + ", grouping", end='')
	else:
		print("-> Operation: " + utils.ope_name[operazione], end='')

	if operazione != "base":
		print(" on " + str(attributi).replace("'", ""), end='')

	else:
		print(" " + names_set[list(operandi)[0]], end='')
	
	print("")

	if operazione != "base" and not qp.is_proj_after_base(i):
		print("-> Candidates: " + str(cand).replace("'", ""))

	print("-> Assignee: " + assegn)
	#Parti di output generate in base all'eventuale cifratura
	for ocd in lista_ocd:
		if i == ocd["figlio"] and ocd["tipo_op"] == "C":
			print("-> Encryption of " + str(ocd["adc"]).replace("'", ""))

		if i == ocd["padre"] and ocd["tipo_op"] == "D":
			print("-> Decryption of " + str(ocd["adc"]).replace("'", ""))

	print("\n\tvp: " + str(list(vp)).replace("'", "") + "\n\tve: " + str(list(ve)).replace("'", "") + "\n\tip: " + str(list(ip)).replace("'", "") + "\n\tie: " + str(list(ie)).replace("'", "") + "\n\teq: " + str(list(eq)).replace("'", ""))

	print("\n=====================\n")

print("\r\n=== KEY ENCRYPTION SETS ===")
for asc in lista_asc:
	print(" • " + str(asc["kes"]).replace("'", "") + " - Key to be given to " + str(asc["sogg"]).replace("'", ""))

print("\nEnd of computation\n\n")

#Eventualmente disegno l'albero
scelta = ""
#while scelta != "n" and scelta != "y":
#	scelta = input("Do you want to draw the resulting query tree plan? [y/n]: ").lower()

#	if scelta != "n" and scelta != "y":
#		print("Invalid option.") 

#if scelta == "y":
utils.draw_tree(qp, names_set, False)
	
temp_in = ""
while temp_in != "exit" and temp_in != "show":
	print("\n=====================\n")
	print("The computation has reached its end. Type 'show' to show the resulting trees in browser, or type 'exit' to exit the program.")
	print("\n=====================")
	print("Choice: ", end="")
	temp_in = input()

	if temp_in == "show":
		webbrowser.open("file://" + os.path.realpath("./output/qp_init.html"))
		webbrowser.open("file://" + os.path.realpath("./output/qp_end.html"))