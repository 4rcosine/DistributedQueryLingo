attr_info = []
subj_info = []
nodes_info = []

def add_attr_info(name, size, enceff):
    attr = { "name" : name.upper(), "size" : str(size), "enceff" : str(enceff)}
    attr_info.append(attr)

def add_subj_info(name, compcost, encrcost, decrcost, transfcost):
    subj = { "name" : name.upper(), "compcost" : str(compcost), "encrcost" : str(encrcost), "decrcost" : str(decrcost), "transfcost" : str(transfcost)}
    subj_info.append(subj)

def add_node_info(name, icard, ocard, opcost, nasize):
    node = { "name" : name.upper(), "icard" : str(icard), "ocard" : str(ocard), "opcost" : str(opcost), "nasize" : str(nasize)}
    nodes_info.append(node)