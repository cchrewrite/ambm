import sys
import Bmch

print "Converting a state-space file from 'dot' format to plain format..."

if len(sys.argv) != 3:
    print "Error: The number of input parameters should be 2."
    exit(1)

print "Source File (Dot Format): ", sys.argv[1]
print "Output File (Plain Format): ", sys.argv[2]



spfile = sys.argv[1]

cfile = open(sys.argv[2],'w') 


import pydotplus
import pydot


pp = pydotplus.graphviz.graph_from_dot_file(spfile)
#gph = pydotplus.graph_from_dot_data(pp.to_string())

from graphviz import Graph

qq = pp.get_edge_list()
cfile.write("%d "%len(qq))
qq = pp.get_node_list()
cfile.write("%d "%len(qq))


# Compute MaxLabelLength.
maxlabellength = 0;
qq = pp.get_edge_list()
for i in xrange(len(qq)):
    x = qq[i].get_source()
    if x == 'root':
        edge_src = -1
    else:
        edge_src = int(x)
    edge_dest = int(qq[i].get_destination())
    y = qq[i].get_label()
    if y != None:
        y = y.replace('"','')
        y = y.replace("'","")
    else:
        y = 'None'
    if len(y) > maxlabellength:
        maxlabellength = len(y)

cfile.write("%d "%maxlabellength)

# Compute NumVble and MaxVbleLength.
numvble = 0;
maxvblelength = 0;
qq = pp.get_node_list()
for i in xrange(len(qq)):
    x = qq[i].get_name()
    if x == 'root':
        node_idx = -1
    elif x == 'graph':
        node_idx = -2
    else:
        node_idx = int(x)
    y = qq[i].get_label()
    y = Bmch.proc_state_label(y)
    if len(y)/2 > numvble:
        numvble = len(y)/2

    for j in xrange(len(y)):
        if j % 2 == 0:
            if len(y[j]) > maxvblelength:
                maxvblelength = len(y[j])
cfile.write("%d %d\n"%(numvble,maxvblelength))


qq = pp.get_edge_list()
for i in xrange(len(qq)):
    x = qq[i].get_source()
    if x == 'root':
        edge_src = -1
    else:
        edge_src = int(x)
    edge_dest = int(qq[i].get_destination())
    y = qq[i].get_label()
    if y != None:
        y = y.replace('"','')
        y = y.replace("'","")
    else:
        y = 'None'


    cfile.write("%d %d %s\n"%(edge_src,edge_dest,y))


qq = pp.get_node_list()
for i in xrange(len(qq)):
    x = qq[i].get_name()
    if x == 'root':
        node_idx = -1
    elif x == 'graph':
        node_idx = -2
    else:
        node_idx = int(x)
    y = qq[i].get_label()
    y = Bmch.proc_state_label(y)
    cfile.write("%d %d"%(node_idx,len(y)/2))
    for j in xrange(len(y)):
        if j % 2 == 1:
            try:
                t = int(y[j])
                cfile.write(" %d"%t)
            except ValueError:
                cfile.write(" %s"%y[j])
        else:
            
            cfile.write(" %s"%y[j])
    cfile.write("\n")

cfile.close()

if len(sys.argv) == 5:
    isocompfile.close()
    fsfile.close()

