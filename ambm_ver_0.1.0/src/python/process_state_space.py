import sys
import Bmch

print "Isolate a faulty state..."

if len(sys.argv) != 5:
    print "Error: The number of input parameters should be 4."
    exit(1)

print "State Space File (Dot Format): ", sys.argv[1]
print "Pretty-Printed Mch File: ", sys.argv[2]
print "Faulty Path File: ", sys.argv[3]
print "Output Mch File: ", sys.argv[4]


spfile = sys.argv[1]
mchfile = sys.argv[2]
fpfile = sys.argv[3]
outfile = open(sys.argv[4],'w')

with open(mchfile) as mchf:
    mch = mchf.readlines()
mch = [x.strip() for x in mch]


with open(fpfile) as fpf:
    fp = fpf.readlines()
fp = [x.strip() for x in fp]



import pydotplus
import pydot


pp = pydotplus.graphviz.graph_from_dot_file(spfile)
#gph = pydotplus.graph_from_dot_data(pp.to_string())

from graphviz import Graph

qq = pp.get_node_list()
for i in xrange(len(qq)):

    if qq[i].get_shape() == "doubleoctagon":
        x = qq[i].get_name()
        rr = pp.get_edge_list()
        for k in xrange(len(rr)):
            q = rr[k].get_destination()
            if q == x:
                p = rr[k].get_source()
                for u in xrange(len(qq)):
                    if qq[u].get_name() == p:
                        break
                break

        y = qq[u].get_label()
        y = Bmch.proc_state_label(y)
        fstate = Bmch.label_to_sentence(y)
        print "Faulty State is << %s >>."%fstate

        iso_cond = "not( %s )"%fstate
        fope = Bmch.get_first_token(fp[-1])
        
        print "Pre-condition \"%s\" is added to Operation \"%s\"."%(iso_cond,fope)

        newmch = Bmch.add_precond_to_mch(mch,fope,iso_cond)

        for item in newmch:
            outfile.write("%s\n"%item)
        outfile.close()
        ppp
        


        vlist = Bmch.get_var_names(mch)

        print Bmch.replace_var_with_init(mch,vlist)
        

        print Bmch.gen_b_disj(Bmch.get_all_precond(mch))
        print Bmch.get_invariants(mch)

        print Bmch.generate_revision_condition(mch)

        sm = Bmch.generate_revision_set_machine(mch)
 
        print sm
        cfile = open('initttt.mch','w')
        for item in sm:
            cfile.write("%s\n"%item)
        cfile.close()
        ppp
        negstr = "[negation,pos(0,0,0,0,0,0),"
        conjstr = "[conjunct,pos(0,0,0,0,0,0),"
        equstr = "[equal,pos(0,0,0,0,0,0),"
        idenstr = "[identifier,pos(0,0,0,0,0,0),"
        intstr = "[integer,pos(0,0,0,0,0,0),"

        initstr = "initialisation(pos(0,0,0,0,0,0),sequence(pos(0,0,0,0,0,0),["
        assstr = "assign(pos(0,0,0,0,0,0),[identifier(pos(0,0,0,0,0,0),"

        resstr = ""
        init_resstr = ""

        for j in xrange(len(y)):
            
            if j % 2 == 1:
                try:
                    t = int(y[j])
                    tmpstr = tmpstr + intstr + "%d]]"%t
                    init_tmpstr = init_tmpstr + "[integer(pos(0,0,0,0,0,0),%d)])"%t
                except ValueError:
                    if y[j] == "TRUE":
                        t = "[boolean_true,pos(0,0,0,0,0,0)]]"
                        init_t = "[boolean_true(pos(0,0,0,0,0,0))])"
                    elif y[j] == "FALSE":
                        t = "[boolean_false,pos(0,0,0,0,0,0)]]"
                        init_t = "[boolean_false(pos(0,0,0,0,0,0))])"
                    else:
                        print ("Warning: Cannot analyse %s!"%y[j])
                        t = "%s-Error!"%y[j]
                        init_t = "%s-Error!"%y[j]
                    tmpstr = tmpstr + "%s"%t
                    init_tmpstr = init_tmpstr + "%s"%init_t
            else:
                tmpstr = equstr + idenstr + "%s],"%y[j]
                init_tmpstr = assstr + "%s)],"%y[j]
            if j >= 3 and j % 2 == 1:
                resstr = conjstr + resstr + "," + tmpstr + "]"
                init_resstr = init_resstr + "," + init_tmpstr
            elif j == 1:
                resstr = tmpstr
                init_resstr = init_tmpstr

        resstr = negstr + resstr + "]."
        init_resstr = initstr + init_resstr + "]))."

        print "Print the isolation component to: ", sys.argv[3]
        isocompfile = open(sys.argv[3],'w')
        print(resstr)
        isocompfile.write(resstr)

        print "Print the initialisation form of the isolation component to: ", sys.argv[3]
        isocompfile = open(sys.argv[3] + ".init",'w')
        print(init_resstr)
        isocompfile.write(init_resstr)



    # Output the faulty state:


    if qq[i].get_shape() == "doubleoctagon":
        x = qq[i].get_name()
        y = qq[i].get_label()
        y = Bmch.proc_state_label(y)

        print "The faulty state is", y
        print "Print the faulty state to: ", sys.argv[4]
        fsfile = open(sys.argv[4],'w')
        for j in xrange(len(y)):
            fsfile.write(y[j] + '\n')

cfile.close()

if len(sys.argv) == 5:
    isocompfile.close()
    fsfile.close()

"""
import os
from graphviz import Source
spfile = open('statespace.txt', 'r')
text=spfile.read()
print text[4]
Source(text)
#print text
"""
