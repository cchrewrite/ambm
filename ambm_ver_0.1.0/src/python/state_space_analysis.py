import sys
import Bmch

print "Analysing a state space..."

if len(sys.argv) != 6:
    print "Error: The number of input parameters should be 5."
    exit(1)

print "State Space File (Dot Format): ", sys.argv[1]
print "Input Pretty-Printed Mch File: ", sys.argv[2]
print "Faulty Path File: ", sys.argv[3]
print "Output Mch File (Please ignore this file): ", sys.argv[4]
print "Output Faulty Transition File: ", sys.argv[5]

spfile = sys.argv[1]
mchfile = sys.argv[2]
fpfile = sys.argv[3]
outfile = sys.argv[4]
ftfile = open(sys.argv[5],'w')

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

# Get the faulty operation.
fope = Bmch.get_first_token(fp[-1])

# Process and output..
qq = pp.get_node_list()
for i in xrange(len(qq)):

    if qq[i].get_shape() == "doubleoctagon":
        x = qq[i].get_name()
        rr = pp.get_edge_list()
        fopelabel = "\"%s\""%fp[-1]
        for k in xrange(len(rr)):
            print Bmch.get_label_pretty(rr[k]), fopelabel
            if Bmch.get_label_pretty(rr[k]) != fopelabel: continue
            q = rr[k].get_destination()
            if q == x:
                kt = k
                p = rr[k].get_source()
                for u in xrange(len(qq)):
                    print "sssssssssss"
                    print p
                    print qq[u].get_name()
                    if qq[u].get_name() == p:
                        ut = u
                        break
                break

        y = Bmch.get_label_pretty(qq[ut])
        y = Bmch.proc_state_label(y)
        fcond = Bmch.label_to_sentence(y)
        z = Bmch.get_label_pretty(qq[i])
        z = Bmch.proc_state_label(z)
        fstate = Bmch.label_to_sentence(z)
        
        print "Faulty Transition is << %s >>  ---%s--->  << %s >>."%(fcond,fope,fstate)
        ftfile.write("%s\n"%fcond)
        ftfile.write("%s\n"%fope)
        ftfile.write("%s\n"%fstate)
        ftfile.close()

        """
        iso_cond = "not( %s )"%fcond

        print "Pre-condition \"%s\" is added to Operation \"%s\"."%(iso_cond,fope)

        newmch = Bmch.add_precond_to_mch(mch,fope,iso_cond)

        Bmch.print_mch_to_file(newmch,outfile)
        """
        print "State space analysis done." 
        exit()
