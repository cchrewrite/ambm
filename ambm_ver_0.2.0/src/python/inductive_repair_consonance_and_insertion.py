
import Bgenlib
import sys
import RepSimpLib
import os


if len(sys.argv) != 5:
    print "Error: The number of input parameters should be 4."
    exit(1)

print "Positive Example File: ", sys.argv[1]
print "Negative Example File: ", sys.argv[2]
print "Variable List: ",sys.argv[3]
print "Result Folder: ", sys.argv[4]

pfn = sys.argv[1]
nfn = sys.argv[2]
vlfn = sys.argv[3]
resdir = sys.argv[4]

pf = open(pfn,"r")
nf = open(nfn,"r")

pexp = []
nexp = []
for x in pf.readlines():
    pexp.append(eval(x))
for x in nf.readlines():
    nexp.append(eval(x))

vlf = open(vlfn,"r")
vble_list = []
for x in vlf.readlines():
    u = x.replace("\n","")
    vble_list.append(u)

if pexp == []:
    cfn = resdir + "/result.subs"
    cf = open(cfn,"w")
    cf.write("No Repair.\n")
    cf.close()
    exit()

pexp_source = pexp
nexp_source = nexp

print "Merging IF conditions..."
pexp = []
for x in pexp_source:
    pexp.append(x[0])
nexp = []
for x in nexp_source:
    nexp.append(x[0])


#for x in nexp: print x
#ppppppp

resdir_tmp = resdir + "/IFsimp/"

cond = RepSimpLib.merge_conditions(pexp,nexp,vble_list,resdir_tmp)

if_cond = cond

print "Done!"
print "The merged condition is \"" + if_cond + "\"."


print "Merging THEN substitutions..."

# Splitting examples by substitutions.

print "Splitting revised transitions by substitutions."
#pexp_sps = RepSimpLib.split_trans_by_subs(pexp_source,vble_list)
pexp_sps = RepSimpLib.transition_partition(pexp_source,vble_list)

#for x in pexp_sps: print x
#ppppp

# Merging each set of examples.

n = 0
SS = []
for i in xrange(len(pexp_sps)):

    SC = pexp_sps[i]
 
    pexp = []
    for x in SC[1]:
        if not (x[0] in pexp):
            pexp.append(x[0])
    pexp = sorted(pexp)

    #print "PEXP"
    #for x in pexp: print x
    #print "ENDOFPESP"

    #for x in pexp_sps:
    #    print x

    nexp = []
    for x in nexp_source:
        if x[0] in pexp:
            print "WARNING:",x[0],"has been in the positive set. Remove it from the negative set."
        if not (x[0] in nexp or x[0] in pexp):
            nexp.append(x[0])
    for j in xrange(len(pexp_sps)):
        if i == j: continue
        SP = pexp_sps[j][1]
        #print SP
        for x in SP:
            #print "LL",x
            #pppp
            if x[0] in pexp:
                print "WARNING:",x[0],"has been in the positive set. Remove it from the negative set."
            if not (x[0] in nexp or x[0] in pexp):
                nexp.append(x[0])

    nexp = sorted(nexp)

    #print "NEXP"
    #for x in nexp: print x
    #print "ENDOFNEXP"
    #x = raw_input("xxx")

    n = n + 1
    resdir_tmp = resdir + "/SUBSsimp" + str(n) + "/"
    cond = RepSimpLib.merge_conditions(pexp,nexp,vble_list,resdir_tmp)
    print cond

    subs = RepSimpLib.convert_subs_to_str(SC[0])
    
    #s = "IF " + cond + " THEN " + subs + " END"
    SS.append([cond,subs])

SS = RepSimpLib.convert_cond_subs_list_to_b(SS)

fp = resdir + "/result.subs"
f = open(fp,"w")
f.write(if_cond),
f.write("\n")
for x in SS:
    f.write(x)
    f.write("\n")

print "Merged substitutions are:"
for x in SS:
    print x

