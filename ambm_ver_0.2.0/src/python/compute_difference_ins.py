import sys
import Bmch
import os
import time
import Bgenlib
import random
import RepSimpLib

#print Bmch.read_config("Tennis.config", "num_tree", "int")

if len(sys.argv) != 4:
    print "Error: The number of input parameters should be 3."
    exit(1)

print "Mch File 1: ", sys.argv[1]
print "Mch File 2: ", sys.argv[2]
print "Result Directory: ", sys.argv[3]

mch1 = sys.argv[1]
mch2 = sys.argv[2]
resdir = sys.argv[3] 


oscmd = "mkdir %s"%(resdir)
os.system(oscmd)

oscmd = "cp %s %s/Machine1.mch"%(mch1,resdir)
os.system(oscmd)

oscmd = "cp %s %s/Machine2.mch"%(mch2,resdir)
os.system(oscmd)




print "Producing the state graph of Machine 1."

mchpp1 = "%s/Machine1_pp.mch"%resdir
sgfile1 = "%s/StateGraph1.txt"%resdir

oscmd = "./../ProB/probcli -pp %s %s/Machine1.mch"%(mchpp1,resdir)
os.system(oscmd)

with open(mchpp1) as mchf:
    mch1 = mchf.readlines()
mch1 = [x.strip() for x in mch1]


bscope1 = Bmch.generate_training_set_condition(mch1)

oscmd = "./../ProB/probcli %s -model_check -df -p MAX_DISPLAY_SET -1 -p MAX_OPERATIONS 1024 -nodead -scope \"%s\" -spdot %s -c"%(mchpp1,bscope1,sgfile1)
os.system(oscmd)


print "Producing the state graph of Machine 2."

mchpp2 = "%s/Machine2_pp.mch"%resdir
sgfile2 = "%s/StateGraph2.txt"%resdir

oscmd = "./../ProB/probcli -pp %s %s/Machine2.mch"%(mchpp2,resdir)
os.system(oscmd)

with open(mchpp2) as mchf:
    mch2 = mchf.readlines()
mch2 = [x.strip() for x in mch2]

bscope2 = Bmch.generate_training_set_condition(mch2)

oscmd = "./../ProB/probcli %s -model_check -df -p MAX_DISPLAY_SET -1 -p MAX_OPERATIONS 1024 -nodead -scope \"%s\" -spdot %s -c"%(mchpp2,bscope2,sgfile2)
os.system(oscmd)


print "Reading State Graph 1..."
sg1 = Bgenlib.BStateGraphForNN()
sg1.ReadStateGraph(sgfile1)
TL1 =  sg1.GetTransList()

vble_list = sg1.GetVbleList()

print "Reading State Graph 2..."
sg2 = Bgenlib.BStateGraphForNN()
sg2.ReadStateGraph(sgfile2)
TL2 =  sg2.GetTransList()


print "Extracting all pre-states of State Graph 2..."
ps2 = RepSimpLib.extract_all_pre_states(TL2)
print "Making Stata Graph 1U..."
init1u = RepSimpLib.initialise_vble_by_examples(vble_list,ps2)
mch1u = Bmch.replace_initialisation(mch1,init1u)

#for x in mch1u: print x

mchpp1u = "%s/Machine1U.mch"%resdir
sgfile1u = "%s/StateGraph1U.txt"%resdir

f = open(mchpp1u,"w")
for x in mch1u:
    f.write(x)
    f.write("\n")
f.close()

bscope1u = Bmch.generate_training_set_condition(mch1u)

oscmd = "./../ProB/probcli %s -model_check -df -p MAX_DISPLAY_SET -1 -p MAX_OPERATIONS 1024 -p MAX_INITIALISATIONS 65536 -nodead -scope \"%s\" -spdot %s -c"%(mchpp1u,bscope1u,sgfile1u)
os.system(oscmd)

print "Reading State Graph 1U..."
sg1u = Bgenlib.BStateGraphForNN()
sg1u.ReadStateGraph(sgfile1u)
TL1u =  sg1u.GetTransList()

print "Computing transitions that need to be revised..."

ope_list = []
for x in TL2:
    if not(x[1] in ope_list):
        ope_list.append(x[1])
for x in TL1u:
    if not(x[1] in ope_list):
        ope_list.append(x[1])

rev_list = []
for y in TL2:
    for x in TL1u:
        if x[0] == y[0] and x[1] == y[1]:
            if not(y in TL1u):
                rev_list.append(y)
            break


"""
revs = []
for i in xrange(len(ope_list)):
    s = []
    for x in rev_list:
        if x[1] != ope_list[i]: continue
        p = x[0]
        f = x[1]
        q = x[2]
        r = []
        for j in xrange(len(p)):
            if p[j] == q[j]: continue
            z = vble_list[j] + " = " + q[j]
            r.append(z)

        s.append([p,f,r])
    s = sorted(s)
    revs.append([ope_list[i],s])

"""



revs = []
for i in xrange(len(ope_list)):
    s = []
    for x in rev_list:
        if x[1] != ope_list[i]: continue 
        if not(x in s): s.append(x)
    s = sorted(s)
    revs.append([ope_list[i],s])


for x in revs:
    print x[0]
    for y in x[1]:
        print y
    



print "Computing transitions that are not revised..."

kep_list = []
for y in TL1u + TL2:
    flag = 0
    for x in rev_list:
        if y[0] == x[0] and y[1] == x[1]:
            flag = 1
            break
    if flag == 0:
        kep_list.append(y)

for x in kep_list: print x

keps = []
for i in xrange(len(ope_list)):
    s = []
    for x in kep_list:
        if x[1] != ope_list[i]: continue
        if not(x in s): s.append(x)
    s = sorted(s)
    keps.append([ope_list[i],s])

"""
for x in keps:
    print x[0]
    for y in x[1]:
        print y
"""
#for x in TL1u: print x

fn = resdir + "/variable_list"
f = open(fn,"w")
for x in vble_list:
    f.write(x)
    f.write("\n")
f.close()

fn = resdir + "/operation_list"
f = open(fn,"w")
for x in ope_list:
    f.write(x)
    f.write("\n")
f.close()

for i in xrange(len(ope_list)):


    p = ope_list[i]
    p_exp = []
    for j in xrange(len(revs)):
        if revs[j][0] == p:
            p_exp = revs[j][1]
            break
    n_exp = []
    for j in xrange(len(keps)):
        if keps[j][0] == p:
            n_exp = keps[j][1]
            break

    p_exp.sort()
    n_exp.sort()

    print "Pos:"
    for x in p_exp: print x
    print "Neg:"
    for x in n_exp: print x

    pfn = resdir + "/" + p + "_rev.p"
    nfn = resdir + "/" + p + "_rev.n"
    pf = open(pfn,"w")
    nf = open(nfn,"w")
    for x in p_exp:
        pf.write(str(x))
        pf.write("\n")
    for x in n_exp:
        nf.write(str(x))
        nf.write("\n")
    pf.close()
    nf.close()


