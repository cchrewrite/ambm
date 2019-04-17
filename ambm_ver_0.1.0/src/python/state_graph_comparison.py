import sys
import Bmch
import os
import time
import Bgenlib
import random


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

print "Reading State Graph 2..."
sg2 = Bgenlib.BStateGraphForNN()
sg2.ReadStateGraph(sgfile2)
TL2 =  sg2.GetTransList()

print "Comparing two state graphs..."
num_same = 0
num_diff_1_to_2 = 0
num_diff_2_to_1 = 0

for x in TL1:
    if x in TL2:
        num_same = num_same + 1
    else:
        num_diff_1_to_2 = num_diff_1_to_2 + 1
        #print x

print "====="

for x in TL2: 
    if x in TL1:
        continue
    else:
        num_diff_2_to_1 = num_diff_2_to_1 + 1
        #print x

num_st_1 = len(TL1)
num_st_2 = len(TL2)

print "======== RESULT ========"
print "Number of State Transitions in Machine 1:", num_st_1
print "Number of State Transitions in Machine 2:", num_st_2
print "Number of Common State Transitions:", num_same
print "Number of Different State Transitions (Graph 1 - Graph 2):", num_diff_1_to_2
print "Number of Different State Transitions (Graph 2 - Graph 1):", num_diff_2_to_1
print "Total Difference:", num_diff_1_to_2 + num_diff_2_to_1


resfile = resdir + "/result"
f = open(resfile,"w")
r = [num_st_1, num_st_2, num_same, num_diff_1_to_2, num_diff_2_to_1, num_diff_1_to_2 + num_diff_2_to_1]

for x in r:
    f.write("%s "%x)
f.close()


