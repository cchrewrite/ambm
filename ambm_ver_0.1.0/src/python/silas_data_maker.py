import sys
import Bmch
import os
import time
import Bgenlib
import random


if len(sys.argv) != 4:
    print "Error: The number of input parameters should be 3."
    print "Usage: python %s xx.mch xx.config resultdir"%sys.argv[0]
    exit(1)

mchfile = sys.argv[1]
conffile = sys.argv[2]
resfolder = sys.argv[3]


print "Input (Pretty-Printed) Mch File:", mchfile
print "Configuration File:", conffile
print "Working Folder:", resfolder


ff = resfolder + "/source.mch"
cmd = "./../ProB/probcli -pp %s %s"%(ff,mchfile)
os.system(cmd)
mchfile = ff

ff = resfolder + "/config"
cmd = "cp %s %s"%(conffile,ff)
os.system(cmd)
conffile = ff

outfile = resfolder + "/trset.mch"
sgfile = resfolder + "/trset.statespace.dot"
dsfile = resfolder + "/data.txt"

#nnetfile = sys.argv[5]

with open(mchfile) as mchf:
    mch = mchf.readlines()
mch = [x.strip() for x in mch]

# Note: the following two functions have been complete, but are not used now.
"""
sd = Bmch.get_enum_sets(mch)
sds = Bmch.convert_enum_sets_to_types(sd)
print sds
"""

additional_sampling = Bmch.read_config(conffile,"additional_sampling","bool")

if additional_sampling == True:
  print "\nUse additional sampling.\n"
  trsetmch = Bmch.generate_training_set_machine(mch,"")
else:
  print "\nNot use additional sampling.\n"
  trsetmch = mch

bscope = Bmch.generate_training_set_condition(mch)

Bmch.print_mch_to_file(trsetmch,outfile)


max_num_sampling_states = Bmch.read_config(conffile,"max_num_sampling_states","int")
max_operations = Bmch.read_config(conffile,"max_operations","int")

print "\nMaximum number of samples is", max_num_sampling_states, ".\n"

# "-mc 100 and -p MAX_INITIALISATIONS 100" works well. But now I am trying more initialisations. 
genmode = "-mc %d -mc_mode random -p MAX_INITIALISATIONS %d -p RANDOMISE_ENUMERATION_ORDER TRUE -p MAX_OPERATIONS %d -p MAX_DISPLAY_SET -1"%(max_num_sampling_states,max_num_sampling_states,max_operations)

# We still need to carefully examine the performance of ProB-SMT and KODKOD.
# When search space is small, NO-SMT, ProB-SMT and KODKOD have similar speed.
#smtmode = "-p KODKOD TRUE -p SMT TRUE -p CLPFD TRUE"
smtmode = ""

mkgraph = "./../ProB/probcli %s %s -nodead -scope \"%s\" -spdot %s %s -c"%(outfile,genmode,bscope,sgfile,smtmode)

os.system(mkgraph)

sg = Bgenlib.BStateGraphForNN()
sg.ReadStateGraph(sgfile)

TL =  sg.GetTransList()

TL = sg.SortSetsInTransList(TL)

SType = sg.GetSetTypeFromTransList(TL)
VList = sg.GetVbleList()

rd_seed = Bmch.read_config(conffile,"rd_seed","int")
neg_prop = Bmch.read_config(conffile,"neg_prop","float")

SilasData = sg.SilasTransListToData(TL,SType,VList,neg_prop,rd_seed)

VData = SilasData[0]
FData = SilasData[1:len(SilasData)]
print len(FData)

random.seed(rd_seed)
random.shuffle(FData)

num_tr = int(len(FData) * 0.8)


TrainingData = [VData] + FData[0:num_tr]
TestData = [VData] + FData[num_tr:len(FData)]

fname = resfolder + "/train.csv"
Bgenlib.write_list_to_csv(TrainingData,fname)
fname = resfolder + "/test.csv"
Bgenlib.write_list_to_csv(TestData,fname)

