import sys
import Bmch
import os
import time
import Bgenlib
import random
import RepSimpLib
import SemLearnLib
from Cartlib import *
from NBayes import *
from SKCART import *
import numpy
import logging
import pickle

# ==================================================

# A Maker of Faulty Machine.
# It makes a faulty B machines by randomly changing corrent transitions to faulty transitions.
# Input - source abstract machine, number of faulty transitions, seed
# Output - 
# Usage: python [this script] [source abstract machine] [number of faulty transitions] [seed] [result folder]

# =================================================

if len(sys.argv) != 5:
    print("Error: The number of input parameters should be 5.")
    print("Usage: python [this script] [source abstract machine] [number of faulty transitions] [seed] [result folder]")
    exit(1)



M = sys.argv[1]
N = sys.argv[2]
SD = sys.argv[3]
resdir = sys.argv[4]

print("Making a faulty abstract machine...")

print("Source Abstract Machine:", M)
print("Number of Faulty Transitions:", N)
print("Seed:", SD)
print("Result Folder:", resdir)

print("Data Preparation...")

N = int(N)
SD = int(SD)
random.seed(SD)

cmd = "mkdir %s"%resdir
os.system(cmd)

s = resdir + "/source.mch"
cmd = "cp %s %s"%(M,s)
os.system(cmd)
M = s

fn = resdir + "/M.mch"
oscmd = "./../ProB/probcli -pp %s %s"%(fn,M)
os.system(oscmd)
M = fn

print("====== D <-- StateDiagram(M) ======")

with open(M) as mchf:
    mch = mchf.readlines()
mch = [x.strip() for x in mch]

D = resdir + "/D.txt"
max_initialisations = 65536 #Bmch.read_config(conffile,"max_initialisations","int")
max_operations = 65536 #Bmch.read_config(conffile,"max_operations","int")
bscope = Bmch.generate_training_set_condition(mch)
oscmd = "./../ProB/probcli %s -model_check -df -p MAX_DISPLAY_SET -1 -p MAX_INITIALISATIONS %d -p MAX_OPERATIONS %d -nodead -scope \"%s\" -spdot %s -c"%(M,max_initialisations,max_operations,bscope,D)
os.system(oscmd)

sg = Bgenlib.BStateGraphForNN()
sg.ReadStateGraph(D)
D = sg.GetTransList()

#for x in D: print x
#x = raw_input("ppp")

print("====== S <-- AllStates(D) ======")

S = RepSimpLib.extract_all_states(D)

print("====== Z <-- GenerateProhibitedStates(S,N,SD) ======")

# SD has been set before.
Z = Bmch.generate_prohibited_states(S,N)

#x = raw_input("ppp")

print("====== PSI <-- ConvertProhibitedStatesToInvariants(Z) ======")
VList = sg.GetVbleList()
PSI = Bmch.convert_prohibited_states_to_invariants(Z,VList)

print("====== MF <-- AddInvariants(M,PSI) ======")

MF = Bmch.add_invariant_to_machine(mch,PSI)

print("====== RD <-- FindDeterministicTransitions(D,SD) ======")
RD = sg.FindDeterministicTransitions(D)

print("Number of Prohibited States:",len(Z))
print("Number of Deterministic Transitions:",len(RD))
#D.sort()
#for x in D: print x
#x = raw_input("press any key to continue")

print("====== RD <-- Shuffle(RD,SD) ======")

# SD has been set before.
random.shuffle(RD)

print("====== RD <-- FirstNItems(RD,N) ======")

if N > len(RD):
    print("Error: N is greater than the number of transitions in the original state diagram!")
    RaiseAnError()
RD = RD[0:N]

#for x in RD: print x
#x = raw_input("pppppp")

print("====== LC <-- RandomlyChangeTransitions(RD,Z,SD) ======")

# SD has been set before.
LC = []
#raw_input("pp")
for x in RD:
    i = int(random.random() * len(Z))
    y = x + [Z[i]]
    LC.append(y)

print("====== MF <-- ApplyChangesToMachine(MF,LC) ======")

subs_list = Bmch.convert_changes_to_substitutions(LC,VList)

for x in subs_list:
    op = x[0]
    cond = x[1]
    subs = x[2]
    MF = Bmch.apply_A_change(MF,op,cond,subs)
    """
    op = x[0]
    subs = x[1]
    MF = Bmch.add_if_then_subs_to_mch(MF,op,subs)
    """

#for x in MF: print x
#ppp

fn = resdir + "/MF.mch"
Bmch.print_mch_to_file(MF,fn)
MF = fn

fn = resdir + "/result.mch"
oscmd = "./../ProB/probcli -pp %s %s"%(fn,MF)
os.system(oscmd)
MF = fn

"""
fn = resdir + "/LC.txt"
f = open(fn,"w")
for x in LC:
    f.write(str(x))
    f.write("\n")
f.close()
LC = fn
"""

print("====== ANS <-- ConvertChangesToAnswer(LC) ======")

ANS = ["BEGIN_ANSWER"]
ANS.append("FORMAT: [ < Pre-state > , < Operation > , < Faulty Post-state > , < Correct Post-state > ]")
ANSD = []
for x in LC:
    y = [x[0],x[1],x[3],x[2]]
    ANSD.append(y)
ANSD.sort()
ANS = ANS + ANSD
ANS.append("END_ANSWER")

fn = resdir + "/answer.txt"
f = open(fn,"w")
for x in ANS:
    f.write(str(x))
    f.write("\n")
f.close()
ANS = fn

s = resdir + "/source.mch"
cmd = "cp %s %s"%(M,s)
os.system(cmd)
M = s

print("Source machine is %s."%M)
print("Changed machine has been written to %s."%MF)
print("Answer has been written to %s."%ANS)

print("Done.")

