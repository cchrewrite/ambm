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
import time

# ==================================================

# The Abstract Machine Batch Modification Approach
# Usage: python [this script] [source abstract machine] [semantics model] [oracle] [configuration file] [result folder]

# =================================================

start_time = time.time()

if len(sys.argv) != 6:
    print "Error: The number of input parameters should be 5."
    print "Usage: python [this script] [source abstract machine] [semantics model] [oracle file] [configuration file] [result folder]"
    exit(1)



M = sys.argv[1]
W = sys.argv[2]
G = sys.argv[3]
conffile = sys.argv[4]
resdir = sys.argv[5]

print "Source Abstract Machine:", M
print "Semantics Model:", W
print "Oracle File:", G
print "Configuration File:", conffile
print "Result Folder:", resdir

print "Data Preparation..."

cmd = "mkdir %s"%resdir
os.system(cmd)

s = resdir + "/source.mch"
cmd = "cp %s %s"%(M,s)
os.system(cmd)
M = s


if W == "NEW":
    print "====== Training a New Semantics Model ======"
    sdir = resdir + "/SemMdlDir/"
    SemLearnLib.TrainingSemanticsModel(M,conffile,sdir)
    cmd = "mv %s/semantics.mdl %s/semantics.mdl"%(sdir,resdir)
    os.system(cmd)
    s = resdir + "/semantics.mdl"
    W = s
else:
    s = resdir + "/semantics.mdl"
    cmd = "cp %s %s"%(W,s)
    os.system(cmd)
    W = s

filehandler = open(W,'r')
W = pickle.load(filehandler)

s = resdir + "/oracle.txt"
cmd = "cp %s %s"%(G,s)
os.system(cmd)
G = s

s = resdir + "/config"
cmd = "cp %s %s"%(conffile,s)
os.system(cmd)
conffile = s

"""
fn = resdir + "/M_pp.mch"
oscmd = "./../ProB/probcli -pp %s %s"%(fn,M)
os.system(oscmd)
M = fn
"""

print "Reading Oracle File..."

G = Bmch.read_oracle_file(G)

print "====== MCSS <-- MonteCarloStateSampling(M) ======"

mcdir = resdir + "/MCSS/"
MCSS = SemLearnLib.MonteCarloStateSampling(M,W,conffile,mcdir)

print "====== MR <-- M ======"

sdir = resdir + "/0/"
cmd = "mkdir %s"%sdir
os.system(cmd)
MR = sdir + "/MR.mch"
cmd = "cp %s %s"%(M,MR)
os.system(cmd)

print "====== CMP <-- {} ======"
CMP = []

print "====== RS <-- {} ======"
RS = []

print "====== while True: ======"

epoch = 0
max_num_repair_epochs = Bmch.read_config(conffile,"max_num_repair_epochs","int")

while True:

    print "====== D <-- StateDiagram(MR) ======"

    fn = sdir + "/MR_pp.mch"
    oscmd = "./../ProB/probcli -pp %s %s"%(fn,MR)
    os.system(oscmd)
    MR = fn

    with open(MR) as mchf:
        mch = mchf.readlines()
    mch = [x.strip() for x in mch]

    D = sdir + "/D.txt"
    max_initialisations = Bmch.read_config(conffile,"max_initialisations","int")
    max_operations = Bmch.read_config(conffile,"max_operations","int")
    bscope = Bmch.generate_training_set_condition(mch)
    oscmd = "./../ProB/probcli %s -model_check -df -p MAX_DISPLAY_SET -1 -p MAX_INITIALISATIONS %d -p MAX_OPERATIONS %d -nodead -scope \"%s\" -spdot %s -c"%(MR,max_initialisations,max_operations,bscope,D)
    os.system(oscmd)

    sg = Bgenlib.BStateGraphForNN()
    sg.ReadStateGraph(D)
    TL = sg.GetTransList()
    VList = sg.GetVbleList()

    print "====== SF <-- FaultyStates(D) + (ProhibitedStates(G) * AllStates(D)) ======"
    FSD = sg.GetStatesWithoutOutgoingTransitions(TL)
    PSG = [] # ProhibitedStates(D,G)
    ASD = RepSimpLib.extract_all_states(TL)
    SF = FSD + Bmch.list_intersect(PSG,ASD)
    SF = Bmch.remove_duplicate_elements(SF)

    print "====== TF <-- FaultyTransitions(D,SF) + (ProhibitedTransitions(D) * D) ======"
    FTDSF = sg.GetTransitionsWithPostStates(TL,SF)
    PTD = [] # ProhibitedTransitions(D)
    TF = FTDSF + Bmch.list_intersect(PTD,D)
    TF = Bmch.remove_duplicate_elements(TF)
 
    if TF == []:
        print "====== if TF is {} then break endif ======"
        print "No faulty transition found. The model has been repaired."
        break


    print "====== SREV <-- AllStates(D) + EnabledStates(G) + MonteCarloStateSampling(M) - ProhibitedStates(G) - SF ======"
    
    ESG = [] # EnabledStates(G)

    SREV = ASD + ESG + MCSS
    SREV = Bmch.list_difference(SREV,PSG)
    SREV = Bmch.list_difference(SREV,SF)
    SREV = Bmch.remove_duplicate_elements(SREV)

    print "====== RREV <-- Revision(TF,SREV) ======"
    RREV = Bmch.RevisionSynthesis(TF,SREV)
    #for x in RREV: print x

    print "====== RISO <-- Isolation(TF) ======"
    RISO = Bmch.IsolationSynthesis(TF)
    #for x in RISO: print x

    print "====== RSEL <-- RepairSelection(W, RISO + RREV) ======"
   
    revdir = sdir + "/revision/"
    cmd = "mkdir %s"%revdir
    os.system(cmd)
 
    REVP = SemLearnLib.ScoreRevisionsUsingSemanticsModel(W,RREV,revdir)
    for i in xrange(len(RREV)):
        RREV[i].append(REVP[i])
    #for x in RREV: print x
    
    RSEL = SemLearnLib.ClassifyAndSortRepairs(RREV + RISO)

    if "ANSWER" in G[0]:
        print "====== \"ANSWER\" in G ======"
        print "====== CMP <-- CMP + CompareRevisionWithAnswer(RSEL,G) ======"
        RVA = SemLearnLib.CompareRevisionWithAnswer(RSEL,G)
        CMP = CMP + RVA

        print "====== R <--- GetRepairAnswer(RSEL,G) ======"
        R = SemLearnLib.GetRepairAnswer(RSEL,G)
        print "====== RB <--- GetBestRepair(RSEL) ======"
        RB = SemLearnLib.GetBestRepair(RSEL)
        print "====== RS <--- RS + RB ======"
        RS = RS + RB
        #for x in RB: print x
        #raw_input("RSEL")
        #for x in R: print x
        #raw_input("R")
        
    else:
        num_displayed_repairs = Bmch.read_config(conffile,"num_displayed_repairs","int")
        pppp

    R = Bmch.convert_changes_to_substitutions(R,VList)

    print "====== MR <-- Update(MR,R) ======"
    #subs_list = Bmch.convert_changes_to_substitutions(R,VList)
    for x in R:
        op = x[0]
        cond = x[1]
        subs = x[2]
        mch = Bmch.apply_A_change(mch,op,cond,subs)

    epoch = epoch + 1
    pdir = sdir + ""
    sdir = resdir + "/" + str(epoch) + "/"
    cmd = "mkdir %s"%sdir
    os.system(cmd)

    fn = sdir + "/MR.mch"
    Bmch.print_mch_to_file(mch,fn)
    MR = fn

    print "Epoch", epoch, "done. Resulting machine is", fn

    if epoch > max_num_repair_epochs:
        epoch = -1
        break

    #x = raw_input("press any symbol + Enter to continue.")


CFG_flag = Bmch.read_config(conffile,"apply_CFG_simplification","bool")

if CFG_flag == True:

    print "====== RCFG <--- CFGRepairSimplification(RS,D) ======"
    cgfdir = sdir + "/CFGGeneration/"
    RCFG = RepSimpLib.CFGRepairSimplification(RS,TL,VList,conffile,cgfdir)
    NumMRep = len(RCFG)
    #RCFG = Bmch.convert_changes_to_substitutions(RCFG,VList)

    print "====== MCFG <--- Update(M,RCFG) ======"

    M = resdir + "/0/MR_pp.mch"
    with open(M) as mchf:
        mch = mchf.readlines()
    mch = [x.strip() for x in mch]
    
    for x in RCFG:
        op = x[0]
        cond = x[1]
        subs = x[2]
        mch = Bmch.apply_A_change(mch,op,cond,subs)

    fn = resdir + "/result_CFG.mch"
    Bmch.print_mch_to_file(mch,fn)

else:
    NumMRep = -1


fn = resdir + "/result.mch"
cmd = "cp %s %s"%(MR,fn)
os.system(cmd)
MR = fn
print "Model Repair Done. The repaired machine is %s."%fn

print "====== ACC <-- ComputeAccuracy(CMP)  ======"

NUM = len(CMP)
ACC = 0.0
for x in CMP:
    ACC = ACC + SemLearnLib.RevisionVariableAccuracy(x[0],x[1])
ACC = ACC / NUM

end_time = time.time()
elapsed_time = end_time - start_time

print "Number of repairs is %d."%NUM
print "Number of merged repairs is %d."%NumMRep
print "Accuracy is %f."%ACC
print "Number of epochs is %d."%epoch
print "Time of repair is %f."%elapsed_time

M = sys.argv[1]
MdlType = W.MdlType

fn = resdir + "/summary"
logf = open(fn,"w")
logf.write("Machine: %s\n"%(M))
logf.write("Type of Semantics Model: %s\n"%(MdlType))
logf.write("Number of Repairs: %d\n"%(NUM))
logf.write("Number of Merged Repairs: %d\n"%(NumMRep))
logf.write("Modification Accuracy: %f\n"%(ACC))
logf.write("Number of Epochs: %d\n"%(epoch))
logf.write("Elapsed Time (s): %f\n"%(elapsed_time))
logf.close()

