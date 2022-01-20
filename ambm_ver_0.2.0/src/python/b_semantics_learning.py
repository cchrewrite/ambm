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

# B Semantics Learning Experiments
# Usage: python [this script] [source abstract machine] [configuration file] [result folder]

# =================================================

start_time = time.time()

if len(sys.argv) != 4:
    print("Error: The number of input parameters should be 3.")
    print("Usage: python [this script] [source abstract machine] [configuration file] [result folder]")
    exit(1)


M = sys.argv[1]
conffile = sys.argv[2]
resdir = sys.argv[3]

LogD = ["Machine: " + M + "","Config: " + conffile + ""]

print("Source Abstract Machine:", M)
print("Configuration File:", conffile)
print("Result Folder:", resdir)

print("Data Preparation...")

cmd = "mkdir %s"%resdir
os.system(cmd)

s = resdir + "/source.mch"
cmd = "cp %s %s"%(M,s)
os.system(cmd)
M = s

print("====== Training a Semantics Model ======")
sdir = resdir + "/SemMdlDir/"
R = SemLearnLib.TrainingSemanticsModel(M,conffile,sdir)
cmd = "mv %s/semantics.mdl %s/semantics.mdl"%(sdir,resdir)
os.system(cmd)
s = resdir + "/semantics.mdl"
W = s
print("====== Semantics Model Training Finished ======")

Num_Tr = R[0]
Num_Cv = R[1]
Mdl_Type = R[2]
ET = R[3]
ACC = R[4]
ROCAUC = R[5]

LogD.append("Number of Training Examples: " + str(Num_Tr))
LogD.append("Number of Validation Examples: " + str(Num_Cv))
LogD.append("Type of Semantics Model: " + str(Mdl_Type))
LogD.append("Elapsed Time (s): " + str(ET))
LogD.append("Classification Accuracy: " + str(ACC))
LogD.append("ROC-AUC: " + str(ROCAUC))

logfile = resdir + "/RESULTS"
f = open(logfile,"w")
print("Log is in %s"%logfile)
for x in LogD:
    f.write(x)
    f.write("\n")
f.close()

