import sys
import Bmch
import os
import time
import Bgenlib
import random
from nnet.nnetlib import *

# ==============================================================

print "Count the number of states and transitions of B-machines in a directory..."
print ""

if len(sys.argv) != 2:
    print "Error: The number of input parameters should be 1."
    exit(1)

print "Directory: ", sys.argv[1]

"""
print "Output Mch File: ", sys.argv[2]
print "Max Cost: ", sys.argv[3]
print "User-defined Constraint File: ", sys.argv[4]
print "Faulty Transition File: ", sys.argv[5]
print "Revision Annotation: ", sys.argv[6]
print "Revision Option: ", sys.argv[7]
print "BNNet Model: ", sys.argv[8]
# Revision Option can be "Default", "NoDead", "NoAss", "NoDeadAss", etc.
"""

fdir = sys.argv[1]
fnames = os.listdir(fdir)
fnames.sort()

res = []
for x in fnames:
    if not(".mch" in x): continue
    fp = fdir + x
    
    print "Counting %s..."%fp
    print "Converting mch file to a pretty-printed version."

    mchfile = fp+"_tmpfileforcount"
    xt = "./../ProB/probcli %s -timeout 5000 -pp %s"%(fp,mchfile)

    os.system(xt)

    st,tr,fs = Bmch.CountMchStateAndTrans(mchfile)
    res.append([x,st,tr,fs])
    os.system("rm %s"%mchfile)


print "RESULT:"
print "FILE   NUM_ST   NUM_TR   NUM_FS"
for x in res:
    print x[0], x[1], x[2], x[3]

resfp = fdir + "RESULT"
resfile = open(resfp,"w")
resfile.write("RESULT:\n")
resfile.write("FILE   NUM_ST   NUM_TR   NUM_FS\n")
for x in res:
    y = "%s %s %s %s\n"%(x[0], x[1], x[2], x[3])
    resfile.write(y)
resfile.close()
