import sys
import Bmch
import os
import time
import Bgenlib
import random
import RepSimpLib
import SemLearnLib
import numpy
import logging
import pickle
import time

# ==================================================

# Collect machine information such as file name and lines of codes (LOC).
# Usage: python [this script] [source folder] [result folder]

# =================================================

if len(sys.argv) != 3:
    print "Error: The number of input parameters should be 2."
    print "Usage: python [this script] [source folder] [result folder]"
    exit(1)


mchdir = sys.argv[1]
resdir = sys.argv[2]
print "Source Folder:", mchdir
print "Result Folder:", resdir

print "Data Preparation..."

cmd = "mkdir %s"%resdir
os.system(cmd)

wdir = resdir + "/pretty_printed_machines"
cmd = "mkdir %s"%wdir
os.system(cmd)

sdir = resdir + "/source_machines"
cmd = "mkdir %s"%(sdir)
os.system(cmd)

FL = os.listdir(mchdir)

D = []
for fn in FL:
    if fn[len(fn)-4:len(fn)] != ".mch":
        continue

    mchfile = mchdir + "/" + fn
    sfile = sdir + "/" + fn
    cmd = "cp %s %s"%(mchfile,sfile)
    os.system(cmd)



    ppfile = wdir + "/" + fn

    cmd = "./../ProB/probcli -model_check -p MAX_INITIALISATIONS 204800 -p MAX_OPERATIONS 204800 -pp %s %s"%(ppfile,sfile)
    #os.system(cmd)
    S = os.popen(cmd)
    S = S.read()
    print S
    S = S.split("\n")
    NS = -1
    NT = -1
    for x in S:
        if "States analysed:" in x:
            NS = x.replace("States analysed:","")
            NS = int(NS)
        if "Transitions fired:" in x:
            NT = x.replace("Transitions fired:","")
            NT = int(NT)
    if NS > 0 and NT > 0:
        NST = NS + NT
    else:
        NST = -1
    ppmch = open(ppfile,"r")
    X = ppmch.readlines()
    ppmch.close()
    N = len(X)
    D.append([fn,N,NST])
    print fn,N,NST

D.sort()
fn = resdir + "/RESULTS"
f = open(fn,"w")
f.write("FILE NAME | LINES OF CODES (LOC) | SIZE \n")
for x in D:
    f.write("%s %d %d\n"%(x[0],x[1],x[2]))
f.close()
    

