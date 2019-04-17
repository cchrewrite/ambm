import sys
import Bmch
import os
import time
import Bgenlib
import random
from nnet.nnetlib import *

# ==============================================================

print "Sort a counting result list..."
print ""

if len(sys.argv) != 2:
    print "Error: The number of input parameters should be 1."
    exit(1)

print "Inputfile ", sys.argv[1]

fname = sys.argv[1]
infile = open(fname,"r")

rlist = []
i = 0
for x in infile.readlines():
    i = i + 1
    if i <= 2: continue
    y = x.split()
    print y
    rlist.append([y[0],int(y[1]),int(y[2])])

rlist = sorted(rlist, key=lambda x: x[2])

print "RESULT:"
print "FILE   NUM_ST   NUM_TR"
for x in rlist:
    print x[0], x[1], x[2]

resfp = fname + "_Sorted"
resfile = open(resfp,"w")
resfile.write("RESULT:\n")
resfile.write("FILE   NUM_ST   NUM_TR\n")
for x in rlist:
    y = "%s %s %s\n"%(x[0], x[1], x[2])
    resfile.write(y)
resfile.close()
