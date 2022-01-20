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

# Count Results for the Fast B-repair Model Repair Approach
# Usage: python [this script] [folder of fast B-repair summaries]

# =================================================

start_time = time.time()

if len(sys.argv) != 2:
    print "Error: The number of input parameters should be 1."
    print "Usage: python [this script] [folder of fast B-repair summaries]"
    exit(1)

wdir = sys.argv[1]

flist = os.listdir(wdir)
for x in flist: print x

slist = []
for x in flist:
    if ".summary" in x:
        y = wdir + "/" + x
        slist.append(y)
slist.sort()

ID = []
NUM = []
ACC = []
EPO = []
TIM = []
TIMdNUM = []

MAX_ID = 0
for fn in slist:
    MAX_ID = MAX_ID + 1
    ID.append(MAX_ID)
    f = open(fn,"r")
    p = f.readlines()
    f.close()
    p = p[1]
    p = p.replace("\n","")
    p = p.split(" ")
    NUM.append(int(p[0]))
    ACC.append(float(p[1]))
    EPO.append(int(p[2]))
    TIM.append(float(p[3]))
    TIMdNUM.append(float(p[3])/int(p[0]))

AVE_NUM = numpy.mean(NUM)
AVE_ACC = numpy.mean(ACC)
AVE_EPO = numpy.mean(EPO)
AVE_TIM = numpy.mean(TIM)
AVE_TIMdNUM = numpy.mean(TIMdNUM)

ID.append("AVE")
NUM.append(AVE_NUM)
ACC.append(AVE_ACC)
EPO.append(AVE_EPO)
TIM.append(AVE_TIM)
TIMdNUM.append(AVE_TIMdNUM)

tab_line = "--------------------------------------------------------------------------------------------"

print tab_line
print "Model ID | Num. Repairs | Accuracy | Num. Epochs | Total Time (s) | Time for Each Repair (s)"
print tab_line
for i in xrange(MAX_ID + 1):
    indend = "          "
    x = str(ID[i])
    x = x + indend + str(NUM[i])
    x = x + indend + "%.3f"%ACC[i]
    x = x + indend + str(EPO[i])
    x = x + indend + "%.3f"%TIM[i]
    x = x + indend + "%.3f"%TIMdNUM[i]
    if i == MAX_ID:
        print tab_line
    print x
print tab_line


