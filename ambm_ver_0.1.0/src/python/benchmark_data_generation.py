from Bgenlib import *
import os

MHP = 3

for i in xrange(100):
    X = BProgram(OPE_NUM=4*MHP, VBLE_NUM=MHP, EXINV_NUM=1, COND_LEN=MHP, EXP_LEN=MHP, SUBS_NUM=4*MHP, INT_SCOPE=MHP, DIST_NUM=MHP)
    Mch = X.GenMch("RandMdl")
    for x in Mch: print x
    f = open("RandBenchmark/RandMdlMHP%dM%d.mch"%(MHP,i),"w")
    for x in Mch:
        f.write(x)
        f.write("\n")
    f.close()

