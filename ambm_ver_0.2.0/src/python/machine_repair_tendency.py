import sys
import Bmch
import os
import time
import Bgenlib
import random
from nnet.nnetlib import *
from Cartlib import *
from NBayes import *
from SKCART import *

"""
sg = Bgenlib.BStateGraphForNN()
sg.ReadStateGraph("restemp/tr_set.statespace.dot")


TL =  sg.GetTransList()

OpeList = sg.GetAllOpeNames(TL)
SType = sg.GetSetTypeFromTransList(TL)

print TL
print OpeList

mchfile = "restemp/tr_set.mch"
with open(mchfile) as mchf:
    mch = mchf.readlines()
mch = [x.strip() for x in mch]

OpeList = Bmch.get_all_ope_names(mch)
dt = sg.TransListToData(TL,SType,OpeList)

sg.WriteDataToTxt(dt[0],"train.txt")
sg.WriteDataToTxt(dt[1],"valid.txt")
sg.WriteDataToTxt(dt[2],"eval.txt")
"""

# ==============================================================

print "Repair a B-machine..."

if len(sys.argv) != 5:
    print "Error: The number of input parameters should be 4."
    exit(1)

print "Model Folder:", sys.argv[1]
print "Model Name:", sys.argv[2]
print "Tendency Model Folder:", sys.argv[3]
print "Configuration File:", sys.argv[4]
#print "Max Cost: ", sys.argv[3]
#print "User-defined Constraint File: ", sys.argv[4]
#print "Faulty Transition File: ", sys.argv[5]
#print "Revision Annotation: ", sys.argv[6]
#print "Revision Option: ", sys.argv[7]
#print "Tendency Model: ", sys.argv[8]
#print "Repair Mode: ", sys.argv[9]
# Revision Option can be "Default", "NoDead", "NoAss", "NoDeadAss", etc.

mchfile = sys.argv[1] + "/" + sys.argv[2] + ".mch"

with open(mchfile) as mchf:
    mch = mchf.readlines()
mch = [x.strip() for x in mch]

outfile = sys.argv[1] + "/" + sys.argv[2] + ".rev.mch"

ftfile = sys.argv[1] + "/" + sys.argv[2] + ".ftrans"
with open(ftfile) as ftf:
    ft = ftf.readlines()
ft = [x.strip() for x in ft]

conffile = sys.argv[4]

no_dead = Bmch.read_config(conffile,"no_dead","bool")
no_ass = Bmch.read_config(conffile,"no_ass","bool")
revision_option = "No"
if no_dead == True:
    revision_option = revision_option + "Dead"
if no_ass == True:
    revision_option = revision_option + "Ass"
if revision_option == "No":
    revision_option = "Default"
rev_opt = revision_option

max_cost = Bmch.read_config(conffile,"max_cost","int")
max_operations = Bmch.read_config(conffile,"max_operations","int")
max_num_rev = Bmch.read_config(conffile,"max_num_rev","int")

logtxt = []

import pydotplus
import pydot

from graphviz import Graph

# Make extra conditions:

fcond = ft[0]
fope = ft[1]
fstate = ft[2]

"""
revsetfilename = sys.argv[1] + ".revset"
revsetfile = open(revsetfilename,"w")
sm = Bmch.generate_revision_set_machine(mch, fstate, max_cost, rev_opt)
for item in sm:
    revsetfile.write("%s\n"%item)
revsetfile.close()

print sm

bth = 2048 #int(sys.argv[3]) + 1
mkgraph = "./../ProB/probcli -model_check -nodead -noinv -noass -p MAX_INITIALISATIONS %d -mc_mode bf -spdot %s.statespace.dot %s"%(bth,revsetfilename,revsetfilename)

os.system(mkgraph)

revset,numrev = Bmch.extract_state_revision_from_file("%s.statespace.dot"%revsetfilename, max_cost)
"""

revset,numrev = Bmch.generate_revision_set(mch, fstate, max_cost, max_operations, max_num_rev, rev_opt, mchfile)

"""
if numrev == 0:
    print "No state revision found."
    if "Dead" in rev_opt:
        while True:
            x = raw_input("Skip the revision of Operation \"%s\" and use isolation? (y/n): "%ft[1])
            if x == "y":
                iso_cond = "not( %s )"%fcond
                print "Pre-condition \"%s\" is added to Operation \"%s\"."%(iso_cond,fope)
                newmch = Bmch.add_precond_to_mch(mch,fope,iso_cond)
                Bmch.print_mch_to_file(newmch,sys.argv[2])
                print "State isolation done."
                exit()
            x = raw_input("Use a bigger cost? (y/n): ")
            if x == "y":
                temp_cost = raw_input("Please input a bigger cost: ")
                temp_cost = int(temp_cost)
                revset,numrev = Bmch.generate_revision_set(mch, fstate, temp_cost, rev_opt, sys.argv[1])
                if numrev > 0: break
    else:
        while True:

            temp_cost = raw_input("Please input a bigger cost: ")
            temp_cost = int(temp_cost)
            revset,numrev = Bmch.generate_revision_set(mch, fstate, temp_cost, rev_opt, sys.argv[1])
            if numrev > 0: break

#revset.sort(key = lambda x: Bmch.state_diff_simple(x,fstate))
"""

# Flatten the revset.
revset = [y for x in revset for y in x]

import pickle

if revset == []:
    revlist = []
else:
    tmfile = sys.argv[3] + "/" + "tendency.mdl"
    filehandler = open(tmfile, 'r')
    TModel = pickle.load(filehandler)
    
    #filehandler = open(nnetfile+".stype", 'r')
    #SType = pickle.load(filehandler)
    MType = TModel.MType
    SType = TModel.SType
    OpeList = TModel.OpeList

    RevBlock = Bgenlib.BStateGraphForNN()
    revlist = []
    for x in revset:
        u = RevBlock.GetRevValue(fcond)
        v = RevBlock.GetRevValue(x)
        uf = RevBlock.StateToVector(u,SType)
        vf = RevBlock.StateToVector(v,SType)
        revf = uf + vf
        #revs = decoderev(revf)
        revlist.append(revf)

    if MType == "ResNet" or MType == "Logistic":
        fopeid = OpeList.index(fope)
        feat = numpy.asarray(revlist)
        revlist = BNNet_Decode_Ope_Score(TModel, feat, fopeid)
    elif MType == "CART":
        fopeid = OpeList.index(fope)
        feat = numpy.asarray(revlist)
        revlist = CART_Decode_Ope_Score(TModel, feat, fopeid)
    elif MType == "BNBayes":
        fopeid = OpeList.index(fope)
        feat = numpy.asarray(revlist)
        revlist = BNBayes_Decode_Ope_Score(TModel, feat, fopeid)
    elif MType == "SKCART":
        fopeid = OpeList.index(fope)
        feat = numpy.asarray(revlist)
        revlist = SKCART_Decode_Ope_Score(TModel, feat, fopeid)
    else:
        print "Not Implemented Error!"
        Not_Implemented_Error

#revlist.sort(key=lambda x: x[1], reverse=True)
#revset = revlist

rep_mode = Bmch.read_config(conffile,"rep_mode","str")
repmode = rep_mode.lower()

if repmode != "auto":
    x = raw_input("Display sorted revisions? (y/n): ")
    if x == "y":
        for p in revlist:
            print p
            print revset[p[0]] 

flag = 0
for rid in xrange(len(revlist)):
    revidx = rid
    r = revlist[rid]
    rs = revset[r[0]]
    rp = r[1]
    if repmode == "auto" and rp < 0.5:
        flag = 2
        break
    for i in xrange(1):
        print "The faulty state transition is << %s >>  ---%s--->  << %s >>."%(fcond,fope,fstate)
        print "The faulty state is << %s >>."%fstate
        x = "a"
        if repmode == "auto":
            x = "y"
        while x != "y" and x != "n":
            x = raw_input("Do you want to revise the faulty state? (y/n): ")
        if x == "n":
            flag = 2
            break
        print "A state revision is << %s >>."%rs
        print "The cost of revision is %.2f."%float(i)
        print "Probability is %.6f."%rp
        x = "a"
        if repmode == "auto":
            x = "y"

        while x != "y" and x != "n":
            x = raw_input("Use this revision? (y/n): ")
        if x == "y":
            flag = 1
            break
    if flag == 1 or flag == 2:
        break
if flag == 0 or flag == 2:
    x = "a"
    if repmode == "auto":
        x = "y"
    while x != "y":
        x = raw_input("No revision selected / found. The faulty state will be isolated. Type \"y\" to continue: ")
    iso_cond = "not( %s )"%fcond
    print "Pre-condition \"%s\" is added to Operation \"%s\"."%(iso_cond,fope)
    newmch = Bmch.add_precond_to_mch(mch,fope,iso_cond)
    Bmch.print_mch_to_file(newmch,outfile)
    print "State isolation done."
    logtxt.append("Use Isolation.")

  
if flag == 1:
    print "Use %s as a revision."%rs
    precond = ft[0]
    #newopename = ft[1] + "_" + sys.argv[6]

    """
    print "Create a new operation: << %s >>  ---%s--->  << %s >>"%(precond,newopename,rs)

    newope = Bmch.create_new_operation(precond,newopename,rs)

    revmch = Bmch.add_new_operation(mch,newope)
    """

    subs = Bmch.gen_if_then_subs(fstate,rs)
    print "Add the revision << %s >>  ==>  << %s >> to Operation \"%s\"."%(fstate,rs,fope)
    revmch = Bmch.add_if_then_subs_to_mch(mch,fope,subs)

    Bmch.print_mch_to_file(revmch,outfile)
    print "State revision done."
    logtxt.append("Use Revision.")
    logtxt.append("%d"%revidx)


logtxt.append("Revision List:")
i = 0
for x in revlist:
    print x
    print revset[x[0]]
    logtxt.append("[%d, %.6lf]"%(i,x[1]))
    logtxt.append(revset[x[0]])
    i = i + 1
logfile = outfile + ".log"
logf = open(logfile,"w")
for x in logtxt:
    logf.write(x+"\n")
logf.close()

print "B-machine repair done. The result is in %s."%outfile
