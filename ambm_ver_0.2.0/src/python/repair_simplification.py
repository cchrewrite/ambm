import sys
import Bmch
import os
import time
import Bgenlib
import random


#print Bmch.read_config("Tennis.config", "num_tree", "int")

if len(sys.argv) != 4:
    print "Error: The number of input parameters should be 3."
    exit(1)

print "Source Machine: ", sys.argv[1]
print "Target Machine: ", sys.argv[2]
print "Result Directory: ", sys.argv[3]

MS = sys.argv[1]
MT = sys.argv[2]

resdir = sys.argv[3]

# Preparing files.

probcli = "./../ProB/probcli"

oscmd = "rm -r " + resdir
os.system(oscmd)
oscmd = "mkdir " + resdir
os.system(oscmd)

fn = resdir + "/MS.mch"
oscmd = "cp %s %s"%(MS,fn)
os.system(oscmd)
MS = fn

fn = resdir + "/MT.mch"
oscmd = "cp %s %s"%(MT,fn)
os.system(oscmd)
MT = fn

probcli = "./../ProB/probcli"
fn = resdir + "/MS_pp.mch"
oscmd = probcli + " -pp %s %s || exit 1; "%(fn,MS)
os.system(oscmd)
MS = fn


# Phase 1.
print "======= Phase 1: Consonance ======="

with open(MS) as mchf:
    mch = mchf.readlines()
mch = [x.strip() for x in mch]

condir = resdir + "/consonance"
oscmd = "python src/python/compute_consonance_transitions.py %s %s %s"%(MS,MT,condir)
os.system(oscmd)

print "\n==== RC <-- Inductive_Repair(PC,NC,'consonance') ====\n\nAND\n\n==== MSC <-- Update(MS,RC) ====\n"

olfn = condir + "/operation_list"
olf = open(olfn,"r")
ope_list = []
for x in olf.readlines():
    ope_list.append(x[0:len(x)-1])


for ope in ope_list:
    tmpdir = condir + "/induction_" + ope
    oscmd = "rm -r " + tmpdir
    os.system(oscmd)
    oscmd = "mkdir " + tmpdir
    os.system(oscmd)

    pfn = condir + "/" + ope + ".p"
    nfn = condir + "/" + ope + ".n"
    vfn = condir + "/variable_list"

    oscmd = "python src/python/inductive_repair_consonance_and_insertion.py %s %s %s %s"%(pfn,nfn,vfn,tmpdir)
    os.system(oscmd)


    cfn = tmpdir + "/result.subs"
    cf = open(cfn,"r")
    rep = cf.readlines()

    for x in rep: print x

    cond = rep[0]
    cond = cond[0:len(cond)-1]
    subs = rep[1:len(rep)]
    for i in xrange(len(subs)):
        subs[i] = subs[i][0:len(subs[i])-1]
    cf.close()



    if cond == "No Repair.":
        print "No repair applied to \"%s\"."%ope
        x = "a"
        while x != "y":
            x = raw_input("Confirm? (y/n): ")
        continue
    else:
        print "Applying \"%s ==> %s\" to \"%s\"."%(cond,subs,ope)
        x = "a"
        while x != "y":
            x = raw_input("Confirm? (y/n): ")
        mch = Bmch.update_consonance(mch,ope,cond,subs)

    for x in mch: print x
    print cond

MSC = resdir + "/MSC.mch"
Bmch.print_mch_to_file(mch,MSC)


#ppp
#MSC = MS

# Phase 2.
print "======= Phase 2: Insertion ======="

with open(MSC) as mchf:
    mch = mchf.readlines()
mch = [x.strip() for x in mch]

condir = resdir + "/insertion"
oscmd = "python src/python/compute_insertion_transitions.py %s %s %s"%(MSC,MT,condir)
os.system(oscmd)


print "\n==== RI <-- Inductive_Repair(PI,NI,'insertion') ====\n\nAND\n\n==== MSCI <-- Update(MSC,RI) ====\n"

olfn = condir + "/operation_list"
olf = open(olfn,"r")
ope_list = []
for x in olf.readlines():
    ope_list.append(x[0:len(x)-1])


for ope in ope_list:
    tmpdir = condir + "/induction_" + ope
    oscmd = "rm -r " + tmpdir
    os.system(oscmd)
    oscmd = "mkdir " + tmpdir
    os.system(oscmd)

    pfn = condir + "/" + ope + ".p"
    nfn = condir + "/" + ope + ".n"
    vfn = condir + "/variable_list"

    oscmd = "python src/python/inductive_repair_consonance_and_insertion.py %s %s %s %s"%(pfn,nfn,vfn,tmpdir)
    os.system(oscmd)


    cfn = tmpdir + "/result.subs"
    cf = open(cfn,"r")
    rep = cf.readlines()

    for x in rep: print x

    cond = rep[0]
    cond = cond[0:len(cond)-1]
    subs = rep[1:len(rep)]
    for i in xrange(len(subs)):
        subs[i] = subs[i][0:len(subs[i])-1]
    cf.close()



    if cond == "No Repair.":
        print "No repair applied to \"%s\"."%ope
        x = "a"
        while x != "y":
            x = raw_input("Confirm? (y/n): ")
        continue
    else:
        print "Applying \"%s ==> %s\" to \"%s\"."%(cond,subs,ope)
        x = "a"
        while x != "y":
            x = raw_input("Confirm? (y/n): ")
        mch = Bmch.update_insertion(mch,ope,cond,subs)

    for x in mch: print x
    print cond

MSCI = resdir + "/MSCI.mch"
Bmch.print_mch_to_file(mch,MSCI)

#MSCI = resdir + "MSCI.mch"

# Step 3.


print "======= Phase 3: Deletion ======="

with open(MSCI) as mchf:
    mch = mchf.readlines()
mch = [x.strip() for x in mch]

condir = resdir + "/deletion"
oscmd = "python src/python/compute_deletion_transitions.py %s %s %s"%(MSCI,MT,condir)
os.system(oscmd)

print "\n==== RD <-- Inductive_Repair(PD,ND,'deletion') ====\n\nAND\n\n==== MR <-- Update(MSCI,RD) ====\n"

olfn = condir + "/operation_list"
olf = open(olfn,"r")
ope_list = []
for x in olf.readlines():
    ope_list.append(x[0:len(x)-1])


for ope in ope_list:
    tmpdir = condir + "/induction_" + ope
    oscmd = "rm -r " + tmpdir
    os.system(oscmd)
    oscmd = "mkdir " + tmpdir
    os.system(oscmd)

    pfn = condir + "/" + ope + ".p"
    nfn = condir + "/" + ope + ".n"
    vfn = condir + "/variable_list"

    oscmd = "python src/python/inductive_repair_deletion.py %s %s %s %s"%(pfn,nfn,vfn,tmpdir)
    os.system(oscmd)


    cfn = tmpdir + "/result.cond"
    cf = open(cfn,"r")
    cond = cf.readlines()
    cond = cond[0]
    cond = cond[0:len(cond)-1]
    cf.close()



    if cond == "No Repair.":
        print "No repair applied to \"%s\"."%ope
        x = "a"
        while x != "y":
            x = raw_input("Confirm? (y/n): ")
        continue
    else:
        print "Applying \"%s\" to \"%s\"."%(cond,ope)
        x = "a"
        while x != "y":
            x = raw_input("Confirm? (y/n): ")
        mch = Bmch.add_precond_to_mch(mch,ope,cond)

    for x in mch: print x
    print cond

MR = resdir + "/result_MR.mch"
Bmch.print_mch_to_file(mch,MR)

print "======= Phase 4: Comparison ======="
compdir = resdir + "/compdir/"
cmd = "python src/python/state_graph_comparison.py %s %s %s"%(MR,MT,compdir)
os.system(cmd)

print "Done."

