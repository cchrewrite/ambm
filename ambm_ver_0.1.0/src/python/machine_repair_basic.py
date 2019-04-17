import sys
import Bmch
import os
import time

print "Repair a B-machine..."

if len(sys.argv) != 8:
    print "Error: The number of input parameters should be 7."
    exit(1)

print "Input (Pretty-Printed) Mch File: ", sys.argv[1]
print "Output Mch File: ", sys.argv[2]
print "Max Cost: ", sys.argv[3]
print "User-defined Constraint File: ", sys.argv[4]
print "Faulty Transition File: ", sys.argv[5]
print "Revision Annotation: ", sys.argv[6]
print "Revision Option: ", sys.argv[7]
# Revision Option can be "Default", "NoDead", "NoAss", "NoDeadAss", etc.

mchfile = sys.argv[1]

mch = Bmch.read_mch_file(mchfile)

outfile = sys.argv[2]

ftfile = sys.argv[5]
with open(ftfile) as ftf:
    ft = ftf.readlines()
ft = [x.strip() for x in ft]

rev_opt = sys.argv[7]

import pydotplus
import pydot

from graphviz import Graph

# Make extra conditions:

max_cost = int(sys.argv[3])
fcond = ft[0]
fope = ft[1]
fstate = ft[2]

autorev = True

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

revset,numrev = Bmch.generate_revision_set(mch, fstate, max_cost, rev_opt, sys.argv[1])

if numrev == 0:
    print "No state revision found."
    temp_cost = max_cost
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
                if autorev == True:
                    temp_cost = temp_cost * 2
                else:
                    temp_cost = raw_input("Please input a bigger cost: ")
                temp_cost = int(temp_cost)
                revset,numrev = Bmch.generate_revision_set(mch, fstate, temp_cost, rev_opt, sys.argv[1])
                if numrev > 0: break
    else:
        while True:
            if autorev == True:
                temp_cost = temp_cost * 2
            else:
                temp_cost = raw_input("Please input a bigger cost: ")
            temp_cost = int(temp_cost)
            revset,numrev = Bmch.generate_revision_set(mch, fstate, temp_cost, rev_opt, sys.argv[1])
            if numrev > 0: break

#revset.sort(key = lambda x: Bmch.state_diff_simple(x,fstate))

flag = 0
for i in xrange(len(revset)):
    for rs in revset[i]:
        print "The faulty state transition is << %s >>  ---%s--->  << %s >>."%(fcond,fope,fstate)
        print "The faulty state is << %s >>."%fstate
        x = "a"
        while x != "y" and x != "n":
            if autorev == True:
                x = "y"
                break
            x = raw_input("Do you want to revise the faulty state? (y/n): ")
        if x == "n":
            flag = 2
            break
        print "A state revision is << %s >>."%rs
        print "The cost of revision is %.2f."%float(i)
        x = "a"
        while x != "y" and x != "n":
            if autorev == True:
                x = "y"
                break
            x = raw_input("Use this revision? (y/n): ")
        if x == "y":
            flag = 1
            break
    if flag == 1 or flag == 2:
        break
if flag == 0:
    print "Error: No state revision are selected!"
    exit()
if flag == 2:
    print "Skip the revision and only isolate this state."
    iso_cond = "not( %s )"%fcond
    print "Pre-condition \"%s\" is added to Operation \"%s\"."%(iso_cond,fope)
    newmch = Bmch.add_precond_to_mch(mch,fope,iso_cond)
    Bmch.print_mch_to_file(newmch,sys.argv[2])
    print "State isolation done."
    exit()
  

print "Use %s as a revision."%rs
precond = ft[0]
newopename = ft[1] + "_" + sys.argv[6]

"""
print "Create a new operation: << %s >>  ---%s--->  << %s >>"%(precond,newopename,rs)

newope = Bmch.create_new_operation(precond,newopename,rs)

revmch = Bmch.add_new_operation(mch,newope)
"""

subs = Bmch.gen_if_then_subs(fstate,rs)

print "Add the revision << %s >>  ==>  << %s >> to Operation \"%s\"."%(fstate,rs,fope)
revmch = Bmch.add_if_then_subs_to_mch(mch,fope,subs)

Bmch.print_mch_to_file(revmch,outfile)

print "B-machine repair done. The result is in %s."%outfile
