import sys
import Bmch
import os
import time
import Bgenlib
import random

if len(sys.argv) != 4:
    print "Error: The number of input parameters should be 3."
    exit(1)

mchfile = sys.argv[1]
conffile = sys.argv[2]
resfolder = sys.argv[3]

probcli = "./../ProB/probcli"

print "Input Mch File: ", mchfile
print "Configuration File: ", conffile
print "Result Folder: ", resfolder

if "-" in mchfile:
    print "Error: the mch file name should not contain any \"-\"!"
    exit()

if mchfile[-4:len(mchfile)] != ".mch":
    print "Error: the mch file should be \".mch\" file!"
    exit()

cmd = "rm -r " + resfolder
os.system(cmd)
cmd = "mkdir " + resfolder
os.system(cmd)


p = mchfile.split("/")
mdl_name = p[-1][0:len(p[-1])-4]
print "\nModel name is: ", mdl_name

tendency_model = Bmch.read_config(conffile,"tendency_model","str")

orgmchfile = "%s/%s.mch"%(resfolder,mdl_name)
orgconffile = "%s/%s_%s.config"%(resfolder,mdl_name,tendency_model)
cmd = "cp %s %s"%(mchfile,orgmchfile)
os.system(cmd)
cmd = "cp %s %s"%(conffile,orgconffile)
os.system(cmd)
mchfile = orgmchfile
conffile = orgconffile

num_epoch = Bmch.read_config(conffile,"num_epoch","int")
max_cost = Bmch.read_config(conffile,"max_cost","int")
no_dead = Bmch.read_config(conffile,"no_dead","bool")
no_ass = Bmch.read_config(conffile,"no_ass","bool")
tendency_model = Bmch.read_config(conffile,"tendency_model","str")
rep_mode = Bmch.read_config(conffile,"rep_mode","str")
max_initialisations = Bmch.read_config(conffile,"max_initialisations","int")
max_operations = Bmch.read_config(conffile,"max_operations","int")

#tendency_model=ResNet
#tendency_model=CART
#tendency_model=Logistic
#rep_mode=Auto



#revision_option = "No"
mc_opt = " "

if no_dead == True:
    #revision_option = revision_option + "Dead"
    mc_opt = mc_opt + " -nodead"


if no_ass == True:
    #revision_option = revision_option + "Ass"
    mc_opt = mc_opt + " -noass"

#if revision_option == "No":
  #revision_option = "Default"

print "Checking the original machine \'%s\'. Results are in \'%s\'."%(mchfile,resfolder)

cmd = "mkdir %s/0"%(resfolder)
os.system(cmd)
orgfile = "%s/0/%s_original.mch"%(resfolder,mdl_name)

cmd = "cp %s %s"%(mchfile,orgfile)
os.system(cmd)

prefix = "%s/0/%s"%(resfolder,mdl_name)
allstate = prefix + ".allstate"
history = prefix + ".history"
statespace = prefix + ".statespace.dot"
ppfile = prefix + ".mch"
logfile = prefix + ".pl.log"

cmd = probcli + " -model_check -df %s -save %s -his %s -spdot %s -pp %s -l %s -p MAX_DISPLAY_SET -1 -p MAX_INITIALISATIONS %d -p MAX_OPERATIONS %d -c %s || exit 1; "%(mc_opt,allstate,history,statespace,ppfile,logfile,max_initialisations,max_operations,orgfile)
os.system(cmd)

print "Generating the tendency model."


tendfolder = "%s/tendency"%resfolder

cmd = "mkdir " + tendfolder
os.system(cmd)

prefix = "%s/tendency/%s"%(resfolder,mdl_name)

cmd = "python src/python/generate_tendency_function.py %s %s %s"%(ppfile,tendfolder,conffile)
os.system(cmd)

new_mdl_name = mdl_name

for j in xrange(1,num_epoch+1):
  p = j - 1
  
  cmd = "test -s " + history
  ffg = os.system(cmd)
  if ffg == 0:
    # If there is a faulty path...
    print "A faulty path found in %s."%new_mdl_name
    print " ------ Epoch %d start: ------"%j

    old_mdl_name = new_mdl_name
    old_prefix = "%s/%d/%s"%(resfolder,p,old_mdl_name)

    cmd = "python src/python/state_space_analysis.py %s.statespace.dot %s.mch %s.history %s.temp %s.ftrans || exit 1; "%(old_prefix,old_prefix,old_prefix,old_prefix,old_prefix)
    os.system(cmd)

    mdl_folder = "%s/%d"%(resfolder,p)

    cmd = "python src/python/machine_repair_tendency.py %s %s %s %s || exit 1; "%(mdl_folder,old_mdl_name,tendfolder,conffile)
    os.system(cmd)

    new_mdl_name = old_mdl_name
    new_folder = "%s/%d"%(resfolder,j)
    cmd = "mkdir %s"%new_folder
    os.system(cmd)
    
    cmd = "cp %s/%s.rev.mch %s/%s_original.mch"%(mdl_folder,old_mdl_name,new_folder,new_mdl_name)
    os.system(cmd)




    # Check the new machine.
    print "Checking the revision..."

    prefix = "%s/%s"%(new_folder,new_mdl_name)
    allstate = prefix + ".allstate"
    history = prefix + ".history"
    statespace = prefix + ".statespace.dot"
    ppfile = prefix + ".mch"
    logfile = prefix + ".pl.log"
    orgfile = "%s/%s_original.mch"%(new_folder,mdl_name)

    cmd = probcli + " -model_check -df %s -save %s -his %s -spdot %s -pp %s -l %s -p MAX_DISPLAY_SET -1 -p MAX_INITIALISATIONS %d -p MAX_OPERATIONS %d -c %s || exit 1; "%(mc_opt,allstate,history,statespace,ppfile,logfile,max_initialisations,max_operations,orgfile)
    os.system(cmd)

    print "------ End of Epoch %d. ------"%j

  else:
    # If no faulty path exists, then break.
    cmd = "cp %s/%d/%s.mch %s/result.%s.mch"%(resfolder,p,new_mdl_name,resfolder,mdl_name)
    os.system(cmd)
    cmd = "echo %d > %s/num_epoch"%(p,resfolder)
    os.system(cmd)
    rtf = Bmch.read_config(conffile,"remove_temp_files","bool")
    if rtf == True:
        print "Removing temporary files."
        for u in xrange(p+1):
            cmd = "rm -r %s/%d"%(resfolder,u)
            os.system(cmd)
    print "Model %s.mch has been repaired. Results is %s/result.%s.mch"%(mdl_name,resfolder,mdl_name)
    break


