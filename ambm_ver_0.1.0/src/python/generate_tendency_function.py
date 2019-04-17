import sys
import Bmch
import os
import time
import Bgenlib
import random

#python src/python/generate_tendency_function.py ${tmp_folder}/0/${mdl_name}.mch ${tmp_folder}/tendency/${mdl_name}_trset.mch ${tmp_folder}/tendency/${mdl_name}_trset.statespace.dot ${tmp_folder}/tendency/data.txt ${tmp_folder}/tendency/tendency.mdl ${tendency_model} || exit 1;


if len(sys.argv) != 4:
    print "Error: The number of input parameters should be 4."
    exit(1)

mchfile = sys.argv[1]
tendfolder = sys.argv[2]
conffile = sys.argv[3]


print "Input (Pretty-Printed) Mch File:", mchfile
print "Tendency Function Folder:", tendfolder
print "Configuration File:", conffile

outfile = tendfolder + "/trset.mch"
sgfile = tendfolder + "/trset.statespace.dot"
dsfile = tendfolder + "/data.txt"
tmfile = tendfolder + "/tendency.mdl"
tmtype = Bmch.read_config(conffile,"tendency_model","str")


#nnetfile = sys.argv[5]

with open(mchfile) as mchf:
    mch = mchf.readlines()
mch = [x.strip() for x in mch]


# Note: the following two functions have been complete, but are not used now.
"""
sd = Bmch.get_enum_sets(mch)
sds = Bmch.convert_enum_sets_to_types(sd)
print sds
"""

additional_sampling = Bmch.read_config(conffile,"additional_sampling","bool")

if additional_sampling == True:
  print "\nUse additional sampling.\n"
  trsetmch = Bmch.generate_training_set_machine(mch,"")
else:
  print "\nNot use additional sampling.\n"
  trsetmch = mch

bscope = Bmch.generate_training_set_condition(mch)

Bmch.print_mch_to_file(trsetmch,outfile)


max_num_sampling_states = Bmch.read_config(conffile,"max_num_sampling_states","int")
max_operations = Bmch.read_config(conffile,"max_operations","int")

print "\nMaximum number of samples is", max_num_sampling_states, ".\n"

# "-mc 100 and -p MAX_INITIALISATIONS 100" works well. But now I am trying more initialisations. 
genmode = "-mc %d -mc_mode random -p MAX_INITIALISATIONS %d -p RANDOMISE_ENUMERATION_ORDER TRUE -p MAX_OPERATIONS %d -p MAX_DISPLAY_SET -1"%(max_num_sampling_states,max_num_sampling_states,max_operations)

# We still need to carefully examine the performance of ProB-SMT and KODKOD.
# When search space is small, NO-SMT, ProB-SMT and KODKOD have similar speed.
#smtmode = "-p KODKOD TRUE -p SMT TRUE -p CLPFD TRUE"
smtmode = ""

mkgraph = "./../ProB/probcli %s %s -nodead -scope \"%s\" -spdot %s %s -c"%(outfile,genmode,bscope,sgfile,smtmode)

os.system(mkgraph)

sg = Bgenlib.BStateGraphForNN()
sg.ReadStateGraph(sgfile)

TL =  sg.GetTransList()

SType = sg.GetSetTypeFromTransList(TL)

OpeList = Bmch.get_all_ope_names(mch)
dt = sg.TransListToData(TL,SType,OpeList)


# The following functions are for the House Example in the FMSD paper.
def FMSD_House_Set_Latex(x):
    if x == [[]]: res = "\{ \}"
    else:
        res = "\{ "
        p = x[0]
        for r in p:
            res = res + str(r) + " , "
        res = res[0:-2] + " \}"
    return res
def FMSD_House_Sampling(TL,dt,OL,ST):

    TBList = []
    print len(dt)
    print len(TL)
    for i in xrange(len(TL)):
        x = TL[i]
        p = x[0]
        f = x[1]
        q = x[2]
        fsym = " \\xrightarrow{%s} "%str(f)
        y = "$ " + FMSD_House_Set_Latex(p) + fsym + FMSD_House_Set_Latex(q) + " $"
        y = y.replace("_","\_")
        z = dt[i]
        TBList.append([str(f),y,z])
    TBList.sort()       

    for x in TBList: 
        print x[1]
        print x[2]
        

    print "\n\nThe state graph of sampling machine is: \n\n"
    for x in TBList: print x[1]
    print "\n\nThe features of samplings are: \n\n"

    for x in TBList: print x[2]

    print "\n\nThe list of operations is: \n\n"
    for x in OL: print x
    print "\n\nThe type of variable is: \n\n"
    for x in ST: print x
    return 0

dt_fmsd = sg.FMSDTransListToData(TL,SType,OpeList)

FMSD_House_Sampling(TL,dt_fmsd,OpeList,SType)

"""
sg.WriteDataToTxt(dt[0],"train.txt")
sg.WriteDataToTxt(dt[1],"valid.txt")
sg.WriteDataToTxt(dt[2],"eval.txt")
"""

from nnet.nnetlib import *
from Cartlib import *
from NBayes import *
from SKCART import *
import numpy
import logging
import pickle


if tmtype == "Logistic":

    # ============== Logistic Model Section ==============

    tr_data = dt[0]+dt[1]+dt[2]
    nnet_idim = len(tr_data[0][0])
    nnet_odim = len(OpeList)
    file_head = ["feat_dim=%d\n"%nnet_idim,"num_opes=%d\n"%nnet_odim]

    sg.WriteDataToTxt(file_head,tr_data,dsfile)

    logging.basicConfig()
    tr_log = logging.getLogger("mlp.optimisers")
    tr_log.setLevel(logging.DEBUG)

    rng = numpy.random.RandomState([2018,03,31])
    rng_state = rng.get_state()

    num_tr_data = len(tr_data)

    lrate = Bmch.read_config(conffile,"logistic_lrate","float")
    max_epochs = Bmch.read_config(conffile,"logistic_max_epochs","int")
    batch_size = Bmch.read_config(conffile,"logistic_minibatch_size","int")

    #max_epochs = 1000
    #lrate = lrate * 2

    BNNet = BLogistic_Init([nnet_idim, nnet_odim], rng)
    lr_scheduler = LearningRateFixed(learning_rate=lrate, max_epochs=max_epochs)
    #lr_scheduler = LearningRateNewBob(start_rate = lrate, scale_by = 0.5, min_derror_ramp_start = -0.1, min_derror_stop = 0, patience = 100, max_epochs = max_epochs)
    dp_scheduler = None #DropoutFixed(p_inp_keep=1.0, p_hid_keep=0.9)
    BNNet, Tr_Stat, Cv_Stat = BNNet_Train(BNNet, lr_scheduler, dsfile, dsfile, dp_scheduler, batch_size = batch_size)

    BNNet.MType = "Logistic"
    BNNet.SType = SType
    BNNet.OpeList = OpeList

    print "Writing logistic tendency model to %s."%tmfile
    filehandler = open(tmfile, 'w')
    pickle.dump(BNNet, filehandler)
    print "Tendency model has been written to the file."

elif tmtype == "ResNet":

    # ============== ResNet Net Section ==============

    tr_data = dt[0]+dt[1]+dt[2]
    nnet_idim = len(tr_data[0][0])
    nnet_odim = len(OpeList)
    file_head = ["feat_dim=%d\n"%nnet_idim,"num_opes=%d\n"%nnet_odim]

    sg.WriteDataToTxt(file_head,tr_data,dsfile)

    logging.basicConfig()
    tr_log = logging.getLogger("mlp.optimisers")
    tr_log.setLevel(logging.DEBUG)

    rng = numpy.random.RandomState([2018,03,31])
    rng_state = rng.get_state()

    num_tr_data = len(tr_data)

    lrate = Bmch.read_config(conffile,"resnet_lrate","float")
    max_epochs = Bmch.read_config(conffile,"resnet_max_epochs","int")
    batch_size = Bmch.read_config(conffile,"resnet_minibatch_size","int")
    num_hid = Bmch.read_config(conffile,"resnet_num_hid","int")
    num_layers = Bmch.read_config(conffile,"resnet_num_layers","int")

    #lrate = lrate * 2
    #max_epochs = 1000

    BNNet = BResNet_Init([nnet_idim, num_hid, num_layers, nnet_odim], rng)
    lr_scheduler = LearningRateFixed(learning_rate=lrate, max_epochs=max_epochs)
    #lr_scheduler = LearningRateNewBob(start_rate = lrate, scale_by = 0.5, min_derror_ramp_start = -0.1, min_derror_stop = 0, patience = 100, max_epochs = max_epochs)
    dp_scheduler = None #DropoutFixed(p_inp_keep=1.0, p_hid_keep=0.9)
    BNNet, Tr_Stat, Cv_Stat = BNNet_Train(BNNet, lr_scheduler, dsfile, dsfile, dp_scheduler, batch_size = batch_size)

    BNNet.MType = "ResNet"
    BNNet.SType = SType
    BNNet.OpeList = OpeList

    print "Writing ResNet tendency model to %s."%tmfile
    filehandler = open(tmfile, 'w')
    pickle.dump(BNNet, filehandler)
    print "Tendency model has been written to the file."

elif tmtype == "CART":

    # ============== Classification and Regression Tree Section ==============

    tr_data = dt[0]+dt[1]+dt[2]

    num_tree = Bmch.read_config(conffile,"cart_num_tree","int")
    min_var_exp = Bmch.read_config(conffile,"cart_min_var_exp","int")
    max_var_exp = Bmch.read_config(conffile,"cart_max_var_exp","int")
    data_prop = Bmch.read_config(conffile,"cart_data_prop","float")
    use_mp = Bmch.read_config(conffile,"cart_use_mp","bool")

    CARTree = RandMultiRegTree(data=tr_data, num_tree=num_tree, min_var_exp_scale=[min_var_exp,max_var_exp], data_prop=data_prop, use_mp=use_mp)

    CARTree.MType = "CART"    
    CARTree.SType = SType
    CARTree.OpeList = OpeList

    print "Writing CART tendency model to %s."%tmfile
    filehandler = open(tmfile, 'w')
    pickle.dump(CARTree, filehandler)
    print "Tendency model has been written to the file."


elif tmtype == "BNBayes":

    # ============== Bernoulli Naive Bayes Section ==============

    tr_data = dt[0]+dt[1]+dt[2]

    #num_tree = Bmch.read_config(conffile,"cart_num_tree","int")
    #min_var_exp = Bmch.read_config(conffile,"cart_min_var_exp","int")
    #max_var_exp = Bmch.read_config(conffile,"cart_max_var_exp","int")
    #data_prop = Bmch.read_config(conffile,"cart_data_prop","float")
    #use_mp = Bmch.read_config(conffile,"cart_use_mp","bool")

    BNB = BNBayes(data=tr_data,conffile=conffile)
    
    BNB.MType = "BNBayes"    
    BNB.SType = SType
    BNB.OpeList = OpeList

    print "Writing BNBayes tendency model to %s."%tmfile
    filehandler = open(tmfile, 'w')
    pickle.dump(BNB, filehandler)
    print "Tendency model has been written to the file."

elif tmtype == "SKCART":

    # ============== Scikit-learn CARTs Section ==============

    tr_data = dt[0]+dt[1]+dt[2]

    #num_tree = Bmch.read_config(conffile,"cart_num_tree","int")
    #min_var_exp = Bmch.read_config(conffile,"cart_min_var_exp","int")
    #max_var_exp = Bmch.read_config(conffile,"cart_max_var_exp","int")
    #data_prop = Bmch.read_config(conffile,"cart_data_prop","float")
    #use_mp = Bmch.read_config(conffile,"cart_use_mp","bool")

    RF = SKCART(data=tr_data,conffile=conffile)
    
    RF.MType = "SKCART"    
    RF.SType = SType
    RF.OpeList = OpeList

    print "Writing BNBayes tendency model to %s."%tmfile
    filehandler = open(tmfile, 'w')
    pickle.dump(RF, filehandler)
    print "Tendency model has been written to the file."




else:
    print "Not Implemented Error!"
    Not_Implemented_Error
