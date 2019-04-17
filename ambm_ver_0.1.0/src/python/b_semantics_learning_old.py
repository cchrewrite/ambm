import sys
import Bmch
import os
import time
import Bgenlib
import random

# ==================================================

# This script is for an experiment for semantic learning
# Usage: python [this script] [training data] [test data] [configuration file] [result folder]

# =================================================

if len(sys.argv) != 5:
    print "Error: The number of input parameters should be 4."
    exit(1)



training_data = sys.argv[1]
test_data = sys.argv[2]
conffile = sys.argv[3]
resdir = sys.argv[4]

print "Training Data:", training_data
print "Test Data", test_data
print "Configuration File:", conffile


from nnet.nnetlib import *
from Cartlib import *
from NBayes import *
from SKCART import *
import numpy
import logging
import pickle

cmd = "mkdir %s"%resdir
os.system(cmd)

s = resdir + "/train.csv"
cmd = "cp %s %s"%(training_data,s)
os.system(cmd)
training_data = s

s = resdir + "/test.csv"
cmd = "cp %s %s"%(test_data,s)
os.system(cmd)
test_data = s

s = resdir + "/config"
cmd = "cp %s %s"%(conffile,s)
os.system(cmd)
conffile = s


tmtype = Bmch.read_config(conffile,"tendency_model","str")
sg = Bgenlib.BStateGraphForNN()
SData = sg.ReadCSVSemanticsData([training_data,test_data])

train_txt = resdir + "/train80.txt"
valid_txt = resdir + "/valid20.txt"
test_txt = resdir + "/test.txt"

sp100 = len(SData[0])
sp80 = int(sp100 * 0.8)
sg.WriteSemanticDataToTxt(SData[0][0:sp80],train_txt)
sg.WriteSemanticDataToTxt(SData[0][sp80:sp100],valid_txt)
sg.WriteSemanticDataToTxt(SData[1],test_txt)

#tmtype = "SKCART"

if tmtype == "Logistic":

    # ============== Logistic Model Section ==============

    nnet_idim = len(SData[0][0][0])
    nnet_odim = 2

    logging.basicConfig()
    tr_log = logging.getLogger("mlp.optimisers")
    tr_log.setLevel(logging.DEBUG)

    rng = numpy.random.RandomState([2018,03,31])
    rng_state = rng.get_state()

    lrate = Bmch.read_config(conffile,"logistic_lrate","float")
    max_epochs = Bmch.read_config(conffile,"logistic_max_epochs","int")
    batch_size = Bmch.read_config(conffile,"logistic_minibatch_size","int")

    #max_epochs = 1000
    #lrate = lrate * 2

    BNNet = BLogistic_Init([nnet_idim, nnet_odim], rng)
    lr_scheduler = LearningRateFixed(learning_rate=lrate, max_epochs=max_epochs)
    #lr_scheduler = LearningRateNewBob(start_rate = lrate, scale_by = 0.5, min_derror_ramp_start = -0.1, min_derror_stop = 0, patience = 100, max_epochs = max_epochs)
    dp_scheduler = None #DropoutFixed(p_inp_keep=1.0, p_hid_keep=0.9)
    BNNet, Tr_Stat, Cv_Stat, Ev_Stat = BNNet_Semantic_Learning(BNNet, lr_scheduler, [train_txt,valid_txt,test_txt], dp_scheduler, batch_size = batch_size)

    tmfile = resdir + "/logistic.mdl"
    print "Writing logistic tendency model to %s."%tmfile
    filehandler = open(tmfile, 'w')
    pickle.dump(BNNet, filehandler)
    print "Tendency model has been written to the file."

elif tmtype == "ResNet":

    # ============== ResNet Net Section ==============

    nnet_idim = len(SData[0][0][0])
    nnet_odim = 2

    logging.basicConfig()
    tr_log = logging.getLogger("mlp.optimisers")
    tr_log.setLevel(logging.DEBUG)

    rng = numpy.random.RandomState([2018,03,31])
    rng_state = rng.get_state()


    lrate = Bmch.read_config(conffile,"resnet_lrate","float")
    max_epochs = Bmch.read_config(conffile,"resnet_max_epochs","int")
    batch_size = Bmch.read_config(conffile,"resnet_minibatch_size","int")
    num_hid = Bmch.read_config(conffile,"resnet_num_hid","int")
    num_layers = Bmch.read_config(conffile,"resnet_num_layers","int")

    #lrate = lrate * 2
    #max_epochs = 200

    BNNet = BResNet_Init([nnet_idim, num_hid, num_layers, nnet_odim], rng, 'Softmax')
    lr_scheduler = LearningRateFixed(learning_rate=lrate, max_epochs=max_epochs)
    #lr_scheduler = LearningRateNewBob(start_rate = lrate, scale_by = 0.5, min_derror_ramp_start = -0.1, min_derror_stop = 0, patience = 100, max_epochs = max_epochs)
    dp_scheduler = None #DropoutFixed(p_inp_keep=1.0, p_hid_keep=0.9)
    BNNet, Tr_Stat, Cv_Stat, Ev_Stat = BNNet_Semantic_Learning(BNNet, lr_scheduler, [train_txt,valid_txt,test_txt], dp_scheduler, batch_size = batch_size)

    tmfile = resdir + "/ResNet.mdl"
    print "Writing ResNet tendency model to %s."%tmfile
    filehandler = open(tmfile, 'w')
    pickle.dump(BNNet, filehandler)
    print "Tendency model has been written to the file."

elif tmtype == "CART":

    # ============== Classification and Regression Tree Section ==============


    print "Not Implemented Error!"
    Not_Implemented_Error

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


    nnet_idim = len(SData[0][0][0])
    nnet_odim = 2

    
    #BNB = BNBayes(data=tr_data,conffile=conffile)
    
    tr_feat = []
    tr_tgt = []
    for x in SData[0]:
        tr_feat.append(x[0])
        tr_tgt.append(x[1])

    ev_feat = []
    ev_tgt = []
    for x in SData[1]:
        ev_feat.append(x[0])
        ev_tgt.append(x[1])

 
    BNB = BernoulliNB(alpha=1.0, binarize=0.5, class_prior=None, fit_prior=True)

    BNB.fit(tr_feat, tr_tgt)

    Acc = BNB.score(ev_feat,ev_tgt)
    print "Accuracy is:", Acc * 100, "%."

    tmfile = resdir + "/BNBayes.mdl"    
    print "Writing BNBayes tendency model to %s."%tmfile
    filehandler = open(tmfile, 'w')
    pickle.dump(BNB, filehandler)
    print "Tendency model has been written to the file."

elif tmtype == "SKCART":

    # ============== Scikit-learn CARTs Section ==============


    rng = numpy.random.RandomState([2018,03,31])
    rng_state = rng.get_state()

    num_tree = Bmch.read_config(conffile,"skcart_num_tree","int")

    tr_feat = []
    tr_tgt = []
    for x in SData[0]:
        tr_feat.append(x[0])
        tr_tgt.append(x[1])
    tr_data = [tr_feat,tr_tgt]

    ev_feat = []
    ev_tgt = []
    for x in SData[1]:
        ev_feat.append(x[0])
        ev_tgt.append(x[1])
    ev_data = [ev_feat,ev_tgt]

    #num_tree = 256
    
    #st_time = time.time()
    # Training

    RF = RandomForestRegressor(n_estimators = num_tree, min_impurity_decrease = 0.0)
   
    RF.fit(tr_feat, tr_tgt)

    # Testing.
    Acc = RF.score(ev_feat,ev_tgt)
    print "Accuracy is:", Acc * 100, "%."
  
    #ed_time = time.time()
    #print ed_time - st_time 
 
    print "Writing SKCART tendency model (single) to %s."%tmfile
    filehandler = open(tmfile, 'w')
    pickle.dump(RF, filehandler)
    print "Tendency model has been written to the file."




else:
    print "Not Implemented Error!"
    Not_Implemented_Error
