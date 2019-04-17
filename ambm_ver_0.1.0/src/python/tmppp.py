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
import numpy
import logging
import pickle


# ==================================================

# This is a library for semantic learning

# =================================================

def GeneratingTrainingData(M,conf,resdir):

    mchfile = M
    conffile = conf
    resfolder = resdir

    print "Generating Training Data for Semantics Learning..."
    print "Source File:", mchfile
    print "Configuration File:", conffile
    print "Working Folder:", resfolder

    cmd = "mkdir %s"%resfolder
    os.system(cmd)

    ff = resfolder + "/source.mch"
    cmd = "./../ProB/probcli -pp %s %s"%(ff,mchfile)
    os.system(cmd)
    mchfile = ff

    ff = resfolder + "/config"
    cmd = "cp %s %s"%(conffile,ff)
    os.system(cmd)
    conffile = ff

    outfile = resfolder + "/trset.mch"
    sgfile = resfolder + "/trset.statespace.dot"
    dsfile = resfolder + "/data.txt"
    
    with open(mchfile) as mchf:
        mch = mchf.readlines()
    mch = [x.strip() for x in mch]


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

    TL = sg.GetTransList()

    TL = sg.SortSetsInTransList(TL)

    # Remove faulty transitions.
    # FS --- Faulty States.
    # FT --- Faulty Transitions.
    FS = sg.GetStatesWithoutOutgoingTransitions(TL)
    FT = sg.GetTransitionsWithPostStates(TL,FS)
    TL = Bmch.list_difference(TL,FT)

    SType = sg.GetSetTypeFromTransList(TL)
    VList = sg.GetVbleList()

    rd_seed = Bmch.read_config(conffile,"rd_seed","int")
    neg_prop = Bmch.read_config(conffile,"neg_prop","float")
    cv_prop = Bmch.read_config(conffile,"cv_prop","float")

    SilasData = sg.SilasTransListToData(TL,SType,VList,neg_prop,rd_seed)

    VData = SilasData[0]
    FData = SilasData[1:len(SilasData)]
    print len(FData)

    random.seed(rd_seed)
    random.shuffle(FData)

    num_tr = int(len(FData) * (1-cv_prop))


    TrData = [VData] + FData[0:num_tr]
    CvData = [VData] + FData[num_tr:len(FData)]

    fname = resfolder + "/train.csv"
    Bgenlib.write_list_to_csv(TrData,fname)
    fname = resfolder + "/valid.csv"
    Bgenlib.write_list_to_csv(CvData,fname)

    fname = resfolder + "/datatypes.txt"
    DataTypes = [VList] + SType
    f = open(fname,"w")
    for x in DataTypes:
        f.write(str(x) + "\n")
    f.close() 

    return 0



def TrainingSemanticsModel(M,conf,resdir):

    cmd = "mkdir %s"%resdir
    os.system(cmd)

    conffile = conf
    s = resdir + "/config"
    cmd = "cp %s %s"%(conffile,s)
    os.system(cmd)
    conffile = s

    GeneratingTrainingData(M,conffile,resdir)

    training_data = resdir + "/train.csv"
    valid_data = resdir + "/valid.csv"
    datatypes_file = resdir + "/datatypes.txt"
    conffile = conf

    f = open(datatypes_file,"r")
    T = f.readlines()
    DType = []
    for x in T:
        DType.append(eval(x))
    VList = DType[0]
    SType = DType[1:len(DType)]

    print "Training Data:", training_data
    print "Cross Validation Data", valid_data

    tmtype = Bmch.read_config(conffile,"tendency_model","str")
    sg = Bgenlib.BStateGraphForNN()
    SData = sg.ReadCSVSemanticsData([training_data,valid_data])

    train_txt = resdir + "/train.txt"
    valid_txt = resdir + "/valid.txt"


    sg.WriteSemanticDataToTxt(SData[0],train_txt)
    sg.WriteSemanticDataToTxt(SData[1],valid_txt)

    #tmtype = "BNBayes"

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

        cv_feat = []
        cv_tgt = []
        for x in SData[1]:
            cv_feat.append(x[0])
            cv_tgt.append(x[1])

     
        BNB = BernoulliNB(alpha=1.0, binarize=0.5, class_prior=None, fit_prior=True)

        BNB.fit(tr_feat, tr_tgt)

        Acc = BNB.score(cv_feat,cv_tgt)
        print "Accuracy is:", Acc * 100, "%."

        tmfile = resdir + "/semantics.mdl"    
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

        cv_feat = []
        cv_tgt = []
        for x in SData[1]:
            cv_feat.append(x[0])
            cv_tgt.append(x[1])
        cv_data = [cv_feat,cv_tgt]

        #num_tree = 256
        
        #st_time = time.time()
        # Training

        RF = RandomForestRegressor(n_estimators = num_tree, min_impurity_decrease = 0.0)
       
        RF.fit(tr_feat, tr_tgt)

        # Testing.
        Acc = RF.score(cv_feat,cv_tgt)
        print "Accuracy on Cross Validation Set is:", Acc * 100, "%."
      
        #ed_time = time.time()
        #print ed_time - st_time 

        RF.MdlType = "SKCART" 
        RF.VList = VList
        RF.SType = SType
 
        tmfile = resdir + "/semantics.mdl" 
        print "Writing SKCART tendency model (single) to %s."%tmfile
        filehandler = open(tmfile, 'w')
        pickle.dump(RF, filehandler)
        print "Tendency model has been written to the file."


    elif tmtype == "Silas":
        
        silas_dir = resdir + "/silas/"
        cmd = "rm -r %s"%silas_dir
        os.system(cmd)
        cmd = "mkdir %s"%silas_dir
        os.system(cmd)
        cmd = "cp -r src/silas-json-schemata/ json-schemata"
        os.system(cmd)

        cmd = "silas gen-all -o %s %s/train.csv %s/valid.csv"%(silas_dir,resdir,resdir)
        os.system(cmd)

        cmd = "silas learn -o %s/model/ %s/settings.json"%(silas_dir,silas_dir)
        os.system(cmd)

        cmd = "silas predict -o %s/predictions.csv %s/model %s/valid.csv"%(silas_dir,silas_dir,resdir)
        os.system(cmd)

        SM = SilasModel()
        SM.MdlType = "Silas"
        SM.Data = []
        SM.Data.append("%s/train.csv"%silas_dir)
        SM.Data.append("%s/valid.csv"%silas_dir)
        SM.VList = VList
        SM.SType = SType
        
        tmfile = resdir + "/semantics.mdl"
        print "Writing silas model to %s."%tmfile
        filehandler = open(tmfile, 'w')
        pickle.dump(SM, filehandler)
        print "Tendency model has been written to the file."

    else:
        print "Not Implemented Error!"
        Not_Implemented_Error


# Predict probablities of transitions using trained semantics model.
# W --- semantics model
# TL --- list of transitions
def PredictUsingSemanticsModel(W,TL):
    MdlType = W.MdlType
    VList = W.VList
    SType = W.SType
    ppp


