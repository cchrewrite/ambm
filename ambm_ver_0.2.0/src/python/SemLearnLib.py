import sys
import Bmch
import os
import time
import Bgenlib
import random
from Cartlib import *
from NBayes import *
from SKCART import *
from SKClassifier import *
import numpy
import logging
import pickle
import json
from sklearn.metrics import roc_auc_score

# ==================================================

# This is a library for semantic learning

# =================================================


# RL --- classified and sorted list of repairs
def GetBestRepair(RL):
    print("Note: Ignore isolation repairs and only get best revision repairs.")
    res = []
    for X in RL:
        T = X[0]
        for P in X:
            if P[0] == "revision":
                T.append(P[1])
                break
        res.append(T)
    return res



# RL --- classified and sorted list of repairs
# G --- Oracle
def GetRepairAnswer(RL,G):
    i = G[0].index("ANSWER")
    ANS = G[1][i]

    """
    for x in RL:
        if x[0][0] != [['PID1'], ['PID3'], ['PID2']]: continue
        for y in x:
            
            print y
    raw_input("pp")
    """
    num_1 = 0
    res = []
    for X in RL:
        T = X[0]
        S = ""
        #input(T)
        for Y in ANS:
            P = [Y[0],Y[1],Y[2]]
            #input(P)
            if P == T:
                S = Y[3]
                break
        if S == "":
            print("WARNING: Cannot find an answer for",T,". Use a self-transition.")
            #res.append(T + ["NotFound"])
            res.append(T + [Y[0]])
            continue
        res.append(T + [S])
        num_1 = num_1 + 1
    """
    input(len(res))
    input(num_1)
    for x in res:
        input(x)
    """
    return res


# RL --- classified and sorted list of repairs
# G --- Oracle
def CompareRevisionWithAnswer(RL,G):
    i = G[0].index("ANSWER")
    ANS = G[1][i]

    res = []
    for X in RL:
        print("\n")
        T = X[0]
        S = ""
        for Y in ANS:
            P = [Y[0],Y[1],Y[2]]
            if P == T:
                S = Y[3]
                break
        if S == "":
            print("WARNING: Cannot find an answer for",T,".")
            res.append(["","NotFound"])
            continue

        # find the answer's rank and probability.
        ans_rank = 0
        ans_prob = -1
        for i in range(1,len(X)):
            V = X[i]
            if V[0] != "revision":
                continue
            ans_rank = ans_rank + 1
            if S == V[1]:
                ans_prob = V[2]
                break
        if ans_prob == -1:
            print("WARNING: Cannot find probability of the answer",S,".")
            ans_rank = -1

        # compare the best revision with the answer and compute accuracy.
        for i in range(1,len(X)):
            V = X[i]
            if V[0] != "revision":
                continue
            # The first revision is the best one.
            best_acc = RevisionVariableAccuracy(V[1],S)
            print("Faulty Transitions is:",T)
            print("Best Revision is:",V[1],", probability is",V[2])
            print("Answer is:",S,", probability is",ans_prob,", rank is",ans_rank)
            res.append([V[1],S])
            break
    return res

def RevisionVariableAccuracy(S,T):
    if T == "NotFound":
        return "None"
    acc = 0.0
    for i in range(len(S)):
       if S[i] == T[i]:
           acc = acc + 1
    acc = acc / len(S) 
    return acc

# M --- file name of an abstract machine
# W --- trained semantics model
# conddile --- configuration file
# resdir --- working directory
def MonteCarloStateSampling(M,W,conffile,sdir):

    cmd = "mkdir %s"%sdir
    os.system(cmd)
    s = sdir + "/M.mch"
    cmd = "cp %s %s"%(M,s)
    os.system(cmd)
    M = s
    
    fn = sdir + "/M_pp.mch"
    oscmd = "./../ProB/probcli -pp %s %s"%(fn,M)
    os.system(oscmd)
    M = fn

    with open(M) as mchf:
        mch = mchf.readlines()
    mch = [x.strip() for x in mch]

    rev_cond = Bmch.generate_revision_condition(mch, [], "")

    # If integers exist in the model, then we limit the search space of integers.
    int_flag = False
    for x in rev_cond:
        for y in [": INTEGER",": NATURAL",": NATURAL1",": INT",": NAT",": NAT1"]:
            if x[len(x)-len(y):len(x)] == y:
                int_flag = True
                break

    Int_CompX = 1
    if int_flag == True:
        SType = W.SType
        VList = W.VList
        for j in range(len(SType)):
            if SType[j][0] != "Int":
                continue
            V = VList[j]
            T = SType[j][1:len(SType[j])]
            Int_CompX = Int_CompX * len(T)

            for i in range(len(rev_cond)):
                x = rev_cond[i]
                for P in [": INTEGER",": NATURAL",": NATURAL1",": INT",": NAT",": NAT1"]:
                    y = V + "_init " + P
                    if x[len(x)-len(y):len(x)] == y:
                        Q = ""
                        for u in T:
                            Q = Q + str(u) + ","
                        Q = Q[0:len(Q)-1]
                        Q = V + "_init : {" + Q + "}"
                        z = x.replace(y,Q)
                        rev_cond[i] = z
                        break

    all_opes = Bmch.get_all_opes(mch)

    # MS --- machine for sampling
    MS = []
    i = 0
    mchlen = len(mch)
    while i < mchlen:
        tt = Bmch.get_first_token(mch[i])
        # Based on the syntax of <The B-book>, p.273.
        if tt == "INITIALIZATION": break
        if tt == "INITIALISATION": break
        MS.append(mch[i])
        i = i + 1
    MS.append("INITIALISATION")
    MS = MS + rev_cond
    #res.append("OPERATIONS")
    #res = res + all_opes
    MS.append("END")
   
    fn = sdir + "/sampling.mch"
    Bmch.print_mch_to_file(MS,fn)
    MS = fn

    mcss_max_num_samples = Bmch.read_config(conffile,"mcss_max_num_samples","int")
    
    D = sdir + "D.txt"
    #genmode = "-mc %d -mc_mode random -p MAX_INITIALISATIONS %d -p RANDOMISE_ENUMERATION_ORDER TRUE -p MAX_DISPLAY_SET -1"%(mcss_max_num_samples * 100, mcss_max_num_samples * 100)

    genmode = "-mc %d -mc_mode random -p MAX_INITIALISATIONS %d -p RANDOMISE_ENUMERATION_ORDER TRUE -p MAX_DISPLAY_SET -1"%(mcss_max_num_samples, mcss_max_num_samples)


    mkgraph = "./../ProB/probcli %s %s -nodead -spdot %s -c"%(MS,genmode,D)
    os.system(mkgraph)

    sg = Bgenlib.BStateGraphForNN()
    sg.ReadStateGraph(D)
    SI = sg.GetInitList()

    """
    random.shuffle(SI)

    if len(SI) > mcss_max_num_samples:
        SI = SI[0:mcss_max_num_samples]
    """
    print("Sample %d times. Get %d samples that satisfies requirements."%(mcss_max_num_samples,len(SI)))

    return SI

# RL --- list of repairs
def ClassifyAndSortRepairs(RL):
    TL = []
    for X in RL:
        P = [X[1],X[2],X[3]]
        if not(P in TL):
            TL.append(P)
    TL.sort()
    L = len(TL)
    res = []
    for i in range(L):
        res.append([TL[i]])

    # Add isolation repairs.
    for X in RL:
        if X[0] != "isolation":
            continue
        P = [X[1],X[2],X[3]]
        idx = TL.index(P)
        Q = [X[0]]
        res[idx].append(Q)

    # Sort revision repairs.
    RevS = []
    for i in range(L):
        RevS.append([])
    for X in RL:
        if X[0] != "revision":
            continue
        P = [X[1],X[2],X[3]]
        idx = TL.index(P)
        Q = [X[0],X[4],X[5]]
        RevS[idx].append(Q)
    for i in range(L):
        RevS[i].sort(key = lambda x: x[2], reverse = True)
        res[i] = res[i] + RevS[i]
   
    return res

def GeneratingTrainingData(M,conf,resdir):

    mchfile = M
    conffile = conf
    resfolder = resdir

    print("Generating Training Data for Semantics Learning...")
    print("Source File:", mchfile)
    print("Configuration File:", conffile)
    print("Working Folder:", resfolder)

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
        print("\nUse additional sampling.\n")
        trsetmch = Bmch.generate_training_set_machine(mch,"")
    else:
        print("\nNot use additional sampling.\n")
        trsetmch = mch

    bscope = Bmch.generate_training_set_condition(mch)

    Bmch.print_mch_to_file(trsetmch,outfile)


    max_num_sampling_states = Bmch.read_config(conffile,"max_num_sampling_states","int")
    max_operations = Bmch.read_config(conffile,"max_operations","int")

    print("\nMaximum number of samples is", max_num_sampling_states, ".\n")

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

    Num_Tr = len(TrData) - 1
    Num_Cv = len(CvData) - 1

    return [Num_Tr,Num_Cv]



def TrainingSemanticsModel(M,conf,resdir):

    cmd = "mkdir %s"%resdir
    os.system(cmd)

    conffile = conf
    s = resdir + "/config"
    cmd = "cp %s %s"%(conffile,s)
    os.system(cmd)
    conffile = s

    start_time = time.time()

    N = GeneratingTrainingData(M,conffile,resdir)
    Num_Tr = N[0]
    Num_Cv = N[1]

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

    print("Training Data:", training_data)
    print("Cross Validation Data", valid_data)

    tmtype = Bmch.read_config(conffile,"tendency_model","str")
    sg = Bgenlib.BStateGraphForNN()
    SD = sg.ReadCSVSemanticsDataAndComputeTypes([training_data,valid_data])
    SData = SD[0]
    SemTypes = SD[1]

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

        rng = numpy.random.RandomState(777)
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
        print("Writing logistic tendency model to %s."%tmfile)
        filehandler = open(tmfile, 'wb')
        pickle.dump(BNNet, filehandler)
        print("Tendency model has been written to the file.")

    elif tmtype == "ResNet":

        # ============== ResNet Net Section ==============

        nnet_idim = len(SData[0][0][0])
        nnet_odim = 2

        logging.basicConfig()
        tr_log = logging.getLogger("mlp.optimisers")
        tr_log.setLevel(logging.DEBUG)

        rng = numpy.random.RandomState(777)
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
        print("Writing ResNet tendency model to %s."%tmfile)
        filehandler = open(tmfile, 'wb')
        pickle.dump(BNNet, filehandler)
        print("Tendency model has been written to the file.")

    elif tmtype == "CART":

        # ============== Classification and Regression Tree Section ==============

        tr_data = []

        for x in SData[0]:
            tr_data.append([x[0], x[1]])

        cv_feat = []
        cv_tgt = []
        for x in SData[1]:
            cv_feat.append(x[0])
            cv_tgt.append(x[1])
        cv_data = [cv_feat,cv_tgt]

        num_tree = Bmch.read_config(conffile,"cart_num_tree","int")
        min_var_exp = Bmch.read_config(conffile,"cart_min_var_exp","int")
        max_var_exp = Bmch.read_config(conffile,"cart_max_var_exp","int")
        data_prop = Bmch.read_config(conffile,"cart_data_prop","float")
        use_mp = Bmch.read_config(conffile,"cart_use_mp","bool")

        CARTree = RandMultiRegTree(data=tr_data, num_tree=num_tree, min_var_exp_scale=[min_var_exp,max_var_exp], data_prop=data_prop, use_mp=use_mp)


        # Testing.
        Acc = CARTree.score(cv_feat,cv_tgt)
        print("Accuracy on Cross Validation Set is:", Acc * 100, "%.")

        cv_proba = CARTree.predict_proba(cv_feat)[:,1]
        AUC = roc_auc_score(cv_tgt, cv_proba)
        print("ROC-AUC is:", AUC, ".")
 
        #ed_time = time.time()
        #print ed_time - st_time 

        CARTree.MdlType = "CART" 
        CARTree.VList = VList
        CARTree.SType = SType
        CARTree.SemTypes = SemTypes
 
        tmfile = resdir + "/semantics.mdl" 
        print("Writing CART tendency model (single) to %s."%tmfile)
        filehandler = open(tmfile, 'wb')
        pickle.dump(CARTree, filehandler)
        print("Tendency model has been written to the file.")

    elif tmtype == "BNB":

        # ============== Bernoulli Naive Bayes Section ==============

        rng = numpy.random.RandomState(777)
        rng_state = rng.get_state()

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

        #RF = RandomForestClassifier(n_estimators = num_tree, min_impurity_decrease = 0.0)
        #RF.fit(tr_feat, tr_tgt)


        BNB = BernoulliNB(alpha=1.0, binarize=0.5, class_prior=None, fit_prior=True)
        BNB.fit(tr_feat, tr_tgt)


        # Testing.
        #Acc = RF.score(cv_feat,cv_tgt)
        Acc = BNB.score(cv_feat,cv_tgt)
        print("Accuracy on Cross Validation Set is:", Acc * 100, "%.")

        cv_proba = BNB.predict_proba(cv_feat)[:,1]
        AUC = roc_auc_score(cv_tgt, cv_proba)
        print("ROC-AUC is:", AUC, ".")


        #ed_time = time.time()
        #print ed_time - st_time 

        BNB.MdlType = "BNB" 
        BNB.VList = VList
        BNB.SType = SType
        BNB.SemTypes = SemTypes
 
        tmfile = resdir + "/semantics.mdl" 
        print("Writing BNB tendency model to %s."%tmfile)
        filehandler = open(tmfile, 'wb')
        pickle.dump(BNB, filehandler)
        print("Tendency model has been written to the file.")

    elif tmtype == "MLP":

        # ============== MLP Section ==============

        rng = numpy.random.RandomState(777)
        rng_state = rng.get_state()

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

        # MLP = MLPClassifier(solver='lbfgs', alpha=1e-5, hidden_layer_sizes=(256,5), random_state=1) # This setting is significantly better than the default.
        MLP = MLPClassifier(solver='lbfgs', alpha=1e-5, random_state=1)
       
        MLP.fit(tr_feat, tr_tgt)


        # Testing.
        #Acc = RF.score(cv_feat,cv_tgt)
        Acc = MLP.score(cv_feat,cv_tgt)
        print("Accuracy on Cross Validation Set is:", Acc * 100, "%.")

        cv_proba = MLP.predict_proba(cv_feat)[:,1]
        AUC = roc_auc_score(cv_tgt, cv_proba)
        print("ROC-AUC is:", AUC, ".")
 
        #ed_time = time.time()
        #print ed_time - st_time 

        MLP.MdlType = "MLP" 
        MLP.VList = VList
        MLP.SType = SType
        MLP.SemTypes = SemTypes
 
        tmfile = resdir + "/semantics.mdl" 
        print("Writing BNB tendency model to %s."%tmfile)
        filehandler = open(tmfile, 'wb')
        pickle.dump(MLP, filehandler)
        print("Tendency model has been written to the file.")


    elif tmtype == "LR":

        # ============== Logistic Regression Section ==============

        rng = numpy.random.RandomState(777)
        rng_state = rng.get_state()

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

        LR = LogisticRegression(random_state=0, solver='lbfgs',multi_class='ovr')
        LR.fit(tr_feat, tr_tgt)


        # Testing.
        #Acc = RF.score(cv_feat,cv_tgt)
        Acc = LR.score(cv_feat,cv_tgt)
        print("Accuracy on Cross Validation Set is:", Acc * 100, "%.")

        cv_proba = LR.predict_proba(cv_feat)[:,1]
        AUC = roc_auc_score(cv_tgt, cv_proba)
        print("ROC-AUC is:", AUC, ".")
 
        #ed_time = time.time()
        #print ed_time - st_time 

        LR.MdlType = "LR" 
        LR.VList = VList
        LR.SType = SType
        LR.SemTypes = SemTypes
 
        tmfile = resdir + "/semantics.mdl" 
        print("Writing LR tendency model to %s."%tmfile)
        filehandler = open(tmfile, 'wb')
        pickle.dump(LR, filehandler)
        print("Tendency model has been written to the file.")

    elif tmtype == "SVM":

        # ============== SVM Section ==============

        rng = numpy.random.RandomState(777)
        rng_state = rng.get_state()

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

        #SVM = svm.SVC(kernel='linear')
        SVM = svm.SVC(kernel='rbf',probability=True)
        SVM.fit(tr_feat, tr_tgt)


        # Testing.
        #Acc = RF.score(cv_feat,cv_tgt)
        Acc = SVM.score(cv_feat,cv_tgt)
        print("Accuracy on Cross Validation Set is:", Acc * 100, "%.")

        cv_proba = SVM.predict_proba(cv_feat)[:,1]
        AUC = roc_auc_score(cv_tgt, cv_proba)
        print("ROC-AUC is:", AUC, ".")
 
        #ed_time = time.time()
        #print ed_time - st_time 

        SVM.MdlType = "SVM" 
        SVM.VList = VList
        SVM.SType = SType
        SVM.SemTypes = SemTypes
 
        tmfile = resdir + "/semantics.mdl" 
        print("Writing SVM tendency model to %s."%tmfile)
        filehandler = open(tmfile, 'wb')
        pickle.dump(SVM, filehandler)
        print("Tendency model has been written to the file.")




    elif tmtype == "RF":

        # ============== Scikit-learn Random Forests Section ==============


        rng = numpy.random.RandomState(777)
        rng_state = rng.get_state()

        num_tree = Bmch.read_config(conffile,"rf_num_tree","int")

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

        #RF = RandomForestRegressor(n_estimators = num_tree, min_impurity_decrease = 0.0)

        #RF = RandomForestClassifier(n_estimators = num_tree, min_impurity_decrease = 0.0)

        if num_tree <= 0:
            # By default, the number of tree is 10 before scikit-learn version 0.20 and 100 after version 0.22. Here we use 100.
            num_tree = 100

        RF = RandomForestClassifier(n_estimators = num_tree)

        #RF = RandomForestClassifier(min_impurity_decrease = 0.0)
       
        RF.fit(tr_feat, tr_tgt)

        # Testing.
        Acc = RF.score(cv_feat,cv_tgt)
        print("Accuracy on Cross Validation Set is:", Acc * 100, "%.")

        cv_proba = RF.predict_proba(cv_feat)[:,1]
        AUC = roc_auc_score(cv_tgt, cv_proba)
        print("ROC-AUC is:", AUC, ".")
 
        #ed_time = time.time()
        #print ed_time - st_time 

        RF.MdlType = "RF" 
        RF.VList = VList
        RF.SType = SType
        RF.SemTypes = SemTypes
 
        tmfile = resdir + "/semantics.mdl" 
        print("Writing RF tendency model (single) to %s."%tmfile)
        filehandler = open(tmfile, 'wb')
        pickle.dump(RF, filehandler)
        print("Tendency model has been written to the file.")


    elif tmtype == "Silas":
        
        silas_dir = resdir + "/silas/"
        cmd = "rm -r %s"%silas_dir
        os.system(cmd)
        cmd = "mkdir %s"%silas_dir
        os.system(cmd)
        cmd = "cp -r src/silas-json-schemata/ json-schemata"
        os.system(cmd)

        cmd = "./silas gen-all -o %s %s/train.csv %s/valid.csv"%(silas_dir,resdir,resdir)
        os.system(cmd)

        silas_num_tree = Bmch.read_config(conffile,"silas_num_tree","int")
        silas_feature_proportion = "1.0"

        #silas_num_tree = 3000

        sf = silas_dir + "/settings.json"
        ChangeSilasSetting(sf,"feature_proportion",0.25,"float")
        ChangeSilasSetting(sf,"max_depth",32,"int")
        ChangeSilasSetting(sf,"desired_leaf_size",32,"int")
        #ChangeSilasSetting(sf,"sampling_method","uniform","str")
        # if silas_num_tree < 0, then use default settings.
        if silas_num_tree > 0:
            # ssf --- Silas setting files
            ChangeSilasSetting(sf,"number_of_trees",silas_num_tree,"int")
            """
            ssf = open(f,"r")
            ss = ssf.readlines()
            ssf.close()
            for i in range(len(ss)):
                x = ss[i]
                if "number_of_trees" in x:
                    y = "    \"number_of_trees\": %d,\n"%silas_num_tree
                    ss[i] = y
                    ssf = open(f,"w")
                    for p in ss:
                        ssf.write(p)
                    ssf.close()
                    break
            """
        cmd = "./silas learn -o %s/model/ %s/settings.json"%(silas_dir,silas_dir)
        #os.system(cmd)
        P = os.popen(cmd)
        P = P.read()
        print(P)
        

        # Get Accuracy.
        i = 0
        x = "Accuracy:"
        while P[i:i+len(x)] != x:
            i = i + 1
        i = i + len(x)
        j = i + 1
        while P[j] != "\n":
            j = j + 1
        Acc = P[i:j]
        Acc = float(Acc)

        # Get ROC-AUC
        i = 0
        x = "ROC-AUC:"
        while P[i:i+len(x)] != x:
            i = i + 1
        i = i + len(x)
        j = i + 1
        while P[j] != "\n":
            j = j + 1
        AUC = P[i:j]
        AUC = float(AUC)

        #cmd = "silas predict -o %s/predictions.csv %s/model %s/valid.csv"%(silas_dir,silas_dir,resdir)
        #os.system(cmd)

        SM = SilasModel()
        SM.MdlType = "Silas"
        SM.SilasNumTrees = silas_num_tree
        SM.SilasDir = silas_dir
        SM.Data = []
        SM.Data.append("%s/train.csv"%resdir)
        SM.Data.append("%s/valid.csv"%resdir)
        SM.VList = VList
        SM.SType = SType
        SM.SemTypes = SemTypes

        # Get output labels.
        # smd --- Silas metadata
        f = silas_dir + "/model/metadata.json"
        ssf = open(f,"r")
        ss = ssf.readlines()
        ssf.close()
        for i in range(len(ss)-1):
            x1 = ss[i]
            x2 = ss[i+1]
            if "Available-Transition" in x1 and "collection_definition" in x2:
                x3 = ss[i+2]
                if "N" in x3:
                    label_N = 0
                    label_Y = 1
                elif "Y" in x3:
                    label_Y = 0
                    label_N = 1
                break
        SM.label_Y = label_Y
        SM.label_N = label_N
        
        tmfile = resdir + "/semantics.mdl"
        print("Writing silas model to %s."%tmfile)
        filehandler = open(tmfile, 'wb')
        pickle.dump(SM, filehandler)
        print("Tendency model has been written to the file.")

    else:
        print("Not Implemented Error!")
        Not_Implemented_Error

    end_time = time.time()
    elapsed_time = end_time - start_time

    print("Training Finished.")
    print("Number of Training Examples:",Num_Tr)
    print("Number of Validation Examples:",Num_Cv)
    print("Type of Semantics Model:",tmtype)
    print("Elapsed Time (s):",elapsed_time)
    print("Classification Accuracy:",Acc)
    print("ROC-AUC:",AUC)

    return [Num_Tr,Num_Cv,tmtype,elapsed_time,Acc,AUC] 

# f --- setting file name.
# t --- setting identifier
# v --- value
# tp --- type of value
def ChangeSilasSetting(f,t,v,tp):
    ssf = open(f,"r")
    ss = ssf.readlines()
    ssf.close()
    for i in range(len(ss)):
        x = ss[i]
        if t in x:
            if tp == "int":
                y = "\"%s\": %d,\n"%(t,v)
            elif tp == "float":
                y = "\"%s\": %.2f,\n"%(t,v)
            else:
                y = "\"%s\": \"%s\",\n"%(t,v)
            ss[i] = y
    ssf = open(f,"w")
    for p in ss:
        ssf.write(p)
    ssf.close()

    return


# W --- semantics model
# RL --- list of revisions
# wdir --- working directory
def ScoreRevisionsUsingSemanticsModel(W,RL,wdir):
    TL = []
    for x in RL:
        s = [x[1],x[2],x[4]]
        TL.append(s)
    res = PredictUsingSemanticsModel(W,TL,wdir)
    return res

# Predict probablities of transitions using trained semantics model.
# W --- semantics model
# TL --- list of transitions
# wdir --- working directory
def PredictUsingSemanticsModel(W,TL,wdir):
    MdlType = W.MdlType
    VList = W.VList
    SType = W.SType
    SemTypes = W.SemTypes

    #DType = W.DType
    P = []
    sg = Bgenlib.BStateGraphForNN()
    PPD = sg.TransListToPrePostData(TL,SType,VList)

    if MdlType == "Silas":
        silas_dir = W.SilasDir
        fname = wdir + "/transitions.csv"
        #SType = sg.GetSetTypeFromTransList(TL)
        #VList = sg.GetVbleList()
        #SilasData = sg.SilasTransListToData(TL,SType,VList,neg_prop,rd_seed)
        Bgenlib.write_list_to_csv(PPD,fname)
        pname = wdir + "/predictions.csv"

        # Re-train Silas:
        silas_dir = W.SilasDir
        tr_data = W.Data[0]
        tname = wdir + "/train.csv"
        cmd = "cp %s %s"%(tr_data,tname)
        os.system(cmd)
        tr_data = tname
        fr_data = fname
        silas_num_tree = W.SilasNumTrees
        cmd = "rm -r %s"%silas_dir
        os.system(cmd)
        cmd = "mkdir %s"%silas_dir
        os.system(cmd)
        cmd = "cp -r src/silas-json-schemata/ json-schemata"
        os.system(cmd)

        cmd = "./silas gen-all -o %s %s %s"%(silas_dir,tr_data,fr_data)
        os.system(cmd)
        sf = silas_dir + "/settings.json"
        ChangeSilasSetting(sf,"feature_proportion",0.25,"float")
        ChangeSilasSetting(sf,"max_depth",32,"int")
        ChangeSilasSetting(sf,"desired_leaf_size",32,"int")
        #ChangeSilasSetting(sf,"sampling_method","uniform","str")
        # if silas_num_tree < 0, then use default settings.
        if silas_num_tree > 0:
            # ssf --- Silas setting files
            ChangeSilasSetting(sf,"number_of_trees",silas_num_tree,"int")
        
        """
        # if silas_num_tree < 0, then use default settings.
        if silas_num_tree > 0:
            # ssf --- Silas setting files
            f = silas_dir + "/settings.json"
            ssf = open(f,"r")
            ss = ssf.readlines()
            ssf.close()
            for i in range(len(ss)):
                x = ss[i]
                if "number_of_trees" in x:
                    y = "    \"number_of_trees\": %d,\n"%silas_num_tree
                    ss[i] = y
                    ssf = open(f,"w")
                    for p in ss:
                        ssf.write(p)
                    ssf.close()
                    break
        """
        cmd = "./silas learn -o %s/model/ %s/settings.json"%(silas_dir,silas_dir)
        os.system(cmd)
        # Get output labels.
        # smd --- Silas metadata
        f = silas_dir + "/model/metadata.json"
        ssf = open(f,"r")
        ss = ssf.readlines()
        ssf.close()
        for i in range(len(ss)-1):
            x1 = ss[i]
            x2 = ss[i+1]
            if "Available-Transition" in x1 and "collection_definition" in x2:
                x3 = ss[i+2]
                if "N" in x3:
                    label_N = 0
                    label_Y = 1
                elif "Y" in x3:
                    label_Y = 0
                    label_N = 1
                break
        W.label_Y = label_Y
        W.label_N = label_N
 
        # Re-training finished.

        cmd = "./silas predict -o %s %s/model %s"%(pname,silas_dir,fname)
        os.system(cmd)
        label_Y = W.label_Y
        label_N = W.label_N
        P = []
        pf = open(pname,"r")
        SP = pf.readlines()
        for i in range(1,len(SP)):
            x = SP[i].split(",")
            t = int(x[0])
            x = x[1]
            x = x.replace("\n","")
            x = float(x)
            if t == label_N:
                x = 1.0 - x
            P.append(x)
        pf.close()
    else:
        SData = sg.VectorisePrePostData(PPD,SemTypes)
        SData = SData[0]
        feat = SData[0]
        tgt = SData[1]
        TgtIdx = SemTypes[-1].index("Y")
        if MdlType in ["RF","BNB","LR","SVM","MLP"]:
            """
            for x in feat:
                input(x)
            """
        #if MdlType == "SKCART":
            Q = W.predict_proba(feat)
            P = []
            for x in Q:
                P.append(x[TgtIdx])

        else:
            pppp
    
    return P


