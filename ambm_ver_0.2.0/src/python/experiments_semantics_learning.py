import os
import sys
import time

cmd_list = []

datadir = "Experiments/SemLearnData"
FL = os.listdir(datadir + "/machines/")
FL.sort()
for fn in FL:

    if fn[len(fn)-4:len(fn)] != ".mch": continue

    mch_id = fn[0:len(fn)-4]

    for sem_mdl_type in ["RF","BNB","LR","SVM","Silas"]:

        
        x = "a"
        while x != "y" and x != "n":
            x = input("Evaluating %s with %s?(y/n): "%(fn,sem_mdl_type))
        if x != "y": continue
        

        mchfile = datadir + "/machines/" + fn
        conffile = datadir + "/config/" + sem_mdl_type + "_config"
        resdir = "Experiments/semantics_learning_results"
        mdldir = resdir + "/mdl"
        logdir = resdir + "/log"
        logfile = logdir + "/%s_%s.RESULT"%(mch_id,sem_mdl_type)

        cmd_list = []
        cmd_list.append("mkdir %s"%(resdir))
        cmd_list.append("rm -r %s"%(mdldir))
        cmd_list.append("python3 src/python/b_semantics_learning.py %s %s %s/"%(mchfile,conffile,mdldir))
        cmd_list.append("mkdir %s"%(logdir))
        cmd_list.append("cp %s/RESULTS %s"%(mdldir,logfile))

        csvdir = resdir + "/csvdata/"
        cmd_list.append("mkdir %s"%(csvdir))
        sem_dir = resdir + "/mdl/SemMdlDir/"
        tr_data = csvdir + "/" + mch_id + "_train.csv"
        cv_data = csvdir + "/" + mch_id + "_test.csv"
        cmd_list.append("cp %s/train.csv %s"%(sem_dir,tr_data))        
        cmd_list.append("cp %s/valid.csv %s"%(sem_dir,cv_data))

        for x in cmd_list:
            os.system(x)
        cmd_list = []
        time.sleep(3)


