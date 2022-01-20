import os
import sys
import time

cmd_list = []

for tm in range(11):

    num_faults = 100
    sd = 777 + tm

    datadir = "Experiments/AbsMacModData"
    FL = os.listdir(datadir + "/machines/")
    FL.sort()

    for fn in FL:
        #fn = "BinomialCoefficientConcurrent.mch"
        #fn = "Mikrowelle.mch"

        #if fn != "Cruise_finite1.mch": continue

        if fn[len(fn)-4:len(fn)] != ".mch": continue

        mch_id = fn[0:len(fn)-4]

        
        for sem_mdl_type in ["RF","BNB","LR","SVM","Silas"]:

            #sem_mdl_type = "SKCART"

            x = "a"
            while x != "y" and x != "n":
                x = input("Evaluating %s with %s and %d faults, seed = %d?(y/n): "%(fn,sem_mdl_type,num_faults,sd))
            if x != "y": continue

            mchfile = datadir + "/machines/" + fn
            conffile = datadir + "/config/" + sem_mdl_type + "_config"
            resdir = "Experiments/abstract_machine_modification_results"
            mdldir = resdir + "/mdl"
            logdir = resdir + "/log"
            logfile = logdir + "/%s_%s_nf%d_sd%d.RESULT"%(mch_id,sem_mdl_type,num_faults,sd)

            cmd_list = []
            cmd_list.append("mkdir %s"%(resdir))
            cmd_list.append("rm -r %s"%(mdldir))
            cmd_list.append("mkdir %s"%(mdldir))
            cmd_list.append("python3 src/python/make_faulty_machine_A.py %s %d %d %s/faulty_model"%(mchfile,num_faults,sd,mdldir))
            cmd_list.append("python3 src/python/abstract_machine_batch_modification.py %s/faulty_model/result.mch NEW %s/faulty_model/answer.txt %s %s/repaired_model/"%(mdldir,mdldir,conffile,mdldir))
            #cmd_list.append("python3 src/python/state_graph_comparison.py %s/repaired_model/result.mch %s %s/comparison/"%(mdldir,mchfile,mdldir))

            cmd_list.append("mkdir %s"%(logdir))
            cmd_list.append("cp %s/repaired_model/summary %s"%(mdldir,logfile))
            for x in cmd_list:
                os.system(x)
            cmd_list = []
            time.sleep(3)


