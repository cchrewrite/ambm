import numpy as np
import gc
import sys
import pickle
import random
import multiprocessing
import time
import threading
import queue

# Silas Model.
class SilasModel(object):
    def __init__(self):
        Data = ""
        SType = ""
        return


# Decode a revision list.
def CART_Decode_Ope_Score(model, feat, opeidx):
    y = []
    for x in feat:
        r = model.decode(x,opeidx)
        y.append(r)
    y = np.asarray(y)
    x = list(range(y.shape[0]))
    z = np.asarray([x,y])
    z = z.T.tolist()
    for i in range(len(z)):
        z[i][0] = int(z[i][0])
    z = sorted(z, key = lambda p: p[1], reverse = True)
    return z



# Regression Tree.
class RegTree(object):
    def __init__(self, data=None, min_var=0.01):

        self.data = data # Features + Targets
        # We can delete some variables to release memory.
        del data
        gc.collect()
        
        self.data_num = self.data.shape[0] # The number of data
        self.feat_dim = self.data.shape[1]-1 # The dimension of features
        self.min_var = min_var # The minimum of variance.
        
        self.LTree = "Nil" # Left tree
        self.RTree = "Nil" # Right tree
        self.AttrIdx = None # The index of attribute for deciding left / right trees.

        # Compute the prediction value of this node.
        self.Value = np.mean(self.data[:,-1])
        
        # Compute the variance of all data.
        self.Var = np.var(self.data[:,-1])
        #print "Var is:",self.Var
        if self.Var < self.min_var:
            self.GainVar = -1
            self.LData = None
            self.RData = None
            
            # We can delete some variables to release memory.
            del self.data
            gc.collect()
            
            return
        else:
            self.GainVar = -1
            self.LData = None
            self.RData = None
            for i in range(self.feat_dim):
                x = self.data
                
                lx = x[x[:,i] > 0.5]
                rx = x[x[:,i] <= 0.5]
                
                if lx.shape[0] > 0 and rx.shape[0] > 0:
                    lvar = np.var(lx[:,-1])
                    rvar = np.var(rx[:,-1])
                    gvar = lvar * lx.shape[0] + rvar * rx.shape[0]
                    # Use gvar - self.GainVar < -0.000001 instead of gvar < self.GainVar to overcome precision issues.
                    if gvar - self.GainVar < -0.000001 or self.GainVar == -1:
                        self.GainVar = gvar
                        self.LData = [lx]
                        self.RData = [rx]
                        self.AttrIdx = [i]
                    # If gvar is very close to self.GainVar, then we randomly select a attribute.
                    elif gvar - self.GainVar < 0.000001:
                        self.LData.append(lx)
                        self.RData.append(rx)
                        self.AttrIdx.append(i)
                else:
                    continue
                
            if self.GainVar != -1:

                i = int(random.random() * len(self.AttrIdx))
                self.AttrIdx = self.AttrIdx[i]
                self.LData = self.LData[i]
                self.RData = self.RData[i]
            
                # We can delete some variables to release memory.
                del self.data
                del lx
                del rx
                gc.collect()

                self.LTree = RegTree(self.LData,self.min_var)
                self.RTree = RegTree(self.RData,self.min_var)
                
                # Again, we can delete some variables to release memory.
                del self.LData
                del self.RData
                gc.collect()
                
             
        return  
        

    # Given a feature x, decode it based on the decision tree.
    def decode(self, x):
        if self.AttrIdx == None:
            res = self.Value
        else:
            if x[self.AttrIdx] > 0.5:
                res = self.LTree.decode(x)
            else:
                res = self.RTree.decode(x)
        return res




# Multi-Dimensional Regression Tree.
# min_var --- the minimal variance.
# data_prop --- the proportion of training data.
class MultiRegTree(object):
    def __init__(self, data=None, min_var=0.01, data_prop=1.0):

        self.data = data # Features + Targets

        # We can delete some variables to release memory.
        del data
        gc.collect()

        # The number of trees is equal to the number of operations.
        self.num_tree = 0
        for x in self.data:
            if x[1]+1 > self.num_tree:
                self.num_tree = x[1]+1

        # Convert labels to vector representations.
        self.feat = []
        self.tgt = []
        for x in self.data:
            u = x[0]
            v = x[1]
            if not(u in self.feat):
                self.feat.append(u)
                z = [0] * self.num_tree
                z[v] = 1
                self.tgt.append(z)
            else:
                i = self.feat.index(u)
                self.tgt[i][v] = 1

        # We can delete some variables to release memory.
        del self.data
        gc.collect()

        """
        # Make isolation supplementary.
        iso_feat = []
        num_data = len(self.tgt)
        num_iso = num_data
        fd = len(self.feat[0])
        fdh = int(fd / 2)
        ni = 0
        iflag = 0
        while ni < num_iso:
            p = int(random.random() * num_data)
            q = int(random.random() * num_data)
            u = self.feat[p][0:fdh] + self.feat[q][fdh:fd]
            if not(u in self.feat):
                iso_feat.append(u)
                ni += 1
                iflag = 0
            else:
                iflag += 1
                if iflag > 10000:
                    print("Warning: Not able to find Iso Relation.")
                    break
        
        self.feat = self.feat + iso_feat
        z = [0] * self.num_tree
        iso_tgt = [z] * len(iso_feat)
        self.tgt = self.tgt + iso_tgt
        """

        # Drop some data to prevent overfitting.
        if data_prop < 1.0:
            x = []
            t = []
            for i in range(len(self.feat)):
                if random.random() <= data_prop:
                    x.append(self.feat[i])
                    t.append(self.tgt[i])
            self.feat = x
            self.tgt = t
            del x
            del t
            gc.collect()
            
        self.feat = np.asarray(self.feat)
        self.tgt = np.asarray(self.tgt)

        # Generate trees.        
        self.tree = []
        for i in range(self.num_tree):
            v = self.tgt[:,i:i+1]
            dt = np.concatenate((self.feat,v),axis=1)
            new_tree = RegTree(data=dt,min_var=min_var)
            self.tree.append(new_tree)

        
        # We can delete some variables to release memory.
        del self.feat
        del self.tgt
        gc.collect()

        return  
        

    """
    def convert_data_by_classes(x,idx):
        y = []
        for p in x:
            r = [0] * num_ope
            r[p[1]] = 1
            u = p[0] + r
            y.append(u)
        res = np.asarray(y)
        return res
    """

    # x --- feature ; idx --- the index of target
    def decode(self,x,idx):
        if idx >= self.num_tree:
            return 0
        return self.tree[idx].decode(x)



# Random Forest of Multi-Dimensional Regression Tree.
from multiprocessing.pool import ThreadPool
class RandMultiRegTree(object):
    def __init__(self, data=None, num_tree=None, min_var_exp_scale=[-8,-2], data_prop=1.0, use_mp=False):

        self.data = data # Features + Targets

        # We can delete some variables to release memory.
        del data
        gc.collect()

        self.num_tree = num_tree

        # Generate a random forest.
        self.tree = []
        vb = min_var_exp_scale[0]
        vs = min_var_exp_scale[1] - min_var_exp_scale[0]
        ldt = len(self.data)

        if use_mp == True:
            tree_threads = []
            tree_args = []

            manager = multiprocessing.Manager()
            re_dict = manager.dict()

        for i in range(self.num_tree):
            # Randomly select minimal variance.
            p_r = random.random() * vs + vb
            p_var = np.exp(p_r)
            print("Training Tree %d, min_var is set to %lf."%(i+1,p_var))
            p_data = []
            """
            # Randomly select training data. The size is 50%.
            for j in range(ldt / 2 + 1):
                k = int(random.random() * ldt)
                p_data.append(self.data[k])
            """

            # Generate a tree.
            if use_mp == False:
                # Do not use multi-processing
                new_tree = MultiRegTree(data=self.data,min_var=p_var,data_prop=data_prop)
                self.tree.append(new_tree)
            else:
                # Use multi-processing
                t = multiprocessing.Process(target=self.create_a_tree, args=(self.data,p_var,data_prop,i,re_dict))
                t.start()
                tree_threads.append(t)

        if use_mp == True:
            print("Using Multiprocessing to train CARTs.")
            for t in tree_threads:
                t.join()

            print(re_dict.values())
            self.tree = re_dict.values()

            if len(self.tree) != self.num_tree:
                ppp
        print("Training Done.")

        # We can delete some variables to release memory.
        del self.data
        gc.collect()

        return
              
    def create_a_tree(self, data, min_var, data_prop, i, re_dict):
        x = MultiRegTree(data=data, min_var=min_var, data_prop=data_prop)
        re_dict[i] = x
        return 0
 
    # x --- feature ; idx --- the index of target
    def decode(self,x,idx):
        y = []
        for i in range(self.num_tree):
            s = self.tree[i].decode(x,idx)
            y.append(s)
        y = np.mean(y)
        return y

    def predict_proba(self, feat):
        res = []
        for x in feat:
            y = []
            ys = 0
            for idx in range(self.tree[0].num_tree):
                s = self.decode(x,idx)
                y.append(s)
                ys = ys + s
            y = np.array(y) / ys
            res.append(y)
        res = np.array(res)
        return res

    def score(self, feat, tgt):
        y = self.predict_proba(feat)
        pred = np.argmax(y, axis = 1)
        Acc = 0.0
        for i in range(len(tgt)):
            if tgt[i] == pred[i]:
                Acc = Acc + 1
        Acc = Acc / len(tgt)
        return Acc

 
       
""" 
x = [[1,0,0,1,0,1,1,0],[0,0,1,0,1,1,0,0],[0,1,0,0,0,1,1,1],[1,1,1,1,1,1,0,1],[0,1,1,1,1,1,0,1]]
X = RegTree(data=x,min_var=0.1)
f = open("res.tree","wb")
pickle.dump(X,f)
f.close()
"""

"""
for p in x:
    print p, X.decode(p)
"""

# Try multiprocessing on Ubuntu.
"""
import multiprocessing
num_cpus = multiprocessing.cpu_count()
p = multiprocessing.Pool(num_cpus)
y = p.map(X.decode,x)
print y
"""
