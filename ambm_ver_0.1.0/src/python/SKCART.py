import numpy
import random
import Bmch
from sklearn.ensemble import RandomForestRegressor
from sklearn.ensemble import RandomForestClassifier

# Decode a revision list.
def SKCART_Decode_Ope_Score(model, feat, opeidx):
    y = []
    for x in feat:
        r = model.decode(x,opeidx)
        y.append(r)
    y = numpy.asarray(y)
    x = list(xrange(y.shape[0]))
    z = numpy.asarray([x,y])
    z = z.T.tolist()
    for i in xrange(len(z)):
        z[i][0] = int(z[i][0])
    z = sorted(z, key = lambda p: p[1], reverse = True)
    return z



# Scikit-learn CART random forest.
class SKCART(object):
    def __init__(self, data, conffile):


        print "Training SKCART models..."
        self.neg_prop = Bmch.read_config(conffile,"skcart_neg_prop","float")
        self.num_tree = Bmch.read_config(conffile,"skcart_num_tree","int")
        self.min_imp_exp = Bmch.read_config(conffile,"skcart_min_imp_exp","float")
        self.max_imp_exp = Bmch.read_config(conffile,"skcart_max_imp_exp","float") 

        vb = self.min_imp_exp
        vs = self.max_imp_exp - self.min_imp_exp

        self.num_labels = 0
        self.labels = []
        for x in data:
            v = x[1]
            if not(v in self.labels):
                self.labels.append(v)
                self.num_labels = self.num_labels + 1
            else:
                continue

        self.labels.sort()
        print self.num_labels
        print self.labels


        self.CARTs = []
        
        for i in xrange(self.num_labels):

            # Make positive data.
            sdata = [u[0] for u in data if u[1] == self.labels[i]]
            

            # Make negative data.
            fd = len(sdata[0])
            fdh = fd / 2

            num_data = len(sdata)
            num_iso = len(sdata) * self.neg_prop
            ni = 0
            iflag = 0
            ndata = []
            while ni < num_iso:
                p = int(random.random() * num_data)
                q = int(random.random() * num_data)
                u = sdata[p][0:fdh] + sdata[q][fdh:fd]
                if not(u in sdata):
                    ndata.append(u)
                    ni += 1
                    iflag = 0
                else:
                    iflag += 1
                    if iflag > 10000:
                        print "Warning: Not able to find Iso Relation."
                        break
            feat = sdata + ndata
            tgt = [1] * len(sdata) + [0] * len(ndata)

            # Train CART
            p_r = random.random() * vs + vb
            p_var = numpy.exp(p_r)
            CART = RandomForestRegressor(n_estimators = self.num_tree, min_impurity_decrease = p_var)
            
            feat = numpy.clip(feat,0,1).astype(int)
            
            CART.fit(feat, tgt)

            s1 = 0.0
            s2 = 0.0
            rr = CART.predict(feat)

            for j in xrange(len(tgt)):
                if j < len(sdata): s1 = s1 + rr[j]
                else: s2 = s2 + rr[j]
            s1 = s1 / len(sdata)
            s2 = s2 / len(ndata)
            print "Average probability for label", self.labels[i], "is Pos---%.2lf vs Neg---%.2lf."%(s1,s2)

            self.CARTs.append(CART)

        print "BNBayes model training done."
        return

    def decode(self,feat,label):
        idx = self.labels.index(label)
        res = self.CARTs[idx].predict([feat])
        res = res[0]
        return res



