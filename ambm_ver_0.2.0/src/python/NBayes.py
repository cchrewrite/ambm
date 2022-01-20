import numpy
import random
import Bmch
from sklearn.naive_bayes import BernoulliNB

"""
X = numpy.random.randint(2, size=(6, 100))
Y = numpy.array([1, 2, 3, 4, 4, 5])
clf = BernoulliNB()
clf.fit(X, Y)

# alpha --- Laplace smoothing parameter (0 for no smoothing).
# binarize --- threshold for binarizing 
BernoulliNB(alpha=1.0, binarize=0.0, class_prior=None, fit_prior=True)
print clf.predict(X[2:3])
print clf.predict_proba(X[2:3])
print numpy.sum(clf.predict_proba(X[2:3]))

"""

# Decode a revision list.
def BNBayes_Decode_Ope_Score(model, feat, opeidx):
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





# Bernoulli Naive Bayes.
class BNBayes(object):
    def __init__(self, data, conffile):


        print("Training BNBayes models...")
        self.neg_prop = Bmch.read_config(conffile,"bnb_neg_prop","float")
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
        print(self.num_labels)
        print(self.labels)


        self.BNBs = []
        
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
                        print("Warning: Not able to find Iso Relation.")
                        break
            feat = sdata + ndata
            tgt = [1] * len(sdata) + [0] * len(ndata)

            # Train BNB
            BNB = BernoulliNB(alpha=1.0, binarize=0.5, class_prior=None, fit_prior=True)
            
            feat = numpy.clip(feat,0,1).astype(int)
            
            BNB.fit(feat, tgt)

            s1 = 0.0
            s2 = 0.0
            rr = BNB.predict_proba(feat)
            for j in xrange(len(tgt)):
                if j < len(sdata): s1 = s1 + rr[j][1]
                else: s2 = s2 + rr[j][1]
            s1 = s1 / len(sdata)
            s2 = s2 / len(ndata)
            print("Average probability for label", self.labels[i], "is Pos---%.2lf vs Neg---%.2lf."%(s1,s2))

            self.BNBs.append(BNB)

        print("BNBayes model training done.")
        return

    def decode(self,feat,label):
        idx = self.labels.index(label)
        res = self.BNBs[idx].predict_proba([feat])
        res = res[0][1]
        return res
