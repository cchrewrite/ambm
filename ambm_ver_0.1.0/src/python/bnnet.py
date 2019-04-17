from nnet.nnetlib import *

import numpy
import logging

logging.basicConfig()
tr_log = logging.getLogger("mlp.optimisers")
tr_log.setLevel(logging.DEBUG)

rng = numpy.random.RandomState([2018,03,31])
rng_state = rng.get_state()

num_tr_data = 10000
lrate = 0.25 / 4
max_epochs = 100000 / num_tr_data

BNNet = BNNet_Init([114, 128, 128, 20], rng)
lr_scheduler = LearningRateFixed(learning_rate=lrate, max_epochs=max_epochs)
BNNet, Tr_Stat, Cv_Stat = BNNet_Train(BNNet, lr_scheduler, "train.txt", "valid.txt")

x1 = "0.55 0.95 0.15 1 0 0 1 0 1 0 0 0 1 1 0 0 0 0 0 0 1 1 0 0 0 1 1 1 1 1 0 0 0 1 0 0 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0 1 0 0 0 0 0 1.0 0.95 0.15 0 1 0 1 0 1 0 0 0 0 0 0 0 0 0 0 0 1 1 0 0 0 1 1 1 1 1 0 0 0 1 0 0 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0 1 0 0 0 0 0"
# 8
x2 = "0.55 0.95 0.55 1 0 0 1 0 1 1 0 1 0 0 0 0 0 1 0 1 0 0 0 0 0 1 1 1 1 1 0 0 0 1 0 0 0 0 0 0 0 0 0 0 0 1 0 0 0 0 0 1 0 0 0 0 0 0.55 0.95 0.85 1 0 0 1 0 1 1 0 1 0 0 0 0 0 1 0 1 0 0 0 0 0 1 1 1 1 1 0 0 0 1 0 0 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0 1 0 0 0 0 0"
# 16
x3 = "0.55 0.4 0.85 1 0 0 1 0 1 0 0 0 0 0 0 0 0 1 0 1 0 0 0 0 0 1 1 1 1 1 0 0 0 1 0 0 0 0 0 0 0 0 0 0 0 1 0 0 0 0 1 0 0 0 0 0 0 0.55 0.95 0.85 1 0 0 1 0 1 0 0 0 0 0 0 0 0 1 0 1 0 0 0 0 0 1 1 1 1 1 0 0 0 1 0 0 0 0 0 0 0 0 0 0 0 1 0 0 0 0 0 1 0 0 0 0 0"
# 0
x4 = "0.6 0.35 0.25 1 0 0 1 0 1 0 0 0 0 0 0 0 0 0 0 0 1 1 0 0 0 1 1 1 1 1 0 0 0 0 0 0 0 1 0 0 0 0 1 0 0 0 0 0 0 0 0 1 0 0 0 0 0 0.6 0.4 0.25 1 0 0 1 0 1 0 0 0 1 1 0 0 0 0 0 0 1 1 0 0 0 1 1 1 1 1 0 0 0 0 0 0 0 1 0 0 0 0 1 0 0 0 0 0 0 0 0 1 0 0 0 0 0"
# 15
x5 = "0.9 0.05 0.5 1 0 0 1 0 1 0 0 0 0 0 0 0 0 0 0 0 1 1 0 0 0 1 1 1 1 1 0 0 0 1 0 0 0 0 0 0 0 0 1 0 0 0 0 0 0 0 0 1 0 0 0 0 0 0.9 0.05 0.0 1 0 0 1 0 1 0 0 0 0 0 0 0 0 0 0 0 1 1 0 0 0 1 1 1 1 1 0 0 0 1 0 0 0 0 0 0 0 0 1 0 0 0 0 0 0 0 0 1 0 0 0 0 0"
# 10
x6 = "0.3 0.4 0.4 1 0 0 1 0 1 0 0 0 1 1 0 0 0 0 0 0 1 1 0 0 0 1 1 1 1 1 0 0 0 0 0 0 0 1 0 0 0 0 1 0 0 0 0 0 0 0 0 1 0 0 0 0 0 0.3 1.0 0.4 1 0 0 1 0 1 0 0 0 1 1 0 0 0 0 0 0 0 0 0 0 0 1 0 1 0 1 0 0 0 0 0 0 0 1 0 0 0 0 1 0 0 0 0 0 0 0 0 1 0 0 0 0 0"
# 13

x = [x1,x2,x3,x4,x5,x6]
y = ""
for i in xrange(len(x)):
    y = y + "[" + x[i].replace(" ",",") + "],"

feat = numpy.asarray(eval("[%s]"%y))
z = BNNet_Decode_Ope_Score(BNNet, feat, 20)
print z
