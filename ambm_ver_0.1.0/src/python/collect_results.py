import os
import sys



fdir = "tmpfile/"
logfile = "exptmp.rev.mch.log"

def CollectLog(fdir, logfile):

    fnames = os.listdir(fdir)
    fnames.sort()
    nep = 0
    num_iso = 0
    num_rev = 0
    while True:
        if not("%d"%(nep+1) in fnames):
            break
        fp = fdir + "%d/"%nep + logfile
        f = open(fp,"r")
        x = f.readline()
        if "Use Isolation." in x:
            num_iso += 1
        if "Use Revision." in x:
            num_rev += 1

        f.close()
        nep = nep + 1

    print "NUM ISO: %d."%num_iso
    print "NUM REV: %d."%num_rev
    print "Totally %d epochs."%nep

