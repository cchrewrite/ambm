
import Bgenlib
import sys
import Bgenlib
import subprocess
import time

# Output essential background knowledge for progol.
def progol_essential():
    res = ["% Essential rules.\n"]
    res.append(":- modeb(*,in_bset(+bobj,+bobj))?")
    res.append("in_bset(X,[X|_]).")
    res.append("in_bset(X,[Y|L]) :- X \= Y, in_bset(X,L).")

    return res

# Output a declaration for isolation examples.
# s --- An example state.
# f --- A functor. e.g. "iso_cond" or "rev_cond".
def make_iso_example_decl(s):
    f = "iso_cond"
    n = len(s)
    arg = "+bobj"
    for i in xrange(n-1):
        arg = arg + ",+bobj"

    res = ["% Isolation Condition Components."]
    res = res + [":- modeh(*,%s(%s))."%(f,arg)]
    res = res + [":- modeb(*,is_bobj(+bobj,#bobj))."]
    res = res + [":- determination(%s/%d,is_bobj/2)."%(f,n)]
    res = res + [":- modeb(*,in_bset(+bobj,#bobj))."]
    res = res + [":- determination(%s/%d,in_bset/2)."%(f,n)]
    #res = res + [":- modeb(*,is_bexp(+bobj,-bobj))."]
    #res = res + [":- modeb(*,is_bexp(+bobj,+bobj,+bobj,#bobj))."]
    #res = res + [":- determination(%s/%d,is_bexp/2)."%(f,n)]
    #res = res + [":- determination(%s/%d,is_bexp/4)."%(f,n)]

    #res = res + [":- modeb(*,iso_cond_good(+bobj,+bobj,+bobj))."]
    #res = res + [":- determination(%s/%d,iso_cond_good/3)."%(f,n)]


    res = res + ["\n% Rules."]
    res = res + [":- modeb(*,in_bset_comp(+bobj,-bobj))."]
    res = res + [":- modeb(*,is_bset(-bobj))."]

    #res = res + [":- modeb(*,is_bexp_comp(+bobj,+bobj,+bobj,-bobj))."]

    #res = res + [":- modeb(*,b_eval(+bobj,-bobj))."]
    #res = res + [":- modeb(*,bCONJ(+bobj,+bobj))."]

    return res



# Output positive or negative examples.
# S --- A set of examples.
# f --- A functor. e.g. "iso_cond" or "rev_cond".
# pn --- Positive of Negative. e.g. "pos" or "neg"
def make_iso_examples(S,pn):
    f = "iso_cond"
    res = []
 
    for x in S:
        y = f + "("
        for u in x:
            y = y + u + ","
        y = y[0:len(y)-1]
        y = y + ")."
        if pn != "pos" and pn != "neg":
            y = pn + y
            print "Warning: pn should be pos or neg! However, it is %s."%pn
        res.append(y)
    return res


# Output type definitions.
def make_type_defs():
    res = [
        "% Type definitions. It seems that these are not necessary for Aleph.",
        "bobj(bTRUE).",
        "bobj(bFALSE).",
        "bobj(lambdaexp).",
    ]
    return res


 
# Output general rules.
def make_general_rules():
    res = [
        "% General Rules.",
        "is_bobj(bTRUE,bTRUE).",
        "is_bobj(bFALSE,bFALSE).",
        "in_bset(X,S) :- in_bset_comp(X,S).",
        "in_bset_comp(X,S) :- is_bset(S), member(X,S).",
    ]
    #f = open("src/python/b_eval_function.pl","r")
    #for x in f.readlines():
    #    res.append(x.replace("\n",""))
    return res

       

# Output general rules.
def make_general_rules():
    res = [
        "% General Rules.",
        "is_bobj(bTRUE,bTRUE).",
        "is_bobj(bFALSE,bFALSE).",
        "in_bset(X,S) :- in_bset_comp(X,S).",
        "in_bset_comp(X,S) :- is_bset(S), member(X,S).",
    ]
    f = open("src/python/b_eval_function.pl","r")
    for x in f.readlines():
        res.append(x.replace("\n",""))
    return res

def convert_pn_examples_to_translist(pn_exp):
    y = []
    for x in pn_exp:
        y.append([x,"",[]])
    return y

def get_types_for_progol(pn_exp):
    sg = Bgenlib.BStateGraphForNN()
    pn_exp_t = convert_pn_examples_to_translist(pn_exp)
    SType = sg.GetSetTypeFromTransList(pn_exp_t)
    #SType = rewrite_state_from_python_to_prolog(SType)
    res = []
    for x in SType:
        res.append(rewrite_state_from_python_to_prolog(x))

        """
        if x[0] == "Dist":
            y = ["bDist"]
            for p in x[1:len(x)]:
                y.append("b"+p)
            res.append(y)
        elif x[0] == "Bool":
            y = ["bBool"]
            for p in x[1:len(x)]:
                y.append("b"+p)
            res.append(y)
        elif x[0] == "Int":
            y = ["bIntNotImplemented"]
            for p in x[1:len(x)]:
                y.append("b"+str(p))
            res.append(y)
        elif x[0] == "Set":
            y = ["bSet"]
            for p in x[1:len(x)]:
                y.append("b"+str(p))
            res.append(y)
        else:
            y = ["bUnknown"]
            for p in x[1:len(x)]:
                y.append("b"+str(p))
            res.append(y)
        """
    return res


# rewrite a state to prolog format.
# e.g. ["1","S0"] => ["b1","bS0"].
def rewrite_state_from_python_to_prolog(s):
    y = []
    for x in s:
        if type(x) == type([]):
            t = []
            for r in x: t.append("b"+r)
            p = set_to_string(t)
        else:
            p = "b" + str(x)
        y.append(p)
    return y


# convert a set to string.
def set_to_string(s):
    y = "bset"
    ss = sorted(s)
    for x in ss:
        y = y + "_" + str(x)
    if y == "bset":
        y = "bsetEmpty"
    return y

# make names of a list of sets.
def make_set_names(P):
    res = []
    for x in P:
        y = set_to_string(x)
        res.append(y)
    return res


# Convert a list to a string, and exclude string notations.
def convert_list_to_string(s):
    y = "["
    for x in s:
        y = y + str(x) + ","
    if y != "[":
        y = y[0:len(y)-1]
    y = y + "]"
    return y

# find all subsets of a set S, and output those with at most N elements.
# Default N = -1: output all subsets.
def sub_sets(S, N = -1):

    subsets = [[]] 

    if N == -1:
        MaxN = len(S)
    else:
        MaxN = N

    while True:
        newsets = []
        for x in subsets:
            for u in S:
                if u in x: continue 
                y = sorted(x + [u])
                if y in subsets: continue
                if y in newsets: continue
                if len(y) > MaxN: continue
                newsets.append(y)
                flag = True
        if newsets == []: break
        subsets = subsets + newsets
    subsets = sorted(subsets)       
    """
    for i in range(len(S) + 1): 
          
        for j in range(i + 1, len(S) + 1): 
              
            sub = S[i:j]
            if len(sub) <= MaxN:
                subsets.append(sub) 
            else:
                break          
    """
    return subsets
  

# Make "in" relations for a single set.
# e.g. 1 in [1,2,3].
# S --- A set.
def make_in_relations(S):
    valS = convert_list_to_string(S)
    nameS = set_to_string(S)
    res = ["% \"in_bset\" relations for " + valS + ".\n"] 
    pname = "in_" + nameS
    pdecl = ":- modeb(*,%s(+bobj))?"%pname
    pdef = "%s(X) :- in_bset(X,%s)."%(pname,valS)
    res = res + [pdecl,pdef]
    return res

# Make "in_bset" relations for all sets in SType.
# SType - The types of all sets.
# N - The maximum number of elements, default (N = -1) means no restriction.
def make_all_in_relations(SType,N = -1):
    res = ["% \"in_bset\" relations.\n"]
    t = []
    for S in SType:
        if S[0] == "bBool": continue
        if S[0] == "bSet": continue
        SS = sub_sets(S[1:len(S)],N)
        for x in SS:
            if x in t: continue
            res = res + make_in_relations(x) + [""]
            t.append(x)
    return res



# Make partial order of set.
# For instance, the set is [1,2,3], then result includes:
# [1,2,3] > [2,3], [1,2,3] > [1,3], [1,2,3] > [1,2],
# [2,3] > [3], [2,3] > [2], [1,3] > [3], [1,3] > [1],
# [1,2] > [2], [1,2] > [1], [3] > [], [2] > [], [1] > []
# S --- A set. N --- Maximum number of elements, default (N = -1) means no restriction.
def make_partial_order_relation_of_set(S, N = -1):
    P = sub_sets(S,N)
    Names = make_set_names(P)
    res = []
    for i in xrange(len(P)):
        x = P[i]
        xs = set(x)
        pname = "bsubst_of_%s"%Names[i]
        res.append("")
        res.append("% \"bsubst_of\" relations for " + Names[i] + ".\n")
        decl = ":- modeb(*,%s(+bobj))?"%pname
        res.append(decl)
        for j in xrange(len(P)):
            y = P[j]
            ys = set(y)
            if ys.issubset(xs):# and not(xs.issubset(ys)):
                rel = "%s(%s)."%(pname,Names[j])
                res.append(rel)
    return res


# Make "bsubst" relations for all sets in SType.
# SType - The types of all sets.
# N - The maximum number of elements, default (N = -1) means no restriction.
def make_all_bsubst_relations(SType,N = -1):
    res = ["% \"bsubst\" relations.\n"]
    t = []
    res = []
    for S in SType:
        if S[0] != "bSet": continue
        SS = make_partial_order_relation_of_set(S[1:len(S)])
        res = res + SS
        #for x in SS:
        #    if x in res: continue
        #    res.append(x)
    return res


  

# Make "is_bool" relations for a Boolean value.
# e.g. X is TRUE.
# S --- A set.
def make_is_bool_relations():
    res = ["% \"is_bool\" relations.\n"]
    for x in ["bTRUE","bFALSE"]: 
        pname = "is_" + x
        pdecl = ":- modeb(*,%s(+bobj))?"%pname
        #pdef = "%s(X) :- X == %s."%(pname,x)
        pdef = "%s(%s)."%(pname,x)
        res = res + [pdecl,pdef]
    return res





# Make "is_bset" rules for all sets in SType.
# SType - The types of all sets.
# N - The maximum number of elements, default (N = -1) means no restriction.
def make_is_bset_rule(SType,N = -1):
    res = ["% \"is_bset\" rules."]
    t = []
    for S in SType:
        if S[0] == "bBool": continue
        if S[0] == "bSet": continue
        SS = sub_sets(S[1:len(S)],N)
        for x in SS:
            if x in t: continue
            #print x
            
            #res = res + make_in_relations(x) + [""]
            t.append(x)
    for x in t:
        y = str(x)
        y = y.replace("\'","")
        y = y.replace("\"","")
        y = "is_bset(" + y + ")."
        res.append(y)
    return res

# Read rules generated by Aleph.
# fn --- filename
def read_aleph_rules(fn):
    f = open(fn,"r")
    rl = ""
    for x in f.readlines():
        rl = rl + x
    rl = rl.replace(" ","")
    rl = rl.replace("\n","")
    rl = rl.split(".")
    res = []
    for x in rl:
        if x == "": continue
        if not(":-" in x):
            y = x[9:len(x)-1]
            y = y.split(",")
            hd = "iso_cond("
            bd = []
            for i in xrange(len(y)):
                p = "V" + str(i)
                hd = hd + p + ","
                q = "is_bobj(%s,%s)"%(p,y[i])
                bd.append(q)
            hd = hd[0:len(hd)-1] + ")"
        else:    
            y = x.split(":-")
            hd = y[0]
            p = y[1] + "."
            i = 0
            j = 0
            l = len(y[1])
            flag = 0
            bd = []
            while i < l:
                if p[j] != "(" and p[j] != ")":
                    j = j + 1
                    continue
                if p[j] == "(":
                    flag = flag + 1
                    j = j + 1
                    continue
                if p[j] == ")" and flag > 1:
                    flag = flag - 1
                    j = j + 1
                    continue
                if p[j] == ")" and flag == 1:
                    u = p[i:j+1]
                    bd.append(u)
                    i = j + 2
                    j = i
                    flag = 0
        res.append([hd] + bd)
    f.close()
    return res

# Remove the "b" prefix from an expression.
# x --- expression
def remove_b_prefix(x):
    y = x.split(" ")
    res = ""
    for p in y:
        if p[0] == "b":
            q = p[1:len(p)]
        else:
            q = p + ""
        res = res + q + " "
    if res[-1] == " ":
        res = res[0:len(res)-1]
    return res

# Convert a rule to a condition.
# r --- rule ; vl --- variable list ; wdir --- working dirctory
def rule_to_cond(r,vl,wdir):

    fid = time.time()
    fid = str(fid).replace(".","")    
    fid = "prolog" + fid

    ul = r[0][9:len(r[0])-1]
    ul = ul.split(",")
    y = []
    for x in r[1:len(r)]:
        u = x
        u = u.replace("("," ( ")
        u = u.replace(")"," ) ")
        u = u.replace("["," [ ")
        u = u.replace("]"," ] ")
        u = u.replace(","," , ")
        for i in xrange(len(ul)):
            p = " " + ul[i] + " "
            q = " b" + vl[i] + " "
            if p in u:
                u = u.replace(p,q)
        print u

        # convert rule to condition.

        u = u.replace(" ","")
        print u

        cond_rewriter = "src/python/conv_rule_to_cond.pl"
        cmd = "swipl -g \"consult(\'%s\'), nl, rule_to_cond(%s), nl, halt\""%(cond_rewriter,u)
        xsahfsa = raw_input("ppppppp")
        pl_res = subprocess.check_output(cmd, shell=True)
        pl_res = pl_res.split("\n")

        cond = pl_res[-2]
        bcond = remove_b_prefix(cond)
        y.append(bcond)

        for xlogg in pl_res: print xlogg       
        print bcond
        fajsdakl = raw_input("qqqqqqq")

    res = "" 
    for x in y:
        res = res + x + " & "
    res = res[0:len(res)-3]

    return res
