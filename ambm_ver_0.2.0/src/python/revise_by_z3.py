from z3 import *


import sys
print "Revising the faulty state..."
print "Source mch File: ", sys.argv[1]
print "Faulty State File: ", sys.argv[2]
print "Maximum Cost: ", sys.argv[3]
print "Output File: ", sys.argv[4]

spname = sys.argv[1]

with open(spname) as sp:
    mdl = sp.readlines()
mdl = [x.strip() for x in mdl] 


fsname = sys.argv[2]

with open(fsname) as fs:
    fstate = fs.readlines()
fstate = [x.strip() for x in fstate]

max_cost = float(sys.argv[3])

def z3_abs(x):
    return If(x >= 0, x, -x)

def z3_bool(x):
    return If(x, 1, 0)


def cost_constraint(fstate, max_cost, cost_type = 'absolute'):
    if cost_type == 'absolute':
        res = ""
        for i in xrange(len(fstate)/2):
            p = i * 2
            q = i * 2 + 1
            if i > 0:
                res = res + " + "
            if fstate[q] != "FALSE" and fstate[q] != "TRUE":
                subs = "z3_abs(%s - %s)"%(fstate[p],fstate[q])
            else:
                if fstate[q] == "TRUE":
                    subs = "z3_bool(%s)"%fstate[p]
                else:
                    subs = "z3_bool(Not(%s))"%fstate[p]
            res = res + subs

        res = res + " <= %f"%(max_cost)
        print "Cost constraint is: " + res
        return res
    elif cost_type == 'square':
        res = ""
        for i in xrange(len(fstate)/2):
            p = i * 2
            q = i * 2 + 1
            if i > 0:
                res = res + " + "
            subs = "(%s - %s)"%(fstate[p],fstate[q])
            res = res + subs + " * " + subs
        res = res + " <= %f * %f"%(max_cost,max_cost)
        print "Cost constraint is: " + res
        return res
    else:
        print "Error: Cost type not defined!"
        return "False"

def b_def_to_z3_def(u):
    len_u = len(u)
    if len_u > 4 and u.find('BOOL') + 4 == len_u:
        vble = u[0:len_u-3-4]
        res1 = "%s = Bool(\'%s\')"%(vble,vble)
        res2 = ""
    elif len_u > 7 and u.find('NATURAL') + 7 == len_u:
        vble = u[0:len_u-3-7]
        res1 = "%s = Int(\'%s\')"%(vble,vble)
        res2 = "%s >= 0"%vble
    elif len_u > 7 and u.find('INTEGER') + 7 == len_u:
        vble = u[0:len_u-3-7]
        res1 = "%s = Int(\'%s\')"%(vble,vble)
        res2 = ""
    # The definition of NAT and INT is not good in ProB, because it defines NAT < maxint and INT < maxint, where maxint seems to be 4. Therefore, we report a warning for NAT and INT here.
    elif len_u > 3 and u.find('NAT') + 3 == len_u:
        print("Warning: A variable is defined as NAT.")
        vble = u[0:len_u-3-3]
        res1 = "%s = Int(\'%s\')"%(vble,vble)
        res2 = "%s >= 0"%vble
    elif len_u > 3 and u.find('INT') + 3 == len_u:
        print("Warning: A variable is defined as INT.")
        vble = u[0:len_u-3-3]
        res1 = "%s = Int(\'%s\')"%(vble,vble)
        res2 = ""
    else:
        res1 = ""
        res2 = u
    return [res1, res2]


def get_invariants(mdl):
    mdllen = len(mdl)
    p = -1
    for i in xrange(mdllen):
        if mdl[i] == 'INVARIANT':
            p = i
            break
    if p == -1:
        print "Warning: Invariants not found!"
        return [[],[]]
    p = p + 1
    q = p
    for i in xrange(mdllen):
        if mdl[i] in ['ASSERTIONS','INITIALIZATION','INITIALISATION','OPERATIONS','END']:
            q = i
            break
    if p == q:
        print "Warning: Invariants not found!"
        return [[],[]]
    for i in xrange(q-p):
        mdl[p + i] = mdl[p + i].replace("& ","")
        mdl[p + i] = process_not(mdl[p + i])
        mdl[p + i] = mdl[p + i].replace(" = "," == ")


    res = [[],[]]
    for i in xrange(q-p):
        u = mdl[p + i]
        #if u.find('NATURAL'):
        res_tmp = b_def_to_z3_def(u)
        if res_tmp[0] != "":
            res[0].append(res_tmp[0])
        if res_tmp[1] != "":
            res[1].append(res_tmp[1])
    return res

    """
    print res
    for i in xrange(len(res[0])):
        exec(res[0][i])
    s = Solver()
    for i in xrange(len(res[1])):
        s.add(eval(res[1][i]))

    #s.add(res[1])

        #if 'NATURAL' in mdl[u]: print (mdl[u])

    while s.check() == sat:
        print s.model()
        need to add all variables here. s.add(Or(x != s.model()[x], y != s.model()[y]))
    """

def process_not(x):
    y = x
    while y.find('not(') != -1:
        p = y.find('not(')
        y = y[:p] + 'Not(And(' + y[p+4:]
        p = p + 9
        u = 1
        while u > 0:
            if y[p] == '(':
                u = u + 1
            elif y[p] == ')':
                u = u - 1
            p = p + 1
        y = y[:p] + ')' + y[p:]
    return y
        
        

def get_preconditions(mdl):
    mdllen = len(mdl)
    p = -1
    for i in xrange(mdllen):
        if mdl[i] == 'PRE':
            p = i
            break
    if p == -1:
        print "Warning: Preconditions not found!"
        return []

    res = []
    p = 0
    while True:
        while p < mdllen:
            if mdl[p] == 'PRE':
                break
            p = p + 1
        if p == mdllen:
            break
        p = p + 1
        q = p
        while q < mdllen:
            if mdl[q] == 'THEN':
                break
            q = q + 1
        if q == mdllen:
            print "Warning: Error occurs when finding preconditions!"
            return res
        pre_conj = ""
        for i in xrange(q-p):
            pre_conj = pre_conj + mdl[p + i]
        
            #mdl[p + i] = mdl[p + i].replace("not","Not")
        pre_conj = process_not(pre_conj)
        pre_conj = pre_conj.replace("&",",")
        pre_conj = pre_conj.replace(" = "," == ")
        pre_conj = pre_conj.replace(" TRUE"," True")
        pre_conj = pre_conj.replace(" FALSE"," False")
        res.append("And(%s)"%pre_conj)
        p = q + 1
    return res
"""
    res = [[],[]]
    for i in xrange(q-p):
        u = mdl[p + i]
        #if u.find('NATURAL'):
        print u
        res_tmp = b_def_to_z3_def(u)
        print(res_tmp[0],res_tmp[1])
        if res_tmp[0] != "":
            res[0].append(res_tmp[0])
        if res_tmp[1] != "":
            res[1].append(res_tmp[1])
 
"""

def get_all_solutions(inv, pre, cost_constraint):
    for i in xrange(len(inv[0])):
        exec(inv[0][i])
    s = Solver()
    s.add(eval(cost_constraint))
    for i in xrange(len(inv[1])):
        s.add(eval(inv[1][i]))
    print pre
    s.add(eval(pre))

    #s.add(res[1])

        #if 'NATURAL' in mdl[u]: print (mdl[u])

    res = []
    while s.check() == sat:
        m = s.model()
        res.append(m)
        curr = "Or("
        for i in m:
            curr = curr + str(i) + " != " + "m[%s]"%str(i) + ", "
        curr = curr[:len(curr)-2] + ')'
        s.add(eval(curr))
    return res


def model_to_assignment(m):
    res = "sequence(pos(0,0,0,0,0,0),["
    for i in m:
        
        if str(m[i]) == "True":
            asgm = "assign(pos(0,0,0,0,0,0),[identifier(pos(0,0,0,0,0,0),%s)],[boolean_true(pos(0,0,0,0,0,0))]),"%str(i)
        elif str(m[i]) == "False":
            asgm = "assign(pos(0,0,0,0,0,0),[identifier(pos(0,0,0,0,0,0),%s)],[boolean_false(pos(0,0,0,0,0,0))]),"%str(i)
        else:
            asgm = "assign(pos(0,0,0,0,0,0),[identifier(pos(0,0,0,0,0,0),%s)],[integer(pos(0,0,0,0,0,0),%s)]),"%(str(i),str(m[i]))
        res = res + asgm
    res = res[:len(res)-1]
    res = res + "])"
    return res

inv = get_invariants(mdl)
pre_list = get_preconditions(mdl)
ccstr = cost_constraint(fstate, max_cost, cost_type = 'absolute')

#print process_not("not(x >= 0, not(y >= 0,x=1,p=0,and(not(p=0))), z >= 0)")

# Output assignments to a file.
sln = get_all_solutions(inv,pre_list[0],ccstr)
outfile = open(sys.argv[4],'w')
outfile.write('[\n')
for i in xrange(len(sln)):
    print i,sln[i]
    if (i > 0):
        outfile.write(',\n')
    outfile.write(model_to_assignment(sln[i]))
outfile.write('\n].\n')

outfile.close()

