
import Bgenlib
import sys
import subprocess
import time
import itertools
import os
import Bmch
import random
from nltk.parse.generate import generate
from nltk import CFG

# Use CFG to simplify repairs.
# RL --- List of Repairs
# DL --- State Diagram
# VL0 --- List of Variables
# conffile --- configuration file
# wdir --- working directory
def CFGRepairSimplification(RL,DL,VL0,conffile,wdir):

    cmd = "mkdir %s"%wdir
    os.system(cmd)

    # VL - rewrite function variables as single variables
    VL = VL0 + []
    VL = [v.replace("|->","_arg_comma_") for v in VL]
    VL = [v.replace("((","_double_braket_left_") for v in VL]
    VL = [v.replace("))","_double_braket_right_") for v in VL]

    RLS = RL + []
    RLS.sort(key = lambda x: x[1])
    RLT = []
    for i in range(len(RLS)):
        if i == 0:
            P = []
        elif i > 0 and RLS[i][1] != RLS[i-1][1]:
            RLT.append(P)
            P = []
        P.append(RLS[i])
        if i == len(RLS)-1:
            RLT.append(P)

    # PT --- List of each operation's transitions that are not changed
    PLT = []
    for i in range(len(RLT)):
        op = RLT[i][0][1]
        # FL --- List of faulty transitions
        FL = []
        for X in RLT[i]:
            FL.append([X[0],X[1],X[2]])
        P = []
        for X in DL:
            if X[1] != op: continue
            if X in FL: continue
            P.append(X)
        PLT.append(P)


    L = Bmch.read_config(conffile,"max_CFG_length","int")
    CFGS = []
    # Generate substitutions for each operation.
    for k in range(len(RLT)):
        X = RLT[k]
        TL = []
        for U in X:
            TL.append([U[0],U[1],U[3]])
        
        op = TL[0][1] + ""
        sdir = wdir + "/" + op + "_simp/"
        Y = CFG_Substitution_Generator(TL,VL,conffile,sdir)
        TP = transition_partition(TL,VL,Y)

        PL = PLT[k]
        # SPS --- stable pre-states
        SPS = []
        for P in PL:
            SPS.append(P[0])

        for i in range(len(TP)):

            SC = TP[i]

            subs = convert_CFG_subs_to_str(SC[0])

            # Make if condition
            
            pexp = []
            for x in SC[1]:
                if not (x[0] in pexp):
                    pexp.append(x[0])
            pexp = sorted(pexp)

            cond = convert_pexp_to_cond(pexp,VL)

            # rewrite _arg_comma_ as commas
            cond = cond.replace("_arg_comma_", "|->")
            cond = cond.replace("_double_braket_left_", "((")
            cond = cond.replace("_double_braket_right_", "))")
            subs = subs.replace("_arg_comma_", "|->")
            subs = cond.replace("_double_braket_left_", "((")
            subs = cond.replace("_double_braket_right_", "))")

            CFGS.append([op,cond,subs])
    
    return CFGS


def convert_pexp_to_cond(pexp,VL):
    res = ""
    for j in range(len(pexp)):
        X = pexp[j]
        P = ""
        for i in range(len(X)):
            if type(X[i]) == type([]):
                Y = Bmch.convert_python_set_to_b_string(X[i])
            else:
                Y = str(X[i])
            V = VL[i]
            VeY = V + " = " + Y
            if i > 0:
                P = P + " & "
            P = P + VeY
        P = "( " + P + " )"
        if j > 0:
            res = res + " or "
        res = res + P
    return res

# Generate CFG substitution candidates
# TL --- List of Transitions for an Operation
# VL --- Variable List
# conffile --- configuration file
# wdir --- working directory
def CFG_Substitution_Generator(TL,VL,conffile,wdir):

    L = Bmch.read_config(conffile,"max_CFG_length","int")

    cmd = "mkdir %s"%wdir
    os.system(cmd)

    op = TL[0][1]
    
    print("====== VT <-- GetVariableTypes(TL) ======")
    sg = Bgenlib.BStateGraphForNN()
    VT = sg.GetSetTypeFromTransList(TL)
    #for x in VT: print x 

    print("====== PPTL <-- ConvertToPreAndPostFormat(TL,VL) ======" )
    PPTL = Convert_Transitions_To_Pre_Post_Operations(TL,VL)

    print("====== CFGL <-- GenerateCFGOperations(VT,VL) ======")
    CFGL = GenerateCFGOperations(VT,VL,conffile,wdir)

    print("====== CM <-- CoverageModel(VT,VL,PPTL,CFGL) ======")
    CM = GenerateCoverageModel(VT,VL,PPTL,CFGL)
    fn = wdir + "/CM.mch"
    Bmch.print_mch_to_file(CM,fn)
    mch = CM + []
    CM = fn

    print("====== D <-- StateDiagram(CM) ======")
    D = "%s/D.txt"%wdir
    #bscope = Bmch.generate_training_set_condition(mch)
    oscmd = "./../ProB/probcli %s -model_check -df -p MAX_DISPLAY_SET -1 -p MAX_INITIALISATIONS %d -p MAX_OPERATIONS %d -noinv -nodead -spdot %s -c"%(CM,len(PPTL)*10,len(CFGL)*10,D)
    os.system(oscmd)
    sg = Bgenlib.BStateGraphForNN()
    sg.ReadStateGraph(D)
    D = sg.GetTransList()
    #for x in D: print x
    #print len(D)

    print("====== CSL <-- FindAllSubstitutionCandidates(D,CFGL) ======")
    CSL = FindAllSubstitutionCandidates(D,CFGL)


    return CSL

def FindAllSubstitutionCandidates(D,CFGL):

    # PPS --- pre and post-states in TS (status 0 --> status 1).
    PPS = []
    for X in D:
        if X[0][0] == "0" and X[2][0] == "1":
            P = X[2][1:len(X[2])]
            if not(P in PPS):
                PPS.append(P)

    # TS --- transitions for substitution (status 1 --> status 2)
    TS = []
    for i in range(len(PPS)):
        TS.append([])
    for X in D:
        if X[0][0] == "1" and X[2][0] == "2":
            P = X[0][1:len(X[0])]
            i = PPS.index(P)
            TS[i].append(X[1])

    res = []
    for i in range(len(PPS)):
        SL = TS[i]
        if len(SL) == 0:
            print("WARNING: Cannot find any substitution for",PPS[i])
            continue
        R = []
        for subs in SL:
            j = int(subs[5:len(subs)])
            y = CFGL[j][1] + "" 
            R.append(y)
        L = len(PPS[i])
        PreS = PPS[i][0:int(L/2)]
        PostS = PPS[i][int(L/2):L]
        T = [PreS,"CurrentOperation",PostS]
        res.append([R,T])

    return res
    

def ExtractVbleIndexList(VL):
    VN = []
    for x in VL:
        y = x.split("(")
        if not(y[0] in VN):
            VN.append(y[0])

    res = []
    for i in range(len(VN)):
        P = []
        for x in VL:
            y = x.split("(")
            if y[0] != VN[i]: continue
            if len(y) == 1: break
            y = y[1].replace(")","")
            if not(y in P):
                P.append(y)
        P.sort()
        res.append([VN[i],P])
    return res

def GenerateCoverageModel(VT,VL,PPTL,CFGL):
    PPVL = Generate_Pre_And_Post_Variables(VL)
    PreVL = PPVL[0]
    PostVL = PPVL[1]

    """
    print "VT:"
    for x in VT: print x
    print "VL:"
    for x in VL: print x
    """

    # Collect all distinct elements.
    UnivSet = ["ThisElementMeansNothing"]
    for T in VT:
        if T[0] != "Dist" and T[0] != "Set":
            continue
        for X in T[1:len(T)]:
            if not(X in UnivSet) and Bmch.CanRepresentInt(X) != True:
                UnivSet.append(X)
    PPVIdxL = ExtractVbleIndexList(PreVL + PostVL)
    for X in PPVIdxL:
        for u in X[1]:
            if Bmch.CanRepresentInt(u) == True:
                continue
            if not(u in UnivSet):
                UnivSet.append(u)

    CM = []
    CM.append("MACHINE CoverageModel")
    if UnivSet != []:
        CM.append("SETS")
        US = "UnivSet = {"
        for X in UnivSet:
            US = US + X + ","
        US = US[0:len(US)-1] + "}"
        CM.append(US)

    CM.append("VARIABLES")
    VD = "cfg_status"
    for X in PPVIdxL:
        VD = VD + "," + X[0]
    CM.append(VD)

    VIdxL = ExtractVbleIndexList(VL)
    
    CM.append("INVARIANT")
    CM.append("cfg_status : INTEGER")
    PreVD = []
    PostVD = []
    VDone = []
    for i in range(len(VT)):
        VN = VL[i].split("(")[0]
        if VN in VDone:
           continue
        VDone.append(VN)
        VIL = None
        for j in range(len(VIdxL)):
            if VIdxL[j][0] == VN:
                VIL = VIdxL[j][1]
                break
        if VIL == None:
            mp = ""
        elif len(VIL) > 0:
            mp = ""
            for u in VIL:
                mp = mp + u + ","
            mp = "{" + mp[0:len(mp)-1] + "} --> "
        else:
            mp = ""
        
        PreVN = PreVL[i].split("(")[0]
        PostVN = PostVL[i].split("(")[0]
        if VT[i][0] == "Int":
            PreS = "& %s : %sINTEGER"%(PreVN,mp)
            PostS = "& %s : %sINTEGER"%(PostVN,mp)
        elif VT[i][0] == "Bool":
            PreS = "& %s : %sBOOL"%(PreVN,mp)
            PostS = "& %s : %sBOOL"%(PostVN,mp)
        elif VT[i][0] == "Dist":
            PreS = "& %s : %sUnivSet"%(PreVN,mp)
            PostS = "& %s : %sUnivSet"%(PostVN,mp)
        elif VT[i][0] == "Set":
            if len(VT[i]) == 1:
                # it should be an empty set.
                PreS = "& %s : %sPOW(UnivSet)"%(PreVN,mp)
                PostS = "& %s : %sPOW(UnivSet)"%(PostVN,mp)
            elif Bmch.CanRepresentInt(VT[i][1]) == True:
                PreS = "& %s : %sPOW(INTEGER)"%(PreVN,mp)
                PostS = "& %s : %sPOW(INTEGER)"%(PostVN,mp)
            else:
                PreS = "& %s : %sPOW(UnivSet)"%(PreVN,mp)
                PostS = "& %s : %sPOW(UnivSet)"%(PostVN,mp)
        else:
            ppp

        PreVD.append(PreS)
        PostVD.append(PostS)
        
        """
        if VT[i][0] == "Int":
            PreVD.append("& %s : INT"%PreVL[i])
            PostVD.append("& %s : INT"%PostVL[i])
        elif VT[i][0] == "Bool":
            PreVD.append("& %s : BOOL"%PreVL[i])
            PostVD.append("& %s : BOOL"%PostVL[i])
        elif VT[i][0] == "Dist":
            PreVD.append("& %s : UnivSet"%PreVL[i])
            PostVD.append("& %s : UnivSet"%PostVL[i])
        elif VT[i][0] == "Set":
            PreVD.append("& %s : POW(UnivSet)"%PreVL[i])
            PostVD.append("& %s : POW(UnivSet)"%PostVL[i])
        else:
            ppp
        """
    CM = CM + PreVD + PostVD

    CM.append("INITIALISATION")
    CM.append("cfg_status := 0")
    VDone = []
    for i in range(len(VT)):
        VN = VL[i].split("(")[0]
        if VN in VDone:
           continue
        VDone.append(VN)
        VIL = None
        for j in range(len(VIdxL)):
            if VIdxL[j][0] == VN:
                VIL = VIdxL[j][1]
                break

        if not(VIL == None) and not(VIL == []):
            PreVN = PreVL[i].split("(")[0]
            PostVN = PostVL[i].split("(")[0]
            CM.append("; %s := {}"%(PreVN))
            CM.append("; %s := {}"%(PostVN))
        
        elif VT[i][0] == "Int":
            CM.append("; %s := 0"%(PreVL[i]))
            CM.append("; %s := 0"%(PostVL[i]))
        elif VT[i][0] == "Bool":
            CM.append("; %s := FALSE"%(PreVL[i]))
            CM.append("; %s := FALSE"%(PostVL[i]))
        elif VT[i][0] == "Dist":
            CM.append("; %s := %s"%(PreVL[i],UnivSet[0]))
            CM.append("; %s := %s"%(PostVL[i],UnivSet[0]))
        elif VT[i][0] == "Set":
            CM.append("; %s := {}"%(PreVL[i]))
            CM.append("; %s := {}"%(PostVL[i]))
        else:
            ppp

    CM.append("OPERATIONS")
    CM = CM + PPTL
    for X in CFGL:
        CM.append(X[0])
    CM.append("OPE_ZERO = PRE cfg_status = 100 THEN skip END")

    CM.append("END")

    return CM



# VT --- Types of variables
def ComputeVariableConnectionMatrix(VT):
    M = []
    for P in VT:
        X = []
        PT = P[1:len(P)]
        for Q in VT:
            QT = Q[1:len(Q)]
            flag = False
            for U in PT:
                if U in QT:
                    flag = True
                    break
            if flag == True:
                X.append(True)
            else:
                X.append(False)
        M.append(X)
    return M



# VT --- Types of variables
# VL --- Names of variables
# conffile --- configuration file
# wdir --- working directory
def GenerateCFGOperations(VT,VL,conffile,wdir):

    MaxCard = Bmch.read_config(conffile,"max_CFG_set_cardinality","int")

    PPVL = Generate_Pre_And_Post_Variables(VL)
    PreVL = PPVL[0]
    PostVL = PPVL[1]
    #print PreVL
    #print PostVL
    #print VT
    NUM_DS = 0
    ST = [] # ST --- Types of substitutions
    CM = ComputeVariableConnectionMatrix(VT) # CM --- Connection Matrix
    vble_types = ""
    const_types = ""
    INTZ = []
    NAT1Z = []
    for i in range(len(VT)):
        T = VT[i]
        if T[0] == "Int":
            S = "S -> INT | INTC\n"
            ST.append(S)
            for X in T[1:len(T)]:
                if not(X in INTZ):
                    INTZ.append(X)
                if X > 0 and not(X in NAT1Z):
                    NAT1Z.append(X)
        elif T[0] == "Bool":
            S = "S -> BOOL | 'TRUE' | 'FALSE' | 'bool(' PRED ')'\n"
            ST.append(S)
            S = "BOOL -> \'%s\'\n"%(PreVL[i])
            vble_types = vble_types + S
        elif T[0] == "Dist":
            NUM_DS = NUM_DS + 1
            DN = "DIST" + str(NUM_DS)
            SN = "SET" + str(NUM_DS)
            S = "S -> %s | %sC\n"%(DN,DN)
            ST.append(S)
            for j in range(len(VT)):
                if CM[i][j] == True and VT[i][0] == VT[j][0]:
                    S = "%s -> \'%s\'\n"%(DN,PreVL[j])
                    vble_types = vble_types + S
            Z = ConvertSetToCFG(T[1:len(T)])
            S = "%sC -> %s\n"%(DN,Z)
            const_types = const_types + S
            Z = EnumerateSubsetCFG(T[1:len(T)],MaxCard)
            S = "%sC -> %s\n"%(SN,Z)
            const_types = const_types + S
        elif T[0] == "Set":
            NUM_DS = NUM_DS + 1
            DN = "DIST" + str(NUM_DS)
            SN = "SET" + str(NUM_DS)
            S = "S -> %s | %sC\n"%(SN,SN)
            ST.append(S)
            for j in range(len(VT)):
                if CM[i][j] == True and VT[i][0] == VT[j][0]:
                    S = "%s -> \'%s\'\n"%(SN,PreVL[j])
                    vble_types = vble_types + S
            Z = EnumerateSubsetCFG(T[1:len(T)],MaxCard)
            S = "%sC -> %s\n"%(SN,Z)
            const_types = const_types + S
        else:
            ppp
    INTZ.sort()
    NAT1Z.sort()
    if len(INTZ) > 0:
        Z = ConvertSetToCFG(INTZ)
        S = "INTC -> %s\n"%(Z)
        const_types = const_types + S
    if len(NAT1Z) > 0:
        Z = ConvertSetToCFG(NAT1Z)
        S = "NAT1C -> %s\n"%(Z)
        const_types = const_types + S

    DS_grammar = ""
    for i in range(1,NUM_DS+1):
        DN = "DIST" + str(i)
        SN = "SET" + str(i)
        S = ProduceDistAndSetCFGRules(DN,SN)
        DS_grammar = DS_grammar + S
    #print vble_types
    #print DS_grammar
    #print ST
    common_grammar = Common_CFG_Grammar()
    #print common_grammar


    MaxL = Bmch.read_config(conffile,"max_CFG_length","int")

    XS = []
    SFlag = True
    for dep in range(1,MaxL+1):
        if SFlag == False:
            break
        X = []
        for i in range(len(ST)):
            subs_type = ST[i]
            vble = PostVL[i]
            b_subs_grammar = subs_type + vble_types + const_types + common_grammar + DS_grammar
            grammar = CFG.fromstring(b_subs_grammar)
            for sentence in generate(grammar, depth=dep, n=1001):
                S = vble + " = " + ' '.join(sentence)
                if S in X:
                    continue
                X.append(S)

        if len(X) > 1000:
            print("as the number of CFGs at depth %d is greater than 1000, we stop search now."%(dep))
            SFlag = False

        random.shuffle(X)

        NX = 0
        for Z in X:
            if not(Z in XS):
                XS.append(Z)
                NX = NX + 1
                if NX >= 1000 and dep >= 4:
                    print("Note: as the number of candidate substitutions at depth %d is greater than 1000, we reduce it to 1000."%(dep))
                    break

    X = XS
    X.sort()

    RedS = Redundant_CFG_Strings(VT)

    res = []
    OPE_ID = -1
    for i in range(len(X)):
        cond = X[i]
        # Removing redundant CFGs.
        flag = True
        for rs in RedS:
            if rs in cond:
                flag = False
                break
        if flag == False:
            continue
        OPE_ID = OPE_ID + 1
        S = "SUBS_%d = PRE cfg_status = 1 & %s THEN cfg_status := 2 END ;"%(OPE_ID,cond)

        # remove preCFGx_ and postCFGx_ prefix and make a substitution
        subs = cond + ""
        j = 0
        while subs[j:j+1] != "=":
            j = j + 1
        subs = subs[0:j] + ":=" + subs[j+1:len(subs)]       
        subs = subs.replace("preCFGx_","")
        subs = subs.replace("postCFGx_","")
        
        res.append([S,subs])

    return res

""" 
# Some CFG are redundant and can be removed.
# X --- CFG Expression.
# VT --- Types of Variables.
def Redundant_CFG(X,VT):
    if "} <: {" in X:
        return True
    if "} = {" in X:
        return True

    return False
"""

# Some CFGs contain redundant strings. These CFGs are redundant and can be removed.
# VT --- Types of Variables.
def Redundant_CFG_Strings(VT):
    res = []

    #res.append("} <: {")
    #res.append("} = {")
    res.append(" : {  }")
    
    return res

def Common_CFG_Grammar():
    common_grammar = """
      PRED -> '(' BOOL '= TRUE )'
      PRED -> '(' BOOL '= FALSE )'
      PRED -> '(' PRED '&' PRED ')'
      PRED -> '(' PRED 'or' PRED ')'
      PRED -> 'not(' PRED ')'
      PRED -> '(' INT '=' INT ')'
      PRED -> '(' INT '=' INTC ')'
      PRED -> '(' INT '>=' INT ')'
      PRED -> '(' INT '>=' INTC ')'
      PRED -> '(' INT '<=' INTC ')'

      INT -> '(' INT '+' INT ')'
      INT -> '(' INT '+' INTC ')'
      INT -> '(' INT '-' INT ')'
      INT -> '(' INT '-' INTC ')'
      INT -> '(' INTC '-' INT ')'
      INT -> '(' INT '*' INT ')'
      INT -> '(' INT '*' INTC ')'
      INT -> '(' INT '/' NAT1C ')'
      INT -> '(' INT 'mod' NAT1C ')'

    """
    return common_grammar


def Generate_Pre_And_Post_Variables(VL):
    P = []
    Q = []
    for x in VL:
        U = "preCFGx_" + x
        V = "postCFGx_" + x
        P.append(U)
        Q.append(V)
    return [P,Q]

# VL --- Variable List
# XL --- Value List
def Assign_Values_To_Variables(VL,XL):
    res = ""
    for i in range(len(VL)):
        V = VL[i]
        X = XL[i]
        if type(X) == type([]):
            X = Bmch.convert_python_set_to_b_string(X)
        VeX = V + " := " + X
        if i > 0:
            res = res + " ; "
        res = res + VeX
    return res

def Convert_Transitions_To_Pre_Post_Operations(TL,VL):
    OpeID = -1
    PPVL = Generate_Pre_And_Post_Variables(VL)
    PreVL = PPVL[0]
    PostVL = PPVL[1]
    res = []
    for X in TL:
        OpeID = OpeID + 1
        OpeName = "TRANS_%d"%(OpeID)
        P = X[0]
        Q = X[2]
        
        PreSubs = Assign_Values_To_Variables(PreVL,P)
        PostSubs = Assign_Values_To_Variables(PostVL,Q)
        W = "%s = PRE cfg_status = 0 THEN cfg_status := 1 ; %s ; %s END ;"%(OpeName,PreSubs,PostSubs)
        res.append(W)
    return res
   

# D --- Name of DIST
# S --- Name of SET
def ProduceDistAndSetCFGRules(D,S):
    X = """
      PRED -> '(' DISTNAME '=' DISTNAME ')'
      PRED -> '(' DISTNAME '=' DISTNAMEC ')'
      PRED -> '(' DISTNAME ':' SETNAME ')'
      PRED -> '(' DISTNAME ':' SETNAMEC ')'
      PRED -> '(' SETNAME '=' SETNAME ')'
      PRED -> '(' SETNAME '=' SETNAMEC ')'
      PRED -> '(' SETNAME '<:' SETNAME ')'
      PRED -> '(' SETNAME '<:' SETNAMEC ')'
      PRED -> '(' SETNAMEC '<:' SETNAME ')'
      SETNAME -> '(' SETNAME '\/' SETNAME ')'
      SETNAME -> '(' SETNAME '\/' SETNAMEC ')'
      SETNAME -> '(' SETNAME '/\\' SETNAME ')'
      SETNAME -> '(' SETNAME '/\\' SETNAMEC ')'
      SETNAME -> '(' SETNAME '-' SETNAME ')'
      SETNAME -> '(' SETNAMEC '-' SETNAME ')'
      SETNAME -> '(' SETNAME '-' SETNAMEC ')'
    """
    X = X.replace("DISTNAME",D)
    X = X.replace("SETNAME",S)
    return X

# S --- A set
# Output is of the form "X0 | X1 | ... | XN", where each Xi is an element in S.
def ConvertSetToCFG(S):
    res = ""
    for i in range(len(S)):
        X = S[i]
        if i > 0:
            res = res + " | "
        res = res + "\'" + str(X) + "\'"
    return res 

# S --- A set
# N --- Maximum number of elements in each subset
# Output is of the form "S0 | S1 | ... | SN", where each Si is a subset of S.
def EnumerateSubsetCFG(S,N):
    SS = []
    for NX in range(N + 1):
        W = list(itertools.combinations(S, NX))
        for X in W:
            Y = list(X)
            Y = Bmch.convert_python_set_to_b_string(Y)
            SS.append(Y)
    res = ""
    for i in range(len(SS)):
        X = SS[i]
        if i > 0:
            res = res + " | "
        res = res + "\'" + str(X) + "\'"
    return res

# Convert a list of cond-subs expressions to b.
def convert_cond_subs_list_to_b(SS):
    res = []
    n = 0
    for s in SS:
        n = n + 1
        cond = s[0]
        subs = s[1]
        res.append("IF " + cond)
        res.append("THEN " + subs)
        res.append("ELSE")
    res = res[0:len(res)-1]
    for i in range(n):
        res.append("END")
    return res

# Convert a list of substitutions to a string.
def convert_subs_to_str(subs):
    if subs == []:
        return " skip "
    res = subs[0]
    for x in subs[1:len(subs)]:
        res = res + " ; " + x
    return res

"""
def convert_CFG_subs_to_str(subs):
    return convert_subs_to_str(subs)
"""

# Convert a list of CFG substitutions to a string.
def convert_CFG_subs_to_str_v2(subs):
    if subs == []:
        return " skip "
    N = len(subs)
    # TVL --- temporary variable list
    TVL = []
    for i in range(N):
        V = "TmpVal" + str(i+1)
        TVL.append(V)

    # SL --- temporary substitution list
    SL = []
    for i in range(N):
        V = subs[i].split(" := ")[0]
        VeX = V + " := " + TVL[i]
        SL.append(VeX)

    TVD = "/* ppp */ ANY "
    for V in TVL:
        TVD = TVD + V + ", "
    TVD = TVD[0:len(TVD)-2]
    TVD = TVD + " WHERE "
    for i in range(N):
        X = subs[i].split(" := ")[1]
        VeX = TVL[i] + " = " + X
        TVD = TVD + VeX + " & "
    #TVD = TVD + " ( "
    TVD = TVD + " THEN "
    for i in range(N):
        TVD = TVD + SL[i] + " ; "
    TVD = TVD[0:len(TVD)-2]
    #TVD = TVD + " ) "
    TVD = TVD + " END"

    return TVD


# Convert a list of CFG substitutions to a string.
def convert_CFG_subs_to_str(subs):
    if subs == []:
        return " skip "
    N = len(subs)
    # TVL --- temporary variable list
    TVL = []
    for i in range(N):
        V = "TmpVal" + str(i+1)
        TVL.append(V)

    # SL --- temporary substitution list
    SL = []
    for i in range(N):
        V = subs[i].split(" := ")[0]
        VeX = V + " := " + TVL[i]
        SL.append(VeX)

    TVD = "/* CFG substitution */ VAR "
    for V in TVL:
        TVD = TVD + V + ", "
    TVD = TVD[0:len(TVD)-2]
    TVD = TVD + " IN "
    for i in range(N):
        X = subs[i].split(" := ")[1]
        VeX = TVL[i] + " := " + X
        TVD = TVD + VeX + " ; "
    #TVD = TVD + " ( "
    for i in range(N):
        TVD = TVD + SL[i] + " ; "
    TVD = TVD[0:len(TVD)-2]
    #TVD = TVD + " ) "
    TVD = TVD + " END"

    return TVD




# Merge conditions (PRE conditions or IF conditions) by positive examples and negative examples.
def merge_conditions(pexp,nexp,vble_list,resdir):

    cmd = "mkdir " + resdir
    os.system(cmd)

    """
    print "SSSSS"
    for x in pexp: print x
    print "TTTTT"
    for x in nexp: print x
    """

    SType = get_types_for_progol(pexp + nexp)

    #for x in pexp: print x
    #ppp

    for i in range(len(pexp)):
        pexp[i] = rewrite_state_from_python_to_prolog(pexp[i])
    for i in range(len(nexp)):
        nexp[i] = rewrite_state_from_python_to_prolog(nexp[i])
 
    prog = ["% Condition simplification using Aleph.\n"]
    prog_d = ["% Directives.\n"]
    prog_b = ["% Background Knowledge Section.\n"]
    prog_f = ["% Positive Examples Section.\n"]
    prog_n = ["% Negative Examples Section.\n"]
    prog_e = ["% End Section.\n"]

    prog_b.append(":-begin_bg.\n")
    prog_f.append(":-begin_in_pos.\n")
    prog_n.append(":-begin_in_neg.\n")

    prog.append("% Module loading.\n")
    prog.append(":- use_module(library(aleph)).\n\n")
    prog.append("% Aleph initialization.\n")
    prog.append(":- aleph.\n\n")


    S = [
      # i --- layers of new variables.
      ":- set(i,5).\n",
      # clauselength --- the maximum length of clause. Default is 4.
      ":- set(clauselength,10).\n",
      # minpos --- the minimum number of positive examples to be covered by a learnt clause
      # ":- set(minpos,2).\n",
      # splitvars --- variables are independent of each other
      ":- set(splitvars,true).\n",
      #":- set(explore,true).\n :- set(depth,100).\n :- set(splitvars,true).\n",

      #":- sphyp."

      #":- set(evalfn,coverage).",
      #":- set(clauselength,4).",
      #":- set(gsamplesize,20).",
    ]
    prog_d = prog_d + S

    S = make_iso_example_decl(pexp[0])


    prog_d = prog_d + S

    #S = RepSimpLib.make_type_defs()
    #prog_b = prog_b + S + [""]
    S = make_general_rules()
    prog_b = prog_b + S + [""]
    #S = RepSimpLib.make_is_bset_rule(SType,5)
    #prog_b = prog_b + S + [""]


    S = make_iso_examples(pexp,"pos")
    prog_f = prog_f + S + [""]

    S = make_iso_examples(nexp,"neg")
    prog_n = prog_n + S + [""]



    prog_d.append("\n")
    prog_b.append(":-end_bg.\n\n")
    prog_f.append(":-end_in_pos.\n\n")
    prog_n.append(":-end_in_neg.\n\n")
    prog_e.append(":-aleph_read_all.\n")
    prog_e.append(":-induce.\n")
    #prog_e.append(":- aleph:sphyp.\n")
    #prog_e.append(":- rdhyp.\n:- iso_cond(A,B,C,D,E,F,G,H).\n:- sphyp.\n:- show(gcws).\n:- addgcws.\n")

    #prog_e.append(":- aleph:rdhyp.\n:- iso_cond(A,B,C,D,E,F,G,H).\n:- aleph:sphyp.\n:- aleph:show(gcws).\n:- aleph:addgcws.\n")
    rfn = resdir + "/result.rule"
    prog_e.append(":-aleph:write_rules(\"%s\").\n"%rfn)

    prog = prog + prog_d + prog_b + prog_f + prog_n + prog_e


    plfn = resdir + "/simp.pl"
    f = open(plfn,"w")
    for x in prog:
        f.write(x)
        f.write("\n")
    f.close()


    #cmd = "swipl -g \"[tttr], nl, halt\""
    cmd = "swipl -g \"consult(\'%s\'), nl, halt\""%plfn
    os.system(cmd)

    rl = read_aleph_rules(rfn)


    cond = ""
    #vble_list.append("havefun")
    for x in rl:
        y = rule_to_cond(x,vble_list,resdir)
        y = "( " + y + " )"
        cond = cond + y + " or "

    cond = cond[0:len(cond)-4]

    print("Done!")
    print("The merged condition is \"" + cond + "\".")

    return cond












# Find simple substitutions for a variable, such as x = FALSE, x = y, etc.
# vble --- the LHS variable (in a post state).
# val --- the value of the LHS variable (in a post state).
# vble_list --- a list of RHS variables (in a pre state).
# value_list --- the values of the RHS variables (in a pre state).

def find_simple_subs_for_a_vble(vble,val,vble_list,val_list):
    res = []
   
    if type(val) == type([]):
        s = vble + " := " + Bmch.convert_python_set_to_b_string(val)
    else:
        s = vble + " := " + val
    res.append(s)
    for i in range(len(vble_list)):

        if val_list[i] == val:
            s = vble + " := " + vble_list[i]
            #s = s.replace("u'","")
            """
            if type(val_list[i]) == type([]):
                s = vble + " := " + Bmch.convert_python_set_to_b_string(val_list[i])
            else:
                s = vble + " := " + val_list[i]
            """
            res.append(s)
    #res = list(set(res))
    resT = []
    for x in res:
        if not(x in resT):
            resT.append(x)
    res = resT

    return res
    
# Find substitutions for a set of transitions
def find_subs_for_transitions(trans_list,vble_list):
    res = []
    vble_list_pre = vble_list

    for trans in trans_list:
    #for i in range(len(vble_list)):
        slist = []
        #vble_post = vble_list[i]
        #for trans in trans_list:
        for i in range(len(vble_list)):
            vble_post = vble_list[i]
            val_post = trans[2][i]
            val_list_pre = trans[0]
            #print val_list_pre
            subs = find_simple_subs_for_a_vble(vble_post,val_post,vble_list_pre,val_list_pre)
            #print trans
            #for x in subs: print subs
            #slist.append([vble_post,subs,trans])
            slist = slist + subs
            
        res.append([slist,trans])

    return res

def best_substitution_partition(WS,free_vbles):

    """
    WS = []
    for x in WST:
        tr = x[1]
        #tr = tr.encode('ascii','ignore')
        SL = []
        for y in x[0]:
            SL.append(y.encode('ascii','ignore'))
        WS.append([SL,tr])
    free_vbles = []
    for x in free_vblesT:
        y = x.encode('ascii','ignore')
        free_vbles.append(y)
    """

    #WS = WST
    #free_vbles = free_vblesT

    subs_list = []
    for x in WS:
        for y in x[0]:
            p = y.split(":=")[0]
            p = p.replace(" ","")
            if p in free_vbles and not(y in subs_list):
                subs_list.append(y) 
    #subs_list = list(set(subs_list))
    subs_list = sorted(subs_list)

    best_idx = -1
    best_coverage = -1
    for i in range(len(subs_list)):
        x = subs_list[i]
        cov = 0
        for p in WS:
            if x in p[0]:
                cov = cov + 1
        if cov > best_coverage:
            best_coverage = cov
            best_idx = i
        elif cov == best_coverage:
            y = x.replace(" ","")
            y = y.split(":=")
            if y[0] == y[1]:
                best_coverage = cov
                best_idx = i

    best_subs = subs_list[best_idx]
    covered_trans = []
    uncovered_trans = []
    best_vble = best_subs.split(" ")[0]
    for p in WS:
        if best_subs in p[0]:
            covered_trans.append(p)
        else:
            uncovered_trans.append(p)

    return [best_vble,best_subs,covered_trans,uncovered_trans]

def transition_partition(ST,vble_list,cand_list = None):
     
    if cand_list == None:
        all_trans_with_subs = find_subs_for_transitions(ST,vble_list)
    else:
        all_trans_with_subs = cand_list
        SSL = find_subs_for_transitions(ST,vble_list)
        for i in range(len(all_trans_with_subs)):
            tr = all_trans_with_subs[i][1]
            for x in SSL:
                if x[1][0] == tr[0] and x[1][2] == tr[2] and (x[1][1] == tr[1] or tr[1] == "CurrentOperation"):
                    all_trans_with_subs[i][0] = all_trans_with_subs[i][0] + x[0]

 
    # U <-- {ST}
    free_vbles = vble_list + []
    U = [[[],free_vbles,all_trans_with_subs]]

    # SR <-- {}
    SR = []

    # while U != {} do
    while U != []:
        
       # SP <-- First_Item(U)
       # U <-- U - {SP}
       SP = U.pop(0)

       # WS <-- SubstitutionCandidates(SP)
       current_subs = SP[0]
       free_vbles = SP[1]
       WS = SP[2]
       
       # PB <-- BestPartition(SP,WS)
       PB = best_substitution_partition(WS,free_vbles)
       generalised_vble = PB[0]
       new_subs = current_subs + [PB[1]]
       new_free_vbles = free_vbles + []
       new_free_vbles.remove(generalised_vble)
       
       # if PB is not null then 
       # U <-- U + PB - {{}}
       # else
       # SR <-- SR + {SP}
       if new_free_vbles == []:
           final_subs = []
           for x in new_subs:
               y = x.replace(" ","")
               y = y.split(":=")
               if y[0] != y[1]:
                   final_subs.append(x)
           X = [final_subs,PB[2]]
           SR.append(X)
       else:
           X = [new_subs,new_free_vbles,PB[2]]
           U.append(X)
       if PB[3] != []:
           X = [current_subs,free_vbles,PB[3]]
           U.append(X)
       
    #for x in SR: print "PPPPPPP",x

    res = []
    for x in SR:
        tl = []
        for y in x[1]:
            tl.append(y[1])
        res.append([x[0],tl])

    return res

"""
def split_trans_by_subs(pexp,vble_list):

    s = [[[]] + pexp]
    n = 0
    vble_record = []
    for i in range(len(vble_list)):
        vble_record.append(False)
    while n < len(vble_list):
        n = n + 1
        st = []
        for r in s:
            current_subs = r[0]
            subs_list = find_subs_for_transitions(r[1:len(r)],vble_list)


            min_num_sets = len(r) + 1000000
            best_subs = "Nothing"
            best_vble = "Nothing"

            print "UUUUUUUUUU"
            print subs_list
            print "UUUUUUUUUUEND"


            for vsubs in subs_list:

                print vsubs

                vble = vsubs[0]

                idx = vble_list.index(vble)
                if vble_record[idx] == True: continue

                # SU --- the set of uncovered transitions.
                # SSC --- the set of sets of covered transitions.
                SU = vsubs[1] + []
                SSC = []

                print "QQQQQQQQQQQQ"
                print SU

                while SU != []:

                    ss = []
                    nn = []
                    for vs in SU:

                        print "HHHHHHHHHHH"
                        print vs
                       

                        print "\n\n"
                        for xdd in vs: print xdd
                        print "\n\n"

                        for u in vs[1:len(vs)]:
                            if not(u in ss): 
                                ss.append(u)
                                nn.append(1)
                            else:
                                i = ss.index(u)
                                nn[i] = nn[i] + 1

                    cvn = max(nn)
                    cvi = nn.index(cvn)
                    cvx = ss[cvi]
                    #print cvx, cvn
                    SC = []
                    SUC = []
                    for vs in SU:
                        if cvx in vs[1:len(vs)]:
                            SC.append(vs)
                        else:
                            SUC.append(vs)
                    SU = SUC
                    SSC.append([cvx] + SC)
                   
                num_sets = len(SSC)

                print "\n\nPPPPPPPPPPPP"
                #for xdd in SSC: print xdd
                print num_sets
                print "PPPPPPPPPPPP\n\n"

                if num_sets < min_num_sets:
                    #print "GOOD!"
                    #ppppppp
                    min_num_sets = num_sets
                    best_subs = SSC
                    best_vble = vble

            if best_subs == "Nothing": continue
                 
            print min_num_sets
            print "\n\nBest Coverage:"
            for x in best_subs: 
                print "\n"
                for y in x: print y

            print "\n\nENDDDDDDDDDDD\n\n"

            # for each best_subs[i] (i.e. vs)
            # best_subs[i][0] is the best subsitution
            # best_subs[i][1:len(best_subs[i])] is the set of covered transitions.
            for vs in best_subs:
                new_subs = current_subs + [vs[0]]
                new_cv = [p[0] for p in vs[1:len(vs)]]
                st.append([new_subs] + new_cv)

            #print subs_list
            

            idx = vble_list.index(best_vble)
            vble_record[idx] = True
            
            
        # Update s
        s = st + []
        for x in s:
          for y in x:
            print "\n\n",y
    for x in s: print x[0]
    
    return s

"""

# Generate random negative examples.
# pexp --- a set of positive examples.
# rds --- seed.
def gen_rand_neg_exps(pexp,rds):
    print("This function is NOT finished.")
    PType = get_types_for_progol(pexp)
    u = []
    for i in range(len(PType)):
        nv = "bNoValue" + str(i)
        u.append(PType[i][1:len(PType[i])] + [nv])
    for x in u: 
        print(x)
    u = str(u)
    u = u[1:len(u)-1]
    #print u
    s = "itertools.product(%s)"%u
    s = eval(s)
    res = []
    for x in s:
        y = list(x)
        if y in pexp: continue
        res.append(y)

    return res

# Extract all pre-states of a state graph
# g --- a state graph
def extract_all_pre_states(g):
    res = []
    for x in g:
        if not(x[0] in res):
            res.append(x[0])
    res = sorted(res)
    return res

# Extract all states of a state graph
# g --- a state graph
def extract_all_states(g):
    res = []
    for x in g:
        if not(x[0] in res):
            res.append(x[0])
        if not(x[2] in res):
            res.append(x[2])
    res = sorted(res)
    return res

# initialise variables of an abstract machine by examples.
# vl --- list of variables ; exs --- examples .
def initialise_vble_by_examples(vl,exs):

    v = vl[0]
    for x in vl[1:len(vl)]:
        v = v + " , " + x

    v_init = vl[0] + "_ivble"
    for x in vl[1:len(vl)]:
        v_init = v_init + " , " + x + "_ivble"

    cond = []

    for p in exs:
        y = p[0]

        # If y is a set.
        if type(y) == type([]):
            y = Bmch.convert_python_set_to_b_string(y)
      
        #print p
                 

        for x in p[1:len(p)]:
            if type(x) == type([]):
                xv = Bmch.convert_python_set_to_b_string(x)
            else:
                xv = x
            y = y + " , " + xv
        #pppp
        s = "( " + v_init + " ) = ( " + y + " )"
        cond.append(s)

    res = []
    res.append("ANY " + v_init + " WHERE")
    res.append(cond[0])
    for i in range(1,len(cond)):
        res.append("or " + cond[i])
    res.append("THEN " + v + " := " + v_init + " END")
    #for x in res: print x
    return res

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
    for i in range(n-1):
        arg = arg + ",+bobj"

    res = ["% Isolation Condition Components."]
    res = res + [":- modeh(*,%s(%s))."%(f,arg)]
    res = res + [":- modeb(*,is_bobj(+bobj,#bobj))."]
    res = res + [":- determination(%s/%d,is_bobj/2)."%(f,n)]
    res = res + [":- modeb(*,in_bset(+bobj,#bobj))."]
    res = res + [":- determination(%s/%d,in_bset/2)."%(f,n)]

    res = res + [":- modeb(*,has_bdist(+bobj,#bobj))."]
    res = res + [":- determination(%s/%d,has_bdist/2)."%(f,n)]

    res = res + ["% Note: is_bsubset function has not been tested!"]
    res = res + [":- modeb(*,is_bsubset(+bobj,#bobj))."]
    res = res + [":- determination(%s/%d,is_bsubset/2)."%(f,n)]


    res = res + ["\n% Rules."]
    res = res + [":- modeb(*,in_bset_comp(+bobj,-bobj))."]
    res = res + [":- modeb(*,is_bset(-bobj))."]

    res = res + [":- modeb(*,has_bdist_comp(+bobj,-bobj))."]

    res = res + [":- modeb(*,is_bsubset_comp(+bobj,-bobj))."]

    #res = res + [":- modeb(*,is_bdist(-bobj))."]


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
            ut = str(u).replace("\"","").replace("\'","")
            y = y + ut + ","
        y = y[0:len(y)-1]
        y = y + ")."
        if pn != "pos" and pn != "neg":
            y = pn + y
            print("Warning: pn should be pos or neg! However, it is %s."%pn)
        res.append(y)
    return res
        

# Output general rules.
def make_general_rules():
    res = [
        "% General Rules.",
        "is_bobj(bTRUE,bTRUE).",
        "is_bobj(bFALSE,bFALSE).",
        "in_bset(X,S) :- in_bset_comp(X,S).",
        "in_bset_comp(X,S) :- is_bset(S), member(X,S).",
        "has_bdist(S,X) :- has_bdist_comp(S,X).",
        "has_bdist_comp(S,X) :- member(X,S).",
        "is_bsubset(X,S) :- is_bsubset_comp(X,S).",
        "is_bsubset_comp(X,S) :- is_bset(S), subset(X,S).",
    ]
    return res

def convert_pn_examples_to_translist(pn_exp):
    y = []
    for x in pn_exp:
        y.append([x,"",[]])
    return y

def get_types_for_progol(pn_exp):
    
    sg = Bgenlib.BStateGraphForNN()
    pn_exp_t = convert_pn_examples_to_translist(pn_exp)
    #for x in pn_exp_t: print x
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
            p = t #set_to_string(t)
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
    for i in range(len(P)):
        x = P[i]
        xs = set(x)
        pname = "bsubst_of_%s"%Names[i]
        res.append("")
        res.append("% \"bsubst_of\" relations for " + Names[i] + ".\n")
        decl = ":- modeb(*,%s(+bobj))?"%pname
        res.append(decl)
        for j in range(len(P)):
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


def splist_to_list(y):
    yt = []
    i = 0
    while i < len(y):
        p = y[i]
        if p[0] == "[":
            u = ""
            while p[-1] != "]":
                u = u + p + ","
                i = i + 1
                p = y[i]
            u = u + p
            yt.append(u)
            i = i + 1
        else:
            yt.append(p)
            i = i + 1
    return yt

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
            y = splist_to_list(y)

            for i in range(len(y)):
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

                # "X=Y" case
                if flag == 0 and (p[j] == "," or p[j] == ".") and ("=" in p[i:j]):
                    u = "is_bobj(" + p[i:j].replace("=",",") + ")"
                    bd.append(u)
                    i = j + 1
                    j = i
                    flag = 0
                    continue
 

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
                    continue
                   
        res.append([hd] + bd)
    f.close()
    return res


# Convert bset string to a B set.
def convert_bset_to_set(x):

    y = x.replace(" ","")
    
    if y == "bsetEmpty":
        return "{}"
    
    y = y.split("_b")

    res = "{ " + y[1]
    for u in y[2:len(y)]:
        res = res + " , " + u
    res = res + " }"

    return res


# Remove the B-prefix from an expression.
# i.e. remove "b" and "bset" in the head of expressions.
# x --- expression
def remove_b_prefix(x):
    y = x + ""
    while True:
        if not("  " in y): break
        y = y.replace("  "," ")
    y = y.replace("\n","")
    y = y.split(" ")
    res = ""
    for p in y:
        if p == "": continue
        if p[0:4] == "bset":
            q = convert_bset_to_set(p)
        elif p[0] == "b":
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
        for i in range(len(ul)):
            p = " " + ul[i] + " "
            q = " b" + vl[i] + " "
       
            if p in u:
                u = u.replace(p,q)
        
        # convert rule to condition.

        u = u.replace(" ","")
        cond_rewriter = "src/python/conv_rule_to_cond.pl"
        cmd = "swipl -g \"consult(\'%s\'), nl, rule_to_cond(%s), nl, halt\""%(cond_rewriter,u)

        pl_res = subprocess.check_output(cmd, shell=True)
        pl_res = pl_res.split("\n")

        cond = pl_res[-2]

       
        bcond = remove_b_prefix(cond)
        y.append(bcond)

    res = "" 
    for x in y:
        res = res + x + " & "
    res = res[0:len(res)-3]

    return res
