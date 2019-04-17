
import random
import pydotplus
import pydot
import sys
import Bmch

def write_list_to_csv(S,fname):
    f = open(fname,"w")
    for x in S:
        f.write(x[0])
        for y in x[1:len(x)]:
            f.write("," + y)
        f.write("\n")
    f.close()
    return 0

class BProgram(object):

    def __init__(self, OPE_NUM, VBLE_NUM, EXINV_NUM, COND_LEN, EXP_LEN, SUBS_NUM, INT_SCOPE, DIST_NUM):
    
        # ============ Grand parameters ============
  
        # The number of operations.
        self.OPE_NUM = OPE_NUM

        # The number of variables of each type.
        self.VBLE_NUM = VBLE_NUM

        # The number of extra invariants
        self.EXINV_NUM = EXINV_NUM

        # The length of conditions (for pre-conditions and extra invariants).
        self.COND_LEN = COND_LEN

        # The length of expressions (for assignments).
        self.EXP_LEN = EXP_LEN

        # The number of substitutions in each operation.
        self.SUBS_NUM = SUBS_NUM


        # The maximum / minimum integer.
        self.MAX_INT = INT_SCOPE
        self.MIN_INT = -INT_SCOPE

        # The number of distinct elements.
        self.NUM_OF_DIST_ELEM = DIST_NUM

        
        # ============ Secondary parameters ============

        # The length of preconditions.
        self.PRECOND_LEN = self.COND_LEN

        # The length of extra invariants.
        self.EXINVCOND_LEN = self.COND_LEN

        # The length (the number of arithmetic operations) of arithmetic expressions.
        self.ARITH_LEN = self.EXP_LEN
        
        # The length (the number of logical operations) of Boolean expressions.
        self.BOOL_LEN = self.EXP_LEN
       
        # The length (the number of set operations) of set expressions.
        self.SETEXP_LEN = self.EXP_LEN

        
        # The number of integer variables.
        self.NUM_OF_INT_VBLE = self.VBLE_NUM
        
        # The number of boolean variables.
        self.NUM_OF_BOOL_VBLE = self.VBLE_NUM
 
        # The number of set variables.
        self.NUM_OF_SET_VBLE = self.VBLE_NUM

        # The number of elemental variables.
        self.NUM_OF_ELEM_VBLE = self.VBLE_NUM

        # The set of integers.
        self.INT_SET = list(xrange(self.MIN_INT,self.MAX_INT+1))

        # The set of boolean.
        self.BOOL_SET = ["TRUE","FALSE"]

        # The set of distinct elements.
        self.DIST_SET = self.GenDistElemSet(self.NUM_OF_DIST_ELEM)


        # The set of integer variables.
        self.INT_VBLE_SET = self.GenIntVbleList(self.NUM_OF_INT_VBLE)
        
        # The set of boolean variables.
        self.BOOL_VBLE_SET = self.GenBoolVbleList(self.NUM_OF_BOOL_VBLE)
        
        # The set of set variables.
        self.SET_VBLE_SET = self.GenSetVbleList(self.NUM_OF_SET_VBLE)
        
        # The set of elemental variables.
        self.ELEM_VBLE_SET = self.GenElemVbleList(self.NUM_OF_ELEM_VBLE)

 
    def RandNat(self, n):
        res = int(random.random() * n)
        return res

    # Generate a set of distinct elements.
    def GenDistElemSet(self, n):
        res = []
        for i in xrange(n):
            x = "D%d"%i
            res.append(x)
        return res

    # Generate a subset of the given set randomly.
    def GenRandSubSet(self, x):
        res = []
        for item in x:
            if random.random() > 0.5:
                res.append(item)
        return res

    # Convert a set to a string.
    def SET_TO_STR(self, x):
        res = ""
        for p in x:
            res = res + p + " , "
        
        if res != "":
            res = res[0:len(res)-3]

        res = "{ " + res + " }"
        return res
        
    # ================== Variable List ===================
        
    def GenIntVbleList(self, n):
        res = []
        for i in xrange(n):
            x = "IntV"+"%s"%i
            res.append(x)
        return res
        
    def GenBoolVbleList(self, n):
        res = []
        for i in xrange(n):
            x = "BoolV"+"%s"%i
            res.append(x)
        return res 
         
    def GenSetVbleList(self, n):
        res = []
        for i in xrange(n):
            x = "SetV"+"%s"%i
            res.append(x)
        return res

         
    def GenElemVbleList(self, n):
        res = []
        for i in xrange(n):
            x = "ElemV"+"%s"%i
            res.append(x)
        return res
 
        
    # ================== Atomic Expression ===================
        
    def AtomicInt(self):
        BigIntSet = self.INT_SET + self.INT_VBLE_SET
        l = len(BigIntSet)
        i = self.RandNat(l)
        res = str(BigIntSet[i])
        if res[0] == "-":
            res = "(%s)"%res
        return res
        
    def AtomicBool(self):
        """
        BigBoolSet = self.BOOL_SET + self.BOOL_VBLE_SET
        l = len(BigBoolSet)
        i = self.RandNat(l)
        res = BigBoolSet[i]
        return res
        """
        x = self.BOOL_VBLE_SET[self.RandNat(len(self.BOOL_VBLE_SET))]
        y = self.BOOL_SET[self.RandNat(len(self.BOOL_SET))]
        res = x + " = " + y
        return res
 
    def AtomicSet(self):
        if random.random() < 0.5:
            res = self.SET_VBLE_SET[self.RandNat(len(self.SET_VBLE_SET))]
        else:
            x = self.GenRandSubSet(self.DIST_SET)
            res = self.SET_TO_STR(x)

        return res

         
    def AtomicElem(self):
        BigElemSet = self.DIST_SET + self.ELEM_VBLE_SET
        l = len(BigElemSet)
        i = self.RandNat(l)
        res = BigElemSet[i]
        return res
        
 
        
    # ================== Complex Expression ===================    
     

    # Generate an arithmetic expression.    
    def GenArithExp(self, n):
        if n == 0:
            res = self.AtomicInt()
            return res

        # Binary arithmetic operations include: + - * / mod **
        # Note: "/", "mod" and "**" can create illegal computation. 
        OpeList = ["+","-","*"] #["+","-","*","/","mod","**"]
        Ope = OpeList[self.RandNat(len(OpeList))]
        
        nt = n - 1
        nl = self.RandNat(nt+1)
        nr = nt - nl
        
        x = self.GenArithExp(nl)
        y = self.GenArithExp(nr)
        
        res = "(" + x + " " + Ope + " " + y + ")"
    
        return res
        
        
    # Generate a boolean expression.    
    def GenBoolExp(self, n):
        if n == 0:
            res = self.AtomicBool()
            return res

        # Binary boolean operations include: & or
       
        OpeList = ["&","or"] #["+","-","*","/","mod","**"]
        Ope = OpeList[self.RandNat(len(OpeList))]
        
        nt = n - 1
        nl = self.RandNat(nt+1)
        nr = nt - nl
        
        x = self.GenBoolExp(nl)
        y = self.GenBoolExp(nr)
        
        if random.random() > 0.5:
            x = "not(%s)"%x
            
        if random.random() > 0.5:
            y = "not(%s)"%y
        
        res = "(" + x + " " + Ope + " " + y + ")"
    
        return res   
 
    # Generate a set expression.    
    def GenSetExp(self, n):
        if n == 0:
            res = self.AtomicSet()
            return res

        # First-order binary set operations include: \/ /\ -
        # Note: "", "mod" and "**" can create illegal computation. 
        OpeList = ["\/","/\\","-"] #["+","-","*","/","mod","**"]
        Ope = OpeList[self.RandNat(len(OpeList))]
        
        nt = n - 1
        nl = self.RandNat(nt+1)
        nr = nt - nl
        
        x = self.GenSetExp(nl)
        y = self.GenSetExp(nr)
        
        res = "(" + x + " " + Ope + " " + y + ")"
    
        return res
        
        
       
 
    # ================== Statement ===================    
    
    # Generate an arithmetic statement.    
    def GenArithStat(self):
    
        OpeList = ["=","/=",">",">=","<","<="]
        Ope = OpeList[self.RandNat(len(OpeList))]
        
        x = self.GenArithExp(self.ARITH_LEN)
        y = self.GenArithExp(self.ARITH_LEN)
        
        res = "(" + x + " " + Ope + " " + y + ")"
    
        return res
        
     
    # Generate a boolean statement.    
    def GenBoolStat(self):
        """
        OpeList = ["=>","<=>"]
        Ope = OpeList[self.RandNat(len(OpeList))]
        
        x = self.GenBoolExp(self.BOOL_LEN)
        y = self.GenBoolExp(self.BOOL_LEN)
        
        res = "(" + x + " " + Ope + " " + y + ")"
        """
        res = self.GenBoolExp(self.BOOL_LEN)
        return res
     
    # Generate a set statement.    
    def GenSetStat(self):
    
        OpeList = ["<:","/<:","<<:","/<<:","=","/="]
        Ope = OpeList[self.RandNat(len(OpeList))]
        
        x = self.GenSetExp(self.SETEXP_LEN)
        y = self.GenSetExp(self.SETEXP_LEN)
        
        res = "(" + x + " " + Ope + " " + y + ")"
    
        return res
      
    # Generate an elemental statement.    
    def GenElemStat(self):
    
        if random.random() > 0.5:
            OpeList = [":","/:"]
            Ope = OpeList[self.RandNat(len(OpeList))]
        
            x = self.AtomicElem()
            y = self.GenSetExp(self.SETEXP_LEN)
        else:
            OpeList = ["=","/="]
            Ope = OpeList[self.RandNat(len(OpeList))]

            x = self.AtomicElem()
            y = self.AtomicElem()

        res = "(" + x + " " + Ope + " " + y + ")"
    
        return res
           
      
    # Generate an arithmetic/set/boolean/other statement.    
    def GenStat(self):
        StatTypeList = ["Arith","Bool","Set","Elem"]#["Arith","Set","Bool","Elem"]
        StatType = StatTypeList[self.RandNat(len(StatTypeList))]
        if StatType == "Arith":
            res = self.GenArithStat()
        elif StatType == "Bool":
            res = self.GenBoolStat()
        elif StatType == "Set":
            res = self.GenSetStat() 
        elif StatType == "Elem":
            res = self.GenElemStat()
  
        if random.random() > 0.5:
            res = "not" + res
            
        return res
        
    # Generate a condition.    
    def GenCond(self,n):
    
        if n == 0:
            res = self.GenStat()
            return res
    
        OpeList = ["&","or"]
        Ope = OpeList[self.RandNat(len(OpeList))]
        
        nt = n - 1
        nl = self.RandNat(nt+1)
        nr = nt - nl
        
        x = self.GenCond(nl)
        y = self.GenCond(nr)
        
        res = "(" + x + " " + Ope + " " + y + ")"
        
        return res
       

    # ================== Assignment =================== 
        
    # Generate an arithmetic assignment.    
    def GenArithAssg(self):
    
        v = self.INT_VBLE_SET[self.RandNat(len(self.INT_VBLE_SET))]
        x = self.GenArithExp(self.ARITH_LEN)
        res = v + " := " + x
        return res
         
    # Generate a Boolean assignment.    
    def GenBoolAssg(self):
    
        v = self.BOOL_VBLE_SET[self.RandNat(len(self.BOOL_VBLE_SET))]
        x = "bool(%s)"%self.GenStat()
        res = v + " := " + x
        return res
         
    # Generate a set assignment.    
    def GenSetAssg(self):
    
        v = self.SET_VBLE_SET[self.RandNat(len(self.SET_VBLE_SET))]
        x = self.GenSetExp(self.SETEXP_LEN)
        res = v + " := " + x
        return res
         
    # Generate an elemental assignment.    
    def GenElemAssg(self):
    
        v = self.ELEM_VBLE_SET[self.RandNat(len(self.ELEM_VBLE_SET))]
        x = self.AtomicElem()
        res = v + " := " + x
        return res
         
        
    # Generate a substitution.
    def GenSubs(self,n):
        res = []
        SubsTypeList = ["Arith","Bool","Set","Elem"]#["Arith","Set","Bool","Elem"]
        for i in xrange(n):
            SubsType = SubsTypeList[self.RandNat(len(SubsTypeList))]
            if SubsType == "Arith":
                x = self.GenArithAssg()
            elif SubsType == "Bool":
                x = self.GenBoolAssg()
            elif SubsType == "Set":
                x = self.GenSetAssg()
            elif SubsType == "Elem":
                x = self.GenElemAssg()
 
            res.append(x)

        return res

    # Generate an operation.
    def GenOpe(self):
        PreCond = self.GenCond(self.PRECOND_LEN)
        Subs = self.GenSubs(self.SUBS_NUM)
        res = ["NoName",PreCond,Subs]
        return res
        
    # Generate all operations.
    def GenAllOpes(self):
        res = []
        for i in xrange(self.OPE_NUM):
            OpeName = "Ope%d"%i
            x = self.GenOpe()
            Ope = [OpeName,x[1],x[2]]
            res.append(Ope)
        return res
            
        
        
    # Generate an initialisation.
    def GenInit(self):
        res = []
        for v in self.INT_VBLE_SET:
            x = self.INT_SET[self.RandNat(len(self.INT_SET))]
            s = v + " := %d"%x
            res.append(s)
        for v in self.BOOL_VBLE_SET:
            bst = ["TRUE","FALSE"]
            x = bst[self.RandNat(len(bst))]
            s = v + " := %s"%x
            res.append(s)
        for v in self.SET_VBLE_SET:
            x = self.SET_TO_STR(self.GenRandSubSet(self.DIST_SET))
            s = v + " := %s"%x
            res.append(s)
        for v in self.ELEM_VBLE_SET:
            x = self.DIST_SET[self.RandNat(len(self.DIST_SET))]
            s = v + " := %s"%x
            res.append(s)


        return res

    # Generate basic invariants, e.g. the definition domain of variables.
    def GenInv(self):
        res = ""
        for i in xrange(len(self.INT_VBLE_SET)):
            x = "  " + self.INT_VBLE_SET[i] + " : " + "%d..%d &"%(self.MIN_INT,self.MAX_INT)
            res = res + x

        for i in xrange(len(self.BOOL_VBLE_SET)):
            x = "  " + self.BOOL_VBLE_SET[i] + " : " + "BOOL &"
            res = res + x

        for i in xrange(len(self.SET_VBLE_SET)):
            x = "  " + self.SET_VBLE_SET[i] + " <: " + "DistElemSet &"
            res = res + x

        for i in xrange(len(self.ELEM_VBLE_SET)):
            x = "  " + self.ELEM_VBLE_SET[i] + " : " + "DistElemSet &"
            res = res + x


        res = res[0:len(res)-2]
        return res

    # Generate extra invariants, e.g. conditional invariants
    def GenExtraInv(self):
        res = ""
        for i in xrange(self.EXINV_NUM):
            Inv = self.GenCond(self.EXINVCOND_LEN)
            res = res + Inv + " & "
        res = res[0:len(res)-2]
        return res


    # Generate the set constraint of distinct elements.
    def GenSetCons(self):
        v = self.SET_TO_STR(self.DIST_SET)
        res = "DistElemSet = %s"%v
        return res

        
        
    
 
    # Generate a B-machine.
    def GenMch(self, MchName):
        res = []
        
        # Machine Name
        x = ["MACHINE", "  %s"%MchName]
        res = res + x

        # Sets
        x = ["SETS", "  %s"%self.GenSetCons()]
        res = res + x
        
        # Variables
        vs = ""
        for i in xrange(len(self.INT_VBLE_SET)):
            vs = vs + ", " + self.INT_VBLE_SET[i]
        for i in xrange(len(self.BOOL_VBLE_SET)):
            vs = vs + ", " + self.BOOL_VBLE_SET[i]
        for i in xrange(len(self.SET_VBLE_SET)):
            vs = vs + ", " + self.SET_VBLE_SET[i]
        for i in xrange(len(self.ELEM_VBLE_SET)):
            vs = vs + ", " + self.ELEM_VBLE_SET[i]
        vs = " " + vs[1:len(vs)]
        x = ["VARIABLES", vs]
        res = res + x
        
        # Invariants
        inv = ["INVARIANT"]
        """
        for i in xrange(len(self.INT_VBLE_SET)):
            x = "  " + self.INT_VBLE_SET[i] + " : " + "%d..%d &"%(self.MIN_INT,self.MAX_INT)
            inv.append(x)
            
        inv[-1] = inv[-1][0:len(inv[-1])-2] 
        """
        inv.append(self.GenInv())
        if self.EXINV_NUM > 0:
            inv.append(" & " + self.GenExtraInv())
        res = res + inv
        
        # Initialisation
        initst = ["INITIALISATION"]
        v = self.GenInit()
        for x in v:
            y = "  " + x + " ;"
            initst.append(y)
        initst[-1] = initst[-1][0:len(initst[-1])-2]
        res = res + initst
        
        # Operations
        opes = ["OPERATIONS"]
        v = self.GenAllOpes()
        for x in v:
            y = []
            y.append("  %s ="%x[0])
            y.append("    PRE")
            y.append("      %s"%x[1])
            y.append("    THEN")
            z = []
            for ss in x[2]:
                st = "      %s ;"%ss
                z.append(st)
            z[-1] = z[-1][0:len(z[-1])-2]
            y = y + z
            y.append("    END ;")
            opes = opes + y
            
        opes[-1] = opes[-1][0:len(opes[-1])-2]
        res = res + opes


        
        res.append("END")
        
        return res
       
    
class BStateGraphForNN(object):

    def __init__(self):

        self.fname = None
        self.graph = None
        self.TList = None

    def ReadStateGraph(self,fname):
        self.fname = fname
        self.graph = pydotplus.graphviz.graph_from_dot_file(self.fname)
        return 0

    def GetRevValue(self,x):
        y = x.replace("&",",")
        res = self.GetLabelValue(y)
        return res

    def SplitLabel(self,x):


        y = x.replace("\\n","")

        y = y.replace("\"","")

        y = y.split(",")

        # Merging multi-dimensional variable names and values.
        res = []
        np = 0
        for t in y:
            lp = t.count("(") 
            rp = t.count(")")
            if np == 0:
                res.append(t)
            else:
                res[-1] = res[-1] + "," + t
            np = np + lp - rp

        return res

    def GetLabelValue(self,x):
        y = self.SplitLabel(x)
        res = []
        #print y
        for t in y:
            v = t.replace(" ","")
            v = v.split("=")
            if v[0] == 'root': return 'ROOT'
            if v[0] == '': return 'NONE'
            if len(v) == 2:
                if "{" in v[1]:
                    sp = v[1]
                    sp = sp.replace("\\","")
                    sp = sp.replace("{","")
                    sp = sp.replace("}","")
                    if sp == "":
                        s = []
                    else:
                        s = [sp]
                else:
                    s = v[1]#int(v[1])
                res.append(s)
            else:
                s = v[0].replace("\\","")
                s = s.replace("}","")
                res[-1].append(s)
        return res


    def GetLabelVble(self,x):
        y = self.SplitLabel(x)
        res = []
        #print y
        for t in y:
            #print t
            v = t.replace(" ","")
            v = v.split("=")
            if v[0] == 'root': return 'ROOT'
            if len(v) == 2:
                s = v[0]
    
                res.append(s)
            else:
                continue
        return res

    def GetVbleList(self):

        # Find a node that is not root or initialisation.

        EdgeList = self.graph.get_edge_list()
        NodeList = self.graph.get_node_list()
        for k in xrange(len(EdgeList)):
            Ope = EdgeList[k].get_label()
            if Ope == "INITIALISATION" or Ope == "SETUP_CONSTANTS":
                continue

            q = EdgeList[k].get_destination()
            v = "None"
            for i in xrange(len(NodeList)):
                nid = NodeList[i].get_name()
                if nid == q:
                    v = i
                if v != "None": break

        X = NodeList[v].get_label()
        if X == None: X = NodeList[v+1].get_label()
        X = self.GetLabelVble(X)
        return X

    def GetInitList(self):
        res = []
        EdgeList = self.graph.get_edge_list()
        NodeList = self.graph.get_node_list()
        S = []
        for k in xrange(len(EdgeList)):
            Ope = EdgeList[k].get_label()
            Ope = Ope.replace("\\n","")
            Ope = Ope.replace("\"","")
            Ope = Bmch.get_first_token(Ope)
            if Ope != "INITIALISATION" and Ope != "INITIALIZATION":
                continue
            q = EdgeList[k].get_destination()
            for i in xrange(len(NodeList)):
                nid = NodeList[i].get_name()
                if nid == q:
                    Y = NodeList[i].get_label()
                    Y = self.GetLabelValue(Y)
                    S.append(Y)
                    break
        self.InitList = S
        return S


    def GetTransList(self):
        D = []
        EdgeList = self.graph.get_edge_list()
        NodeList = self.graph.get_node_list()
        for k in xrange(len(EdgeList)):
            Ope = EdgeList[k].get_label()
            #print Ope
            Ope = Ope.replace("\\n","")
            Ope = Ope.replace("\"","")
            Ope = Bmch.get_first_token(Ope)
            p = EdgeList[k].get_source()
            q = EdgeList[k].get_destination()
            u = "None"
            v = "None"
            for i in xrange(len(NodeList)):
                nid = NodeList[i].get_name()
                if nid == p:
                    u = i
                if nid == q:
                    v = i
                if u != "None" and v != "None": break
            X = NodeList[u].get_label()
            Y = NodeList[v].get_label()
            X = self.GetLabelValue(X)
            Y = self.GetLabelValue(Y)
            #X = self.SplitLabel(X)
            #Y = self.SplitLabel(Y)
            #print X,Ope,Y
            if X != "ROOT" and X != "NONE" and Ope != "INITIALISATION" and Ope != "SETUP_CONSTANTS":
                D.append([X,Ope,Y])
        D.sort()
        res = [D[0]]
        for i in xrange(1,len(D)):
            if D[i] != D[i-1]:
                res.append(D[i])
        self.TList = res
        return res

    def GetAllOpeNames(self,TList):
        res = []
        for x in TList:
            p = x[1]
            if p in res: continue
            res.append(p)
        res.sort()
        return res

    def IntToVector(self,x,s):
        #print s
        y = []
        for t in s:
            if x >= t:
                y.append(1)
            else:
                y.append(-1)
        """
        if xmax == xmin:
            return [0.0]
        y = (x - xmin) * 1.0 / (xmax - xmin)
        if y > 1.0: y = 1.0
        if y < 0.0: y = 0.0
        y = [y]
        """
        return y

    def DistToVector(self,x,s):
        y = [0] * len(s)
        if x in s:
            i = s.index(x)
            y[i] = 1
        return y


    def SetToVector(self,x,s):
        y = [-1] * len(s)
        for p in x:
            #if p == "{}": return y
            if p in s:
                i = s.index(p)
                y[i] = 1
        return y

    def StateToVector(self,state,stype):
        res = []
        for i in xrange(len(state)):
            x = state[i]
            t = stype[i]
            if t[0] == "Int":
                y = self.IntToVector(int(x),t[1:len(t)])
            elif t[0] == "Dist":
                y = self.DistToVector(x,t[1:len(t)])
            elif t[0] == "Bool":
                y = self.DistToVector(x,["TRUE","FALSE"])
            elif t[0] == "Set":
                y = self.SetToVector(x,t[1:len(t)])
            else:
                print "State Type Error: ", state, stype
                exit()
            res = res + y
        return res

    def get_grand_type(self,v):
        if type(v) == type([]):
            return "Set"
        x = v.replace(" ","")
        if x == "TRUE" or x == "FALSE": return "Bool"
        try:
            t = int(x)
            return "Int"
        except ValueError:
            t = -1
        return "Dist"


    def GetSetTypeFromTransList(self,TList):
        x = TList[0]
        res = []
        #print TList
        #sys.stdin.readline()
        for i in xrange(len(x[0])):
            res.append([])
        for x in TList:
            #print x
            #print res
            for p in [x[0],x[2]]:
                #print "PPPQ",p
                for i in xrange(len(p)):
                    #print "PPP",i,p[i]
                    if p[i] in res[i]: continue
                    res[i].append(p[i])
        for i in xrange(len(res)):
            res[i].sort()
            t = self.get_grand_type(res[i][0])
            #print t
            #sys.stdin.readline()
            if t == "Int":
                rt = []
                for x in res[i]:
                    rt.append(int(x))
                rt.sort()
                res[i] = ["Int"] + rt
                #print res[i]
                #sys.stdin.readline()
                """
                xmin = 10000000000000
                xmax = -10000000000000
                for x in res[i]:
                    v = int(x)
                    if v < xmin: xmin = v
                    if v > xmax: xmax = v
                res[i] = ["Int",xmin,xmax]
                """
            elif t == "Set":
                y = [p for q in res[i] for p in q]
                y = list(set(y))
                #if "{}" in y: y.remove("{}")
                y.sort()
                res[i] = [t] + y
            else:
                res[i] = [t] + res[i]
   
        #print res
        #sys.stdin.readline()
        return res

    def TransListToData(self,TList,SType,OpeList):
        res = []
        """
        # MinDims is the minimum dimension of data. It is very useful for ResNet. 
        if MinDims == None:
            kdim = 1
        else:
            p = TLIst[0]
            x = self.StateToVector(p[0],SType)+self.StateToVector(p[2],SType)
            kdim = MinDims / len(x) + 1
        """
        for p in TList:
            x = self.StateToVector(p[0],SType)+self.StateToVector(p[2],SType)
            #x = x * kdim
            opename = Bmch.get_first_token(p[1])
            t = OpeList.index(opename)
            res.append([x,t])
        random.shuffle(res)
        l = len(res)
        ltr = int(l * 0.8)
        lcv = int(l * 0.9)
        tr_res = res[0:ltr]
        cv_res = res[ltr:lcv]
        te_res = res[lcv:l]
        return [tr_res,cv_res,te_res]

    

    # For the example in FMSD
    def FMSDTransListToData(self,TList,SType,OpeList):
        res = []
        """
        # MinDims is the minimum dimension of data. It is very useful for ResNet. 
        if MinDims == None:
            kdim = 1
        else:
            p = TLIst[0]
            x = self.StateToVector(p[0],SType)+self.StateToVector(p[2],SType)
            kdim = MinDims / len(x) + 1
        """
        for p in TList:
            x = self.StateToVector(p[0],SType)+self.StateToVector(p[2],SType)
            #x = x * kdim
            opename = Bmch.get_first_token(p[1])
            t = OpeList.index(opename)
            res.append([x,t])
        return res

    # FL - List of data files. e.g. [data/train.csv,data/test.csv]
    def ReadCSVSemanticsDataAndComputeTypes(self,FL):
        SData = []
        AllData = []
        for fname in FL:
            f = open(fname,"r")
            D = f.readlines()
            for i in xrange(len(D)):
                D[i] = D[i].replace("\n","")
                D[i] = D[i].split(",")
            SData.append(D)
            AllData = AllData + D[1:len(D)]
        fhead = SData[0][0]

        #for x in AllData: print x
        DType = []
        for i in xrange(len(fhead)):
            DType.append([])
        
        for P in AllData:
            for i in xrange(len(P)):
                if not(P[i] in DType[i]):
                    DType[i].append(P[i])

        FeatDim = 0
        for x in DType[0:len(DType)-1]:
            FeatDim = FeatDim + len(x)

        NumClass = len(DType[-1])

        VData = []
        for DSet in SData:
            S = []
            sflag = 0
            for D in DSet:
                # Skip file header.
                if sflag == 0:
                    sflag = 1
                    continue

                # Label
                T = DType[-1].index(D[-1])
                
                # Feature
                V = []
                for i in xrange(len(D)-1):
                    P = [0] * len(DType[i])
                    idx = DType[i].index(D[i])
                    P[idx] = 1
                    V = V + P
                
                S.append([V,T])
            VData.append(S)

        return VData,DType
            


    # PPD --- Pre-Post-Data
    # DType --- Types
    def VectorisePrePostData(self,PPD,DType):
        SData = [PPD]
        AllData = PPD[1:len(PPD)]
        """
        for fname in FL:
            f = open(fname,"r")
            D = f.readlines()
            for i in xrange(len(D)):
                D[i] = D[i].replace("\n","")
                D[i] = D[i].split(",")
            SData.append(D)
            AllData = AllData + D[1:len(D)]
        """
        fhead = SData[0][0]

        FeatDim = 0
        for x in DType[0:len(DType)-1]:
            FeatDim = FeatDim + len(x)

        NumClass = len(DType[-1])

        VData = []
        for DSet in SData:
            SV = []
            ST = []
            sflag = 0
            for D in DSet:
                # Skip file header.
                if sflag == 0:
                    sflag = 1
                    continue

                # Label
                if (D[-1] in DType[-1]):
                    T = DType[-1].index(D[-1])
                else:
                    T = "NoLabel"
                
                # Feature
                V = []
                for i in xrange(len(D)-1):
                    P = [0] * len(DType[i])
                    if D[i] in DType[i]:
                        idx = DType[i].index(D[i])
                        P[idx] = 1
                    V = V + P
                SV.append(V)
                ST.append(T)
            VData.append([SV,ST])

        return VData
         

    # FL - List of data files. e.g. [data/train.csv,data/test.csv]
    def ReadCSVSemanticsData(self,FL):
        SData = []
        AllData = []
        for fname in FL:
            f = open(fname,"r")
            D = f.readlines()
            for i in xrange(len(D)):
                D[i] = D[i].replace("\n","")
                D[i] = D[i].split(",")
            SData.append(D)
            AllData = AllData + D[1:len(D)]
        fhead = SData[0][0]

        #for x in AllData: print x
        DType = []
        for i in xrange(len(fhead)):
            DType.append([])
        
        for P in AllData:
            for i in xrange(len(P)):
                if not(P[i] in DType[i]):
                    DType[i].append(P[i])

        FeatDim = 0
        for x in DType[0:len(DType)-1]:
            FeatDim = FeatDim + len(x)

        NumClass = len(DType[-1])

        VData = []
        for DSet in SData:
            S = []
            sflag = 0
            for D in DSet:
                # Skip file header.
                if sflag == 0:
                    sflag = 1
                    continue

                # Label
                T = DType[-1].index(D[-1])
                
                # Feature
                V = []
                for i in xrange(len(D)-1):
                    P = [0] * len(DType[i])
                    idx = DType[i].index(D[i])
                    P[idx] = 1
                    V = V + P
                
                S.append([V,T])
            VData.append(S)

        return VData
            
    def WriteSemanticDataToTxt(self,D,fname):
        f = open(fname,"w")
        for i in xrange(len(D)):
            for j in xrange(len(D[i][0])):
                f.write(str(D[i][0][j]))
                f.write(" ")
            f.write("\n")
            f.write(str(D[i][1]))
            f.write("\n")
        return 0

    # fh - Head of file.
    # dt - Data.
    def WriteDataToTxt(self,fh,dt,fname):
        f = open(fname,"w")
        for x in fh:
            f.write(x)
        for x in dt:
            for p in x[0]:
                f.write(str(p))
                f.write(" ")
            f.write("\n")
            f.write(str(x[1]))
            f.write("\n")
        f.close()
        return 0

    def SortSetsInTransList(self,TL):

        TLT = []
        for x in TL:
            p = []
            for u in x[0]:
                if type(u) == type([]):
                    p.append(sorted(u))
                else:
                    p.append(u)
            q = []
            for u in x[2]:
                if type(u) == type([]):
                    q.append(sorted(u))
                else:
                    q.append(u)
            TLT.append([p,x[1],q])
        return TLT 

    def GetSilasVList0(self,VList,SType):
        res = ["Operation-Name"]

        B = []
        for i in xrange(len(VList)):
            V = VList[i]
            T = SType[i]
            if T[0] == "Set":
                for x in T[1:len(T)]:
                    s = V + "-" + x 
                    B.append(s)
            else:
                B.append(V)
        for x in B:
            s = "Pre-" + x
            res.append(s)
        for x in B:
            s = "Post-" + x
            res.append(s)
        res.append("Available-Transition")
        return res

    def GetSilasState0(self,S,SType):
        res = []
        for i in xrange(len(S)):
            V = S[i]
            T = SType[i]
            if T[0] == "Set":
                r = []
                for x in T[1:len(T)]:
                    if x in V:
                        r.append("In")
                    else:
                        r.append("NotIn")
                res = res + r
            else:
                res = res + [V]
        return res


    def GetSilasVList(self,VList,SType):
        res = ["Operation-Name"]

        B = []
        for i in xrange(len(VList)):
            V = VList[i]
            T = SType[i]
            if T[0] == "Set":
                for x in T[1:len(T)]:
                    s = V + "-" + x 
                    B.append(s)
            else:
                B.append(V)
        for x in B:
            s = "Pre-" + x
            res.append(s)
        for x in B:
            s = "Post-" + x
            res.append(s)
        res.append("Available-Transition")
        return res

    def GetSilasState(self,S,SType):
        res = []
        for i in xrange(len(S)):
            V = S[i]
            T = SType[i]
            if T[0] == "Set":
                r = []
                for x in T[1:len(T)]:
                    if x in V:
                        r.append("In")
                    else:
                        r.append("NotIn")
                res = res + r
            elif T[0] == "Int":
                res = res + ["I%s"%V]
            else:
                res = res + [V]
        return res


    def GetSilasVList2(self,VList,SType):
        res = ["Operation-Name"]

        B = []
        for i in xrange(len(VList)):
            V = VList[i]
            T = SType[i]
            for x in T[1:len(T)]:
                s = V + "-" + str(x) 
                B.append(s)
        for x in B:
            s = "Pre-" + x
            res.append(s)
        for x in B:
            s = "Post-" + x
            res.append(s)
        res.append("Available-Transition")
        return res

    def GetSilasState2(self,S,SType):
        res = []
        for i in xrange(len(S)):
            V = S[i]
            T = SType[i]
            TP = []
            for x in T[1:len(T)]:
                TP.append(str(x))
            if T[0] == "Set":
                VP = []
                for x in V:
                    VP.append(str(x))
            else:
                VP = [str(V)]

            r = []
            # For Silas, "NotIn" + "In" is faster than "0" + "1"
            for j in xrange(len(TP)):
                r.append("NotIn")
            for x in VP:
                if x in TP:
                    j = TP.index(V)
                    r[j] = "In"
            res = res + r
        return res



    def TransListToPrePostData(self,TList,SType,VList):

        VData =  self.GetSilasVList(VList,SType)

        P = []
        for x in TList:
            u = self.GetSilasState(x[0],SType)
            v = self.GetSilasState(x[2],SType)
            s = [x[1]] + u + v + ["Y"]
            P.append(s)

        return [VData] + P


    def SilasTransListToData(self,TList,SType,VList,NProp,RSeed):

        random.seed(RSeed)

        VData =  self.GetSilasVList(VList,SType)

        States = []
        Opes = []
        PosExp = []
        for T in TList:
            if len(T) != 3: continue
            PosExp.append(T)
            if not(T[0] in States):
                States.append(T[0])
            if not(T[1] in Opes):
                Opes.append(T[1])
            if not(T[2] in States):
                States.append(T[2])

        
        NegExp = []
        while len(NegExp) * 1.0 / len(PosExp) < NProp:
            i = random.randint(0,len(States)-1)
            j = random.randint(0,len(States)-1)
            k = random.randint(0,len(Opes)-1)
            T = [States[i],Opes[k],States[j]]
            if not(T in PosExp):
                NegExp.append(T)

        P = []
        for x in PosExp:
            u = self.GetSilasState(x[0],SType)
            v = self.GetSilasState(x[2],SType)
            s = [x[1]] + u + v + ["Y"]
            P.append(s)

        N = []
        for x in NegExp:
            u = self.GetSilasState(x[0],SType)
            v = self.GetSilasState(x[2],SType)
            s = [x[1]] + u + v + ["N"]
            N.append(s)


        return [VData] + P + N

    # TL --- List of transitions
    # SF --- List of post-states
    # Output --- List of transitions that are in TL and have a post state in SF
    def GetTransitionsWithPostStates(self,TL,SF):
        res = []
        for x in TL:
            if x[2] in SF:
                res.append(x)
        return res

    def GetStatesWithoutOutgoingTransitions(self,TL):
        # US --- set of pre-states
        # PS --- set of post-states
        US = []
        PS = []
        for x in TL:
            if not(x[0] in US):
                US.append(x[0])
            if not(x[2] in PS):
                PS.append(x[2])
        res = []
        for x in PS:
            if not(x in US) and not(x in res):
                res.append(x)
        print "Note: Some operations perform computations on constants and do not change the values of variables. These operations are not shown in the state diagram, but they can resolve all deadlocks. As a result, this function cannot deal with this situtation."
        
        return res

    # find deterministic transitions in TL
    def FindDeterministicTransitions(self,TL):
        res = []
        TL.sort()
        TLD = [TL[0]]
        for i in xrange(1,len(TL)):
            if TL[i] != TL[i-1]:
                TLD.append(TL[i])
        res = []
        for i in xrange(len(TLD)):
            Flag = True
            X = TLD[i]
            if i > 0:
                Y = TLD[i-1]
                if X[0] == Y[0] and X[1] == Y[1] and X[2] != Y[2]:
                    Flag = False
            if i < len(TLD)-1:
                Y = TLD[i+1]
                if X[0] == Y[0] and X[1] == Y[1] and X[2] != Y[2]:
                    Flag = False
            if Flag == True:
                res.append(X)
        return res
        """
            x = TL[i]
            P = x[0]
            op = x[1]
            Q = x[2]
            flag = True

            for y in TL:
                if y[0] == P and y[1] == op and y[2] != Q:
                    flag = False
                    break

            if flag == True:
                res.append(x)
        return res
        """
""" 
X = BProgram()
Mch = X.GenMch("Try")
for x in Mch: print x
f = open("try.mch","w")
for x in Mch:
    f.write(x)
    f.write("\n")
f.close()

print X.AtomicSet()
"""

"""

vname = ["IntV0","IntV1","IntV2","BoolV0","BoolV1","BoolV2","SetV0","SetV1","SetV2","ElemV0","ElemV1","ElemV2"]
inttype = ["Int",-10,10]
booltype = ["Bool"]
settype = ["Set","D0","D1","D2","D3","D4","D5","D6","D7"]
disttype = ["Dist","D0","D1","D2","D3","D4","D5","D6","D7"]
stype = [inttype,inttype,inttype,booltype,booltype,booltype,settype,settype,settype,disttype,disttype,disttype]
 
sg = BStateGraphForNN()
sg.ReadStateGraph("restemp/tr_set.statespace.dot")


TL =  sg.GetTransList()

OpeList = sg.GetAllOpeNames(TL)
SType = sg.GetSetTypeFromTransList(TL)

print TL
print OpeList

mchfile = "restemp/tr_set.mch"
with open(mchfile) as mchf:
    mch = mchf.readlines()
mch = [x.strip() for x in mch]

OpeList = Bmch.get_all_ope_names(mch)


dt = sg.TransListToData(TL,SType,OpeList)

sg.WriteDataToTxt(dt[0],"train.txt")
sg.WriteDataToTxt(dt[1],"valid.txt")
sg.WriteDataToTxt(dt[2],"eval.txt")

"""

