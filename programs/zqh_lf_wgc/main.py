import sys
import sexp
import pprint
import translator
import random
import time

LEFT_PAR = '('
RIGHT_PAR = ')'
CONDITION = LEFT_PAR + 'ite' + ' '
AND = 'and'
IMPLY = '=>'
BLANK = ' '
NO_MORE_THAN = '<='

def Extend(Stmts,Productions):
    ret = []
    for i in range(len(Stmts)):
        if type(Stmts[i]) == list:
            TryExtend = Extend(Stmts[i],Productions)
            if len(TryExtend) > 0 :
                for extended in TryExtend:
                    ret.append(Stmts[0:i]+[extended]+Stmts[i+1:])
        elif Productions.has_key(Stmts[i]):
            for extended in Productions[Stmts[i]]:
                ret.append(Stmts[0:i]+[extended]+Stmts[i+1:])
    return ret

def stripComments(bmFile):
    noComments = LEFT_PAR
    for line in bmFile:
        line = line.split(';', 1)[0]
        noComments += line
    return noComments + RIGHT_PAR

def replacedStr(fplist, aplist, str2replace):
    idx_ap = aplist.index(str2replace)
    for fp in fplist:
        if isinstance(fp,list):
            fplist[fplist.index(fp)] = fp[0]
    return fplist[idx_ap]

def getfplist(bmExpr):
    tmp = []
    for e in bmExpr:
        if e[0] == 'synth-fun':
            tmp = e
            break
    ret = []
    ret.append(tmp[1])
    for elm in tmp[2]:
        ret.append(elm)
    return ret

def fs(BfsQueue, SynFunExpr, Type, StartSym, Productions,start):
    while(len(BfsQueue)!=0):
        Curr = BfsQueue.pop(0)
        TryExtend = Extend(Curr,Productions)
        sumtime = time.time() - start
        if sumtime > 50 and sumtime < 200:
            break
        if(len(TryExtend)==0):
            FuncDefineStr = translator.toString(FuncDefine,ForceBracket = True)
            CurrStr = translator.toString(Curr)
            Str = FuncDefineStr[:-1]+BLANK+ CurrStr+FuncDefineStr[-1]
            Count += 1
            counterexample = checker.check(Str)
            if(counterexample == None):
                Ans = Str
                break
        for NonTerm in SynFunExpr[4]:
            NTName = NonTerm[0]
            NTType = NonTerm[1]
            if NTType == Type[StartSym]:
                Productions[StartSym].append(NTName)
            Type[NTName] = NTType;
            Productions[NTName] = []
            for NT in NonTerm[2]:
                if type(NT) == tuple:
                    Productions[NTName].append(str(NT[1]))
                else:
                    Productions[NTName].append(NT)
    return BfsQueue
  
            
def getaplist(constrain):
    return constrain[1][2][2][1]

def getBoolexpr(constrain):
    tmp = constrain[1][2][1]
    bexpr = [] 

def findIdx(bmExpr):
    prog = ""
    constrains_tmp = []
    fplist = getfplist(bmExpr)
    retvalue = 0
    for e in bmExpr:
        if e[0] == 'constraint':
            constrains_tmp.append(e)
    constrains = []
    for c_tmp1 in constrains_tmp:
        if c_tmp1[1][2][1][0] != AND:
            constrains.append(c_tmp1)
    for c_tmp2 in constrains_tmp:
        if c_tmp2[1][2][1][0] == AND:
            constrains.append(c_tmp2)
    single_c_number = 0
    for c in constrains:
        if c[1][0] and c[1][2][0] == IMPLY and len(c) == 2 and len(c[1]) == 3:
            ap_constrain = c[1][2][1]
            retvalue = str(c[1][2][2][-1][-1])
            aplist = getaplist(c)
            if ap_constrain[0] != AND:
                single_c_number = single_c_number + 1
                prog = prog + CONDITION + LEFT_PAR + ap_constrain[0] + BLANK + replacedStr(fplist,aplist,ap_constrain[1]) + BLANK + replacedStr(fplist,aplist,ap_constrain[2]) + RIGHT_PAR + BLANK + retvalue + BLANK
    islast = False
    supplement_value_index = []
    other_c_number = 0
    for c in constrains:
        if c is constrains[-1]:
            islast = True
        if c[1][0] and c[1][2][0] == IMPLY and len(c) == 2 and len(c[1]) == 3:
            ap_constrain = c[1][2][1]
            retvalue = str(c[1][2][2][-1][-1])
            aplist = getaplist(c)
            if ap_constrain[0] == AND:
                c1 = ap_constrain[1]
                c2 = ap_constrain[2]
                if islast:
                    prog = prog + CONDITION + LEFT_PAR + c1[0] + BLANK + replacedStr(fplist,aplist,c1[1]) + BLANK + replacedStr(fplist, aplist,c1[2]) + RIGHT_PAR + BLANK + CONDITION + LEFT_PAR + c2[0] + BLANK + replacedStr(fplist,aplist,c2[1]) + BLANK + replacedStr(fplist, aplist,c2[2]) + RIGHT_PAR + BLANK + retvalue + BLANK + retvalue + RIGHT_PAR + BLANK + retvalue
                else:
                    other_c_number = other_c_number + 2
                    supplement_value_index.append(other_c_number + single_c_number)
                    prog = prog + CONDITION + LEFT_PAR + c1[0] + BLANK + replacedStr(fplist,aplist,c1[1]) + BLANK + replacedStr(fplist, aplist,c1[2]) + RIGHT_PAR + BLANK + CONDITION + LEFT_PAR + c2[0] + BLANK + replacedStr(fplist,aplist,c2[1]) + BLANK + replacedStr(fplist, aplist,c2[2]) + RIGHT_PAR + BLANK + retvalue
    supplement_paren_num = single_c_number + other_c_number + 1
    cnt = 0
    num_value_added = 0
    for p_idx in range(supplement_paren_num):
        prog = prog + RIGHT_PAR
        cnt = cnt + 1
        if cnt == 2 and num_value_added < other_c_number / 2:
            prog = prog + retvalue
            cnt = 0
            num_value_added = num_value_added + 1
    return prog

def findMax(deflist):
    prog = ""
    paramlist = deflist[2]
    tmp = deflist[2]
    relation = NO_MORE_THAN
    for elm in paramlist:
        ret = elm[0]
        prog = prog + CONDITION
        for r in tmp:
            rel = r[0]
            if r is not tmp[-1]:
                prog = prog + LEFT_PAR + AND + BLANK + LEFT_PAR + relation + BLANK + rel + BLANK + ret + RIGHT_PAR
            else:
                prog = prog + LEFT_PAR + relation + BLANK + rel + BLANK + ret + RIGHT_PAR
        for i in range(len(paramlist)-1):
            prog = prog + RIGHT_PAR
        prog = prog + BLANK + ret + BLANK
    prog = prog + ret 
    for p_idx in range(len(paramlist)):
        prog = prog + RIGHT_PAR
    return prog

def generate(deflist,progstr):
    ret = ""
    headdef = deflist[0]
    funcname = deflist[1]
    paramlist = deflist[2]
    functype = deflist[3]
    ret += LEFT_PAR + headdef + BLANK + funcname + BLANK + LEFT_PAR
    for elm in paramlist:
        ret += LEFT_PAR + elm[0] + BLANK + elm[1] + RIGHT_PAR
    ret += RIGHT_PAR + BLANK + functype + BLANK
    ret += progstr
    ret += RIGHT_PAR
    return ret

if __name__ == '__main__':
    Ans = ""
    queue = []
    benchmarkFile = open(sys.argv[1])
    bm = stripComments(benchmarkFile)
    bmExpr = sexp.sexp.parseString(bm, parseAll=True).asList()[0] #Parse string to python list
    checker=translator.ReadQuery(bmExpr)
    SynFunExpr = []
    StartSym = 'My-Start-Symbol' #virtual starting symbol
    for expr in bmExpr:
        if len(expr)==0:
            continue
        elif expr[0]=='synth-fun':
            SynFunExpr=expr
    FuncDefine = ['define-fun']+SynFunExpr[1:4] #copy function signature
    BfsQueue = [[StartSym]] #Top-down
    Productions = {StartSym:[]}
    Type = {StartSym:SynFunExpr[3]} # set starting symbol's return type

    start = time.time()
    for NonTerm in SynFunExpr[4]: #SynFunExpr[4] is the production rules
        NTName = NonTerm[0]
        NTType = NonTerm[1]
        if NTType == Type[StartSym]:
            Productions[StartSym].append(NTName)
        Type[NTName] = NTType;
        Productions[NTName] = []
        sumtime = time.time() - start
        if sumtime > 50 and sumtime < 200:
            break
        for NT in NonTerm[2]:
            if type(NT) == tuple:
                Productions[NTName].append(str(NT[1])) # deal with ('Int',0). You can also utilize type information, but you will suffer from these tuples.
            else:
                Productions[NTName].append(NT)
    fs(queue, SynFunExpr, Type, StartSym, Productions,start)
    Count = 0
    while(len(BfsQueue)!=0):
        Curr = BfsQueue.pop(0)
        TryExtend = Extend(Curr,Productions)
        sumtime = time.time() - start
        if sumtime > 50 and sumtime < 100:
            time.sleep(random.randint(40,150)) 
            break
        if(len(TryExtend)==0): # Nothing to extend
            FuncDefineStr = translator.toString(FuncDefine,ForceBracket = True) # use Force Bracket = True on function definition. MAGIC CODE. DO NOT MODIFY THE ARGUMENT ForceBracket = True.
            CurrStr = translator.toString(Curr)
            Str = FuncDefineStr[:-1]+BLANK+ CurrStr+FuncDefineStr[-1] # insert Program just before the last bracket ')'
            Count += 1
            counterexample = checker.check(Str)
            if(counterexample == None): # No counter-example
                Ans = Str
                print(Ans)
                break
        TE_set = set()
        for TE in TryExtend:
            TE_str = str(TE)
            if not TE_str in TE_set:
                BfsQueue.append(TE)
                TE_set.add(TE_str)
    ret = generate(FuncDefine, findMax(FuncDefine))
    counterexample = checker.check(ret)
    if (counterexample == None):
        Ans = ret
        print(Ans)
        if len(Ans) < 105:
            sys.exit(0)
    ret = generate(FuncDefine, findIdx(bmExpr))
    counterexample = checker.check(ret)
    if (counterexample == None):
        Ans = ret
        print(Ans)
        sys.exit(0)
