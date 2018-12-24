import sys
import sexp
import pprint
import translator

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
    noComments = '('
    for line in bmFile:
        line = line.split(';', 1)[0]
        noComments += line
    return noComments + ')'

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
        if c_tmp1[1][2][1][0] != 'and':
            constrains.append(c_tmp1)
    for c_tmp2 in constrains_tmp:
        if c_tmp2[1][2][1][0] == 'and':
            constrains.append(c_tmp2)
    single_c_number = 0
    for c in constrains:
        if c[1][0] and c[1][2][0] == '=>' and len(c) == 2 and len(c[1]) == 3:
            ap_constrain = c[1][2][1]
            retvalue = str(c[1][2][2][-1][-1])
            aplist = getaplist(c)
            if ap_constrain[0] != 'and':
                single_c_number = single_c_number + 1
                prog = prog + "(ite (" + ap_constrain[0] + " " + replacedStr(fplist,aplist,ap_constrain[1]) + " " + replacedStr(fplist,aplist,ap_constrain[2]) + ") " + retvalue + " "
    islast = False
    supplement_value_index = []
    other_c_number = 0
    for c in constrains:
        if c is constrains[-1]:
            islast = True
        if c[1][0] and c[1][2][0] == '=>' and len(c) == 2 and len(c[1]) == 3:
            ap_constrain = c[1][2][1]
            retvalue = str(c[1][2][2][-1][-1])
            aplist = getaplist(c)
            if ap_constrain[0] == 'and':
                c1 = ap_constrain[1]
                c2 = ap_constrain[2]
                if islast:
                    prog = prog + "(ite (" + c1[0] + " " + replacedStr(fplist,aplist,c1[1]) + " " + replacedStr(fplist, aplist,c1[2]) + ") " + "(ite (" + c2[0] + " " + replacedStr(fplist,aplist,c2[1]) + " " + replacedStr(fplist, aplist,c2[2]) + ") " + retvalue + " " + retvalue + ") " + retvalue
                else:
                    other_c_number = other_c_number + 2
                    supplement_value_index.append(other_c_number + single_c_number)
                    prog = prog + "(ite (" + c1[0] + " " + replacedStr(fplist,aplist,c1[1]) + " " + replacedStr(fplist, aplist,c1[2]) + ") " + "(ite (" + c2[0] + " " + replacedStr(fplist,aplist,c2[1]) + " " + replacedStr(fplist, aplist,c2[2]) + ") " + retvalue
    supplement_paren_num = single_c_number + other_c_number + 1
    cnt = 0
    num_value_added = 0
    for p_idx in range(supplement_paren_num):
        prog = prog + ")"
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
    relation = "<="
    for elm in paramlist:
        ret = elm[0]
        prog = prog + "(ite "
        for r in tmp:
            rel = r[0]
            if r is not tmp[-1]:
                prog = prog + "(and (" + relation + " " + rel + " " + ret + ")"
            else:
                prog = prog + "(" + relation + " " + rel + " " + ret + ")"
        for i in range(len(paramlist)-1):
            prog = prog + ")"
        prog = prog + " " + ret + " " 
    prog = prog + ret 
    for p_idx in range(len(paramlist)):
        prog = prog + ")"
    return prog

def generate(deflist,progstr):
    ret = ""
    headdef = deflist[0]
    funcname = deflist[1]
    paramlist = deflist[2]
    functype = deflist[3]
    ret += "(" + headdef + " " + funcname + " ("
    for elm in paramlist:
        ret += "(" + elm[0] + " " + elm[1] + ")"
    ret += ") " + functype + " "
    ret += progstr
    ret += ")"
    return ret

if __name__ == '__main__':
    benchmarkFile = open(sys.argv[1])
    bm = stripComments(benchmarkFile)
    bmExpr = sexp.sexp.parseString(bm, parseAll=True).asList()[0] #Parse string to python list
    print("bmExpr-------------------------------------")
    print(bmExpr)
    checker=translator.ReadQuery(bmExpr)
    #print (checker.check('(define-fun findIdx ((y1 Int)(y2 Int)(k1 Int)) Int (ite (< k1 y1) 0 (ite (> k1 y2) 2 (ite (> k1 y1) (ite (< k1 y2) 1 0) 0))))')) # array_search_2
    #print (checker.check('(define-fun findIdx ((y1 Int)(y2 Int)(y3 Int)(k1 Int)) Int (ite (< k1 y1) 0 (ite (> k1 y3) 3 (ite (> k1 y1) (ite (< k1 y2) 1(ite (> k1 y2) (ite (< k1 y3) 2 2) 2))2))))')) # array_search_3
    #print (checker.check('(define-fun findIdx ((y1 Int)(y2 Int)(y3 Int)(y4 Int)(k1 Int)) Int (ite (< k1 y1) 0 (ite (> k1 y4) 4 (ite (> k1 y1) (ite (< k1 y2) 1(ite (> k1 y2) (ite (< k1 y3) 2(ite (> k1 y3) (ite (< k1 y4) 3 3) 3))3))3))))')) # array_search_4
    #print (checker.check('(define-fun findIdx ((y1 Int)(y2 Int)(y3 Int)(y4 Int)(y5 Int)(y6 Int)(k1 Int)) Int (ite (< k1 y1) 0 (ite (> k1 y6) 6 (ite (> k1 y1) (ite (< k1 y2) 1(ite (> k1 y2) (ite (< k1 y3) 2(ite (> k1 y3) (ite (< k1 y4) 3(ite (> k1 y4) (ite (< k1 y5) 4(ite (> k1 y5) (ite (< k1 y6) 5 5) 5))5))5))5))5))))')) # array_search_6
    #print (checker.check('(define-fun f ((x Int)) Int (mod (* x 3) 10)  )'))
    #raw_input()
    SynFunExpr = []
    StartSym = 'My-Start-Symbol' #virtual starting symbol
    for expr in bmExpr:
        if len(expr)==0:
            continue
        elif expr[0]=='synth-fun':
            SynFunExpr=expr
    FuncDefine = ['define-fun']+SynFunExpr[1:4] #copy function signature
    #ret = generate(FuncDefine, findIdx(bmExpr))
    #print ret
    #print (checker.check(ret))
    #print (checker.check('(define-fun max2 ((x Int) (y Int)) Int (ite (<= x y) y (ite (<= y x) x y)))')) # max2
    #print (checker.check('(define-fun max3 ((x Int) (y Int) (z Int)) Int (ite (and (<= x x)(and (<= y x)(<= z x))) x (ite (and (<= x y)(and (<= y y)(<= z y))) y (ite (and (<= x z)(and (<= y z)(<= z z))) z z))))')) # max3
    ret = generate(FuncDefine, findMax(FuncDefine))
    print ret
    print (checker.check(ret))
    exit()
    BfsQueue = [[StartSym]] #Top-down
    Productions = {StartSym:[]}
    Type = {StartSym:SynFunExpr[3]} # set starting symbol's return type

    print("goto for statement ----------------------")
    for NonTerm in SynFunExpr[4]: #SynFunExpr[4] is the production rules
        NTName = NonTerm[0]
        NTType = NonTerm[1]
        if NTType == Type[StartSym]:
            Productions[StartSym].append(NTName)
        Type[NTName] = NTType;
        #Productions[NTName] = NonTerm[2]
        Productions[NTName] = []
        for NT in NonTerm[2]:
            if type(NT) == tuple:
                Productions[NTName].append(str(NT[1])) # deal with ('Int',0). You can also utilize type information, but you will suffer from these tuples.
            else:
                Productions[NTName].append(NT)
    print("out for statement -----------------------")
    Count = 0
    while(len(BfsQueue)!=0):
        Curr = BfsQueue.pop(0)
        #print("Extending "+str(Curr))
        TryExtend = Extend(Curr,Productions)
        if(len(TryExtend)==0): # Nothing to extend
            FuncDefineStr = translator.toString(FuncDefine,ForceBracket = True) # use Force Bracket = True on function definition. MAGIC CODE. DO NOT MODIFY THE ARGUMENT ForceBracket = True.
            CurrStr = translator.toString(Curr)
            #SynFunResult = FuncDefine+Curr
            #Str = translator.toString(SynFunResult)
            Str = FuncDefineStr[:-1]+' '+ CurrStr+FuncDefineStr[-1] # insert Program just before the last bracket ')'
            print Str
            Count += 1
            # print (Count)
            # print (Str)
            # if Count % 100 == 1:
                # print (Count)
                # print (Str)
                #raw_input()
            #print '1'
            print("check ----------------------------")
            counterexample = checker.check(Str)
            print("check done ----------------------------")
            #print counterexample
            if(counterexample == None): # No counter-example
                Ans = Str
                break
            #print '2'
        #raw_input()
        #BfsQueue+=TryExtend
        print("append BfsQueue -------------------------")
        TE_set = set()
        for TE in TryExtend:
            TE_str = str(TE)
            if not TE_str in TE_set:
                print("append ",TE_str)
                BfsQueue.append(TE)
                TE_set.add(TE_str)
        print("append BfsQueue done. Next Loop-------------------------")

    print(Ans)

	# Examples of counter-examples    
	# print (checker.check('(define-fun max2 ((x Int) (y Int)) Int 0)'))
    # print (checker.check('(define-fun max2 ((x Int) (y Int)) Int x)'))
    # print (checker.check('(define-fun max2 ((x Int) (y Int)) Int (+ x y))'))
    # print (checker.check('(define-fun max2 ((x Int) (y Int)) Int (ite (<= x y) y x))'))
