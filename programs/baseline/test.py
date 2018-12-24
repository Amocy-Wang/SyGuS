import os
import sys
def replacedStr(fplist, aplist, str2replace):
    idx_ap = aplist.index(str2replace)
    for fp in fplist:
        if isinstance(fp,list):
            fplist[fplist.index(fp)] = fp[0]
    print fplist[idx_ap]

replacedStr(['f',['x1','INT'],['x2','INT']],['f','a','b'],'b')
