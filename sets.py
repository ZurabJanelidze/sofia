import sofia

def axiom_restrictedcomprehension(formula,pars,svar):
    A=sofia.prop("Restricted comprehension")
    #line=''
    #for i in range(0,len(pars)):
    #    line=line+'['+pars[i]+'][set'+pars[i]+']'
    #line='['+line+':'+
    #A.postulate('[[[X][set[X]]:[Y][set[Y]][[x][set[x]]:[[[x]in[Y]]:[[x]in[X]]['+formula+']][[[x]in[X]]['+formula+']:[[x]in[Y]]]]]]')
    #return A

def axiom_subsetinclusion():
    A=sofia.prop("Subset inclusion")
    A.postulate('[[X][set[X]][Y][set[Y]]:[[[X]subset[Y]]=[[x][set[x]][[x]in[X]]:[[x]in[Y]]]]]')
    return A

def axiom_setequality():
    B=sofia.prop("Set equality")
    B.postulate('[[X][set[X]][Y][set[Y]]:[[[X]=[Y]]:[[[X]subset[Y]][[Y]subset[X]]]][[[X]subset[Y]][[Y]subset[X]]:[[X]=[Y]]]]')
    return B

def thm_subsetreflexivity():
    C=sofia.prop("Subset reflexivity")
    l1=C.assume('[X][set[X]]')
    l2=C.recall(axiom_subsetinclusion())
    l3=C.apply(l2,[[l1,1],[l1,1]])
    l4=C.assume("[x][set[x]][[x]in[X]]")
    l5=C.restate(l4,3)
    l6=C.synapsis()
    l7=C.restate(l6,1,['x'])
    l8=C.lsub(l3)
    C.synapsis()
    return C

def thm_subsettransitivity():
    A=axiom_subsetinclusion()
    D=sofia.prop("Subset transitivity")
    l1=D.assume('[X][set[X]][Y][set[Y]][Z][set[Z]]')
    l2=D.assume('[[X]subset[Y]][[Y]subset[Z]]')
    l3=D.recall(A)
    l4=D.apply(l3,[[l1,1],[l1,3]])
    l5=D.rsub(l4,l2)
    l6=D.apply(l3,[[l1,3],[l1,5]])
    l7=D.rsub(l6,l2)
    l8=D.assume("[x][set[x]][[x]in[X]]")
    l9=D.apply(l5,[l8,1])
    l10=D.apply(l7,[l8,1])
    l11=D.synapsis()
    l12=D.restate(l11,1,['x'])
    l13=D.apply(l3,[[l1,1],[l1,5]])
    l14=D.lsub(l13,l12)
    l15=D.synapsis()
    D.synapsis()
    return D

