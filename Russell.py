import sofia

def theorem(constant1='in',constant2='False'):
    T=sofia.prop("Russel's Paradox")
    l1=T.assume('[X][[x]:[[[x]'+constant1+'[X]]:[[[x]'+constant1+'[x]]:['+constant2+'[]]]][[[[x]'+constant1+'[x]]:['+constant2+'[]]]:[[x]'+constant1+'[X]]]]')
    l2=T.apply(l1,[l1],2)
    l3=T.assume('[[X]'+constant1+'[X]]')
    l4=T.apply(l2)
    l5=T.apply()
    l6=T.synapsis()
    l7=T.apply(l2,[],2)
    l8=T.apply(l6)
    return T

def theorem(elrel,falseform,contextstat):
    T=sofia.prop("Russel's Paradox")
    c=T._statcontext(contextstat)
    X=T._renamevar('X',c)
    x=T._renamevar('x',c)
    sX=T._lb+X+T._rb
    sx=T._lb+x+T._rb
    shift=len(c)
    l1=T.assume(contextstat+sX+T._lb+sx+T._im+T._lb+T.subin(elrel,[x,X],c)+T._im+T._lb+T.subin(elrel,[x,x],c)+T._im+T._lb+falseform+T._rb+T._rb+T._rb+T._lb+T._lb+T.subin(elrel,[x,x],c)+T._im+T._lb+falseform+T._rb+T._rb+T._im+T.subin(elrel,[x,X],c)+T._rb+T._rb)
    l2=T.apply(l1,[[l1,1+shift]],2+shift)
    l3=T.assume(T.subin(elrel,[X,X],c))
    l4=T.apply(l2)
    l5=T.apply()
    l6=T.synapsis()
    l7=T.apply(l2,[],2)
    l8=T.apply(l6)
    l9=T.synapsis()
    return T

