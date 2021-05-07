import sofia

def form_False():
    return 'False'+sofia.prop._lb+sofia.prop._rb
def form_True():
    return 'True'+sofia.prop._lb+sofia.prop._rb
def form_Conj(statements=[]):
    c=''
    for i in range(0,len(statements)):
        c=c+statements[i]
    if c=='':
        c=form_True()
    else:
        c='Conj'+c
    return c
def stat_Conj(statements=[]):
    return sofia.prop._lb+form_Conj(statements)+sofia.prop._rb

def dr_FalseElim(formula):
    A=sofia.prop("False Elimination (Boolean.py)")
    #line=''
    #for i in range(0,len(pars)):
    #    line=line+sofia.prop._lb+pars[i]+sofia.prop._rb
    A.postulate(sofia.prop._lb+sofia.prop._lb+form_False()+sofia.prop._rb+sofia.prop._im+sofia.prop._lb+formula+sofia.prop._rb+sofia.prop._rb)
    return A

def dr_TrueIntro():
    A=sofia.prop("Truth Introduction (Boolean.py)")
    line=''
    #for i in range(0,len(pars)):
    #    line=line+sofia.prop._lb+pars[i]+sofia.prop._rb
    A.postulate(sofia.prop._lb+sofia.prop._lb+sofia.prop._rb+sofia.prop._im+sofia.prop._lb+form_True()+sofia.prop._rb+sofia.prop._rb)
    return A

def dr_ConjElim(form1,form2,contextstat):
    A=sofia.prop("Conjunction Elimination (Boolean.py)")
    stat1=A._lb+form1+A._rb
    stat2=A._lb+form2+A._rb
    A.postulate(sofia.prop._lb+contextstat+sofia.prop._lb+form_Conj([stat1,stat2])+sofia.prop._rb+sofia.prop._im+stat1+stat2+sofia.prop._rb)
    return A

def dr_ConjIntro(form1,form2,contextstat):   
    A=sofia.prop("Conjunction Introduction (Boolean.py)")
    stat1=A._lb+form1+A._rb
    stat2=A._lb+form2+A._rb
    A.postulate(sofia.prop._lb+contextstat+stat1+stat2+sofia.prop._im+sofia.prop._lb+form_Conj([stat1,stat2])+sofia.prop._rb+sofia.prop._rb)
    return A

def thm_ConjAssoc(form1,form2,form3,contextstat=''):
    A=sofia.prop("Associativity of Conjunction")
    stat1=A._lb+form1+A._rb
    stat2=A._lb+form2+A._rb
    stat3=A._lb+form3+A._rb
    ref=[]
    context=A._statcontext(contextstat)
    for i in range(1,len(context)+1):
        ref.append([1,i])
    l1=A.assume(contextstat+stat_Conj([stat_Conj([stat1,stat2]),stat3]))
    l2=A.recall(dr_ConjElim(form_Conj([stat1,stat2]),form3,contextstat))
    l3=A.apply(l2,ref)
    l4=A.recall(dr_ConjElim(form1,form2,contextstat))
    l5=A.apply(l4,ref)
    l6=A.recall(dr_ConjIntro(form2,form3,contextstat))
    l7=A.apply(l6,ref)
    l8=A.recall(dr_ConjIntro(form1,form_Conj([stat2,stat3]),contextstat))
    l9=A.apply(l8,ref)
    A.synapsis()
    return A