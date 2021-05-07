import sofia

def axiom_binary():
    A=sofia.prop()
    A.postulate('[[M][semigroup[M]][x][[x]in[M]][y][[y]in[M]]:[[x]+[y]][[[x]+[y]]in[M]]]')
    return A

def thm_ternary():
    T=sofia.prop()
    l1=T.assume('[M][semigroup[M]][x][[x]in[M]][y][[y]in[M]][z][[z]in[M]]')
    l2=T.recall(axiom_binary())
    l3=T.apply(l2,[[l1,1],[l1,3],[l1,5]])
    l4=T.apply(l2,[[l1,1],[l3,1],[l1,7]])
    T.synapsis()
    return T
