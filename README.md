# sofia
Python implementation of the SOFiA proof system

This is still work in progress. Currently the software implements all deduction rules of SOFiA, but more flexibility in the deduction rules needs to be added.

SOFiA stands for "Synaptic First-Order Assembler". The small "i" indicates that the default base of the language is a bit less than that of intuitionistic logic. Namely, disjunction and false are not implemented. The founding authors of the SOFiA project are myself (Zurab Janelidze) and Brandon Laing. Further cotributors of the project are Gregor Feierabend and Louise Beyers.

Below are some examples showing how to use the software.

>>>> import sofia
>>>> sofia.help() 
 ================
 SOFiA (ver 2102021)
 ================
 General commands.
  ■ Create new proposition: P=sofia.prop("Prop") will create a proposition named "Prop".
  ■ Postulate: P.p("[X]") will turn a proposition into an axiom stating [X].
  ■ Show: P.show() will print proposition P on the screen.
  ■ Show: P.showh() will print proposition building history for P.
 ================
 Proof building commands. For a given proposition P, the following proof building commands are available.
  ■ Assumption: P.a("[X]") will assume [X].
  ■ Restate: P.r([[1,1],[2,3]],["x"]) will combine the statements from line 1, position 1, and from line 2, position 3, in a single line. It will in addition rename the first free variable in each of these statements to "x".
  ■ Recall: P.c(Prop) will recall a proposition (axiom/theorem) stored as Prop.
  ■ Selfequate: P.e(2,1) will self-equate the statement at line 2, position 1.
  ■ Synapsis: P.s() will step out from an assumption block.
  ■ Apply: P.d(2,[[1,1],[1,2]],3) will apply an implication at line 2, position 3, to variables at line 1, position 1, and line 1, position 2.
  ■ Left substitution: P.ls(1,2,[3,4],5,6) will substitute the left side of equality at line 1, position 5, in line 2, position 6, replacing occurences 3 and 4 of the right side of the equality.
  ■ Right substitution: P.rs(1,2,[],5,6) will substitute the right side of equality at line 1, position 5, in line 2, position 6, replacing all occurences of the left side of the equality.
  ■ Delete: P.x() will delete the last line of the proof.

>>>> T=sofia.prop("Reflexivity of Equality")
>>>> T.a("[X]")
>>>> T.e(1)
>>>> T.s()

Theorem: Reflexivity of Equality.
[[X]:[[X]=[X]]]
Proof.
 ╔[X] /L1: assumption.
 ╚[[X]=[X]] /L2: self-equate from L1(1).
 [[X]:[[X]=[X]]] /L3: synapsis (L1-2).
QED

>>>> M=sofia.prop("A Mistake")
>>>> M.s()

Theorem: A Mistake.
[[]:[]]
Proof.
 [[]:[]] /L1: synapsis (void).
QED
>>>> M.showh()
Synapsis
 - no input for synapsis at L1

>>>> S=sofia.prop("Symmetry of Equality")
>>>> S.a("[X][Y][[X]=[Y]]")
>>>> S.e(1,1)
>>>> S.rs(1,2,[1],3,1)
>>>> S.s()

Theorem: Symmetry of Equality.
[[X][Y][[X]=[Y]]:[[Y]=[X]]]
Proof.
 ╔[X][Y][[X]=[Y]] /L1: assumption.
 ║[[X]=[X]] /L2: self-equate from L1(1).
 ╚[[Y]=[X]] /L3: right substitution, L1(3) in L2(1).
 [[X][Y][[X]=[Y]]:[[Y]=[X]]] /L4: synapsis (L1-3).
QED

>>>> T=sofia.prop("Transitivity of Equality")
>>>> T.a("[X][Y][Z][[X]=[Y]][[Y]=[Z]]")
>>>> T.rs(1,1,[],5,4)
>>>> T.s()

Theorem: Transitivity of Equality.
[[X][Y][Z][[X]=[Y]][[Y]=[Z]]:[[X]=[Z]]]
Proof.
 ╔[X][Y][Z][[X]=[Y]][[Y]=[Z]] /L1: assumption.
 ╚[[X]=[Z]] /L2: right substitution, L1(5) in L1(4).
 [[X][Y][Z][[X]=[Y]][[Y]=[Z]]:[[X]=[Z]]] /L3: synapsis (L1-2).
QED

>>>> S=sofia.prop("Mark can feel)
>>>> S.a("[[Mark[]] is human][[X][[X] is human]:[[X] can feel]]")
>>>> S.a("[Mark[]]")
>>>> S.d(1,[[2,1]],2)
>>>> S.s()
>>>> S.s()

Theorem: Mark can feel.
[[[Mark[]] is human][[X][[X] is human]:[[X] can feel]]:[[Mark[]]:[[Mark[]] can feel]]]
Proof.
 ╔[[Mark[]] is human][[X][[X] is human]:[[X] can feel]] /L1: assumption.
 ║╔[Mark[]] /L2: assumption.
 ║╚[[Mark[]] can feel] /L3: application of L1.2 (with concretization [Mark[]]).
 ╚[[Mark[]]:[[Mark[]] can feel]] /L4: synapsis (L2-3).
 [[[Mark[]] is human][[X][[X] is human]:[[X] can feel]]:[[Mark[]]:[[Mark[]] can feel]]] /L5: synapsis (L1-4).
QED

>>>> S=sofia.prop("Mark can feel 2")
>>>> S.a("[Mark[]][[Mark[]] is human][[X][[X] is human]:[[X] can feel]]")
>>>> S.d(1,[[1,1]],3)
>>>> S.s()

Theorem: Mark can feel 2.
[[Mark[]][[Mark[]] is human][[X][[X] is human]:[[X] can feel]]:[[Mark[]] can feel]]
Proof.
 ╔[Mark[]][[Mark[]] is human][[X][[X] is human]:[[X] can feel]] /L1: assumption.
 ╚[[Mark[]] can feel] /L2: application of L1.3 (with concretization [Mark[]]).
 [[Mark[]][[Mark[]] is human][[X][[X] is human]:[[X] can feel]]:[[Mark[]] can feel]] /L3: synapsis (L1-2).
QED

>>>> A=sofia.prop("Subset Axiom")
>>>> A.p("[[X][[X] is a set][Y][[Y] is a set]:[[[X] sub [Y]]=[[x][[x] is a set]:[[[x] in [X]]:[[x] in [Y]]]]]]")

Axiom: Subset Axiom.
[[X][[X] is a set][Y][[Y] is a set]:[[[X] sub [Y]]=[[x][[x] is a set]:[[[x] in [X]]:[[x] in [Y]]]]]]

>>>> T=sofia.prop("Subset Reflexivity")
>>>> T.a("[X][[X] is a set]")
>>>> T.a("[x][[x] is a set]")
>>>> T.a("[[x] in [X]]")
>>>> T.r([[3,1]])
>>>> T.s()
>>>> T.s()
>>>> T.c(A)
>>>> T.d(7,[[1,1],[1,1]])
>>>> T.ls(8,6)
>>>> T.s()

Theorem: Subset Reflexivity.
[[X][[X] is a set]:[[X] sub [X]]]
Proof.
 ╔[X][[X] is a set] /L1: assumption.
 ║╔[x][[x] is a set] /L2: assumption.
 ║║╔[[x] in [X]] /L3: assumption.
 ║║╚[[x] in [X]] /L4: restatement (see lines 3).
 ║╚[[[x] in [X]]:[[x] in [X]]] /L5: synapsis (L3-4).
 ║[[x][[x] is a set]:[[[x] in [X]]:[[x] in [X]]]] /L6: synapsis (L2-5).
 ║[[X'][[X'] is a set][Y][[Y] is a set]:[[[X'] sub [Y]]=[[x][[x] is a set]:[[[x] in [X']]:[[x] in [Y]]]]]] /L7: recalling Subset Axiom.
 ║[[[X] sub [X]]=[[x][[x] is a set]:[[[x] in [X]]:[[x] in [X]]]]] /L8: application of L7.1 (with concretization [X],[X]).
 ╚[[X] sub [X]] /L9: left substitution, L8(1) in L6(1).
 [[X][[X] is a set]:[[X] sub [X]]] /L10: synapsis (L1-9).
QED

>>>> T=sofia.prop("Russell")
>>>> T.a("[X][[x]:[[[x] in [X]]=[[[x] in [x]]:[False[]]]]]")
>>>> T.d(1,[[1,1]],2)
>>>> T.a("[[X] in [X]]")
>>>> T.rs(2,3)
>>>> T.d(4)
>>>> T.s()
>>>> T.ls(2,6)
>>>> T.d(6)
>>>> T.s()

Theorem: Russell.
[[X][[x]:[[[x] in [X]]=[[[x] in [x]]:[False[]]]]]:[False[]]]
Proof.
 ╔[X][[x]:[[[x] in [X]]=[[[x] in [x]]:[False[]]]]] /L1: assumption.
 ║[[[X] in [X]]=[[[X] in [X]]:[False[]]]] /L2: application of L1.2 (with concretization [X]).
 ║╔[[X] in [X]] /L3: assumption.
 ║║[[[X] in [X]]:[False[]]] /L4: right substitution, L2(1) in L3(1).
 ║╚[False[]] /L5: application of L4.1.
 ║[[[X] in [X]]:[False[]]] /L6: synapsis (L3-5).
 ║[[X] in [X]] /L7: left substitution, L2(1) in L6(1).
 ╚[False[]] /L8: application of L6.1.
 [[X][[x]:[[[x] in [X]]=[[[x] in [x]]:[False[]]]]]:[False[]]] /L9: synapsis (L1-8).
QED

>>>> A=sofia.prop("Addition")
>>>> A.p("[[x][y][[x]num][[y]num]:[[x]+[y]][[[x]+[y]]num]]")

Axiom: Addition.
[[x][y][[x]num][[y]num]:[[x]+[y]][[[x]+[y]]num]]

>>>> B=sofia.prop("Number construction")
>>>> B.p("[0[]][[0[]]num][1[]][[1[]]num]")

Axiom: Number construction.
[0[]][[0[]]num][1[]][[1[]]num]

>>>> C=sofia.prop("Commutativity")
>>>> C.p("[[x][y][[x]num][[y]num]:[[[x]+[y]]=[[y]+[x]]]]")

Axiom: Commutativity.
[[x][y][[x]num][[y]num]:[[[x]+[y]]=[[y]+[x]]]]

>>>> As=sofia.prop("Associativity")
>>>> As.p("[[x][y][z][[x]num][[y]num][[z]num]:[[[[x]+[y]]+[z]]=[[x]+[[y]+[z]]]]]")

Axiom: Associativity.
[[x][y][z][[x]num][[y]num][[z]num]:[[[[x]+[y]]+[z]]=[[x]+[[y]+[z]]]]]

>>>> I=sofia.prop("Identity")
>>>> I.p("[[x][[x]num]:[[[[0[]]+[x]]=[x]]]]")

Axiom: Identity.
[[x][[x]num]:[[[[0[]]+[x]]=[x]]]]

>>>> II=sofia.prop("Right Identity")
>>>> II.a("[x][[x]num]")
>>>> II.c(I)
>>>> II.c(C)
>>>> II.d(2,[[1,1]])
>>>> II.c(B)
>>>> II.d(3,[[1,1],[5,1]])

Theorem: Right Identity.
[]
Proof.
 ╔[x][[x]num] /L1: assumption.
 ║[[x'][[x']num]:[[[[0[]]+[x']]]=[x']]] /L2: recalling Identity.
 ║[[x'][y][[x']num][[y]num]:[[[x']+[y]]=[[y]+[x']]]] /L3: recalling Commutativity.
 ║[[[[0[]]+[x]]]=[x]] /L4: application of L2.1 (with concretization [x]).
 ║[0[]][[0[]]num][1[]][[1[]]num] /L5: recalling Number construction.
 ║[[[x]+[0[]]]=[[0[]]+[x]]] /L6: application of L3.1 (with concretization [x],[0[]]).
QED
>>>> I=sofia.prop("Identity")
>>>> I.p("[[x][[x]num]:[[[0[]]+[x]]=[x]]]")

Axiom: Identity.
[[x][[x]num]:[[[0[]]+[x]]=[x]]]
>>>> II.c(I)
>>>> II.d(7,[[1,1]])
>>>> II.rs(8,6)
>>>> II.s()

Theorem: Right Identity.
[[x][[x]num]:[[[x]+[0[]]]=[x]]]
Proof.
 ╔[x][[x]num] /L1: assumption.
 ║[[x'][[x']num]:[[[[0[]]+[x']]]=[x']]] /L2: recalling Identity.
 ║[[x'][y][[x']num][[y]num]:[[[x']+[y]]=[[y]+[x']]]] /L3: recalling Commutativity.
 ║[[[[0[]]+[x]]]=[x]] /L4: application of L2.1 (with concretization [x]).
 ║[0[]][[0[]]num][1[]][[1[]]num] /L5: recalling Number construction.
 ║[[[x]+[0[]]]=[[0[]]+[x]]] /L6: application of L3.1 (with concretization [x],[0[]]).
 ║[[x'][[x']num]:[[[0[]]+[x']]=[x']]] /L7: recalling Identity.
 ║[[[0[]]+[x]]=[x]] /L8: application of L7.1 (with concretization [x]).
 ╚[[[x]+[0[]]]=[x]] /L9: right substitution, L8(1) in L6(1).
 [[x][[x]num]:[[[x]+[0[]]]=[x]]] /L10: synapsis (L1-9).
QED

>>>> V=sofia.prop("Variable Introduction")
>>>> V.p("[[x]:[y][[y]=[x]]")

Axiom: Variable Introduction.
[]
>>>> V.showh()
Postulated [[x]:[y][[y]=[x]]
 - inval. expr. at L0
>>>> V.p("[[x]:[y][[y]=[x]]]")

Axiom: Variable Introduction.
[[x]:[y][[y]=[x]]]

>>>> E=sofia.prop("Existential Theorem Example")
>>>> E.c(B)
>>>> E.c(II)
>>>> E.c(V)
>>>> E.d(3,[[1,1]])
>>>> E.ls(4,1,[],2,2)
>>>> E.ls(4,2,[],2,1)

Theorem: Existential Theorem Example.
[y'][[x][[x]num]:[[[x]+[y']]=[x]]]
Proof.
 [0[]][[0[]]num][1[]][[1[]]num] /L1: recalling Number construction.
 [[x][[x]num]:[[[x]+[0[]]]=[x]]] /L2: recalling Right Identity.
 [[x]:[y][[y]=[x]]] /L3: recalling Variable Introduction.
 [y'][[y']=[0[]]] /L4: application of L3.1 (with concretization [0[]]).
 [[y']num] /L5: left substitution, L4(2) in L1(2).
 [[x][[x]num]:[[[x]+[y']]=[x]]] /L6: left substitution, L4(2) in L2(1).
QED
>>>> E.r([[5,1],[6,1]])

Theorem: Existential Theorem Example.
[y'][[y']num][[x][[x]num]:[[[x]+[y']]=[x]]]
Proof.
 [0[]][[0[]]num][1[]][[1[]]num] /L1: recalling Number construction.
 [[x][[x]num]:[[[x]+[0[]]]=[x]]] /L2: recalling Right Identity.
 [[x]:[y][[y]=[x]]] /L3: recalling Variable Introduction.
 [y'][[y']=[0[]]] /L4: application of L3.1 (with concretization [0[]]).
 [[y']num] /L5: left substitution, L4(2) in L1(2).
 [[x][[x]num]:[[[x]+[y']]=[x]]] /L6: left substitution, L4(2) in L2(1).
 [[y']num][[x][[x]num]:[[[x]+[y']]=[x]]] /L7: restatement (see lines 5 6).
QED




