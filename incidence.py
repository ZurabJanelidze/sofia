import sofia
sofia.help()
BL=sofia.bool()

#Axioms

I1A=sofia.prop("I1 - point may only lie on a line or a plane")
I1A.p("[[p][q][[p]point][[p]in[q]][[[q]line]:[![]]][[[q]plane]:[![]]]:[![]]]")

I1B=sofia.prop("I1 - line may only lie on a plane")
I1B.p("[[l][p][[l]line][[l]in[p]]:[[p]plane]]")

I1C=sofia.prop("I1 - transitivity of incidence")
I1C.p("[[p][q][r][[p]point][[p]in[q]][[q]in[r]]:[[p]in[r]]]")

I2A=sofia.prop("I2 - existence of four non coplanar points")
I2A.p("[a][b][c][d][[a]point][[b]point][[c]point][[d]point][[[a]=[b]]:[![]]][[[a]=[c]]:[![]]][[[a]=[d]]:[![]]][[[b]=[c]]:[![]]][[[b]=[d]]:[![]]][[[c]=[d]]:[![]]][[p][[p]plane][[a]in[p]][[b]in[p]][[c]in[p]][[d]in[p]]:[![]]]")

I2B=sofia.prop("I2 - existence of a plane")
I2B.p("[p][[p]plane]")

I2C=sofia.prop("I2 - plane has three noncolinear points")
I2C.p("[[p][[p]plane]:[a][b][c][[[a]=[b]]:[![]]][[[a]=[c]]:[![]]][[[b]=[c]]:[![]]][[a]point][[b]point][[c]point][[a]in[p]][[b]in[p]][[c]in[p]][[l][[l]line][[a]in[l]][[b]in[l]][[c]in[l]]:[![]]]]")

I2D=sofia.prop("I2 - every line has at least two points")
I2D.p("[[l][[l]line]:[a][b][[a]point][[b]point][[[a]=[b]]:[![]]][[a]in[l]][[b]in[l]]]")

I3A=sofia.prop("I3 - unique line from two points")
I3A.p("[[a][b][[a]point][[b]point][[[a]=[b]]:[![]]]:[l][[l]line][[a]in[l]][[b]in[l]][[r][[r]line][[a]in[r]][[b]in[r]]:[[l]=[r]]]]")

I3B=sofia.prop("I3 - unique plane from three noncolinear points")
I3B.p("[[a][b][c][[a]point][[b]point][[c]point][[[a]=[b]]:[![]]][[[a]=[c]]:[![]]][[[b]=[c]]:[![]]][[l][[l]line][[a]in[l]][[b]in[l]][[c]in[l]]:[![]]]:[p][[p]plane][[a]in[p]][[b]in[p]][[c]in[p]][[q][[q]plane][[a]in[q]][[b]in[q]][[c]in[q]]:[[p]=[q]]]]")

I4=sofia.prop("I4 - line forced on a plane")
I4.p("[[l][a][b][p][[l]line][[[a]=[b]]:[![]]][[p]plane][[a]in[p]][[b]in[p]][[a]in[l]][[b]in[l]]:[[l]in[p]]]")

I5=sofia.prop("I5 - planes intesect in at least two points")
I5.p("[[p][q][[p]plane][[q]plane][a][[a]in[p]][[a]in[q]]:[b][[b]point][[[a]=[b]]:![]][[b]in[p]][[b]in[q]]]")

#Example Theorems

sofia.showing=False

T1=sofia.prop("On any given plane, there is a point outside any given line")
T1.a("[l][p][[l]line][[p]plane]")
T1.c(I2C)
T1.d(2,[[1,2]])
T1.a("[[d][[d]point][[d]in[p]]:[[d]in[l]]]")
T1.d(4,[[3,1]])
T1.d(4,[[3,2]])
T1.d(4,[[3,3]])
T1.d(3,[[1,1]],13)
T1.s()
T1.a("[[d][[d]point][[d]in[p]][[[d]in[l]]:[![]]]:[![]]]")
T1.a("[d'][[d']point][[d']in[p]]")
T1.a("[[[d']in[l]]:[![]]]")
T1.d(10,[[11,1]])
T1.s()
T1.c(BL.n("[[d']in[l]]","[d'][l]"))
T1.d(15,[[11,1],[1,1]])
T1.s()
T1.r([[17,1]],["d"])
T1.d(9)
T1.s()
T1.c(BL.n("[d][[d]point][[d]in[p]][[[d]in[l]]:[![]]]","[l][p]"))
T1.d(21,[[1,1],[1,2]])
T1.s()
T1.r([[23,1]],["l","p","a"])
T1.show()

T2=sofia.prop("For any line there is a point not lying on it")
T2.a("[l][[l]line]")
T2.c(I2B)
T2.c(T1)
T2.d(3,[[1,1],[2,1]])
T2.r([[4,1],[4,2],[4,4]])
T2.s()
T2.r([[6,1]],["l","a"])
T2.show()

#Derive Your Own Theorems from the Axioms


