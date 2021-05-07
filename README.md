# sofia
Python implementation of the SOFiA proof system

This is still work in progress. Currently the software implements all deduction rules of SOFiA, but more flexibility in the deduction rules needs to be added.

SOFiA stands for "Synaptic First-Order Assembler". The small "i" indicates that the default base of the language is a bit less than that of intuitionistic logic. Namely, disjunction and false are not implemented. The founding authors of the SOFiA project are myself (Zurab Janelidze) and Brandon Laing. Further cotributors of the project are Gregor Feierabend and Louise Beyers.

Boolean.py, semigroup.py, sets.py and Russell.py are extensions (work in progress) of the main module sofia.py with axiom/theorem schemes. Look at these as well as theorems.py to see how the software works.

As a starting point, run theorems.py to see how the proofs are displayed.
