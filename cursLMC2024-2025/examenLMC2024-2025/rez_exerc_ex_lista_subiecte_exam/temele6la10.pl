:- [lab4lmc3].

ordinedinsucc(Succ,Mult,Ord) :- inchtranz(Succ,OrdStr), 
				inchrefl(OrdStr,Mult,Ord).
