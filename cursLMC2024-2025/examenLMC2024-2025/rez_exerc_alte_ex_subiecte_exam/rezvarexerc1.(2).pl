:- [lab6lmc3].

diamant([0,a,b,c,1],Ord) :- 
	ordinedinsucc([(0,a),(0,b),(0,c),(a,1),(b,1),(c,1)],[0,a,b,c,1],Ord). 

pentagon([0,x,y,z,1],Ord) :- 
	ordinedinsucc([(0,x),(x,1),(0,y),(y,z),(z,1)],[0,x,y,z,1],Ord). 

morfinjposeturi(ListaMorfisme) :- diamant(M1,Ord1), pentagon(M2,Ord2),
	colectfct(M1,Ord1,M2,Ord2,critmorfinjposet,ListaMorfisme), scrielistafct(ListaMorfisme).




