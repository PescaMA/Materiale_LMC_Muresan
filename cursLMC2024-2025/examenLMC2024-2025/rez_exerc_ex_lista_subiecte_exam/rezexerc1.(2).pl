:- [lab6lmc3].

rombplusl2([0,a,b,c,1],Ord) :- 
	ordinedinsucc([(0,a),(0,b),(a,c),(b,c),(c,1)],[0,a,b,c,1],Ord). 

pentagon([0,x,y,z,1],Ord) :- 
	ordinedinsucc([(0,x),(x,1),(0,y),(y,z),(z,1)],[0,x,y,z,1],Ord). 

morfL2xL2plusl2laN5(ListaMorfisme) :- rombplusl2(M1,Ord1), pentagon(M2,Ord2),
	morflatmarg(M1,Ord1,M2,Ord2,ListaMorfisme), scrielistafct(ListaMorfisme).




