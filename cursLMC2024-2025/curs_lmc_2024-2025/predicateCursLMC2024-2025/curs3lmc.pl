concat([],L,L).
concat([H|T],L,[H|M]) :- concat(T,L,M).

lung([],0).
lung([_|T],N) :- lung(T,K), N is K+1.

/* 
?- lung([1,2,3],NrElem).
   lung      lung
   /  \      /  \
  []   0   [|]   N
           / \
          H   T
T=[2,3]
N=NrElem
?- lung([2,3],K), NrElem is K+1.
?- lung([3],K1), K is K1+1.
?- lung([],K2), K1 is K2+1.
K2=0, K1 is 0+1 ---> K1=1
K1=1, K is 1+1 ---> K=2
K=2, NrElem is 2+1 ---> NrElem=3.
?- lung(CeLista,3).
CeLista=[H|T], N=3
?- lung(T,K), 3 is K+1.
  lung
  /  \
 T    K
T=[], K=0, 3 is 0+1 ---> 3=1: false
T=[H1|T1], K=1
?- lung(T1,K1), K is K1+1.
T1=[], K1=0, K is 0+1 ---> K=1, 3 is 1+1 ---> 3=3: false
T1=[H2|T2], K1=N2
?- lung(T2,K2), K1 is K2+1.
T2=[], K2=0, K1 is 0+1 ---> K1=1, K is 1+1 ---> K=2, 3 is 2+1 ---> 3=3: true
T2=[], T1=[H2|[]]=[H2], T=[H1|[H2]]=[H1,H2], CeLista=[H|[H1,H2]]=[H,H1,H2]
*/