:- [lab5lmc3].

/* Notez suma ordinala cu + si ridicarea la putere cu ^. Sa construim cateva poseturi (P,OrdP), introducand multimea suport P si relatia de succesiune, apoi obtinand din acestea relatia de ordine OrdP cu predicatul orddinsucc: */

% A = L2^2+L2: suma ordinala dintre romb si lantul cu doua elemente:

posetA(A,OrdA) :- A=[0,a,b,c,1],
	orddinsucc([(0,a),(0,b),(a,c),(b,c),(c,1)],A,OrdA).

% B = "V rasturnat":

posetB(B,OrdB) :- B=[u,v,1], orddinsucc([(u,1),(v,1)],B,OrdB).

% L2^2: rombul:

romb(R,OrdR) :- R=[0,a,b,1], orddinsucc([(0,a),(0,b),(a,1),(b,1)],R,OrdR).

% L2: lantul cu doua elemente:

l2([0,1],OrdL2) :- orddinsucc([(0,1)],[0,1],OrdL2).

% L2+L2^2+L2:

latL(L,OrdL) :- L=[0,a,x,y,b,1],
	orddinsucc([(0,a),(a,x),(a,y),(x,b),(y,b),(b,1)],L,OrdL).

/* Predicat care testeaza daca o functie F:A->B pastreaza relatiile binare R<=A^2 si S<=B^2, mai precis daca duce pe R in S, adica are proprietatea ca, pentru orice x,y in A, daca (x,y) in R, atunci (F(x),F(y)) in S: */

pastrrel(F,R,S) :- not((member((X,Y),R), member((X,FX),F), member((Y,FY),F),
			not(member((FX,FY),S)))).

% Functiile crescatoare F:P->Q intre doua poseturi (P,OrdP) si (Q,OrdQ):

fctcresc(F,P,OrdP,Q,OrdQ) :- functie(F,P,Q), pastrrel(F,OrdP,OrdQ).

% Functiile strict crescatoare F:P->Q intre doua poseturi (P,OrdP) si (Q,OrdQ):

fctstrcresc(F,P,OrdP,Q,OrdQ) :- functie(F,P,Q), ordstrdinord(OrdStrP,OrdP),
		ordstrdinord(OrdStrQ,OrdQ), pastrrel(F,OrdStrP,OrdStrQ).

/* Interogati:
?- posetB(B,OrdB), l2(L2,OrdL2), fctcresc(F,B,OrdB,L2,OrdL2).
?- posetB(B,OrdB), l2(L2,OrdL2), fctstrcresc(F,B,OrdB,L2,OrdL2).
?- posetA(A,OrdA), posetB(B,OrdB), fctstrcresc(F,A,OrdA,B,OrdB).
si dati ;/Next pentru a obtine toate solutiile.
*/

% Multimea functiilor crescatoare injective de la posetul A la posetul B:

fctlecrescinjAlaB(LF) :- posetA(A,OrdA), posetB(B,OrdB),
	setof(F, (fctcresc(F,A,OrdA,B,OrdB), injectiv(F)), LF), !.
fctlecrescinjAlaB([]).

% Multimea functiilor crescatoare surjective de la posetul A la posetul B:

fctlecrescsurjAlaB(LF) :- posetA(A,OrdA), posetB(B,OrdB),
	setof(F, (fctcresc(F,A,OrdA,B,OrdB), surjectiv(F,B)), LF), !.
fctlecrescsurjAlaB([]).

/* Interogati:
?- fctlecrescinjAlaB(LF).
?- fctlecrescsurjAlaB(LF).
*/

/* Determinarea minorantilor, respectiv a majorantilor M ai unei submultimi S a unui poset (P,OrdP): */

minoreaza(M,S,Ord) :- not((member(X,S), not(member((M,X),Ord)))).

minorant(M,S,P,OrdP) :- member(M,P), minoreaza(M,S,OrdP).

minorantii(S,P,OrdP,LM) :- setof(M, minorant(M,S,P,OrdP), LM), !.
minorantii(_,_,_,[]).

majoreaza(M,S,Ord) :- not((member(X,S), not(member((X,M),Ord)))).

majorant(M,S,P,OrdP) :- member(M,P), majoreaza(M,S,OrdP).

majorantii(S,P,OrdP,LM) :- setof(M, majorant(M,S,P,OrdP), LM), !.
majorantii(_,_,_,[]).

/* Determinarea minimului, respectiv a maximului M unei multimi S raportat la ordinea Ord; ca si in cazul predicatelor minoreaza si majoreaza, Ord poate fi o  ordine pe S sau pe o multime care include pe S; de fapt, pentru ca aceste predicate sa functioneze, este suficient ca Ord sa fie o lista care include o relatie de ordine pe S: */

min(S,Ord,M) :- minorant(M,S,S,Ord).

max(S,Ord,M) :- majorant(M,S,S,Ord).

/* Determinarea infimumului, respectiv a supremumului M al unei submultimi S a unui poset (P,OrdP): */

inf(S,P,OrdP,M) :- minorantii(S,P,OrdP,LM), max(LM,OrdP,M).

sup(S,P,OrdP,M) :- majorantii(S,P,OrdP,LM), min(LM,OrdP,M).

/* Interogati:
?- posetA(A,OrdA), minorantii([a,b],A,OrdA,Minorantii), majorantii([a,b],A,OrdA,Majorantii).
?- posetA(A,OrdA), inf([a,b],A,OrdA,Inf), sup([a,b],A,OrdA,Sup).
?- posetA(A,OrdA), min([a,b],OrdA,Min).
?- posetA(A,OrdA), max([a,b],OrdA,Max).
?- posetA(A,OrdA), min([0,a,b,c],OrdA,Min), max([0,a,b,c],OrdA,Max).
?- posetA(A,OrdA), min(A,OrdA,Min), max(A,OrdA,Max).
?- posetB(B,OrdB), min(B,OrdB,Min).
?- posetB(B,OrdB), max(B,OrdB,Max).
*/

% Multimea functiilor crescatoare de la L2^2 la L2:

fctlecrescRomblaL2(LF) :- romb(R,OrdR), l2(L2,OrdL2),
		setof(F, fctcresc(F,R,OrdR,L2,OrdL2), LF), !.
fctlecrescRomblaL2([]).

/* Interogati:
?- fctlecrescRomblaL2(LF), afislista(LF), length(LF,NrFct).
*/

/* Sa determinam daca un poset (L,OrdL) este latice (Ore), respectiv latice marginita, respectiv latice marginita complementata: */

latice(L,OrdL) :- not((member(X,L), member(Y,L),
	not((inf([X,Y],L,OrdL,_), sup([X,Y],L,OrdL,_))))).

latmarg(L,OrdL) :- latice(L,OrdL), min(L,OrdL,_), max(L,OrdL,_).

latmargcomplem(L,OrdL) :- latice(L,OrdL), min(L,OrdL,Zero), max(L,OrdL,Unu),
		not((member(X,L), not((member(Y,L), 
		inf([X,Y],L,OrdL,Zero), sup([X,Y],L,OrdL,Unu))))).

/* Interogati:
?- latL(L,OrdL), latice(L,OrdL).
?- latL(L,OrdL), latmarg(L,OrdL).
?- latL(L,OrdL), latmargcomplem(L,OrdL).
?- posetA(A,OrdA), latmarg(A,OrdA).
?- posetA(A,OrdA), latmargcomplem(A,OrdA).
?- posetB(B,OrdB), latice(B,OrdB).
?- romb(R,OrdR), latmargcomplem(R,OrdR).
*/

/* Determinarea sublaticilor, respectiv a sublaticilor marginite S, ale unei latici, respectiv latici marginite date prin laticea sa (Ore) subiacenta (L,OrdL): */

sublat(S,L,OrdL) :- sublista(S,L), not((member(X,S), member(Y,S),
	inf([X,Y],L,OrdL,XsiY), sup([X,Y],L,OrdL,XsauY),
	not((member(XsiY,S), member(XsauY,S))))).

sublatmarg(S,L,OrdL) :- sublat(S,L,OrdL), 
	min(L,OrdL,Zero), max(L,OrdL,Unu), member(Zero,S), member(Unu,S).

% Sublaticile si sublaticile marginite ale lui L2+L2^2+L2:

sublaticileL(LS) :- latL(L,OrdL), setof(S, sublat(S,L,OrdL), LS), !.
sublaticileL([]).

sublaticilemargL(LS) :- latL(L,OrdL), setof(S, sublatmarg(S,L,OrdL), LS), !.
sublaticilemargL([]).

/* Interogati:
?- sublaticileL(LS), afislista(LS), length(LS,NrSublat).
?- sublaticilemargL(LS), afislista(LS), length(LS,NrSublatmarg).
*/
