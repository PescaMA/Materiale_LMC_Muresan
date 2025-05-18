/* Vom folosi predicatele din baza de cunostinte lab4lmc1.pl, asadar o includem aici,
plasand-o in acelasi folder cu aceasta baza de cunostinte si folosind urmatoarea directiva,
care poate fi modificata pentru includerea unor baze de cunostinte din alte foldere, cu
sintaxa pentru incarcarea bazelor de cunostinte in interpretorul de Prolog desktop: */

:- [lab4lmc1].

/* Testarea functionalitatii unei relatii binare (i.e. a faptului de a fi functie partiala),
cu ajutorul injectivitatii si a inversei: */

fctpart(R) :- invrel(R,S), inj(S).

% Generarea functiilor partiale de la A la B:

relfct(R,A,B) :- relbin(R,A,B), fctpart(R).

functiipart(A,B,M) :- setof(R, relfct(R,A,B), M).

/* Testarea totalitatii unei relatii binare de la A la o multime, cu ajutorul
surjectivitatii si a inversei: */

tot(R,A) :- invrel(R,S), surj(S,A).

% Generarea relatiilor binare totale de la A la B:

reltot(R,A,B) :- relbin(R,A,B), tot(R,A).

relatiitot(A,B,M) :- setof(R, reltot(R,A,B), M).

% Generarea functiilor de la A la B:

functiile(A,B,M) :- setof(R, (relbin(R,A,B), fctpart(R), tot(R,A)), M).

% mai eficient:

fct([],[],_).
fct([(H,FH)|U],[H|T],B) :- member(FH,B), fct(U,T,B).

functii(A,B,M) :- setof(F, fct(F,A,B), M).

% Generarea functiilor bijective de la o multime A la o multime B:

functiibij(A,B,M) :- setof(F, (fct(F,A,B), inj(F), surj(F,B)), M), !.
functiibij(_,_,[]).

% Mai eficient:

prodscalar([],[],[]).
prodscalar([H|T],[K|U],[(H,K)|L]) :- prodscalar(T,U,L).

fctbij(F,A,B) :- permutare(B,P), prodscalar(A,P,F).

functiilebij(A,B,M) :- setof(F, fctbij(F,A,B), M), !.
functiilebij(_,_,[]).

/* Interogati:
?- functii([1,2,3],[a,b,c],M), scrielista(M), length(M,Cate).
?- functii([1,2,3],[a,b],M), scrielista(M), length(M,Cate).
?- functiibij([1,2,3],[a,b,c],M), scrielista(M), length(M,Cate).
?- functiilebij([1,2,3],[a,b,c],M), scrielista(M), length(M,Cate).
?- functiibij([1,2,3],[a,b],M), scrielista(M), length(M,Cate).
?- functiilebij([1,2,3],[a,b],M), scrielista(M), length(M,Cate).
*/

% Multimea primelor N numere naturale nenule:

multimeNrNat(0,[]) :- !.
multimeNrNat(N,[N|L]) :- P is N-1, multimeNrNat(P,L).

/* Pentru a compara timpii de executie ai predicatelor de mai sus, interogati:
?- multimeNrNat(10,A), multimeNrNat(2,B), Init is cputime, functii(A,B,M), Final is cputime, length(M,NrFct), Durata is Final-Init.
?- multimeNrNat(10,A), multimeNrNat(2,B), Init is cputime, functiile(A,B,M), Final is cputime, length(M,NrFct), Durata is Final-Init.
?- multimeNrNat(10,A), multimeNrNat(3,B), Init is cputime, functii(A,B,M), Final is cputime, length(M,NrFct), Durata is Final-Init.
?- multimeNrNat(10,A), multimeNrNat(3,B), Init is cputime, functiile(A,B,M), Final is cputime, length(M,NrFct), Durata is Final-Init.
?- multimeNrNat(7,A), multimeNrNat(7,B), Init is cputime, functiibij(A,B,M), Final is cputime, length(M,NrFct), Durata is Final-Init.
?- multimeNrNat(7,A), multimeNrNat(7,B), Init is cputime, functiilebij(A,B,M), Final is cputime, length(M,NrFct), Durata is Final-Init.
Operatorul aritmetic zeroar predefinit cputime intoarce timpul curent al unitatii centrale,
in secunde. */

/* Determinarea ordinii stricte a unui poset (A,Ord) (cu multimea suport A si relatia de 
ordine Ord - subinteles in cele ce urmeaza): */

ordstrdinord(Ord,A,OrdStr) :- diag(A,D), dif(Ord,D,OrdStr).

% varianta fara multimea A ca argument:

ordstrictadinord([],[]).
ordstrictadinord([(H,H)|T],R) :- ordstrictadinord(T,R), !.
ordstrictadinord([NuBucla|T],[NuBucla|R]) :- ordstrictadinord(T,R).

% Determinarea ordinii Ord asociate unei ordini stricte OrdStr pe o multime A:

orddinordstr(OrdStr,A,Ord) :- inchrefl(OrdStr,A,Ord).

% Determinarea relatiei de succesiune Succ asociate unei ordini Ord:

succdinord(Ord,Succ) :- setof((X,Y), (member((X,Y),Ord), X\=Y, 
	not((member((X,Z),Ord), X\=Z, member((Z,Y),Ord), Z\=Y))), Succ), !.
succdinord(_,[]).

% Determinarea relatiei de succesiune Succ asociate unei ordini stricte OrdStr:

succdinordstr(OrdStr,Succ) :- setof((X,Y), (member((X,Y),OrdStr),
	not((member((X,Z),OrdStr), member((Z,Y),OrdStr)))), Succ), !.
succdinordstr(_,[]).

/* Desigur, relatia de succesiune asociate unei ordini Ord pe o multime A poate fi 
determinata si astfel: */

acopdinord(Ord,A,Succ) :- ordstrdinord(Ord,A,OrdStr), succdinordstr(OrdStr,Succ).

% sau, cu aceleasi argumente ca ale predicatului succdinord (i.e. fara multimea A):

acoperiredinord(Ord,Succ) :- ordstrictadinord(Ord,OrdStr), succdinordstr(OrdStr,Succ).

/* Determinarea ordinii stricte OrdStr asociate unei relatii de succesiune Succ pe o
multime finita: */

ordstrdinsucc(Succ,OrdStr) :- inchtranz(Succ,OrdStr).

% Determinarea ordinii Ord asociate unei relatii de succesiune Succ pe o multime finita A:

orddinsucc(Succ,A,Ord) :- preordgen(Succ,A,Ord).

% Asadar putem defini rombul, diamantul, respectiv pentagonul astfel:

romb([0,a,b,1],Ord) :- orddinsucc([(0,a),(0,b),(a,1),(b,1)],[0,a,b,1],Ord).

m3([0,a,b,c,1],Ord) :- orddinsucc([(0,a),(0,b),(0,c),(a,1),(b,1),(c,1)],[0,a,b,c,1],Ord).

n5([0,x,y,z,1],Ord) :- orddinsucc([(0,x),(0,y),(y,z),(x,1),(z,1)],[0,x,y,z,1],Ord).

/* Daca elementele X1,X2,...,Xn sunt doua cate doua distincte, atunci predicatul 
succlant([X1,X2,...,Xn],Succ) determina relatia de succesiune Succ a lantului cu multimea
suport {X1,X2,...,Xn} avand X1<X2<...<Xn: */

succlant([],[]).
succlant([_],[]).
succlant([H,K|T],[(H,K)|U]) :- succlant([K|T],U).

/* Folosind predicatul de mai sus putem construi astfel lantul cu multimea suport A si
ordinea Ord data de succesiunea elementelor listei A: */

lant(A,Ord) :- succlant(A,Succ), orddinsucc(Succ,A,Ord).

/* Asadar putem construi lantul cu N elemente  ca fiind multimea primelor N numere naturale
nenule inzestrata cu ordinea naturala cu predicatul lantul(+Nr,-MultElem,-Ord) de mai jos: */

lantul(N,A,Ord) :- multimeNrNat(N,M), reverse(M,A), lant(A,Ord).

/* Interogati:
?- lantul(2,A,Ord).
?- lant([0,1],Ord).
?- lantul(4,A,Ord), write(Ord).
?- lant([0,a,b,1],Ord), write(Ord).
*/

% Calculul produsului a doua relatii binare:

prodrelbin(R,S,RxS) :- setof(((A,X),(B,Y)), (member((A,B),R), member((X,Y),S)), RxS), !.
prodrelbin(_,_,[]).

% Calculul produsului (Prod,OrdProd) a doua poseturi (P,OrdP) si (Q,OrdQ):

prodposeturi(P,OrdP,Q,OrdQ,Prod,OrdProd) :- prodcart(P,Q,Prod), 
				prodrelbin(OrdP,OrdQ,OrdProd).

% Asadar rombul, respectiv cubul pot fi obtinute astfel:

rombul(L2la2,OrdRomb) :- lant([0,1],Ord), prodposeturi([0,1],Ord,[0,1],Ord,L2la2,OrdRomb).

cubul(L2la3,OrdCub) :- lant([0,1],Ord), rombul(L2la2,OrdRomb), prodposeturi([0,1],Ord,L2la2,OrdRomb,L2la3,OrdCub).

% Calculul posetului dual (A,OrdD) al unui poset (A,Ord):

dualposet(A,Ord,A,OrdD) :- invrel(Ord,OrdD).

/* In predicatele urmatoare S va fi o submultime a (multimii suport P a) unui poset cu
multimea suport P si relatia de ordine Ord. Predicatele de mai jos care determina elemente
intorc false daca nu exista astfel de elemente, iar predicatele care determina multimi 
intorc lista vida in acest caz. */

% Determinarea minorantilor M (si a listei acestora LM) ai submultimii S in posetul (P,Ord):

minorant(M,S,P,Ord) :- member(M,P), minoreaza(M,S,Ord).

minoreaza(M,S,Ord) :- not((member(X,S), not(member((M,X),Ord)))).

minorantii(S,P,Ord,LM) :- setof(M, minorant(M,S,P,Ord), LM), !.
minorantii(_,_,_,[]).

% varianta pentru predicatul minoreaza:

eminorant(_,[],_).
eminorant(M,[H|T],Ord) :- member((M,H),Ord), eminorant(M,T,Ord).

% varianta pentru predicatul minorantii:

minoranti(_,[],_,[]).
minoranti(S,[H|T],Ord,[H|LM]) :- eminorant(H,S,Ord), !, minoranti(S,T,Ord,LM).
minoranti(S,[_|T],Ord,LM) :- minoranti(S,T,Ord,LM).

% Determinarea majorantilor M (si a listei acestora LM) ai submultimii S in posetul (P,Ord):

majorant(M,S,P,Ord) :- member(M,P), majoreaza(M,S,Ord).

majoreaza(M,S,Ord) :- not((member(X,S), not(member((X,M),Ord)))).

majorantii(S,P,Ord,LM) :- setof(M, majorant(M,S,P,Ord), LM), !.
majorantii(_,_,_,[]).

% varianta pentru predicatul majoreaza:

emajorant(_,[],_).
emajorant(M,[H|T],Ord) :- member((H,M),Ord), emajorant(M,T,Ord).

% varianta pentru predicatul majorantii:

majoranti(_,[],_,[]).
majoranti(S,[H|T],Ord,[H|LM]) :- emajorant(H,S,Ord), !, majoranti(S,T,Ord,LM).
majoranti(S,[_|T],Ord,LM) :- majoranti(S,T,Ord,LM).

/* Determinarea elementelor minimale, respectiv maximale M (si a listelor acestora LM) ale
submultimii S in posetul (P,Ord); desigur, nu are importanta daca in locul acestuia
consideram subposetul sau (S,Ord^(SxS)) cu multimea suport S si ordinea indusa pe multimea
S de ordinea Ord de pe multimea P, rezultatele vor fi aceleasi: */

elemminimal(M,S,Ord) :- member(M,S), not((member(X,S), member((X,M),Ord), M\=X)).

elementeleminimale(S,Ord,LM) :- setof(M, elemminimal(M,S,Ord), LM), !.
elementeleminimale(_,_,[]).

elemmaximal(M,S,Ord) :- member(M,S), not((member(X,S), member((M,X),Ord), M\=X)).

elementelemaximale(S,Ord,LM) :- setof(M, elemmaximal(M,S,Ord), LM), !.
elementelemaximale(_,_,[]).

/* Determinarea minimului, maximului, infimumului, respectiv supremumului lui S in posetul
(P,Ord); desigur, pentru minim si maxim nu are importanta daca in locul acestuia consideram 
subposetul sau (S,Ord^(SxS)), rezultatele vor fi aceleasi: */

minim(M,S,Ord) :- minorant(M,S,S,Ord).

maxim(M,S,Ord) :- majorant(M,S,S,Ord).

inf(M,S,P,Ord) :- minorantii(S,P,Ord,L), maxim(M,L,Ord).

sup(M,S,P,Ord) :- majorantii(S,P,Ord,L), minim(M,L,Ord).

/* Exemplul de poset din curs cu diagrama Hasse in forma de stea cu 3 colturi, unul jos
(minimul posetului) si doua sus (elementele maximale ale acestui poset): */

exdincurs([a,b,c,d],Ord) :- orddinsucc([(a,b),(b,c),(b,d)],[a,b,c,d],Ord).

/* Interogati:
?- exdincurs(P,Ord), minorantii([c,d],P,Ord,LMinor), minoranti([c,d],P,Ord,ListaMinor), majorantii([c,d],P,Ord,LMajor), majoranti([c,d],P,Ord,ListaMajor), elementeleminimale(P,Ord,LMinPoset), elementelemaximale(P,Ord,LMaxPoset).
?- exdincurs(P,Ord), minim(MinPoset,P,Ord).
?- exdincurs(P,Ord), maxim(MaxPoset,P,Ord). 
?- exdincurs(P,Ord), inf(Inf,[c,d],P,Ord).
?- exdincurs(P,Ord), sup(Sup,[c,d],P,Ord).
*/

% Predicatul urmator testeaza daca un poset (P,Ord) este latice:

latice(P,Ord) :- not((member(X,P), member(Y,P), 
		not((inf(_,[X,Y],P,Ord), sup(_,[X,Y],P,Ord))))).

/* Predicat care testeaza daca o functie F de la o multime inzestrata cu ordinea OrdA la o 
multime inzestrata cu ordinea OrdB e crescatoare: */

cresc(F,OrdA,OrdB) :- not((member((X,Y),OrdA), member((X,FX),F), member((Y,FY),F),
				not(member((FX,FY),OrdB)))).

/* Determinarea morfismelor de poseturi (i.e. a functiilor crescatoare) F (si a listei lor 
LF, care nu va fi niciodata vida, pentru ca va contine functiile constante, i.e. cu 
imaginea singleton) de la un poset (A,OrdA) la un poset (B,OrdB): */

fctcresc(F,A,OrdA,B,OrdB) :- fct(F,A,B), cresc(F,OrdA,OrdB).

functiilecresc(A,OrdA,B,OrdB,LF) :- setof(F, fctcresc(F,A,OrdA,B,OrdB), LF).

/* Determinarea izomorfismelor de poseturi F (si a listei lor LF) de la un poset (A,OrdA) 
la un poset (B,OrdB): */

izomposeturi(F,A,OrdA,B,OrdB) :- fct(F,A,B), inj(F), surj(F,B), cresc(F,OrdA,OrdB),
				invrel(F,InvF), cresc(InvF,OrdB,OrdA).

izomorfismeleposeturi(A,OrdA,B,OrdB,LF) :- setof(F, izomposeturi(F,A,OrdA,B,OrdB), LF), !.
izomorfismeleposeturi(_,_,_,_,[]).

% varianta:

izomord(F,A,OrdA,B,OrdB) :- fctbij(F,A,B), cresc(F,OrdA,OrdB),
			invrel(F,InvF), cresc(InvF,OrdB,OrdA).

izomorfismeleord(A,OrdA,B,OrdB,LF) :- setof(F, izomord(F,A,OrdA,B,OrdB), LF), !.
izomorfismeleord(_,_,_,_,[]).

% Predicatul urmator testeaza daca doua poseturi (A,OrdA) si (B,OrdB) sunt izomorfe:

poseturiizomorfe(A,OrdA,B,OrdB) :- izomposeturi(_,A,OrdA,B,OrdB).

% varianta:

poseturiizom(A,OrdA,B,OrdB) :- izomorfismeleposeturi(A,OrdA,B,OrdB,[_|_]).

/* Determinarea morfismelor de latici F (si a listei lor LF, care nu va fi niciodata vida, 
pentru ca va contine functiile constante, i.e. cu imaginea singleton) de la o latice Ore 
(A,OrdA) la o latice Ore (B,OrdB): */

pastrdisjconj(F,A,OrdA,B,OrdB) :- not((member(X,A), member(Y,A), 
		member((X,FX),F), member((Y,FY),F), 
		inf(XsiY,[X,Y],A,OrdA), sup(XsauY,[X,Y],A,OrdA),
		member((XsiY,FXsiY),F), member((XsauY,FXsauY),F),
	not((inf(FXsiY,[FX,FY],B,OrdB), sup(FXsauY,[FX,FY],B,OrdB))))).

morflat(F,A,OrdA,B,OrdB) :- fct(F,A,B), pastrdisjconj(F,A,OrdA,B,OrdB).

morfismelelatici(A,OrdA,B,OrdB,LF) :- setof(F, morflat(F,A,OrdA,B,OrdB), LF).

/* Determinarea morfismelor de latici marginite F (si a listei lor LF) de la o latice Ore
(A,OrdA) la o latice Ore (B,OrdB): */

pastr0si1(F,A,OrdA,B,OrdB) :- minim(ZeroA,A,OrdA), maxim(UnuA,A,OrdA), 
			minim(ZeroB,B,OrdB), maxim(UnuB,B,OrdB),
			member((ZeroA,ZeroB),F), member((UnuA,UnuB),F).

morflatmarg(F,A,OrdA,B,OrdB) :- morflat(F,A,OrdA,B,OrdB), pastr0si1(F,A,OrdA,B,OrdB).

morfismelelatmarg(A,OrdA,B,OrdB,LF) :- setof(F, morflatmarg(F,A,OrdA,B,OrdB), LF), !.
morfismelelatmarg(_,_,_,_,[]).

% Posetul "V rasturnat", de cardinal 3, cu un maxim si doua elemente minimale:

vrasturnat(P,Ord) :- P=[u,v,1], orddinsucc([(u,1),(v,1)],P,Ord).

% Suma ordinala a rombului cu lantul cu 2 elemente:

rombplusL2(L,Ord) :- L=[0,b,x,y,1], orddinsucc([(0,x),(0,y),(x,b),(y,b),(b,1)],L,Ord).

/* Interogati:
?- rombul(L2xL2,OrdL2xL2), lant([0,1],OrdL2), functiilecresc(L2xL2,OrdL2xL2,[0,1],OrdL2,LF), scrielista(LF), length(LF,NrFctCresc).
?- rombul(L2xL2,OrdL2xL2), lant([0,1],OrdL2), morfismelelatici(L2xL2,OrdL2xL2,[0,1],OrdL2,LF), scrielista(LF), length(LF,NrMorfLat).
?- rombul(L2xL2,OrdL2xL2), lant([0,1],OrdL2), morfismelelatmarg(L2xL2,OrdL2xL2,[0,1],OrdL2,LF), scrielista(LF), length(LF,NrMorfLatMarg).
?- rombplusL2(L,OrdL), vrasturnat(P,OrdP), functiilecresc(L,OrdL,P,OrdP,LF), scrielista(LF), length(LF,NrFctCresc).
?- rombplusL2(L,OrdL), vrasturnat(P,OrdP), findall(F, (fctcresc(F,L,OrdL,P,OrdP), inj(F)), LF).
?- rombplusL2(L,OrdL), vrasturnat(P,OrdP), findall(F, (fctcresc(F,L,OrdL,P,OrdP), surj(F,P)), LF).
?- romb(R,OrdR), rombul(L2xL2,OrdL2xL2), poseturiizomorfe(R,OrdR,L2xL2,OrdL2xL2).
?- romb(R,OrdR), rombul(L2xL2,OrdL2xL2), poseturiizom(R,OrdR,L2xL2,OrdL2xL2).
?- m3(M3,OrdM3), n5(N5,OrdN5), poseturiizomorfe(M3,OrdM3,N5,OrdN5).
?- m3(M3,OrdM3), n5(N5,OrdN5), poseturiizom(M3,OrdM3,N5,OrdN5).
?- romb(R,OrdR), rombul(L2xL2,OrdL2xL2), izomorfismeleposeturi(R,OrdR,L2xL2,OrdL2xL2,LF), scrielista(LF), length(LF,NrIzomOrd).
?- romb(R,OrdR), rombul(L2xL2,OrdL2xL2), izomorfismeleord(R,OrdR,L2xL2,OrdL2xL2,LF), scrielista(LF), length(LF,NrIzomOrd).
*/

/* Determinarea sublaticilor S (si a listei lor LS, care nu va fi niciodata vida, pentru ca
intotdeauna va contine laticea vida) ale unei latici Ore (L,OrdL): */

sublatice(S,L,OrdL) :- sublista(S,L), inchdisjconj(S,L,OrdL).

inchdisjconj(S,L,OrdL) :- not((member(X,S), member(Y,S), 
	inf(XsiY,[X,Y],L,OrdL), sup(XsauY,[X,Y],L,OrdL),
	not((inf(XsiY,[X,Y],S,OrdL), sup(XsauY,[X,Y],S,OrdL))))).

sublaticile(L,OrdL,LS) :- setof(S, sublatice(S,L,OrdL), LS).

/* Determinarea sublaticilor marginite S (si a listei lor LS, care nu va fi niciodata vida,
pentru ca intotdeauna va contine laticea {0,1}) ale unei latici Ore marginite (L,OrdL): */

inch0si1(S,L,OrdL) :- minim(Zero,L,OrdL), maxim(Unu,L,OrdL), member(Zero,S), member(Unu,S).

sublaticemarg(S,L,OrdL) :- sublatice(S,L,OrdL), inch0si1(S,L,OrdL).

sublaticilemarg(L,OrdL,LS) :- setof(S, sublaticemarg(S,L,OrdL), LS).

% Suma ordinala a lantului cu 2 elemente cu rombul si cu inca o copie a lantului cu 2 elemente:

l2plusrombplusL2(L,Ord) :- L=[0,a,b,x,y,1], orddinsucc([(0,a),(a,x),(a,y),(x,b),(y,b),(b,1)],L,Ord).

/* Interogati:
?- romb(L,OrdL), sublaticile(L,OrdL,LS), scrielista(LS), length(LS,NrSublatici).
?- romb(L,OrdL), sublaticilemarg(L,OrdL,LS), scrielista(LS), length(LS,NrSublaticiMarg).
?- l2plusrombplusL2(L,OrdL), sublaticile(L,OrdL,LS), scrielista(LS), length(LS,NrSublatici).
?- l2plusrombplusL2(L,OrdL), sublaticilemarg(L,OrdL,LS), scrielista(LS), length(LS,NrSublaticiMarg).
Putem determina sublaticile acestei sume ordinale care nu sunt lanturi astfel:
?- l2plusrombplusL2(L,OrdL), setof(S, (sublatice(S,L,OrdL), not(totala(OrdL,S))), LS), scrielista(LS), length(LS,Nr).
Iar pe cele marginite care nu sunt lanturi astfel:
?- l2plusrombplusL2(L,OrdL), setof(S, (sublaticemarg(S,L,OrdL), not(totala(OrdL,S))), LS), scrielista(LS), length(LS,Nr).
*/

/* Determinarea perechilor de elemente comparabile, respectiv incomparabile intr-un poset 
(P,Ord); fiecare element e comparabil cu el insusi, deci lista perechilor de elemente 
comparabile va fi intotdeauna nevida: */

compar(X,Y,Ord) :- member((X,Y),Ord) ; member((Y,X),Ord).

perelemcompar(X,Y,P,Ord) :- member(X,P), member(Y,P), compar(X,Y,Ord).

perechileelemcompar(P,Ord,ListaPer) :- setof((X,Y), perelemcompar(X,Y,P,Ord), ListaPer).

incompar(X,Y,Ord) :- not(compar(X,Y,Ord)).

perelemincompar(X,Y,P,Ord) :- member(X,P), member(Y,P), incompar(X,Y,Ord).

perechileelemincompar(P,Ord,ListaPer) :- setof((X,Y), perelemincompar(X,Y,P,Ord), ListaPer), !.
perechileelemincompar(_,_,[]).

/* Interogati:
?- l2plusrombplusL2(L,OrdL), perechileelemincompar(L,OrdL,ListaPer).
?- l2plusrombplusL2(L,OrdL), perechileelemcompar(L,OrdL,ListaPer), write(ListaPer), length(ListaPer,NrPer).
*/
