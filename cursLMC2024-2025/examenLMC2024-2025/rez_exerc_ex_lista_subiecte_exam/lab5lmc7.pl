:- [lab4lmc3]. /* directiva care produce includerea bazei de cunostinte lab4lmc3.pl
din folderul curent (se poate da si calea, daca dorim s-o pastram in alt folder) in 
baza de cunostinte curenta; se pot include mai multe baze de cunostinte, cu numele
de fisiere separate prin virgula */

/* A se vedea in fisierul .pl pentru primul laborator de la seria ID mai multe 
detalii despre urmatoarele predicate, precum si conventia privind notatia pentru
argumentele predicatelor din documentatia Prolog-ului online, folosita in setul 
anterior de teme.
Folosind urmatorul predicat sub forma stergesaunu(+Element,+DinLista,-Lista), 
respectiv sub forma stergesaunu(+Element,-Lista,+LaLista), se realizeaza stergerea 
unui element de pe o pozitie arbitrara dintr-o lista sau pastrarea listei 
neschimbate, respectiv adaugarea unui element pe o pozitie arbitrara intr-o lista sau
pastrarea listei neschimbate: */

stergesaunu(_,[],[]).
stergesaunu(H,[H|T],T).
stergesaunu(X,[H|T],[H|L]) :- stergesaunu(X,T,L).

% Permutarile sublistelor unei liste:

permsublista([],[]).
permsublista([H|T],P) :- permsublista(T,Q), stergesaunu(H,P,Q).

% Multimea permutarilor sublistelor unei liste:

listapermsubliste(L,LP) :- setof(P, permsublista(L,P), LP).

/* Folosind urmatorul predicat sub forma stergesaunu(+Element,+DinLista,-Lista), 
respectiv sub forma stergesaunu(+Element,-Lista,+LaLista), se realizeaza stergerea 
unui element de pe o pozitie arbitrara dintr-o lista sau pastrarea listei 
neschimbate, respectiv adaugarea unui element pe o pozitie arbitrara intr-o lista sau
pastrarea listei neschimbate. Observati avertismentul ca a fost deja definit in 
lab4lmc3.pl, si la fel pentru alte predicate de aici: aceste clauze nu se vor adauga
la cele din baza de cunostinte lab4lmc3.pl, ci se vor inlocui predicatele din 
lab4lmc3.pl cu cele cu acelasi nume din aceasta baza de cunostinte. */

sterge(_,[],[]) :- fail.
sterge(H,[H|T],T).
sterge(X,[H|T],[H|L]) :- sterge(X,T,L).

% Permutarile unei liste:

permutare([],[]).
permutare([H|T],P) :- permutare(T,Q), sterge(H,P,Q).

% Multimea permutarilor unei liste:

listapermutari(L,LP) :- setof(P, permutare(L,P), LP).

% Stergerea primei aparitii a unui element intr-o lista:

stergeprim(_,[],[]) :- fail.
stergeprim(H,[H|T],T) :- !.
stergeprim(X,[H|T],[H|L]) :- stergeprim(X,T,L).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

/* Lantul cu doua elemente, respectiv rombul, date ca poseturi (Multime,Ordine): */

l2([0,1],[(0,0),(0,1),(1,1)]).
rombul([0,a,b,1],[(0,0),(a,a),(b,b),(1,1),(0,a),(a,1),(0,b),(b,1),(0,1)]).

/* functie(Domeniu,Codomeniu,Functie) e satisfacut ddaca Functie este o functie de la
multimea Domeniu la multimea Codomeniu, data ca relatie binara functionala totala: */

functie([],_,[]).
functie([H|T],Codom,[(H,FH)|U]) :- member(FH,Codom), functie(T,Codom,U).

/* morfposet(OrdineDomeniu,OrdineCodomeniu,Functie) e satisfacut ddaca relatia binara
Functie este morfism de poseturi de la un poset (Domeniu,OrdineDomeniu) la un poset
(Codomeniu,OrdineCodomeniu): */

morfposet(Ord1,Ord2,Fct) :- not((member((A,B),Ord1),
	member((A,FA),Fct), member((B,FB),Fct),
	not(member((FA,FB),Ord2)))).

/* multmorfposet(Domeniu,OrdineDomeniu,Codomeniu,OrdineCodomeniu,MultimeFunctii) e 
satisfacut ddaca MultimeFunctii este multimea morfismelor de poseturi de la posetul
(Domeniu,OrdineDomeniu) la posetul (Codomeniu,OrdineCodomeniu), data ca lista de 
relatii binare functionale totale: */

multmorfposet(Mult1,Ord1,Mult2,Ord2,ListaFct) :- 
	setof(Fct, (functie(Mult1,Mult2,Fct),
	morfposet(Ord1,Ord2,Fct)), ListaFct).

% Scrierea elementelor unei liste cu fiecare element pe alt rand:

scrie([]).
scrie([H|T]) :- write(H), nl, scrie(T).

/* Interogati:
?- rombul(Mult1,Ord1), l2(Mult2,Ord2), multmorfposet(Mult1,Ord1,Mult2,Ord2,ListaFct), scrie(ListaFct).
*/

% einj e satisfacut ddaca relatia binara din argumentul sau e injectiva:

einj(Fct) :- not((member((A,FA),Fct), member((B,FA),Fct), A\=B)).

/* esurj(RelatieBinara,Codomeniu) e satisfacut ddaca relatia binara RelatieBinara cu 
codomeniul Codomeniu e surjectiva : */

esurj(_,[]).
esurj(Fct,[H|T]) :- member((_,H),Fct), esurj(Fct,T).

% invrel(RelBin,Inv) e satisfacut ddaca Inv e inversa relatiei binare RelBin:

invrel([],[]).
invrel([(A,B)|Fct],[(B,A)|InvFct]) :- invrel(Fct,InvFct).

/* critmorfposet(Mult1,Ord1,Mult2,Ord2,Fct) e satisfacut ddaca Fct e morfism de
poseturi de la posetul (Mult1,Ord1) la posetul (Mult2,Ord2): */

critmorfposet(Mult1,Ord1,Mult2,Ord2,Fct) :- 
	functie(Mult1,Mult2,Fct),
	morfposet(Ord1,Ord2,Fct).

/* critmorfinjposet(Mult1,Ord1,Mult2,Ord2,Fct) e satisfacut ddaca Fct e morfism
injectiv de poseturi de la posetul (Mult1,Ord1) la posetul (Mult2,Ord2): */

critmorfinjposet(Mult1,Ord1,Mult2,Ord2,Fct) :- 
	functie(Mult1,Mult2,Fct),
	morfposet(Ord1,Ord2,Fct), einj(Fct).

/* critmorfsurjposet(Mult1,Ord1,Mult2,Ord2,Fct) e satisfacut ddaca Fct e morfism
surjectiv de poseturi de la posetul (Mult1,Ord1) la posetul (Mult2,Ord2): */

critmorfsurjposet(Mult1,Ord1,Mult2,Ord2,Fct) :- 
	functie(Mult1,Mult2,Fct),
	morfposet(Ord1,Ord2,Fct), esurj(Fct,Mult2).

/* critmorfbijposet(Mult1,Ord1,Mult2,Ord2,Fct) e satisfacut ddaca Fct e morfism
bijectiv de poseturi de la posetul (Mult1,Ord1) la posetul (Mult2,Ord2): */

critmorfbijposet(Mult1,Ord1,Mult2,Ord2,Fct) :- 
	functie(Mult1,Mult2,Fct),
	morfposet(Ord1,Ord2,Fct), einj(Fct), esurj(Fct,Mult2).

/* critizomposet(Mult1,Ord1,Mult2,Ord2,Fct) e satisfacut ddaca Fct e izomorfism de
poseturi de la posetul (Mult1,Ord1) la posetul (Mult2,Ord2): */

critizomposet(Mult1,Ord1,Mult2,Ord2,Fct) :- 
	functie(Mult1,Mult2,Fct), einj(Fct), esurj(Fct,Mult2),
	morfposet(Ord1,Ord2,Fct), 
	invrel(Fct,InvFct), morfposet(Ord2,Ord1,InvFct).

/* colectfct(Mult1,Ord1,Mult2,Ord2,Criteriu,MultFct) e satisfacut ddaca MultFct e
multimea functiilor Fct de la posetul (Mult1,Ord1) la posetul (Mult2,Ord2) care 
satisfac conditia Criteriu(Mult1,Ord1,Mult2,Ord2,Fct): */

colectfct(Mult1,Ord1,Mult2,Ord2,Criteriu,MultFct) :- 
	findall(Fct, 
	(T=..[Criteriu,Mult1,Ord1,Mult2,Ord2,Fct], T), 
	ListaFct), elimdup(ListaFct,MultFct).

/* Eliminarea duplicatelor dintr-o lista cu pastrarea ultimelor aparitii ale 
elementelor in acea lista: */

elimdup([],[]).
elimdup([H|T],U) :- member(H,T), !, elimdup(T,U).
elimdup([H|T],[H|U]) :- elimdup(T,U).

/* Interogati:
?- rombul(Mult1,Ord1), l2(Mult2,Ord2), colectfct(Mult1,Ord1,Mult2,Ord2,critmorfposet,ListaFct), scrie(ListaFct).
?- rombul(Mult1,Ord1), l2(Mult2,Ord2), colectfct(Mult1,Ord1,Mult2,Ord2,critmorfinjposet,ListaFct), scrie(ListaFct).
?- rombul(Mult1,Ord1), l2(Mult2,Ord2), colectfct(Mult1,Ord1,Mult2,Ord2,critmorfsurjposet,ListaFct), scrie(ListaFct).
*/

/* multizomposet(Mult1,Ord1,Mult2,Ord2,MultFct) e satisfacut ddaca MultFct e multimea
izomorfismelor de poseturi de la posetul (Mult1,Ord1) la posetul (Mult2,Ord2): */

multizomposet(Mult1,Ord1,Mult2,Ord2,MultFct) :- 
	colectfct(Mult1,Ord1,Mult2,Ord2,critizomposet,MultFct).

/* suntizomorfe(Mult1,Ord1,Mult2,Ord2) si auunizomorfism(Mult1,Ord1,Mult2,Ord2) sunt
satisfacute ddaca posetul (Mult1,Ord1) este izomorf cu posetul (Mult2,Ord2): */

suntizomorfe(Mult1,Ord1,Mult2,Ord2) :- multizomposet(Mult1,Ord1,Mult2,Ord2,[_|_]).

auunizomorfism(Mult1,Ord1,Mult2,Ord2) :- critizomposet(Mult1,Ord1,Mult2,Ord2,_), !.

/* Suficient pentru testarea bijectiei intre doua multimi, dar nu si pentru
a fi folosit la testarea izomorfismului intre poseturi: bijectie(L,M,Bij) e 
satisfacut ddaca listele L si M au acelasi numar n de elemente, astfel ca
L=[E1,E2,...,En] si M=[F1,F2,...,Fn], iar Bij=[(E1,F1),(E2,F2),...,(En,Fn)]: */

bijectie([],[],[]).
bijectie([],[_|_],_) :- fail.
bijectie([_|_],[],_) :- fail.
bijectie([H|T],[K|U],[(H,K)|Bij]) :- bijectie(T,U,Bij).

% Generarea tuturor bijectiilor de la o multime M la o multime N:

bijarbitrara(M,N,Bij) :- permutare(N,P), bijectie(M,P,Bij).

% Determinarea multimii bijectiilor de la o multime M la o multime N:

multbij(M,N,MultBij) :- setof(Bij, bijarbitrara(M,N,Bij), MultBij), ! ; MultBij=[].

/* testizomposet(Mult1,Ord1,Mult2,Ord2,Fct) e satisfacut ddaca Fct e izomorfism de
poseturi de la posetul (Mult1,Ord1) la posetul (Mult2,Ord2):  */

testizomposet(Mult1,Ord1,Mult2,Ord2,Fct) :- 
	bijarbitrara(Mult1,Mult2,Fct), morfposet(Ord1,Ord2,Fct), 
	invrel(Fct,InvFct), morfposet(Ord2,Ord1,InvFct).

/* izomorfe(Mult1,Ord1,Mult2,Ord2) e satisfacut ddaca posetul (Mult1,Ord1) este 
izomorf cu posetul (Mult2,Ord2): */

izomorfe(Mult1,Ord1,Mult2,Ord2) :- testizomposet(Mult1,Ord1,Mult2,Ord2,_), !.

/* autodual(Mult,Ord) e satisfacut ddaca posetul (Mult,Ord) este autodual, i.e.
izomorf cu dualul sau: */

autodual(Mult,Ord) :- invrel(Ord,OrdDuala), izomorfe(Mult,Ord,Mult,OrdDuala).

/* multizomposeturi(Mult1,Ord1,Mult2,Ord2,MultFct) e satisfacut ddaca MultFct e 
multimea izomorfismelor de poseturi de la posetul (Mult1,Ord1) la posetul (Mult2,Ord2): */

multizomposeturi(Mult1,Ord1,Mult2,Ord2,MultFct) :- 
	colectfct(Mult1,Ord1,Mult2,Ord2,testizomposet,MultFct).

% elemminimal(M,Mult,Ord) e satisfacut ddaca M e element minimal al posetului (Mult,Ord):

elemminimal(M,Mult,Ord) :- member(M,Mult),
	not((member(X,Mult), member((X,M),Ord), X\=M)).

% elemmaximal(M,Mult,Ord) e satisfacut ddaca M e element maximal al posetului (Mult,Ord):

elemmaximal(M,Mult,Ord) :- member(M,Mult),
	not((member(X,Mult), member((M,X),Ord), X\=M)).

/* elemminimale(Mult,Ord,LM) e satisfacut ddaca LM este lista elementelor minimale 
ale posetului (Mult,Ord): */

elemminimale(Mult,Ord,LM) :- setof(M, elemminimal(M,Mult,Ord), LM).

/* elemmaximale(Mult,Ord,LM) e satisfacut ddaca LM este lista elementelor maximale 
ale posetului (Mult,Ord): */

elemmaximale(Mult,Ord,LM) :- setof(M, elemmaximal(M,Mult,Ord), LM).

% TEMA OBLIGATORIE: de scris elemminimale si elemmaximale recursiv, fara setof.

/* minorant(M,Submult,Ord) e satisfacut ddaca M este minorant al multimii Submult 
intr-un poset (Mult,Ord): */

minorant(_,[],_).
minorant(M,[H|T],Ord) :- member((M,H),Ord), minorant(M,T,Ord).

/* majorant(M,Submult,Ord) e satisfacut ddaca M este majorant al multimii Submult 
intr-un poset (Mult,Ord): */

majorant(_,[],_).
majorant(M,[H|T],Ord) :- member((H,M),Ord), majorant(M,T,Ord).

/* minoranti(Submult,Mult,Ord,LM) e satisfacut ddaca LM e lista minorantilor multimii
Submult in posetul (Mult,Ord): */

minoranti(Submult,Mult,Ord,LM) :- setof(M, 
	(member(M,Mult), minorant(M,Submult,Ord)), LM), ! ; LM=[].

/* majoranti(Submult,Mult,Ord,LM) e satisfacut ddaca LM e lista majorantilor multimii
Submult in posetul (Mult,Ord): */

majoranti(Submult,Mult,Ord,LM) :- setof(M, 
	(member(M,Mult), majorant(M,Submult,Ord)), LM), ! ; LM=[].

/* minorantii(Submult,Mult,Ord,LM) e satisfacut ddaca LM e lista minorantilor 
multimii Submult in posetul (Mult,Ord); observati ca e definit recursiv, fara setof: */

minorantii(_,[],_,[]).
minorantii(Submult,[H|T],Ord,[H|LM]) :- minorant(H,Submult,Ord), !,
					minorantii(Submult,T,Ord,LM).
minorantii(Submult,[_|T],Ord,LM) :- minorantii(Submult,T,Ord,LM).

/* majorantii(Submult,Mult,Ord,LM) e satisfacut ddaca LM e lista majorantilor 
multimii Submult in posetul (Mult,Ord); observati ca e definit recursiv, fara setof: */

majorantii(_,[],_,[]).
majorantii(Submult,[H|T],Ord,[H|LM]) :- majorant(H,Submult,Ord), !,
					majorantii(Submult,T,Ord,LM).
majorantii(Submult,[_|T],Ord,LM) :- majorantii(Submult,T,Ord,LM).

/* minim(Submult,Ord,M) e satisfacut ddaca M este minimul multimii Submult 
intr-un poset (Mult,Ord): */

minim(Submult,Ord,M) :- member(M,Submult), minorant(M,Submult,Ord).

/* maxim(Submult,Ord,M) e satisfacut ddaca M este maximul multimii Submult 
intr-un poset (Mult,Ord): */

maxim(Submult,Ord,M) :- member(M,Submult), majorant(M,Submult,Ord).

/* inf(Submult,Mult,Ord,M) e satisfacut ddaca M este infimumul multimii Submult 
in posetul (Mult,Ord): */

inf(Submult,Mult,Ord,M) :- minorantii(Submult,Mult,Ord,LM), maxim(LM,Ord,M).

/* sup(Submult,Mult,Ord,M) e satisfacut ddaca M este supremumul multimii Submult 
in posetul (Mult,Ord): */

sup(Submult,Mult,Ord,M) :- majorantii(Submult,Mult,Ord,LM), minim(LM,Ord,M).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Produsul cartezian a doua multimi:

prodcart(M,N,P) :- setof((X,Y), (member(X,M), member(Y,N)), P).

/* prodcartnrarb([M1,M2,...,Mn],Prod) e satisfacut ddaca Prod este produsul cartezian
al multimilor M1,M2,...,Mn: */

prodcartnrarb([],[_]).
prodcartnrarb([M],M) :- !.
prodcartnrarb([M|LM],P) :- prodcartnrarb(LM,Q), prodcart(M,Q,P).

% Produsul cartezian a doua relatii binare:

relprod(R,S,RoriS) :- setof(((A,X),(B,Y)), (member((A,B),R), member((X,Y),S)), RoriS).

/* nrabrrelprod([R1,R2,...,Rn],Prod) e satisfacut ddaca Prod este produsul cartezian
al relatiilor binare R1,R2,...,Rn: */

nrabrrelprod([],[(Elem,Elem)]).
nrabrrelprod([R],R) :- !.
nrabrrelprod([R|LR],RelProd) :- nrabrrelprod(LR,P), relprod(R,P,RelProd).

% Produsul direct a doua poseturi:

posetprodus(Mult1,Ord1,Mult2,Ord2,MultProdus,OrdProdus) :- 
	prodcart(Mult1,Mult2,MultProdus), relprod(Ord1,Ord2,OrdProdus).

/* posetprodusnrarb([Mult1,Ord1,Mult2,Ord2,...,Multn,Ordn],ProdMult,OrdProd) e 
satisfacut ddaca (ProdMult,OrdProd) este produsul cartezian al poseturilor 
(Mult1,Ord1), (Mult2,Ord2), ... , (Multn,Ordn): */

posetprodusnrarb([],[Elem],[(Elem,Elem)]).
posetprodusnrarb([Mult,Ord],Mult,Ord) :- !.
posetprodusnrarb([Mult,Ord|Lista],ProdMult,ProdOrd) :- 
	posetprodusnrarb(Lista,M,O), 
	posetprodus(Mult,Ord,M,O,ProdMult,ProdOrd).

% Scrierea unui poset sub forma (MultimeaElementelor,RelatiaDeOrdine):

scrieposet(MultElem,RelOrd) :- write('('), write(MultElem), write(' , '), 
				write(RelOrd), write(')').

% Rombul ca produsul direct al lantului cu doua elemente cu el insusi:

romb(Mult,Ord) :- l2(M,O), posetprodus(M,O,M,O,Mult,Ord).

% Interogati: ?- romb(Mult,Ord), scrieposet(Mult,Ord).

/* Predicat zeroar care testeaza daca rombul memorat cu predicatul binar rombul este
izomorf cu cel calculat cu predicatul binar romb, ca produs direct al lantului cu
doua elemente memorat in baza de cunostinte cu predicatul binar l2: */

testromb :- romb(Mult,Ord), rombul(AltaMult,AltaOrd), 
		izomorfe(Mult,Ord,AltaMult,AltaOrd).

/* Scrierea unei functii f pe o multime {a1,a2,...,an} data ca relatie binara 
functionala totala sub forma: a1->f(a1) | a2->f(a2) | ... | an->f(an) |: */

scriefct([]).
scriefct([(A,FA)|Fct]) :- write(A), write('->'), write(FA), tab(1), 
				write('|'), tab(1), scriefct(Fct).

/* Scrierea unei liste de functii [Fct1,Fct2,...,Fctk] sub forma:
functia 1: Fct1 scrisa ca mai sus
functia 2: Fct2 scrisa ca mai sus
...
functia k: Fctk scrisa ca mai sus: */

auxscrielistafct([],_).
auxscrielistafct([Fct|ListaFct],Nr) :- write('functia '), write(Nr), 
	write(':'), tab(1), scriefct(Fct), nl, 
	N is Nr+1, auxscrielistafct(ListaFct,N).

scrielistafct(ListaFct) :- auxscrielistafct(ListaFct,1).

/* Interogati:
?- rombul(A,O), romb(B,P), multizomposeturi(A,O,B,P,Mult), scrielistafct(Mult).
*/

/* Fiecare dintre predicatele cub(MultElem,RelOrd), cubul(MultElem,RelOrd) si
algBoole8elem(MultElem,RelOrd) e satisfacut ddaca posetul (MultElem,RelOrd) este
algebra Boole cu 8 elemente, anume puterea a treia a lantului cu doua elemente, i.e.
cubul: */

cub(MultElem,RelOrd) :- l2(M,O), romb(Mult,Ord), 
	posetprodus(M,O,Mult,Ord,MultElem,RelOrd).

cubul(MultElem,RelOrd) :- romb(Mult,Ord), l2(M,O), 
	posetprodus(Mult,Ord,M,O,MultElem,RelOrd).

algBoole8elem(MultElem,RelOrd) :- l2(M,O), 
	posetprodusnrarb([M,O,M,O,M,O],MultElem,RelOrd).

/* Interogati:
?- cub(MultElem,RelOrd), scrieposet(MultElem,RelOrd).
?- cubul(MultElem,RelOrd), scrieposet(MultElem,RelOrd).
?- algBoole8elem(MultElem,RelOrd), scrieposet(MultElem,RelOrd).
?- cubul(A,O), cub(B,P), multizomposeturi(A,O,B,P,Mult), scrielistafct(Mult).
?- cubul(A,O), algBoole8elem(B,P), multizomposeturi(A,O,B,P,Mult), scrielistafct(Mult).
?- cub(A,O), algBoole8elem(B,P), multizomposeturi(A,O,B,P,Mult), scrielistafct(Mult).
*/

/* Fiecare dintre predicatele teseract(MultimeElemente,RelatieOrdine) si
teseractul(MultimeElemente,RelatieOrdine) e satisfacut ddaca posetul 
(MultimeElemente,RelatieOrdine) este algebra Boole cu 16 elemente, anume puterea a 
patra a lantului cu doua elemente, adica teseractul, i.e. cubul cvadridimensional: */

teseract(MultimeElemente,RelatieOrdine) :- l2(M,O), cub(MultElem,RelOrd),
	posetprodus(M,O,MultElem,RelOrd,MultimeElemente,RelatieOrdine).

teseractul(MultimeElemente,RelatieOrdine) :- romb(Mult,Ord),
	posetprodus(Mult,Ord,Mult,Ord,MultimeElemente,RelatieOrdine).

/* De curiozitate, putem rula, pentru a vedea cat timp dureaza determinarea
automorfismelor de poset ale teseractului, i.e. a izomorfismelor de poseturi de la
teseract la el insusi: */

testduratadetautomteseract :- teseractul(A,O), teseract(B,P), Initial is cputime,
	multizomposeturi(A,O,B,P,Mult), Final is cputime, scrielistafct(Mult),
	Durata is Final-Initial, nl, 
	write('Timpul pentru determinarea automorfismelor teseractului: '),
	write(Durata), write(' secunde.').

/* Dar, pentru a determina daca teseractul calculat cu predicatul teseract este 
izomorf cu cel calculat cu predicatul teseractul, e suficient sa folosim: */

testteseract :- teseract(Mult,Ord), teseractul(AltaMult,AltaOrd), 
		izomorfe(Mult,Ord,AltaMult,AltaOrd).

/* TEMA OBLIGATORIE: determinarea relatiei de succesiune a unui produs direct de 
poseturi direct din relatiile de succesiune ale celor doua poseturi;
determinarea relatiei de succesiune a unui produs direct de poseturi cu ajutorul 
predicatului relprod de mai sus si a predicatului succesiune din tema obligatorie;
testarea faptului ca relatiile de succesiune determinate in cele doua moduri de mai 
sus sunt una si aceeasi. */

ordinedinsucc(Succ,Mult,Ord) :- inchtranz(Succ,OrdStr), 
				inchrefl(OrdStr,Mult,Ord).

% suma ordinala a rombului cu lantul cu doua elemente, ca poset:

rombplusl2([0,a,b,c,1],Ord) :- 
	ordinedinsucc([(0,a),(a,c),(0,b),(b,c),(c,1)],[0,a,b,c,1],Ord).

% pentagonul ca poset:

pentagon([0,u,v,w,1],Ord) :- 
	ordinedinsucc([(0,u),(u,1),(0,v),(v,w),(w,1)],[0,u,v,w,1],Ord).

/* lista morfismelor de latici marginite de la suma ordinala a 
rombului cu lantul cu doua elemente la pentagon: */

morfcerute(ListaFct) :- rombplusl2(M1,Ord1), pentagon(M2,Ord2), 
	colectfct(M1,Ord1,M2,Ord2,critmorflatmarg,ListaFct).

/* Interogati:
?- morfcerute(ListaFct), scrielistafct(ListaFct). */

/* generarea morfismelor de latici marginite Fct de la laticea Ore (M1,Ord1) la 
laticea Ore (M2,Ord2): */

critmorflatmarg(M1,Ord1,M2,Ord2,Fct) :- critmorflat(M1,Ord1,M2,Ord2,Fct),
	minim(M1,Ord1,Min1), minim(M2,Ord2,Min2),
	maxim(M1,Ord1,Max1), maxim(M2,Ord2,Max2),
	member((Min1,Min2), Fct), member((Max1,Max2), Fct).

/* generarea morfismelor de latici Fct de la laticea Ore (M1,Ord1) la 
laticea Ore (M2,Ord2): */

critmorflat(M1,Ord1,M2,Ord2,Fct) :- functie(M1,M2,Fct),
   not((member(X,M1), member(Y,M1), member((X,FX), Fct), member((Y,FY), Fct),
	inf([X,Y],M1,Ord1,Inf1), sup([X,Y],M1,Ord1,Sup1),
	inf([FX,FY],M2,Ord2,Inf2), sup([FX,FY],M2,Ord2,Sup2),
	(not(member((Inf1,Inf2), Fct)) ; not(member((Sup1,Sup2), Fct))))).

/* A se vedea si exemplul de lista de subiecte de examen si modul in care ar fi 
trebuit rezolvat subiectul de mai sus in cazul in care nu am fi scris aceste 
predicate la laborator. */

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% MATERIAL FACULTATIV:

% Suma directa a doua poseturi:

sumadirecta(Mult1,Ord1,Mult2,Ord2,Mult,Ord) :- 
	posetprodus(Mult1,Ord1,[1],[(1,1)],Mult1Produs,Ord1Produs),
	posetprodus(Mult2,Ord2,[2],[(2,2)],Mult2Produs,Ord2Produs),
	append(Mult1Produs,Mult2Produs,Mult),
	append(Ord1Produs,Ord2Produs,PerechiledinCeleDouaOrdini),
	prodcart(Mult1Produs,Mult2Produs,RestulPerechilor),
	append(PerechiledinCeleDouaOrdini,RestulPerechilor,Ord).

% Diferenta dintre doua multimi:

dif(M,[],M).
dif(M,[H|T],D) :- stergeprim(H,M,N), dif(N,T,D).

/* Obtinerea dintr-un poset (Mult,Ord) a subposetului (MultfaraMax,OrdfaraMax)=
=(Mult\{max(Mult,Ord)},restrictia relatiei de ordine Ord la Mult\{max(Mult,Ord)}, 
i.e. Ord intersectata cu patratul multimii Mult\{max(Mult,Ord)}, anume 
Ord\{(X,max(Mult,Ord)) | X element al multimii Mult}): */

scoatemaxim(Mult,Ord,MultfaraMax,OrdfaraMax) :- 
	maxim(Mult,Ord,Max), stergeprim(Max,Mult,MultfaraMax), 
	prodcart(Mult,[Max],Perechi), dif(Ord,Perechi,OrdfaraMax).

/* Obtinerea dintr-un poset (Mult,Ord) a subposetului (MultfaraMin,OrdfaraMin)=
=(Mult\{min(Mult,Ord)},restrictia relatiei de ordine Ord la Mult\{min(Mult,Ord)}, 
i.e. Ord intersectata cu patratul multimii Mult\{min(Mult,Ord)}, anume 
Ord\{(min(Mult,Ord),X) | X element al multimii Mult}): */

scoateminim(Mult,Ord,MultfaraMin,OrdfaraMin) :- 
	minim(Mult,Ord,Min), stergeprim(Min,Mult,MultfaraMin), 
	prodcart([Min],Mult,Perechi), dif(Ord,Perechi,OrdfaraMin).

% Suma ordinala a doua poseturi:

sumaordinala(Mult1,Ord1,Mult2,Ord2,Mult,Ord) :- 
	scoatemaxim(Mult1,Ord1,M1,O1), scoateminim(Mult2,Ord2,M2,O2),
	posetprodus(M1,O1,[1],[(1,1)],Mult1Produs,Ord1Produs),
	posetprodus(M2,O2,[2],[(2,2)],Mult2Produs,Ord2Produs),
	append(Mult1Produs,[(centru,3)|Mult2Produs],Mult),
	prodcart(Mult1Produs,[(centru,3)],Partea1Ord),
	prodcart([(centru,3)],Mult2Produs,Partea2Ord),
	append(Partea1Ord,[((centru,3),(centru,3))|Partea2Ord],ParteaOrd),
	prodcart(Mult1Produs,Mult2Produs,RestOrd),
	append(Ord1Produs,Ord2Produs,OrdProdus),
	append(ParteaOrd,RestOrd,RestulOrd),
	append(OrdProdus,RestulOrd,Ord).









