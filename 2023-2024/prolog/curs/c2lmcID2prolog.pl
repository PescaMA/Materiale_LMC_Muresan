p(1).
p(2).
% p(X) :- p(Y), p(Z), X is Y+Z.

implica(P,Q) :- not(P) ; Q. % varianta: implica(P,Q) :- \+(P) ; Q.
echiv(P,Q) :- implica(P,Q), implica(Q,P).

/* Demonstratie pentru faptul ca orice multime A satisface (cu ^ reprezentand intersectia):
A^(multimea vida)=(multimea vida), cu variabila Prolog A reprezentand proprietatea:
"x apartine multimii A", pentru un x arbitrar: */

intersvida :- not((member(A,[false,true]), write(A), nl, not(echiv((A,false),false)))).

% Predicat pentru concatenare de liste, echivalent cu acesta predefinit: append(?L1,?L2,?L):

concat([],L,L).
concat([H|T],L,[H|U]) :- concat(T,L,U).

% Predicate pentru inversarea unei liste, echivalente cu acesta predefinit: reverse(?L,?M):

inv([],[]).
inv([H|T],L) :- inv(T,U), append(U,[H],L).

inversa([],[]).
inversa([H|T],L) :- inversa(T,U), concat(U,[H],L).

/* Produsul cartezian (de multimi, cel putin avand rezultatul o multime,
i.e. o lista fara duplicate): */

prodcart(A,B,P) :- setof((X,Y), (member(X,A), member(Y,B)), P), !.
prodcart(_,_,[]).

% varianta:

produscartez(A,B,P) :- setof((X,Y), (member(X,A), member(Y,B)), P).
produscartez(_,[],[]).
produscartez([],[_|_],[]).

% Prefixele unei liste:

prefix([],_).
prefix([H|T],[H|U]) :- prefix(T,U).

/* Sublistele unei liste, cu elementele in ordinea in care apar in acea lista,
dar nu neaparat pe pozitii consecutive in acea lista: */

sublista([],_).
sublista([H|T],[H|U]) :- sublista(T,U).
sublista([H|T],[_|U]) :- sublista([H|T],U).

% Partile unei multimi sau, aplicat unei liste arbitrare, multimea sublistelor unei liste:

parti(M,P) :- setof(S, sublista(S,M), P).

% Scrierea unei liste cu fiecare element pe alta linie:

scrielista([]).
scrielista([H|T]) :- write(H), nl, scrielista(T).

% relbin(-RelBin,+MultA,+MultB) genereaza in RelBin relatiile binare de la MultA la MultB:

relbin(R,A,B) :- prodcart(A,B,P), sublista(R,P).

% Asadar multimea relatiilor binare de la A la B poate fi obtinuta astfel:

relatiibinare(A,B,M) :- setof(R, relbin(R,A,B), M).

% varianta pentru predicatul anterior:

relatiilebinare(A,B,M) :- prodcart(A,B,P), parti(P,M).

% Inversa unei relatii binare:

inversarel(R,S) :- setof((Y,X), member((X,Y),R), S).
inversarel([],[]).

% varianta:

invrel([],[]).
invrel([(X,Y)|T],[(Y,X)|U]) :- invrel(T,U).

/* findall(Termen,Conditie,ListaTermeni) cuantifica existential variabilele din Conditie
care nu apar in Termen, spre deosebire de setof si bagof. Spre exemplu, interogati:
?- setof(X, (member(A,[1,2,10]), member(B,[1,10,100,1000]), X is A+B), M), write(M).
?- bagof(X, (member(A,[1,2,10]), member(B,[1,10,100,1000]), X is A+B), M), write(M).
?- findall(X, (member(A,[1,2,10]), member(B,[1,10,100,1000]), X is A+B), M), write(M).
Cuantificare existentiala explicita pentru aceste variabile:
?- setof(X, (A,B)^(member(A,[1,2,10]), member(B,[1,10,100,1000]), X is A+B), M), write(M).
Observati ca interogarea:
?- bagof(X, (A,B)^(member(A,[1,2,10]), member(B,[1,10,100,1000]), X is A+B), M), write(M).
este echivalenta cu:
?- findall(X, (member(A,[1,2,10]), member(B,[1,10,100,1000]), X is A+B), M), write(M).
*/

% Compunerea a doua relatii binare:

comp(R,S,SoR) :- setof((X,Z), Y^(member((X,Y),R), member((Y,Z),S)),SoR), !.
comp(_,_,[]).

/* Testarea injectivitatii unei relatii binare, suficienta pentru o relatie binara data ca
o lista de perechi de constante (la fel pentru predicatele de mai jos care testeaza 
proprietati ale relatiilor binare: toate se aplica relatiilor binare date de liste de
perechi de constante): */

inj(R) :- not((member((X,U),R), member((Y,U),R), X\=Y)).

% varianta cu literal identitate:

injectivitate(R) :- not((member((X,U),R), member((Y,V),R), U==V, X\==Y)).

% Testarea surjectivitatii unei relatii binare cu codomeniul B, i.e. de la o multime la B:

surj(R,B) :- not((member(U,B), not(member((_,U),R)))).

% Putem memora in baza de cunostinte exemple de relatii binare:

q([(1,a),(2,a)]).
r([(1,a),(1,b)]).
s([(1,a),(2,a),(1,b)]).

/* si sa interogam:
?- q(R), inj(R).
?- r(R), inj(R).
?- s(R), inj(R).
?- s(R), surj(R,[a,b]).
?- s(R), surj(R,[a,b,c]).
?- q(Q), r(R), comp(Q,R,Compunerea).
?- q(Q), r(R), invrel(R,I), comp(Q,I,Compunerea).
?- q(Q), r(R), invrel(R,I), comp(I,Q,Compunerea).
?- q(Q), r(R), invrel(Q,I), comp(I,R,Compunerea).
*/

% Generarea relatiilor binare injective de la A la B:

relinj(R,A,B) :- relbin(R,A,B), inj(R).

relatiiinj(A,B,M) :- setof(R, relinj(R,A,B), M).

% Generarea relatiilor binare surjective de la A la B:

relsurj(R,A,B) :- relbin(R,A,B), surj(R,B).

relatiisurj(A,B,M) :- setof(R, relsurj(R,A,B), M).

% Generarea relatiilor binare injective si surjective de la A la B:

relatiiinjsurj(A,B,M) :- setof(R, (relbin(R,A,B), inj(R), surj(R,B)), M).

/* Interogati:
?- relatiiinjsurj([a,b],[1,2,3],M), scrielista(M).
?- relatiiinjsurj([a,b,c],[1,2],M), scrielista(M).
Observati ca multimile {a,b} si {1,2,3}, respectiv {a,b,c} si {1,2}
nu sunt cardinal echivalente. */

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

% Generarea functiilor bijective de la A la B:

functiibij(A,B,M) :- setof(F, (fct(F,A,B), inj(F), surj(F,B)), M), !.
functiibij(_,_,[]).

/* Interogati:
?- functiibij([1,2,3,4],[a,b,c,d],M), scrielista(M), length(M,Cate).
?- functii([1,2,3,4],[a,b,c,d],M), tell('d:/tempwork/functii.txt'), scrielista(M), told, length(M,Cate).
*/

% Multimea primelor N numere naturale:

multimeNrNat(0,[]) :- !.
multimeNrNat(N,[P|L]) :- P is N-1, multimeNrNat(P,L).

/* Interogati:
?- multimeNrNat(10,A), multimeNrNat(2,B), Init is cputime, functii(A,B,M), Final is cputime, length(M,NrFct), Durata is Final-Init.
?- multimeNrNat(10,A), multimeNrNat(2,B), Init is cputime, functiile(A,B,M), Final is cputime, length(M,NrFct), Durata is Final-Init.
?- multimeNrNat(10,A), multimeNrNat(3,B), Init is cputime, functii(A,B,M), Final is cputime, length(M,NrFct), Durata is Final-Init.
?- multimeNrNat(10,A), multimeNrNat(3,B), Init is cputime, functiile(A,B,M), Final is cputime, length(M,NrFct), Durata is Final-Init.
*/

% Relatia de ordine naturala pe multimea de numere naturale {1,2}:

mmsauegal12([(1,1),(1,2),(2,2)]).

% Diagonala multimii {a,b}:

diagab([(a,a),(b,b)]).

% Produsul cartezian de relatii binare:

prodcartrelbin(R,S,RxS) :- setof(((X,Y),(U,V)), (member((X,U),R), member((Y,V),S)), RxS), !.
prodcartrelbin(_,_,[]).

/* Interogati:
?- mmsauegal12(MME), diagab(Dab), prodcartrelbin(MME,Dab,ProdusulCartezianCaRelatiiBinare).
?- mmsauegal12(MME), diagab(Dab), prodcart(MME,Dab,ProdusulCartezianCaMultimi).
Ignorati faptul ca Prologul nu parantezeaza a doua pereche din fiecare pereche de perechi.
*/

%%% Relatii binare pe o multime:

% Testarea reflexivitatii unei relatii binare R pe o multime A:

refl(R,A) :- not((member(X,A), not(member((X,X),R)))).

% Testarea ireflexivitatii:

irefl(R) :- not(member((X,X),R)).

% Testarea simetriei:

sim(R) :- not((member((X,Y),R), not(member((Y,X),R)))).

% Testarea tranzitivitatii:

tranz(R) :- not((member((X,Y),R), member((Y,Z),R), not(member((X,Z),R)))).

% Testarea antisimetriei:

antisim(R) :- not((member((X,Y),R), member((Y,X),R), X\=Y)).

% Testarea asimetriei:

asim(R) :- not((member((X,Y),R), member((Y,X),R))).

% Generarea relatiilor binare reflexive pe o multime A:

relrefl(R,A) :- relbin(R,A,A), refl(R,A).

relatiirefl(A,MultR) :- setof(R, relrefl(R,A), MultR).

% Generarea relatiilor binare ireflexive pe o multime A:

relirefl(R,A) :- relbin(R,A,A), irefl(R).

relatiiirefl(A,MultR) :- setof(R, relirefl(R,A), MultR).

% Generarea relatiilor binare simetrice pe o multime A:

relsim(R,A) :- relbin(R,A,A), sim(R).

relatiisim(A,MultR) :- setof(R, relsim(R,A), MultR).

% Generarea relatiilor binare tranzitive pe o multime A:

reltranz(R,A) :- relbin(R,A,A), tranz(R).

relatiitranz(A,MultR) :- setof(R, reltranz(R,A), MultR).

% Generarea relatiilor binare antisimetrice pe o multime A:

relantisim(R,A) :- relbin(R,A,A), antisim(R).

relatiiantisim(A,MultR) :- setof(R, relantisim(R,A), MultR).

% Generarea relatiilor binare asimetrice pe o multime A:

relasim(R,A) :- relbin(R,A,A), asim(R).

relatiiasim(A,MultR) :- setof(R, relasim(R,A), MultR).

% Testarea proprietatii de a fi preordine (relatie de preordine):

preord(R,A) :- refl(R,A), tranz(R).

% Testarea proprietatii de a fi echivalenta (relatie de echivalenta):

echivalenta(R,A) :- preord(R,A), sim(R).

% Testarea proprietatii de a fi ordine (relatie de ordine):

ord(R,A) :- preord(R,A), antisim(R).

/* Testarea proprietatii de a fi ordine stricta (relatie de ordine stricta), 
cu fiecare dintre cele doua definitii echivalente: */

ordstr(R) :- irefl(R), tranz(R).

ordinestr(R) :- asim(R), tranz(R).

% Generarea preordinilor (relatiilor de preordine) pe o multime A:

relpreord(R,A) :- relbin(R,A,A), preord(R,A).

relatiipreord(A,OrdA) :- setof(R, relpreord(R,A), OrdA).

% Generarea echivalentelor (relatiilor de echivalenta) pe o multime A:

relechiv(R,A) :- relbin(R,A,A), echivalenta(R,A).

relatiiechiv(A,EqA) :- setof(R, relechiv(R,A), EqA).

% Generarea ordinilor (relatiilor de ordine) pe o multime A:

relord(R,A) :- relbin(R,A,A), ord(R,A).

relatiiord(A,OrdA) :- setof(R, relord(R,A), OrdA).

% Generarea ordinilor stricte (relatiilor de ordine stricta) pe o multime A:

relordstr(R,A) :- relbin(R,A,A), ordstr(R).

relordinestr(R,A) :- relbin(R,A,A), ordinestr(R).

relatiiordstr(A,OrdStrA) :- setof(R, relordstr(R,A), OrdStrA).

relatiiordinestr(A,OrdStrA) :- setof(R, relordinestr(R,A), OrdStrA).

% Stergerea tuturor aparitiilor unui element dintr-o lista:

stergetot(_,[],[]).
stergetot(H,[H|T],M) :- stergetot(H,T,M), !.
stergetot(X,[H|T],[H|M]) :- stergetot(X,T,M).

% Eliminarea duplicatelor dintr-o lista, transformand lista in multime:

% varianta cu pastrarea ultimei aparitii a fiecarui element in lista:

elimdup([],[]).
elimdup([H|T],M) :- member(H,T), !, elimdup(T,M).
elimdup([H|T],[H|M]) :- elimdup(T,M).

% varianta cu pastrarea primei aparitii a fiecarui element in lista:

elimdupl([],[]).
elimdupl([H|T],[H|M]) :- stergetot(H,T,L), elimdupl(L,M).

% Stergerea a exact unei aparitii a unui element, de pe o pozitie arbitrara, dintr-o lista:

sterge(_,[],_) :- fail.
sterge(H,[H|T],T).
sterge(X,[H|T],[H|M]) :- sterge(X,T,M).

/* Interogati:
?- stergetot(a,[a,1,a,2,a],L).
?- stergetot(a,[1,2],L).
?- elimdup([2,a,1,1,a,2,a],M).
?- elimdupl([2,a,1,1,a,2,a],M).
?- sterge(a,[1,2],L).
?- sterge(a,[a,1,a,2,a],L).
si dati ;/Next pentru obtinerea tuturor solutiilor.
Observati ca predicatul sterge poate fi folosit si pentru adaugarea unui element pe o
pozitie arbitrara intr-o lista: interogati, si dati ;/Next pentru a obtine toate solutiile:
?- sterge(a,DinCeLista,[1,2]).
Prin urmare, acest predicat poate fi folosit pentru generarea permutarilor unei liste: */

permutare([],[]).
permutare([H|T],P) :- permutare(T,Q), sterge(H,P,Q).

permutarile(L,LP) :- setof(P, permutare(L,P), LP).

/* Interogati:
?- permutarile([1,2,3],LP).
?- permutarile([a,a,b],LP).
*/

/* Calculul reuniunii a doua multimi (scrise, desigur, ca liste in Prolog); a nu se confunda
cu proprietatea de apartenenta a unui element arbitrar la reuniunea a doua multimi: */

reun(L,M,R) :- append(L,M,C), elimdup(C,R).

% varianta:

reuni(L,M,R) :- append(L,M,C), elimdupl(C,R).

% varianta propusa de un student pentru calculul reuniunii, direct cu definitia ei:

reuniune([],[],[]).
reuniune(L,M,R) :- setof(X, (member(X,L) ; member(X,M)), R).

% Calculul diferentei a doua multimi: dif(A,B,A\B):

dif([],_,[]).
dif([H|T],M,D) :- member(H,M), !, dif(T,M,D).
dif([H|T],M,[H|D]) :- dif(T,M,D).

% varianta:

difer(M,[],M).
difer(M,[H|T],D) :- stergetot(H,M,L), difer(L,T,D).

% varianta similara cu cea propusa de un student pentru reuniune:

diferenta(L,M,D) :- setof(X, (member(X,L), not(member(X,M))), D), !.
diferenta(_,_,[]).

/* Interogati:
?- reun([0,1,3,4,5,7],[0,2,4,6],R).
?- reuni([0,1,3,4,5,7],[0,2,4,6],R).
?- reuniune([0,1,3,4,5,7],[0,2,4,6],R).
Puteti observa ca setof face si o sortare a elementelor.
?- dif([0,1,3,4,5,7],[0,2,4,6],D).
?- difer([0,1,3,4,5,7],[0,2,4,6],D).
?- diferenta([0,1,3,4,5,7],[0,2,4,6],D).
*/

/* Determinarea relatiei de echivalenta asociate unei partitii: recurenta de mai jos 
functioneaza astfel: S e relatia de echivalenta pe multimea A\C avand partitia asociata LC
ddaca R=SU(CxC) e relatia de echivalenta pe multimea A avand partitia asociata [C|LC]: */

part2eq([],[]).
part2eq([C|LC],R) :- part2eq(LC,S), prodcart(C,C,P), reun(S,P,R).

/* Interogati:
?- part2eq([[a,b,c,d]],E), write(E).
?- part2eq([[a,b,c],[d]],E).
?- part2eq([[a,b],[c,d]],E).
?- part2eq([[a,b],[c],[d]],E).
?- part2eq([[a],[b],[c],[d]],E).
*/

% Lista relatiilor de echivalenta asociate partitiilor dintr-o lista de partitii:

parts2eqs([],[]).
parts2eqs([P|LP],[E|LE]) :- part2eq(P,E), parts2eqs(LP,LE).

% Determinarea clasei de echivalenta C=X/R a unui element X raportat la o echivalenta R:

clsechiv(X,R,C) :- setof(Y, member((X,Y),R), C).

/* Determinarea partitiei PartitiaAsociataRelEchivPeA asociate unei relatii de echivalenta
RelEchivPeA pe o multime MultA: eq2part(+MultA, +RelEchivPeA, -PartitiaAsociataRelEchivPeA):
*/

eq2part([],_,[]).
eq2part([H|T],R,[C|LC]) :- clsechiv(H,R,C), dif(T,C,D), eq2part(D,R,LC).

% Lista partitiilor asociate echivalentelor dintr-o lista de echivalente:

eqs2parts(_,[],[]).
eqs2parts(A,[E|LE],[P|LP]) :- eq2part(A,E,P), eqs2parts(A,LE,LP).

/* Pentru a determina relatiile de echivalenta pe o multime {a,b,c,d} (desigur, de cardinal
4, i.e. cu elementele a,b,c,d doua cate doua distincte) si partitiile asociate lor, interogati:
?- relatiiechiv([a,b,c,d],Eqs), eqs2parts([a,b,c,d],Eqs,Parts), scrielista(Eqs), write('-------------'), nl, scrielista(Parts), length(Parts,Nr).
*/

% Determinarea diagonalei unei multimi:

diag([],[]).
diag([H|T],[(H,H)|U]) :- diag(T,U).

% varianta:

diagonala([],[]).
diagonala(A,D) :- setof((X,X), member(X,A), D).

% Calculul inchiderii reflexive a unei relatii binare R pe o multime A:

inchrefl(R,A,Q) :- diag(A,D), reun(D,R,Q).

% Calculul inchiderii simetrice a unei relatii binare R:

inchsim(R,S) :- invrel(R,I), reun(R,I,S).

/* Calculul inchiderii tranzitive a unei relatii binare R pe o multime: pentru fiecare n
natural nenul, la al n-lea pas predicatul auxiliar auxinchtranz(R,Tn,T) va avea ca argumente
relatia binara R, relatia binara Tn egala cu reuniunea primelor n puteri naturale nenule ale
lui R (puteri raportat la compunere: RoRo...oR) si inchiderea tranzitiva T a lui R pe care o
va calcula; recurenta din auxinchtranz se incheie cu T=Tn pentru primul n natural nenul 
pentru care Tn e tranzitiva: */

inchtranz(R,T) :- auxinchtranz(R,R,T).

auxinchtranz(_,T,T) :- tranz(T), !.
auxinchtranz(R,Tn,T) :- comp(R,Tn,C), reun(R,C,Tsn), auxinchtranz(R,Tsn,T).

% Preordinea generata de o relatie binara R pe o multime A:

preordgen(R,A,P) :- inchtranz(R,T), inchrefl(T,A,P).

% Echivalenta generata de o relatie binara R pe o multime A:

echivgen(R,A,E) :- inchsim(R,S), inchrefl(S,A,Q), inchtranz(Q,E).

% Sa memoram in baza de cunostinte:

exderel([(a,b),(b,c)]).
exderelpe(R,[a,b,c]) :- exderel(R).
altexderel([(a,b),(b,c),(c,d)]).
incaunexderel([(a,b),(b,c),(c,d),(d,b)]).
siincaunexderel([(a,b),(b,c),(c,d),(d,a)]).

/* Interogati:
?- exderelpe(R,A), inchrefl(R,A,Inchiderea).
?- exderel(R), inchsim(R,Inchiderea).
?- exderel(R), inchtranz(R,Inchiderea).
?- incaunexderel(R), inchtranz(R,Inchiderea), write(Inchiderea).
?- siincaunexderel(R), inchtranz(R,Inchiderea), write(Inchiderea), length(Inchiderea,CatePer).
?- exderelpe(R,A), preordgen(R,A,Inchiderea).
?- exderelpe(R,A), echivgen(R,A,Inchiderea), write(Inchiderea), length(Inchiderea,CatePer).
?- exderel(R), echivgen(R,[a,b,c,d],Inchiderea), write(Inchiderea), length(Inchiderea,CatePer).
?- echivgen([(a,b),(c,d)],[a,b,c,d],Inchiderea), write(Inchiderea), length(Inchiderea,CatePer).
?- echivgen([(a,b)],[a,b,c,d],Inchiderea), write(Inchiderea), length(Inchiderea,CatePer).
*/

% Ordinea stricta OrdStr asociata unei relatii de succesiune Succ a unui poset finit:

ordstrdinsucc(Succ,OrdStr) :- inchtranz(Succ,OrdStr).

% Ordinea Ord asociata unei relatii de succesiune Succ pe o multime finita A:

orddinsucc(Succ,A,Ord) :- preordgen(Succ,A,Ord).

% Ordinea Ord asociata unei ordini stricte OrdStr pe o multime A:

orddinordstr(OrdStr,A,Ord) :- inchrefl(OrdStr,A,Ord).

% Ordinea stricta OrdStr asociata unei ordini Ord pe o multime A:

ordstrdinord(Ord,A,OrdStr) :- diag(A,D), dif(Ord,D,OrdStr).

% Relatia de succesiune Succ asociata unei ordini Ord:

succdinord(Ord,Succ) :- setof((X,Y), (member((X,Y),Ord), X\=Y,
	not((member((X,Z),Ord), X\=Z, member((Z,Y),Ord), Z\=Y))), Succ), !.
succdinord(_,[]).

% Relatia de succesiune Succ asociata unei ordini stricte OrdStr:

succdinordstr(OrdStr,Succ) :- setof((X,Y), (member((X,Y),OrdStr),
	not((member((X,Z),OrdStr), member((Z,Y),OrdStr)))), Succ), !.
succdinordstr(_,[]).

/* Interogati:
?- mmsauegal12(Ord), succdinord(Ord,Succ).
?- diagab(Ord), succdinord(Ord,Succ).
Acum sa vedem relatiile de ordine pe o multime {a,b,c} de cardinal 3, impreuna cu relatiile
de ordine stricta si relatiile de succesiune asociate lor: */

listaposeturi(A) :- relatiiord(A,OrdA), afisareposeturi(A,OrdA).

afisareposeturi(_,[]).
afisareposeturi(A,[H|T]) :- afisareposet(A,H), nl, write('----------------'), nl,
				afisareposeturi(A,T).

afisareposet(A,Ord) :- write('ordinea: '), write(Ord), nl, ordstrdinord(Ord,A,OrdStr),
		write('ordinea stricta: '), write(OrdStr), nl, succdinordstr(OrdStr,Succ),
		write('relatia de succesiune: '), write(Succ).

/* Interogati:
?- listaposeturi([a,b,c]).
*/

/* Generarea functiilor crescatoare F de la posetul (P,OrdP) la posetul (Q,OrdQ), ca mai
sus: ca relatii binare de la P la Q, i.e. date prin graficele lor: */

fctcresc(F,P,OrdP,Q,OrdQ) :- fct(F,P,Q), cresc(F,OrdP,OrdQ).

cresc(F,OrdP,OrdQ) :- not((member((X,Y),OrdP), member((X,FX),F), member((Y,FY),F),
			not(member((FX,FY),OrdQ)))).

% Lista LF a functiilor crescatoare de la posetul (P,OrdP) la posetul (Q,OrdQ):

functiicresc(P,OrdP,Q,OrdQ,LF) :- setof(F, fctcresc(F,P,OrdP,Q,OrdQ), LF).

/* Interogati:
?- mmsauegal12(MME), diagab(Dab), functiicresc([1,2],MME,[a,b],Dab,LF), scrielista(LF), length(LF,NrFctCresc).
?- mmsauegal12(MME), diagab(Dab), functiicresc([a,b],Dab,[1,2],MME,LF), scrielista(LF), length(LF,NrFctCresc).
?- orddinsucc([(a,b),(b,c),(b,d)],[a,b,c,d],OrdP), orddinsucc([(1,2),(2,3),(3,4)],[1,2,3,4],OrdQ), functiicresc([a,b,c,d],OrdP,[1,2,3,4],OrdQ,LF), scrielista(LF), length(LF,NrFctCresc).
?- orddinsucc([(a,b),(b,c),(b,d)],[a,b,c,d],OrdP), orddinsucc([(1,2),(2,3),(3,4)],[1,2,3,4],OrdQ), functiicresc([1,2,3,4],OrdQ,[a,b,c,d],OrdP,LF), scrielista(LF), length(LF,NrFctCresc).
Observati ca, in primele doua interogari de mai sus:
-> posetul de suport (i.e. multime suport, i.e. multime de elemente) {1,2} este total (i.e.
liniar) ordonat, deci este lant de lungime 2, i.e. lant cu (exact) doua elemente;
-> posetul de suport {a,b} este antilant, adica are elementele incomparabile (doua cate 
doua, daca ar avea cel putin 3).
Observati ca, in ultimele doua interogari de mai sus:
-> posetul de suport {1,2,3,4} este lant (de lungime 4);
-> posetul de suport {a,b,c,d} are minimul a si elementele maximale c,d, iar b comparabil
cu a,c,d; il vedeti reprezentat in curs: are diagrama Hasse in forma de stea cu 3 colturi,
unul jos si doua sus, cu centrul stelei etichetat cu b, coltul de jos etichetat cu a si 
colturile de sus etichetate cu c, d. */



