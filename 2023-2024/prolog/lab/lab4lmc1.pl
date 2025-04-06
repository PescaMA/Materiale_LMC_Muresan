% Scrierea unei liste cu fiecare element pe alt rand:

scrielista([]).
scrielista([H|T]) :- write(H), nl, scrielista(T).

/* Produsul cartezian a doua multimi; amintesc ca setof intoarce false si nu lista vida []
daca nu exista termeni care sa satisfaca scopul (conditia), asadar acel caz poate fi tratat
astfel: */

prodcart(L,M,P) :- setof((X,Y), (member(X,L), member(Y,M)), P), !.
prodcart(_,_,[]).

/* Sublistele unei liste cu elementele in ordinea in care se gasesc in acea lista,
dar nu neaparat pe pozitii consecutive in lista respectiva: */

sublista([],_).
sublista([H|T],[H|L]) :- sublista(T,L).
sublista([H|T],[_|L]) :- sublista([H|T],L).

/* Aplicat unei multimi, adica unei liste fara duplicate, predicatul sublista determina
submultimile acelei multimi, astfel ca putem obtine multimea partilor unei multimi astfel: */

parti(M,P) :- setof(S, sublista(S,M), P).

/* Daca scoatem ultima clauza din definitia predicatului sublista (aceea care permite
saltul peste capul listei), atunci obtinem prefixele unei liste: */

prefix([],_).
prefix([H|T],[H|L]) :- prefix(T,L).

prefixe(L,Prefixe) :- setof(P, prefix(P,L), Prefixe).

/* Interogati:
?- parti([1,2,3],P), scrielista(P), length(P,NrSubmultimi).
?- prefixe([1,2,3],P), scrielista(P), length(P,NrPrefixe).
*/

% Predicat care determina relatiile binare R de la multimea A la multimea B:

relbin(R,A,B) :- prodcart(A,B,P), sublista(R,P).

% Avem doua variante pentru determinarea multimii relatiilor binare de la A la B:

relatiilebinare(A,B,MultRel) :- prodcart(A,B,P), parti(P,MultRel).

relatiibinare(A,B,MultRel) :- setof(R, relbin(R,A,B), MultRel).

/* Interogati:
?- relatiilebinare([1,2],[a,b],MultRel), scrielista(MultRel), length(MultRel,NrRelBin).
?- relatiibinare([1,2],[a,b],MultRel), scrielista(MultRel), length(MultRel,NrRelBin).
*/

% Doua modalitati de a determina inversa unei relatii binare:

inversarelbin([],[]).
inversarelbin(R,I) :- setof((Y,X), member((X,Y),R), I).

invrel([],[]).
invrel([(X,Y)|T],[(Y,X)|U]) :- invrel(T,U).

% Compunerea unei relatii binare S cu o relatie binara R:

comp(R,S,SoR) :- setof((X,Z), Y^(member((X,Y),R), member((Y,Z),S)), SoR), !.
comp(_,_,[]).

% Putem memora in baza de cunostinte cateva relatii binare:

r([(1,2),(1,3)]).
s([(2,4),(3,4),(3,5)]).

/* Interogati:
?- r(R), inversarelbin(R,I).
?- s(R), inversarelbin(R,I).
?- r(R), invrel(R,I).
?- s(R), invrel(R,I).
?- r(R), s(S), comp(R,S,SoR).
?- r(R), s(S), comp(S,R,RoS).
*/

% Injectivitatea unei relatii binare:

inj(R) :- not((member((X,U),R), member((Y,U),R), X\=Y)).

/* Daca X si Y sunt constante, de exemplu daca R e o lista de perechi de constante, ca mai
sus, atunci ele unifica ddaca sunt egale, respectiv nonunificarea lor X\=Y semnifica faptul
ça sunt diferite. Atentie: faptul ca R are un membru de forma (X,U) si unul de forma (Y,U)
semnifica doar ca al doilea element al primei perechi unifica cu al doilea element al celei
de-a doua perechi. In functie de necesitatile de utilizare, se poate folosi, de exemplu,
literal identitatea in locul unificarii in acest predicat si in urmatoarele.
Predicat care determina in primul sau argument relatiile binare injective de la A la B: */

relinj(R,A,B) :- relbin(R,A,B), inj(R).

% Surjectivitatea unei relatii binare cu codomeniul B:

surj(R,B) :- not((member(U,B), not(member((_,U),R)))).

% Predicat care determina in primul sau argument relatiile binare surjective de la A la B:

relsurj(R,A,B) :- relbin(R,A,B), surj(R,B).

/* Multimile relatiilor binare injective, respectiv surjective, respectiv injective si
surjective de la A la B: */

relatiibinareinj(A,B,MultRelInj) :- setof(R, relinj(R,A,B), MultRelInj).

relatiibinaresurj(A,B,MultRelSurj) :- setof(R, relsurj(R,A,B), MultRelSurj).

relatiibinareinjsurj(A,B,InjSurj) :- setof(R, (relbin(R,A,B), inj(R), surj(R,B)), InjSurj).

/* Interogati:
?- relatiibinareinj([1,2,3],[a,b],RelInj), scrielista(RelInj), length(RelInj,NrRelInj).
?- relatiibinaresurj([1,2,3],[a,b],RelSurj), scrielista(RelSurj), length(RelSurj,NrRelSurj).
?- relatiibinareinjsurj([1,2,3],[a,b],InjSurj), scrielista(InjSurj), length(InjSurj,NrRel).
?- relatiibinareinjsurj([a,b],[1,2,3],InjSurj), scrielista(InjSurj), length(InjSurj,NrRel).
si observati ca multimile {1,2,3} si {a,b} au cardinale diferite. */

% Testarea reflexivitatii unei relatii binare R pe A:

refl(R,A) :- not((member(X,A), not(member((X,X),R)))).

% Determinarea relatiilor binare reflexive pe A:

relrefl(R,A) :- relbin(R,A,A), refl(R,A).

relatiibinarerefl(A,MultRelRefl) :- setof(R, relrefl(R,A), MultRelRefl).

% Testarea ireflexivitatii unei relatii binare R pe A:

irefl(R) :- not(member((X,X),R)).

% Determinarea relatiilor binare ireflexive pe A:

relirefl(R,A) :- relbin(R,A,A), irefl(R).

relatiibinareirefl(A,MultRelIrefl) :- setof(R, relirefl(R,A), MultRelIrefl).

% Testarea simetriei unei relatii binare R:

sim(R) :- not((member((X,Y),R), not(member((Y,X),R)))).

% Determinarea relatiilor binare simetrice pe A:

relsim(R,A) :- relbin(R,A,A), sim(R).

relatiibinaresim(A,MultRelSim) :- setof(R, relsim(R,A), MultRelSim).

% Testarea antisimetriei unei relatii binare R:

antisim(R) :- not((member((X,Y),R), member((Y,X),R), X\=Y)).

% Determinarea relatiilor binare antisimetrice pe A:

relantisim(R,A) :- relbin(R,A,A), antisim(R).

relatiibinareantisim(A,MultRelAntisim) :- setof(R, relantisim(R,A), MultRelAntisim).

% Testarea asimetriei unei relatii binare R:

asim(R) :- not((member((X,Y),R), member((Y,X),R))).

% Determinarea relatiilor binare asimetrice pe A:

relasim(R,A) :- relbin(R,A,A), asim(R).

relatiibinareasim(A,MultRelAsim) :- setof(R, relasim(R,A), MultRelAsim).

% Testarea tranzitivitatii unei relatii binare R:

tranz(R) :- not((member((X,Y),R), member((Y,Z),R), not(member((X,Z),R)))).

% Determinarea relatiilor binare tranzitive pe A:

reltranz(R,A) :- relbin(R,A,A), tranz(R).

relatiibinaretranz(A,MultRelTranz) :- setof(R, reltranz(R,A), MultRelTranz).

% Testarea totalitatii unei relatii binare R pe o multime A:

totala(R,A) :- not((member(X,A), member(Y,A), X\=Y,
	not(member((X,Y),R)), not(member((Y,X),R)))).

% Determinarea relatiilor binare totale pe A:

reltotala(R,A) :- relbin(R,A,A), totala(R,A).

relatiibinaretotale(A,MultRelTotale) :- setof(R, reltotala(R,A), MultRelTotale).

% Testarea proprietatii de a fi preordine pe o multime A:

preord(R,A) :- refl(R,A), tranz(R).

% Determinarea preordinilor pe A:

relpreord(R,A) :- relbin(R,A,A), preord(R,A).

relatiipreord(A,PreA) :- setof(R, relpreord(R,A), PreA).

% Testarea proprietatii de a fi echivalenta pe o multime A:

echiv(R,A) :- preord(R,A), sim(R).

% Determinarea echivalentelor pe A:

relechiv(R,A) :- relbin(R,A,A), echiv(R,A).

relatiiechiv(A,EqA) :- setof(R, relechiv(R,A), EqA).

% Testarea proprietatii de a fi ordine pe o multime A:

ord(R,A) :- preord(R,A), antisim(R).

% Determinarea ordinilor pe A:

relord(R,A) :- relbin(R,A,A), ord(R,A).

relatiiord(A,OrdA) :- setof(R, relord(R,A), OrdA).

% Testarea proprietatii de a fi ordine totala, i.e. liniara, pe o multime A:

ordlin(R,A) :- ord(R,A), totala(R,A).

% Determinarea ordinilor totale, i.e. liniare, pe A:

relordlin(R,A) :- relbin(R,A,A), ordlin(R,A).

relatiiordlin(A,OrdLinA) :- setof(R, relordlin(R,A), OrdLinA).

/* Testarea proprietatii de a fi ordine stricta (relatie de ordine stricta), 
cu fiecare dintre cele doua definitii echivalente: */

ordstr(R) :- irefl(R), tranz(R).

ordinestr(R) :- asim(R), tranz(R).

% Generarea ordinilor stricte (relatiilor de ordine stricta) pe o multime A:

relordstr(R,A) :- relbin(R,A,A), ordstr(R).

relordinestr(R,A) :- relbin(R,A,A), ordinestr(R).

relatiiordstr(A,OrdStrA) :- setof(R, relordstr(R,A), OrdStrA).

relatiiordinestr(A,OrdStrA) :- setof(R, relordinestr(R,A), OrdStrA).

/* Interogati:
?- relatiibinarerefl([a,b,c],MultRel), scrielista(MultRel), length(MultRel,NrRel).
?- relatiibinareirefl([a,b,c],MultRel), scrielista(MultRel), length(MultRel,NrRel).
?- relatiibinaresim([a,b,c],MultRel), scrielista(MultRel), length(MultRel,NrRel).
?- relatiibinareantisim([a,b,c],MultRel), scrielista(MultRel), length(MultRel,NrRel).
?- relatiibinareasim([a,b,c],MultRel), scrielista(MultRel), length(MultRel,NrRel).
?- relatiibinaretranz([a,b,c],MultRel), scrielista(MultRel), length(MultRel,NrRel).
?- relatiipreord([a,b,c],MultRel), scrielista(MultRel), length(MultRel,NrRel).
?- relatiiechiv([a,b,c],MultRel), scrielista(MultRel), length(MultRel,NrRel).
?- relatiiord([a,b,c],MultRel), scrielista(MultRel), length(MultRel,NrRel).
?- relatiiordlin([a,b,c],MultRel), scrielista(MultRel), length(MultRel,NrRel).
?- relatiiordstr([a,b,c],MultRel), scrielista(MultRel), length(MultRel,NrRel).
?- relatiiordinestr([a,b,c],MultRel), scrielista(MultRel), length(MultRel,NrRel).
*/

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

% Desigur, se poate folosi si setof pentru eliminarea duplicatelor:

elimduplic([],[]).
elimduplic(L,M) :- setof(X, member(X,L), M).

% Stergerea a exact unei aparitii a unui element, de pe o pozitie arbitrara, dintr-o lista:

sterge(_,[],_) :- fail.
sterge(H,[H|T],T).
sterge(X,[H|T],[H|M]) :- sterge(X,T,M).

/* Interogati:
?- stergetot(a,[a,1,a,2,a],L).
?- stergetot(a,[1,2],L).
?- elimdup([2,a,1,1,a,2,a],M).
?- elimdupl([2,a,1,1,a,2,a],M).
?- elimduplic([2,a,1,1,a,2,a],M).
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

/* Pentru a determina relatiile de echivalenta pe o multime {a,b,c,d} (de cardinal 4, i.e. 
cu elementele a,b,c,d doua cate doua distincte) si partitiile asociate lor, interogati:
?- relatiiechiv([a,b,c,d],Eqs), eqs2parts([a,b,c,d],Eqs,Parts), scrielista(Eqs), write('-------------'), nl, scrielista(Parts), length(Parts,Nr).
*/

% Varianta, cu afisare mai prietenoasa: relatiiechivpart(+A,-EqA,-PartA)

relatiiechivpart(A,EqA,PartA) :- relatiiechiv(A,EqA), length(EqA,Nr),
	write('numarul de relatii de echivalenta/partitii: '), write(Nr), nl,
	write('--------------------------------'), nl,
	eqs2partscuafis(A,EqA,PartA).

eqs2partscuafis(_,[],[]).
eqs2partscuafis(A,[E|LE],[P|LP]) :- eq2part(A,E,P),
	write('relatia de echivalenta: '), write(E), nl,
	write('corespunde partitiei: '), write(P), nl, write('--------'), nl,
	eqs2partscuafis(A,LE,LP).

/* Interogati:
?- relatiiechivpart([a,b,c,d],EqA,PartA).
*/

% Pentru a verifica raspunsul Prolog-ului, sa scriem si:

/* predicat care testeaza daca fiecare element dintr-o lista de liste e permutare a
elementului de pe aceeasi pozitie din alta lista de liste: */

egalfiecmult([],[]).
egalfiecmult([H|T],[K|U]) :- permutare(H,K), egalfiecmult(T,U).

/* predicat care testeaza daca doua liste de liste coincid modulo o permutare a acestora si
cate o permutare a fiecarui element al acestora: */

egalmultdemult(L,M) :- permutare(L,P), egalfiecmult(P,M).

/* Interogati:
?- A=[a,b,c,d], relatiiechiv(A,EqA), eqs2parts(A,EqA,PartA), parts2eqs(PartA,Eq), egalfiecmult(EqA,Eq), !.
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
?- exderelpe(R,A), inchrefl(R,A,InchRefl), preordgen(R,A,PreordGen), echivgen(R,A,EchivGen), write(EchivGen).
?- exderel(R), inchsim(R,InchSim), inchtranz(R,InchTranz).
?- incaunexderel(R), inchtranz(R,Inchiderea), write(Inchiderea).
?- siincaunexderel(R), inchtranz(R,Inchiderea), write(Inchiderea), length(Inchiderea,CatePer).
?- exderel(R), echivgen(R,[a,b,c,d],Inchiderea), write(Inchiderea), length(Inchiderea,CatePer).
?- echivgen([(a,b),(c,d)],[a,b,c,d],Inchiderea), write(Inchiderea), length(Inchiderea,CatePer).
?- echivgen([(a,b)],[a,b,c,d],Inchiderea), write(Inchiderea), length(Inchiderea,CatePer).
*/
