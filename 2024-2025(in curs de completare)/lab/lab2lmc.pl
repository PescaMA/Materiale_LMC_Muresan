ciur(N,LP) :- lista(2,N,L), ciuruire(L,LP).

lista(K,N,[]) :- K>N, !.
lista(K,N,[K|T]) :- SK is K+1, lista(SK,N,T).

/* Urmatoarele cut(!)-uri optionale sunt pentru intreruperea executiei imediat dupa gasirea unicei solutii, astfel ca Prolog-ul sa nu mai lase utilizatorul sa ceara alte solutii (cu ;/Next), apoi sa intoarca false, indicand faptul ca nu mai exista alte solutii. */

ciuruire([],[]).   %%% Optional: ciuruire([],[]) :- !.
ciuruire([H|T],[H|LP]) :- filtreaza(H,T,L), ciuruire(L,LP).

filtreaza(_,[],[]) :- !.
filtreaza(X,L,LfaraMX) :- auxfilt(X,X,L,LfaraMX).

auxfilt(_,_,[],[]).   %%% Optional: auxfilt(_,_,[],[]) :- !.
auxfilt(X,1,[_|T],L) :- auxfilt(X,X,T,L), !.
auxfilt(X,Contor,[H|T],[H|L]) :- PC is Contor-1, auxfilt(X,PC,T,L).

/* Interogati:
?- ciur(15,L).
?- ciur(1500,L), write(L).
La ultima interogare, lista L rezultata este lunga, asadar Prolog-ul o afiseaza truchiat ca valoare de variabila, asadar o afisam explicit, cu predicatul predefinit write.
*/

membru(_,[]) :- fail.
membru(H,[H|_]).
membru(X,[_|T]) :- membru(X,T).

testmembru(H,[H|T]) :- T=[], ! ; true.
testmembru(X,[_|T]) :- T\=[], testmembru(X,T).

/* Metapredicate care colecteaza solutiile altor predicate:
setof(Termen, Conditie, Lista)=true <=> Lista este lista termenilor de forma Termen care satisfac conditia Conditie, ca lista fara duplicate, si intorcand false cand nu exista termeni de forma Termen care sa satisfaca scopul Conditie;
bagof(Termen, Conditie, Lista) <=> Lista este lista termenilor de forma Termen care satisfac conditia Conditie, ca lista cu duplicate, si intorcand false cand nu exista termeni de forma Termen care sa satisfaca scopul Conditie;
findall(Termen, Conditie, Lista) <=> Lista este lista termenilor de forma Termen care satisfac conditia Conditie, ca lista cu duplicate, si intorcand Lista=[] cand nu exista termeni de forma Termen care sa satisfaca scopul Conditie.
findall mai difera fata de bagof si in tratarea conditiilor Conditie in care apar variabile care nu apar in termenul Termen - vom vedea.
Interogati:
?- setof(X, member(X,[a,1,b,0,a,b,c,a,1,1]), LfaraDuplicate).
?- setof((X,Y,Z), (member(X,[false,true]), member(Y,[false,true]), member(Z,[false,true])), ListaTripleteValoriBooleene), write(ListaTripleteValoriBooleene).
*/

elimdup([],[]).
elimdup([H|T],L) :- member(H,T), !, elimdup(T,L).
elimdup([H|T],[H|L]) :- elimdup(T,L).

sterge(_,[],[]).
sterge(H,[H|T],L) :- !, sterge(H,T,L).
sterge(X,[H|T],[H|L]) :- sterge(X,T,L).

elimdupl([],[]).
elimdupl([H|T],[H|L]) :- sterge(H,T,M), elimdupl(M,L).

% Produsul cartezian (de multimi):

prodcart(L,M,LxM) :- setof((X,Y), (member(X,L),member(Y,M)), LxM), !.
prodcart(_,_,[]).

% Produsul cartezian de liste:

prodcartlist(L,M,LxM) :- bagof((X,Y), (member(X,L),member(Y,M)), LxM).
prodcartlist(_,_,[]).

prodcartliste(L,M,LxM) :- findall((X,Y), (member(X,L),member(Y,M)), LxM).

% Afisarea unei liste cu fiecare element pe alt rand:

afislista([]).
afislista([H|T]) :- write(H), nl, afislista(T).

/* Interogati:
?- setof((X,Y,Z), (member(X,[false,true]), member(Y,[false,true]), member(Z,[false,true])), ListaTripleteValoriBooleene), afislista(ListaTripleteValoriBooleene).
*/

/* Pentru Exercitiul 4 din Seminarul I, partea 1, sa notam cu variabilele booleene A,B,C,D proprietatile a,b,c,d, respectiv: */

implica(P,Q) :- not(P); Q.
echiv(P,Q) :- implica(P,Q), implica(Q,P).
xor(P,Q) :- P,not(Q) ; Q,not(P).

ipoteza1(A,B,C,D) :- implica((A,B), xor(C,D)).
ipoteza2(A,B,C,D) :- implica((B,C), (A,D ; not(A),not(D))).
ipoteza3(A,B,C,D) :- implica((not(A),not(B)), (not(C),not(D))).

ipoteza(A,B,C,D) :- ipoteza1(A,B,C,D), ipoteza2(A,B,C,D), ipoteza3(A,B,C,D).

concluzia1(A,B,C) :- implica((A,B), not(C)).
concluzia2(A,B,C) :- not((A,B,C)).

dedem1(A,B,C,D) :- implica(ipoteza(A,B,C,D), concluzia1(A,B,C)).
dedem2(A,B,C,D) :- implica(ipoteza(A,B,C,D), concluzia2(A,B,C)).

dem1 :- not((member(A,[false,true]), member(B,[false,true]), member(C,[false,true]), 		member(D,[false,true]), write((A,B,C,D)), nl, not(dedem1(A,B,C,D)))).
dem2 :- not((member(A,[false,true]), member(B,[false,true]), member(C,[false,true]), 		member(D,[false,true]), write((A,B,C,D)), nl, not(dedem2(A,B,C,D)))).


test(aba).