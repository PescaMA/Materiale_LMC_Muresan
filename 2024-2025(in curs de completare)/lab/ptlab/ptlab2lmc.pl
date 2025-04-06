ciur(N,LP) :- lista(2,N,L), ciuruire(L,LP).

lista(K,N,[]) :- K>N, !.
lista(K,N,[K|T]) :- SK is K+1, lista(SK,N,T).

ciuruire([],[]).
ciuruire([H|T],[H|L]) :- filtreaza(H,H,T,M), ciuruire(M,L).

filtreaza(_,_,[],[]).
filtreaza(X,1,[_|T],L) :- filtreaza(X,X,T,L).
filtreaza(X,Contor,[H|T],[H|L]) :- Contor>1, PC is Contor-1, filtreaza(X,PC,T,L).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

inversa([],[]).
inversa([H|T],L) :- inversa(T,M), append(M,[H],L).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

membru(_,[]) :- fail.
membru(H,[H|_]).
membru(X,[_|T]) :- membru(X,T).

testmembru(X,[X]) :- !.
testmembru(X,[H|T]) :- T\=[], (X=H; testmembru(X,T)).

/*
setof(Termen, Conditie, Lista)
bagof
findall
?- setof(X, member(X,[a,2,1,0,b,a,2,1,1]),M).
MEMO: DE FACUT SI LA GRUPA 144:
?- setof(X, member((X,Y),[(a,1),(b,1),(a,2),(c,3),(c,3),(d,3)]), L).
?- bagof(X, member((X,Y),[(a,1),(b,1),(a,2),(c,3),(c,3),(d,3)]), L).
?- findall(X, member((X,Y),[(a,1),(b,1),(a,2),(c,3),(c,3),(d,3)]), L).
?- bagof(X, Y^member((X,Y),[(a,1),(b,1),(a,2),(c,3),(c,3),(d,3)]), L).
?- setof(X, Y^member((X,Y),[(a,1),(b,1),(a,2),(c,3),(c,3),(d,3)]), L).
*/

elimdup([],[]).
elimdup([H|T],L) :- member(H,T), !, elimdup(T,L).
elimdup([H|T],[H|L]) :- elimdup(T,L).

sterge(_,[],[]).
sterge(H,[H|T],L) :- !, sterge(H,T,L).
sterge(X,[H|T],[H|L]) :- sterge(X,T,L).

elimdupl([],[]).
elimdupl([H|T],[H|L]) :- sterge(H,T,M), elimdupl(M,L).

/*
?- elimdup([a,2,1,0,b,a,2,1,1],L).
L=[0,b,a,2,1]
?- elimdupl([a,2,1,0,b,a,2,1,1],L).
L=[a,2,1,0,b]
*/

prodmult(L,M,LxM) :- setof((X,Y), (member(X,L), member(Y,M)), LxM), !.
prodmult(_,_,[]).

prodliste(L,M,LxM) :- bagof((X,Y), (member(X,L), member(Y,M)), LxM), !.
prodliste(_,_,[]).

prodlist(L,M,LxM) :- findall((X,Y), (member(X,L), member(Y,M)), LxM).

% MEMO: DE FACUT SI LA 144:

prodcart([],_,[]).
prodcart([H|T],L,P) :- prodsgl(H,L,Q), prodcart(T,L,R), append(Q,R,P).

prodsgl(_,[],[]).
prodsgl(H,[K|T],[(H,K)|U]) :- prodsgl(H,T,U).

prodcartmult(L,M,LxM) :- prodcart(L,M,P), elimdupl(P,LxM).

/*
(1)	(a si b) => (c xor d)
(2)	(b si c) => [(a si d) sau (non a si non d)] <=> non(a xor d)
(3)	(non a si non b) => (non c si non d)
Sa demonstram:
(I)	(non a si non b) => non c
(II)	non(a si b si c)
Notam cu variabilele A,B,C,D (sau _a,_b,_c,_d) proprietatile a,b,c,d, respectiv.
*/

implica(P,Q) :- not(P);Q.
echiv(P,Q) :- implica(P,Q), implica(Q,P).
xor(P,Q) :- P, not(Q) ; Q, not(P).

ipoteza1(A,B,C,D) :- implica((A,B), xor(C,D)).
ipoteza2(A,B,C,D) :- implica((B,C), (A,D ; not(A),not(D))).
ipoteza3(A,B,C,D) :- implica((not(A),not(B)), (not(C);not(D))).

ipoteza(A,B,C,D) :- ipoteza1(A,B,C,D), ipoteza2(A,B,C,D), ipoteza3(A,B,C,D).

cerintaI(A,B,C) :- implica((not(A),not(B)), not(C)).
cerintaII(A,B,C) :- not((A,B,C)).

dedemI(A,B,C,D) :- implica(ipoteza(A,B,C,D), cerintaI(A,B,C)).
dedemII(A,B,C,D) :- implica(ipoteza(A,B,C,D), cerintaII(A,B,C)).

demcerintaI :- not((member(A,[false,true]), member(B,[false,true]),
		member(C,[false,true]), member(D,[false,true]), write((A,B,C,D)), nl,
		not(dedemI(A,B,C,D)))).

demcerintaII :- not((member(A,[false,true]), member(B,[false,true]),
		member(C,[false,true]), member(D,[false,true]), write((A,B,C,D)), nl,
		not(dedemII(A,B,C,D)))).
