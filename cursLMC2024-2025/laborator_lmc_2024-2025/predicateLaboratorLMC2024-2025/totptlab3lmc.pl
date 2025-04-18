% Produsul cartezian de liste, definit recursiv, fara metapredicate:

prodcart(_,[],[]).
prodcart(L,[H|T],P) :- prodsgl(L,H,Q), prodcart(L,T,R), append(Q,R,P).

prodsgl([],_,[]).
prodsgl([H|T],X,[(H,X)|U]) :- prodsgl(T,X,U).

% Produsul cartezian (de multimi, i.e.) fara duplicate:

prodcartmult(L,M,P) :- prodcart(L,M,Q), elimdupl(Q,P).

/* Eliminarea duplicatelor dintr-o lista, cu pastrarea
primei aparitii a fiecarui element: */

elimdupl([],[]).
elimdupl([H|T],[H|L]) :- sterge(H,T,U), elimdupl(U,L).

sterge(_,[],[]).
sterge(H,[H|T],L) :- sterge(H,T,L), !.
sterge(X,[H|T],[H|L]) :- sterge(X,T,L).

relbin(A,B,R) :- prodcartmult(A,B,P), sublista(R,P).

sublista([],_).
sublista([H|T],[H|L]) :- sublista(T,L).
sublista([H|T],[_|L]) :- sublista([H|T],L).

sublistele(L,LS) :- setof(S, sublista(S,L), LS).

relatiibin(A,B,LR) :- setof(R, relbin(A,B,R), LR).

afislista([]).
afislista([H|T]) :- write(H), nl, afislista(T).

relatiibinare(A,B,LR) :- prodcartmult(A,B,P), sublistele(P,LR).

/* f:A->B <=> f = {(a,f(a)) | a in A} <= AxB, unde (-Va in A)(f(a) in B)
-Va in A si -Vb in B: a f b <=> (a,b) in f <=> b=f(a)
*/

functie([],_,[]).
functie([H|T],B,[(H,FH)|L]) :- member(FH,B), functie(T,B,L).

functiile(A,B,LF) :- setof(F, functie(A,B,F), LF), !.
functiile(_,_,[]).

% (A<=B si A<=C) <=> A<=B^C

implica(P,Q) :- not(P) ; Q.
echiv(P,Q) :- implica(P,Q), implica(Q,P).

incl2mult(_a,_b,_c) :- echiv((implica(_a,_b), implica(_a,_c)), 
				implica(_a,(_b,_c))).

demincl2mult :- not((listaValBool([_a,_b,_c]), not(incl2mult(_a,_b,_c)))).

% A\B=A\(A^B)

difsufinters(_a,_b) :- echiv((_a,not(_b)), (_a,not((_a,_b)))).

demdifsufinters :- not((listaValBool([_a,_b]), not(difsufinters(_a,_b)))).

listaValBool(L) :- listaBool(L), write(L), nl.

listaBool([]).
listaBool([H|T]) :- member(H,[false,true]), listaBool(T).

% Pt. A<=T>=B: -(AUB)=-A^-B.

deMorgan1(A,B) :- echiv(not(A;B), (not(A),not(B))).

demdeMorgan1 :- not((listaValBool([A,B]), not(deMorgan1(A,B)))).
