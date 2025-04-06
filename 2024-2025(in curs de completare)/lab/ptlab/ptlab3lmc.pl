/* Fie A,B,C multimi arbitrare. Fie x arbitrar.
Notam cu variabilele booleene _a,_b,_c urmatoarele enunturi:
_a: x apartine lui A
_b: x apartine lui B
_c: x apartine lui C
Sa demonstram ca: (A<=B si A<=C) <=> A<=B^C.
*/

implica(P,Q) :- not(P) ; Q.
echiv(P,Q) :- implica(P,Q), implica(Q,P).

incl2multvsinters(_a,_b,_c) :- 
	echiv((implica(_a,_b), implica(_a,_c)), implica(_a,(_b,_c))).

demincl2multvsinters :- not((listaValBool([_a,_b,_c]),
			not(incl2multvsinters(_a,_b,_c)))).

listaValBool(L) :- listaBool(L), write(L), nl.

listaBool([]).
listaBool([H|T]) :- member(H,[false,true]), listaBool(T).

% Sa demonstram ca: A\B=A\(A^B).

difsufinters(_a,_b) :- echiv((_a,not(_b)), (_a,not((_a,_b)))).

demdifsufinters :- not((listaValBool([_a,_b]), not(difsufinters(_a,_b)))).

/* Fie T,A,B multimi a.i. A<=T si B<=T. => A^T=A si B^T=B.
   Notez:
cuantificatorul universal cu -V;
pentru orice multime M cu M<=T, cu -M=T\M;
pentru orice x si orice multime M, cu "x in M" faptul ca x apartine lui M.
   A=B <=> A^T=B^T <=> (-Vx)(x in A^T <=> x in B^T)
<=> (-Vx)[(x in A si x in T) <=> (x in B si x in T)]
<=> (-Vx)[x in T => (x in A <=> x in B)]
<=> (-Vx in T)(x in A <=> x in B)
   A<=B <=> A^T<=B^T <=> (-Vx)(x in A^T => x in B^T)
<=> (-Vx)[(x in A si x in T) => (x in B si x in T)]
<=> (-Vx)[x in T => (x in A => x in B)]
<=> (-Vx in T)(x in A => x in B)
   Fie x in T, arbitrar, fixat.
   Pentru orice multime M cu M<=T, avem, intrucat x in T e adevarata:
x in -M <=> x in T\M <=> [x in T si not(x in M)] <=> not(x in M).
   Notam cu variabilele booleene A,B enunturile:
A: x apartine lui A
B: x apartine lui B
   Sa demonstram ca: A\B=A^-B.
*/

difinterscomplem(A,B) :- echiv((A,not(B)), (A,not(B))).

demdifinterscomplem :- not((listaValBool([A,B]), not(difinterscomplem(A,B)))).

% Sa demonstram ca: --A=A.

complemcomplem(A) :- echiv(not(not(A)), A).

demcomplemcomplem :- not((listaValBool([A]), not(complemcomplem(A)))).

% Sa demonstram a doua lege a lui De Morgan: -(A^B)=-AU-B.

deMorgan2(A,B) :- echiv(not((A,B)), not(A);not(B)).

demdeMorgan2 :- not((listaValBool([A,B]), not(deMorgan2(A,B)))).

/* Cand sunt A si B parti complementare ale lui T: sa demonstram ca:
(AUB=T si A^B=0) <=> A=-B <=> B=-A. */

reunemulttot(A,B) :- echiv(A;B,true).

multdisj(A,B) :- echiv((A,B),false).

msechiv1particomplem(A,B) :- reunemulttot(A,B), multdisj(A,B).

egalcucomplem(A,B) :- echiv(A,not(B)).

echiv1particomplem(A,B) :- echiv(msechiv1particomplem(A,B), egalcucomplem(A,B)).

echiv2particomplem(A,B) :- echiv(egalcucomplem(A,B),egalcucomplem(B,A)).

particomplem(A,B) :- echiv1particomplem(A,B), echiv2particomplem(A,B).

demparticomplem :- not((listaValBool([A,B]), not(particomplem(A,B)))).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

prodcart(_,[],[]).
prodcart(L,[H|T],P) :- prodsgl(L,H,Q), prodcart(L,T,R), append(Q,R,P).

prodsgl([],_,[]).
prodsgl([H|T],X,[(H,X)|U]) :- prodsgl(T,X,U).

prodcartmult(L,M,P) :- prodcart(L,M,Q), elimdupl(Q,P).

elimdupl([],[]).
elimdupl([H|T],[H|L]) :- sterge(H,T,U), elimdupl(U,L).

sterge(_,[],[]).
sterge(H,[H|T],L) :- sterge(H,T,L), !.
sterge(X,[H|T],[H|L]) :- sterge(X,T,L).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

sublista([],_).
sublista([H|T],[H|L]) :- sublista(T,L).
sublista([H|T],[_|L]) :- sublista([H|T],L).

sublistele(L,LS) :- setof(S, sublista(S,L), LS).

afislista([]).
afislista([H|T]) :- write(H), nl, afislista(T).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

relbin(A,B,R) :- prodcartmult(A,B,P), sublista(R,P).

listarelbin(A,B,LR) :- setof(R, relbin(A,B,R), LR).

listrelbin(A,B,LR) :- prodcartmult(A,B,P), sublistele(P,LR).

/* f:A->B <=> f = {(a,f(a)) | a in A} <= AxB, iar (-Va in A)(f(a) in B).
Pentru orice a in A si b in B:
   a f b <=> (a,b) in f <=> b=f(a).
*/

functie([],_,[]).
functie([H|T],B,[(H,FH)|L]) :- member(FH,B), functie(T,B,L).

functiile(A,B,LF) :- setof(F, functie(A,B,F), LF).

functionala(A,R) :- not((member(X,A), member((X,B1),R), member((X,B2),R), B1\=B2)).

fctpart(A,B,R) :- relbin(A,B,R), functionala(A,R).

functiipart(A,B,LF) :- setof(F, fctpart(A,B,F), LF).
