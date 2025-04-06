/* Fie A,B,T multimi cu A<=T si B<=T.
Fie x in T, arbitrar, fixat.
Notez cu variabilele Prolog A,B:
A: x in A
B: x in B
*/

implica(P,Q) :- not(P);Q.
echiv(P,Q) :- implica(P,Q), implica(Q,P).

particomplem(A,B) :- echiv(A;B,true), echiv((A,B),false).

egalcomplem(A,B) :- echiv(A,not(B)).

charparticomplem(A,B) :- echiv(particomplem(A,B), egalcomplem(A,B)),
			echiv(egalcomplem(A,B),egalcomplem(B,A)).

demcharparticomplem :- not((listaValBool([A,B]), not(charparticomplem(A,B)))).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

listaValBool(L) :- listaBool(L), write(L), nl.

listaBool([]).
listaBool([H|T]) :- member(H,[false,true]), listaBool(T).

listaVal(L,ListaValori) :- instantiazaLista(L,ListaValori), write(L), nl.

instantiazaLista([],_).
instantiazaLista([H|T],LVal) :- member(H,LVal), instantiazaLista(T,LVal).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

prodcart(A,B,P) :- setof((X,Y), (member(X,A), member(Y,B)), P), !.
prodcart(_,_,[]).

prodcartliste([],_,[]).
prodcartliste([H|T],L,P) :- prodsgl(H,L,Q), prodcartliste(T,L,R), append(Q,R,P).

prodsgl(_,[],[]).
prodsgl(X,[H|T],[(X,H)|U]) :- prodsgl(X,T,U).

/*
?- setof(X, member(X, [1,2,3,2,1,0]), M).
*/

elimdupl([],[]).
elimdupl([H|T],[H|L]) :- sterge(H,T,M), elimdupl(M,L).

sterge(_,[],[]).
sterge(H,[H|T],L) :- sterge(H,T,L), !.
sterge(X,[H|T],[H|L]) :- sterge(X,T,L).

prodcartmult(A,B,P) :- prodcartliste(A,B,L), elimdupl(L,P).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

reuniune(A,B,R) :- append(A,B,C), elimdupl(C,R).

inters([],_,[]).
inters([H|T],B,[H|L]) :- member(H,B), !, inters(T,B,L).
inters([_|T],B,L) :- inters(T,B,L).

intersectie(A,B,I) :- inters(A,B,J), elimdupl(J,I).

dif([],_,[]).
dif([H|T],B,L) :- member(H,B), !, dif(T,B,L).
dif([H|T],B,[H|L]) :- dif(T,B,L).

diferenta(A,B,D) :- dif(A,B,E), elimdupl(E,D).

difer(A,[],A).
difer(A,[H|T],L) :- sterge(H,A,M), difer(M,T,L).

diferen(A,B,D) :- difer(A,B,E), elimdupl(E,D).

difsim(A,B,D) :- dif(A,B,AminusB), dif(B,A,BminusA), reuniune(AminusB,BminusA,D).

difersim(A,B,D) :- diferenta(A,B,AminusB), diferenta(B,A,BminusA),
			append(AminusB,BminusA,D).

/*
?- reuniune([1,2,3,4,5],[0,2,4,6],Cat).
?- reuniune([1,2,2,4,5,5],[0,2,4,4,6],Cat).
?- intersectie([1,2,3,4,5],[0,2,4,6],Cat).
?- inters([1,2,2,4,5,5],[0,2,4,4,6],Cat).
?- intersectie([1,2,2,4,5,5],[0,2,4,4,6],Cat).
?- dif([1,2,2,4,5,5],[0,2,4,4,6],Cat).
?- diferenta([1,2,2,4,5,5],[0,2,4,4,6],Cat).
?- difer([1,2,2,4,5,5],[0,2,4,4,6],Cat).
?- diferen([1,2,2,4,5,5],[0,2,4,4,6],Cat).
?- difsim([1,2,2,4,5,5],[0,2,4,4,6],Cat).
?- difersim([1,2,2,4,5,5],[0,2,4,4,6],Cat).
*/

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

egalmult(A,B) :- permutare(A,B).

stergeuna(_,[],_) :- fail.
stergeuna(H,[H|T],T).
stergeuna(X,[H|T],[H|L]) :- stergeuna(X,T,L).

permutare([],[]).
permutare([H|T],P) :- permutare(T,Q), stergeuna(H,P,Q).

permutari(L,LP) :- setof(P, permutare(L,P), LP).

afislista([]).
afislista([H|T]) :- write(H), nl, afislista(T).

/*
?- permutari([1,2,3,4],L), afislista(L), length(L,Nr).
*/

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

relbin(R,A,B) :- prodcartmult(A,B,P), sublista(R,P).

sublista([],_).
sublista([H|T],[H|L]) :- sublista(T,L).
sublista([H|T],[_|L]) :- sublista([H|T],L).

sublistele(L,LS) :- setof(S, sublista(S,L), LS).

/*
?- sublistele([1,2,3],L), afislista(L), length(L,N).
*/

relatiibinare(A,B,LR) :- setof(R, relbin(R,A,B), LR).

relbinare(A,B,LR) :- prodcartmult(A,B,P), sublistele(P,LR).

/*
?- relatiibinare([a,b],[1,2,3],L), afislista(L), length(L,N).
?- relbinare([a,b],[1,2,3],L), afislista(L), length(L,N).
*/

fctpart(F,A,B) :- relbin(F,A,B), functionala(F,A).

functionala(F,A) :-  not((member(X,A), member((X,B),F), member((X,C),F), B\=C)).

reltot(R,A,B) :- relbin(R,A,B), tot(R,A,B).

tot(R,A,B) :- not((member(X,A), not((member(Y,B), member((X,Y),R))))).

reltotala(R,A,B) :- relbin(R,A,B), totala(R,A).

totala(R,A) :- not((member(X,A), not(member((X,_),R)))).

functie([],[],_).
functie([(H,FH)|L],[H|T],B) :- member(FH,B), functie(L,T,B).

functiile(A,B,LF) :- setof(F, functie(F,A,B), LF), !.
functiile(_,_,[]).

/*
?- functiile([a,b],[1,2,3],L), afislista(L), length(L,N).
?- setof(F, (fctpart(F,[a,b],[1,2,3]), tot(F,[a,b],[1,2,3])), L), afislista(L), length(L,N).
?- setof(F, (fctpart(F,[a,b],[1,2,3]), totala(F,[a,b])), L), afislista(L), length(L,N).
*/

invrel([],[]).
invrel([(X,Y)|T],[(Y,X)|L]) :- invrel(T,L).

inversarel(R,Q) :- setof((Y,X), member((X,Y),R), Q), !.
inversarel(_,[]).

/*
?- invrel([(a,1),(a,2),(b,1),(c,2),(c,3)],Inversa).
?- inversarel([(a,1),(a,2),(b,1),(c,2),(c,3)],Inversa).
*/

relinj(R,A,B) :- relbin(R,A,B), inj(R,B).

inj(R,B) :-  not((member(Y,B), member((A,Y),R), member((U,Y),R), A\=U)).

relsurj(R,A,B) :- relbin(R,A,B), surj(R,A,B).

surj(R,A,B) :- not((member(Y,B), not((member(X,A), member((X,Y),R))))).

relsurjectiva(R,A,B) :- relbin(R,A,B), surjectiva(R,B).

surjectiva(R,B) :- not((member(Y,B), not(member((_,Y),R)))).

functiebij(F,A,B) :- functie(F,A,B), inj(F,B), surj(F,A,B).

functiebijectiva(F,A,B) :- functie(F,A,B), inj(F,B), surjectiva(F,B).

/*
?- setof(F, (functie(F,[a,b],[1,2,3]), inj(F,[1,2,3])), L), afislista(L), length(L,N).
?- setof(F, (functie(F,[a,b],[1,2,3]), surj(F,[a,b],[1,2,3])), L), afislista(L), length(L,N).
?- setof(F, (functie(F,[a,b],[1,2,3]), surjectiva(F,[1,2,3])), L), afislista(L), length(L,N).
?- setof(F, functiebij(F,[a,b],[1,2,3]), L), afislista(L), length(L,N).
?- setof(F, functiebijectiva(F,[a,b],[1,2,3]), L), afislista(L), length(L,N).
?- setof(F, functiebij(F,[a,b,c],[1,2,3]), L), afislista(L), length(L,N).
?- setof(F, functiebijectiva(F,[a,b,c],[1,2,3]), L), afislista(L), length(L,N).
?- setof(F, (functie(F,[a,b,c],[1,2,3]), inj(F,[1,2,3])), L), afislista(L), length(L,N).
?- setof(F, (functie(F,[a,b,c],[1,2,3]), surj(F,[a,b,c],[1,2,3])), L), afislista(L), length(L,N).
?- setof(F, (functie(F,[a,b,c],[1,2,3]), surjectiva(F,[1,2,3])), L), afislista(L), length(L,N).
?- setof(F, (functie(F,[a,b,c,d],[1,2,3]), inj(F,[1,2,3])), L), afislista(L), length(L,N).
?- setof(F, (functie(F,[a,b,c,d],[1,2,3]), surj(F,[a,b,c,d],[1,2,3])), L), afislista(L), length(L,N).
?- setof(F, (functie(F,[a,b,c,d],[1,2,3]), surjectiva(F,[1,2,3])), L), afislista(L), length(L,N).
?- setof(F, functiebij(F,[a,b,c,d],[1,2,3]), L), afislista(L), length(L,N).
?- setof(F, functiebijectiva(F,[a,b,c,d],[1,2,3]), L), afislista(L), length(L,N).
?- (setof(F, functiebijectiva(F,[a,b,c,d],[1,2,3]), L), !; L=[]), afislista(L), length(L,N).
*/

functieListaVal([],[],_).
functieListaVal([FH|L],[_|T],B) :- member(FH,B), functieListaVal(L,T,B).

injFunctieListaVal(F) :- elimdupl(F,F).

surjFunctieListaVal(F,B) :- elimdupl(F,G), egalmult(G,B).

/*
?- setof(F, functiebij(F,[a,b,c],[1,2,3]), L), afislista(L), length(L,N).
?- setof(F, functiebij(F,[1,2,3],[1,2,3]), L), afislista(L), length(L,N).
?- setof(F, functiebijectiva(F,[a,b,c],[1,2,3]), L), afislista(L), length(L,N).
?- setof(F, functiebijectiva(F,[1,2,3],[1,2,3]), L), afislista(L), length(L,N).
?- setof(F, (functieListaVal(F,[a,b,c],[1,2,3]), injFunctieListaVal(F), surjFunctieListaVal(F,[1,2,3])), L), afislista(L), length(L,N).
?- setof(F, (functieListaVal(F,[1,2,3],[1,2,3]), injFunctieListaVal(F), surjFunctieListaVal(F,[1,2,3])), L), afislista(L), length(L,N).
?- permutari([1,2,3],L), afislista(L), length(L,N).
*/
