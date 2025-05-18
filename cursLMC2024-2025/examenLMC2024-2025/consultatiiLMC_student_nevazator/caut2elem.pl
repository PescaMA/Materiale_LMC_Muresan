contine2elem(X,Y,L) :- member(X,L), member(Y,L).

cautlistacu2elem(X,Y,LL) :- member(L,LL), contine2elem(X,Y,L), write(L), nl.

% Varianta:

cautalistacu2elem(X,Y,LL) :- member(L,LL), member(X,L), member(Y,L), write(L), nl.

/* Interoghez:
?- cautlistacu2elem(3,10,[[1,2,3],[],[2,10,5,3],[10,20],[1,2,3,10,0]]).
?- cautalistacu2elem(3,10,[[1,2,3],[],[2,10,5,3],[10,20],[1,2,3,10,0]]).
si dau ;/Next pentru a gasi toate solutiile.
*/

% Determinarea numarului listei care contine cele doua elemente (X si Y):

nrlistacu2elem(X,Y,LL) :- auxnrlistacu2elem(X,Y,LL,0).

auxnrlistacu2elem(_,_,[],_) :- fail.
auxnrlistacu2elem(X,Y,[L|LL],N) :- Nr is N+1, (member(X,L), member(Y,L), !,
	write('A '), write(Nr), write('-a lista contine elementele '), 
	write(X), write(' si '), write(Y), nl ; true), auxnrlistacu2elem(X,Y,LL,Nr).

/* Interoghez:
?- nrlistacu2elem(3,10,[[1,2,3],[],[2,10,5,3],[10,20],[1,2,3,10,0]]).
?- nrlistacu2elem(10,10,[[1,2,3],[],[2,10,5,3],[10,20],[1,2,3,10,0],[1,10],[],[],[X],[3,10],[]]).
si dau ;/Next pentru a gasi toate solutiile.
*/

