/* functie(+Domeniu,+Codomeniu,-Grafic)
Identificam fiecare functie f:A->B, f=(A,G,B), cu graficul ei: f=G={(a,f(a)) | a in A}. */

functie([],_,[]).
functie([H|T],B,[(H,FH)|U]) :- member(FH,B), functie(T,B,U).

% Putem genera aceste functii si ca triplete (domeniu,grafic,codomeniu):

functiecatriplet([],B,([],[],B)).
functiecatriplet([H|T],B,([H|T],[(H,FH)|U],B)) :- member(FH,B), functiecatriplet(T,B,(T,U,B)).

functiile(A,B,ListaFct) :- setof(Fct, functie(A,B,Fct), ListaFct).

/* Afisarea acestor functii f:A->B sub forma:
  x | ...elementele a ale lui A...
_______________________________________

f(x)| ...f(a) pentru fiecare a din A...
Exemplu:
  x | 1 2 3
____________

f(x)| a a b
f:{1,2,3}->{a,b}, f(1)=f(2)=a, f(3)=b
*/

scriefunctiile(A,B) :- functiile(A,B,ListaFct), scrielistafct(ListaFct).

scrielistafct([]).
scrielistafct([Fct|ListaFct]) :- scriefct(Fct), nl, nl, scrielistafct(ListaFct).

% scriefct(Fct) 

detdom([],[]).
detdom([(H,_)|U],[H|T]) :- detdom(U,T).

detimag([],[]).
detimag([(_,FH)|U],[FH|T]) :- detimag(U,T).

scrielista([]).
scrielista([H|T]) :- write(H), tab(1), scrielista(T).

scriefct(Fct) :- detdom(Fct,A), detimag(Fct,Im), write('  x | '), scrielista(A), nl,
		length(A,Nr), tragelinie(Nr), nl, nl, write('f(x)| '), scrielista(Im).

tragelinie(0) :- write('__'), !.
tragelinie(Nr) :- write('__'), P is Nr-1, tragelinie(P).

scriefunctiilecunr(A,B) :- functiile(A,B,ListaFct), scrielistafctcunr(ListaFct,0).

scrielistafctcunr([],_).
scrielistafctcunr([Fct|ListaFct],Nr) :- S is Nr+1, write('A '), write(S), write('-a functie:'), nl,
					scriefct(Fct), nl, nl, scrielistafctcunr(ListaFct,S).



