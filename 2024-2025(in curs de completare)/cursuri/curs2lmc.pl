/* Amintesc ca Prolog-ul permite supraincarcarea operatorilor, inclusiv a predicatelor.
iar predicatele din fapte si membrii stangi ai regulilor pot avea ca argumente termeni
compusi, nu doar variabile sau constante; la fel pentru predicatele din interogari: */

f.
f(g(_)).
f(X) :- write(X).
f(h(X)) :- write(X), tab(5), write(***).
f(X,Y) :- write(X), tab(3), write(Y).
f(_,f(_),g(_)).
f(X,h(_),g(X)).

/* Interogati (dand ;/Next pentru obtinerea tuturor solutiilor):
?- f.
?- f(Cine).
?- f(10).
?- f(h(Cine)).
?- f(f(Cine)).
 f   f   f   f
 |   |   |   |
 g   X   h   f
 |       |   |
 V       X  Cine
?- f(V,W,f(U)).
    f         f        f
  / | \     / | \    / | \
 A  f  g   X  h  g  V  W  f
    |  |      |  |        |
    B  C      V  X        U
?- f(A,h(B),C).
*/

/* Amintesc sintaxa pentru liste in Prolog:
   constanta [] este lista vida;
   listele nevide: [Head|Tail] = [|](Head,Tail)
De exemplu: [1,2,3] = [1|[2,3]] = [1,2|[3]] = [1,2,3|[]] = [1,2|[3|[]]] = [1|[2|[3|[]]]] = [|](1,[|](2,[|](3,[]))) (ultimele doua scrieri sunt desfasurate ca termeni Prolog, ultima fiind cu operatorul binar [|] scris sub forma uzuala pentru orice operator binar:
nume_operator(lista_argumentelor)).

Interogati:
?- [1,2,3|[4,5]]=L.
?- [1,2,3|[4,5]]=[1|[2,3|[4|[5]]]].
?- [1,B,3|[D,5]]=[A|[2,C|[4|[E]]]].

Interogati:
?- X is 20+2.
?- X is +(20,2).

Predicatul predefinit =.. :
Termen =.. [OpDominantTermen | ListaArgumenteTermen]

Interogati:
?- f(A,f(X),g(1,2),[a,b]) =.. L.
?- f(A,f(X),g(1,2),[a,b]) =.. [Op|LA].
?- T =.. [f,A,f(X),g(1,2),[a,b]].
?- f(1,g(2),X,Y,Z) =.. [O,A,B,10,20,[3]].
?- f(B,V,X,Y,Z) =.. [O,A,B,10,20,[3]].
?- [1,2,3] =.. [Op|LA].
?- [2,3] =.. [Op|LA].
?- [3] =.. [Op|LA].
?- [] =.. [Op|LA].
?- c =.. [Op|LA].
?- 10 =.. [Op|LA].
?- T=..L.
?- T=..[Op|LA].
*/





