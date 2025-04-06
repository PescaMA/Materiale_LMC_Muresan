/* Clauzele, atat cele din baza de cunostinte (faptele si regulile), cat si cele din
interogari (clauzele scop) trebuie sa fie predicate, i.e. termeni booleeni.
Interogati:
?- 2**10.
?- X=2**10.
?- X is 2**10.
*/

% Daca L e o lista de numere, atunci: eordcresc(L)=true <=> L e ordonata crescator.

eordcresc([]).
eordcresc([_]).
eordcresc([H,K|T]) :- H=<K, eordcresc([K|T]).

/* nrapar(X,L,Nr)=true <=> nraparitii(X,L,Nr)=true <=> Nr e numarul de aparitii
ale lui X in lista L, mai precis numarul de elemente din lista L care unifica cu X.
nrap(X,L,Nr)=true <=> numarap(X,L,Nr)=true <=> Nr e numarul de aparitii literal identice
ale lui X in lista L, adica numarul de elemente literal identice cu X ale listei L.
Negatia logica: not, \+
Negatia egalului de unificare: not(X=Y) <=> X\=Y
Negatia egalului de literal identitate: not(X==Y) <=> X\==Y
Predicatul zeroar predefinit cut, scris !, "taie" backtracking-ul, i.e., daca
scopul curent a fost satisfacut cu, regula in care apare cut, atunci Prolog-ul
nu va mai cauta o alta satisfacere pentru acel scop. */

nrapar(_,[],0).
nrapar(H,[H|T],Nr) :- nrapar(H,T,N), Nr is N+1.
nrapar(X,[H|T],Nr) :- X\=H, nrapar(X,T,Nr).

nraparitii(_,[],0).
nraparitii(H,[H|T],Nr) :- nraparitii(H,T,N), Nr is N+1, !.
nraparitii(X,[_|T],Nr) :- nraparitii(X,T,Nr).

nrap(_,[],0).
nrap(X,[H|T],Nr) :- X==H, nrap(X,T,N), Nr is N+1.
nrap(X,[H|T],Nr) :- X\==H, nrap(X,T,Nr).

numarap(_,[],0).
numarap(X,[H|T],Nr) :- X==H, numarap(H,T,N), Nr is N+1, !.
numarap(X,[_|T],Nr) :- numarap(X,T,Nr).

/* Interogati:
?- nrapar(3,[1,2,3,0,3,3,5,3],Nr).
?- nraparitii(3,[1,2,3,0,3,3,5,3],Nr).
?- nrap(3,[1,2,3,0,3,3,5,3],Nr).
?- numarap(3,[1,2,3,0,3,3,5,3],Nr).
?- nrapar(3,[1,2,X,3,0,Y,3,3,f(V),5,3],Nr).
?- nraparitii(3,[1,2,X,3,0,Y,3,3,f(V),5,3],Nr).
?- nrap(3,[1,2,X,3,0,Y,3,3,f(V),5,3],Nr).
?- numarap(3,[1,2,X,3,0,Y,3,3,f(V),5,3],Nr).
?- nrapar(X,[1,2,X,3,0,Y,3,3,f(V),5,3],Nr).
?- nraparitii(X,[1,2,X,3,0,Y,3,3,f(V),5,3],Nr).
?- nrap(X,[1,2,X,3,0,Y,3,3,f(V),5,3],Nr).
?- numarap(X,[1,2,X,3,0,Y,3,3,f(V),5,3],Nr).
?- nrapar(f(X),[1,2,X,3,0,Y,3,3,f(V),5,3],Nr).
?- nraparitii(f(X),[1,2,X,3,0,Y,3,3,f(V),5,3],Nr).
?- nrap(f(X),[1,2,X,3,0,Y,3,3,f(V),5,3],Nr).
?- numarap(f(X),[1,2,X,3,0,Y,3,3,f(V),5,3],Nr).
?- nrapar(f(X),[1,2,3,0,3,3,f(V),5,3],Nr).
?- nraparitii(f(X),[1,2,3,0,3,3,f(V),5,3],Nr).
?- nrap(f(X),[1,2,3,0,3,3,f(V),5,3],Nr).
?- numarap(f(X),[1,2,3,0,3,3,f(V),5,3],Nr).
*/

/* nrvar(Termen,Nr)=true <=> Nr e numarul de variabile care apar in termenul Termen.
nrvarlista(L,Nr)=true <=> Nr e numarul de variabile care apar in toti termenii din lista L.
Predicatul unar predefinit var testeaza daca argumentul sau e variabila.
Predicatul predefinit =.. poate fi folosit pentru determinarea operatorului dominant al unui
termen si a argumentelor acestuia, precum si pentru construirea unui termen dintr-o lista,
dar nu poate fi folosit sub forma Variabila1=..Variabila2. */

nrvar(V,1) :- var(V), !.
nrvar(Termen,0) :- Termen=..[_], !.
nrvar(Termen,Nr) :- Termen=..[_|T], nrvarlista(T,Nr).

nrvarlista([],0).
nrvarlista([H|T],Nr) :- nrvar(H,N1), nrvarlista(T,N2), Nr is N1+N2.

/* Interogati:
?- nrvar([V,2,X,V,f(X),g(X,Y),c,h(f(V,W),g(h(X)))],Nr).
*/

/* Predicat pentru aplicarea unui operator aritmetic binar la doua liste,
element cu element, lasand neschimbata coada listei celei mai lungi:
calculliste(Op,[E1,E2,...,Ek],[F1,F2,...,Fn],L)=true <=> Op este un operator aritmetic binar,
E1,E2,...,Ek,F1,F2,...,Fn sunt numere (k,n fiind numere naturale), iar L=[G1,G2,...,Gm],
unde: m=max{k,n} si, daca i=min{k,n}, atunci G1,G2,...,Gi sunt rezultatele aplicarii lui Op
asupra perechilor de numere: (E1,F1),(E2,F2),...,(Ei,Fi), respectiv, i.e. satisfac:
G1 is E1 Op F1, G2 is E2 Op F2,..., Gi is Ei Op Fi, iar:
   daca m=k, atunci G(i+1)=E(i+1),...,Gk=Ek;
   daca m=n, atunci G(i+1)=F(i+1),...,Gn=Fn. */

calculliste(_,[],L,L) :- !.
calculliste(_,L,[],L) :- !. % cut ca sa incheie calculul in loc sa permita cererea unei
	% alte solutii in cazul in care prima lista e strict mai lunga decat a doua
calculliste(Op,[H|T],[K|U],[Cap|Coada]) :- Termen=..[Op,H,K], Cap is Termen,
					calculliste(Op,T,U,Coada).

/* Interogati:
?- calculliste(+,[10,2,-5,300],[7,20,2,60],L).
?- calculliste(-,[10,2,-5,300,7,0,100],[7,20,2,60],L).
?- calculliste(*,[10,2,-5,300],[7,20,2,60,0],L).
?- calculliste(div,[10,2,-5,300],[7,20,2,60,0,10,100,0],L).
?- calculliste(mod,[10,2,-5,300],[7,20,2,60],L).
?- calculliste(rem,[10,2,-5,300],[7,20,2,60],L).
?- calculliste(**,[10,2,-5,300],[7,20,2,60],L).
*/

/* Predicatul zeroar predefinit fail esueaza intotdeauna, adica mereu intoarce false.
Predicat binar predefinit member este echivalent cu predicatul membru de mai jos, care
testeaza apartenenta unui element la o lista, mai precis daca acel element unifica, cu
macar un element al listei. */

membru(_,[]) :- fail. % echivalent cu: not(membru(_,[]))., pentru ca aceasta e singura
	% clauza de definitie pentru predicatul membru cu al doilea argument [], asadar
	% aceasta regula, care spune ca membru(_,[]) e satisfacut daca fail e satisfacut,
	% devine: membru(_,[]) e satisfacut ddaca fail e satisfacut
membru(H,[H|_]).
membru(X,[_|T]) :- membru(X,T).

apartine(_,[]) :- fail.
apartine(H,[H|_]) :- !.
apartine(X,[_|T]) :- apartine(X,T).

/* Interogati:
?- membru(3,[1,2,3,4,5]).
?- apartine(3,[1,2,3,4,5]).
?- membru(7,[1,2,3,4,5]).
?- apartine(7,[1,2,3,4,5]).
?- membru(X,[1,2,3,4,5]). % si dati ;/Next, pentru a vedea toate solutiile
?- apartine(X,[1,2,3,4,5]).
Spre deosebire de predicatul apartine, membru genereaza toate elementele listei.
Interogati:
?- membru(X,[1,2,3,4,5]), write(X), tab(1), fail.
?- not((membru(X,[1,2,3,4,5]), write(X), tab(1), fail)).
Generarea tripletelor de valori booleene cu ;/Next, apoi ca in interogarile anterioare: */

gentriplet(P,Q,R) :- member(P,[false,true]), member(Q,[false,true]), member(R,[false,true]).

gentriplete :- member(P,[false,true]), member(Q,[false,true]), member(R,[false,true]),
			write((P,Q,R)), nl, fail.

generaretriplete :- not((member(P,[false,true]), member(Q,[false,true]), member(R,[false,true]),
			write((P,Q,R)), nl, fail)).

/* Interogati:
?- gentriplet(P,Q,R).
?- gentriplete.
?- generaretriplete.
*/

implica(P,Q) :- not(P);Q.
echiv(P,Q) :- implica(P,Q), implica(Q,P).

/* Interogati:
?- implica(false,true)=implica(true,true).
?- echiv(implica(false,true),implica(true,true)).
*/

/* Demonstrarea distributivitatii conjunctiei fata de disjunctie, prin tabel semantic,
i.e. tabel de valori de adevar (valori booleene): */

ms(P,Q,R) :- P,(Q;R).
md(P,Q,R) :- P,Q;P,R.

distribsifatadesau :- not((gentriplet(P,Q,R), write((P,Q,R)), nl,
			not(echiv(ms(P,Q,R),md(P,Q,R))))).

% Demonstrarea distributivitatii disjunctiei fata de conjunctie, prin tabel semantic:

mstg(P,Q,R) :- P;Q,R.
mdr(P,Q,R) :- (P;Q),(P;R).

distribsaufatadesi :- not((gentriplet(P,Q,R), write((P,Q,R)), nl,
			not(echiv(mstg(P,Q,R),mdr(P,Q,R))))).

% Ca predicatele membru(<=>member) si apartine, dar cu literal identitate in loc de unificare:

membruid(_,[]) :- fail.
membruid(X,[H|_]) :- X==H.
membruid(X,[_|T]) :- membruid(X,T).

apartineid(_,[]) :- fail.
apartineid(X,[H|_]) :- X==H, !.
apartineid(X,[_|T]) :- apartineid(X,T).

/* Interogati:
?- membruid(X,[1,2,V,3,4,5]).
?- apartineid(X,[1,2,V,3,4,5]).
?- membruid(X,[1,V,2,X,3,f(X),4,X,5,X]). % si dati ;/Next, pentru a vedea toate solutiile
?- apartineid(3,[1,V,2,X,3,f(X),4,X,5,X]).
*/

/* Conventia din documentatia Prolog-ului:
argumentele precedate de + trebuie furnizate in interogari;
argumentele precedate de - sunt calculate de predicatul respectiv;
argumentele precedate de ? pot avea ambele roluri.
factorial(+N,-F)=true <=> fact(+N,-F)=true <=> factorial-de-cat(-N,+F)=true <=> F=N !
(F este egal cu N factorial).
*/

factorial(0,1).
factorial(N,F) :- N>0, P is N-1, factorial(P,G), F is N*G.

fact(0,1) :- !.
fact(N,F) :- P is N-1, fact(P,G), F is N*G.

factorial-de-cat(0,1).
factorial-de-cat(N,F) :- auxfact(N,F,1,1).

auxfact(1,1,1,1) :- !.
auxfact(_,F,_,Ftemp) :- Ftemp>F, fail.
auxfact(N,F,N,F) :- !.
auxfact(N,F,Ntemp,Ftemp) :- Ftemp<F, S is Ntemp+1, H is S*Ftemp, auxfact(N,F,S,H).

/* Interogati:
?- factorial(5,Cat).
?- fact(5,Cat).
?- factorial-de-cat(Cat,120).
?- factorial-de-cat(Cat,110).
?- factorial-de-cat(Cat,130).
*/

% Sirul lui Fibonacci:

sirfib(0,[0]).
sirfib(1,[1,0]).
sirfib(N,[X,Y,Z|T]) :- N>1, P is N-1, sirfib(P,[Y,Z|T]), X is Y+Z.

fibonacci(N,F) :- sirfib(N,[F|_]).

sirfibonacci(N,L) :- sirfib(N,S), inversa(S,L). % de la cap la coada

% Concatenarea de liste: concat <=> append, predicat predefinit:

concat([],L,L).
concat([H|T],L,[H|M]) :- concat(T,L,M).

% Inversa unei liste: inversa <=> reverse, predicat predefinit:

inversa([],[]).
inversa([H|T],L) :- inversa(T,U), concat(U,[H],L).

/* Predicate predefinite care colecteaza Termenii care satisfac Conditia in ListaTermeni:
fara duplicate: setof(Termen,Conditie,ListaTermeni)
cu duplicate: bagof(Termen,Conditie,ListaTermeni), findall(Termen,Conditie,ListaTermeni).
*/

elimina-duplicate(L,M) :- setof(X, member(X,L), M).

produs-cartezian(L,M,P) :- setof((X,Y), (member(X,L),member(Y,M)), P).

produs-cartezian-liste(L,M,P) :- bagof((X,Y), (member(X,L),member(Y,M)), P).

prod-cart-liste(L,M,P) :- findall((X,Y), (member(X,L),member(Y,M)), P).

/* Interogati:
?- elimina-duplicate([a,1,a,0,1,1],M).
?- produs-cartezian([1,2,3],[a,b],P).
?- produs-cartezian-liste([1,2,3],[a,b],P).
?- prod-cart-liste([1,2,3],[a,b],P).
?- produs-cartezian([1,2,1,3],[a,b],P).
?- produs-cartezian-liste([1,2,1,3],[a,b],P).
?- prod-cart-liste([1,2,1,3],[a,b],P).
?- produs-cartezian([],[a,b],P).
?- produs-cartezian-liste([],[a,b],P).
?- prod-cart-liste([],[a,b],P).
Observati o prima diferenta dintre bagof si findall: cand niciun Termen nu satisface
Conditia, setof si bagof intorc false, in timp ce findall intoarce [].
Uitati inca una: interogati:
?- setof(X, (member(X,[10,20,30]),member(Y,[15,25]),X<Y), L).
?- bagof(X, (member(X,[10,20,30]),member(Y,[15,25]),X<Y), L).
?- findall(X, (member(X,[10,20,30]),member(Y,[15,25]),X<Y), L).
Pentru fiecare valoare posibila a variabilelor din Conditie care nu apar in Termen,
setof si bagof intorc cate o lista separata, spre deosebire de findall.
Cuantificare existentiala pentru variabilele din Conditie care nu apar in Termen,
care este facuta automat de findall:
?- setof(X, Y^(member(X,[10,20,30]),member(Y,[15,25]),X<Y), L).
?- bagof(X, Y^(member(X,[10,20,30]),member(Y,[15,25]),X<Y), L).
*/

/* Sa se determine tripletele de valori booleene pentru enunturile p, q, r
care satisfac urmatoarele enunturi compuse:
enunt1 = [(p=>q) si non r] => [p <=> (q sau r)];
enunt2 = [(p=>q) sau (q <=> non r)] => [(q si r) => non p];
enunt3 = [[p => (q si r)] sau (p<=>q)] <=> [non r <=> (p sau q)]. */

enunt1(P,Q,R) :- implica((implica(P,Q),not(R)),echiv(P,Q;R)).

enunt2(P,Q,R) :- implica(implica(P,Q);echiv(Q,not(R)),implica((Q,R),not(P))).

enunt3(P,Q,R) :- echiv(implica(P,(Q,R));echiv(P,Q),echiv(not(R),P;Q)).

triplete-care-satisfac-enuntul1(P,Q,R) :- gentriplet(P,Q,R), enunt1(P,Q,R).

triplete-care-satisfac-enuntul2(P,Q,R) :- gentriplet(P,Q,R), enunt2(P,Q,R).

triplete-care-satisfac-enuntul3(P,Q,R) :- gentriplet(P,Q,R), enunt3(P,Q,R).

lista-tripletelor-care-satisfac-enuntul1(L) :- setof((P,Q,R),
		triplete-care-satisfac-enuntul1(P,Q,R), L).

lista-tripletelor-care-satisfac-enuntul2(L) :- setof((P,Q,R),
		triplete-care-satisfac-enuntul2(P,Q,R), L).

lista-tripletelor-care-satisfac-enuntul3(L) :- setof((P,Q,R),
		triplete-care-satisfac-enuntul3(P,Q,R), L).

numar-triplete-care-satisfac-enuntul1(N) :- lista-tripletelor-care-satisfac-enuntul1(L),
						length(L,N).

numar-triplete-care-satisfac-enuntul2(N) :- lista-tripletelor-care-satisfac-enuntul2(L),
						length(L,N).

numar-triplete-care-satisfac-enuntul3(N) :- lista-tripletelor-care-satisfac-enuntul3(L),
						length(L,N).

% Varianta:

triplete-care-satisfac-enunt(P,Q,R,Enunt) :- gentriplet(P,Q,R), Termen=..[Enunt,P,Q,R], Termen.

lista-triplete-care-satisfac-enunt(L,Enunt) :- setof((P,Q,R),
		triplete-care-satisfac-enunt(P,Q,R,Enunt), L).

numar-triplete-care-satisfac-enunt(N,Enunt) :- lista-triplete-care-satisfac-enunt(L,Enunt),
						length(L,N).

/* Interogati:
?- lista-triplete-care-satisfac-enunt(L,enunt1).
?- lista-triplete-care-satisfac-enunt(L,enunt2).
?- lista-triplete-care-satisfac-enunt(L,enunt3).
?- numar-triplete-care-satisfac-enunt(L,enunt1).
?- numar-triplete-care-satisfac-enunt(L,enunt2).
?- numar-triplete-care-satisfac-enunt(L,enunt3).
*/



