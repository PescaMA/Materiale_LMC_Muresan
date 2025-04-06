/* Variabilele care apar intr-un fapt sau in membrul stang al unei reguli sunt
cuantificate universal: pentru orice P, Q, au loc: */

implica(P,Q) :- not(P);Q.
echiv(P,Q) :- implica(P,Q), implica(Q,P).

/* Sa demonstram principiul dublei negatii: non non p <=> p.
Amintesc ca lucram numai cu enunturi care sunt fie false, fie adevarate, si nu pot fi
simultan false si adevarate: in logica clasica exista numai doua valori de adevar:
{fals,adevarat}, si ele sunt distincte: fals=/=adevarat (=/= nu este un predicat in Prolog,
doar am reprezentat nonegalitatea cu acest simbol, si voi mai proceda astfel in comentarii).
Amintesc si ca am facut conventia ca (in scrierea curenta, matematica, nu ma refer acum la
Prolog) non, conectorul logic unar, sa fie considerat mai prioritar decat cei binari:
si, sau, =>, <=>, xor etc., astfel ca enuntul (non p sau q) este echivalent cu
[(non p) sau q], nu cu enuntul non(p sau q). */

demgresitadublaneg :- member(P,[false,true]), echiv(not(not(P)),P).

/* Variabilele care apar intr-o interogare (i.e. intr-o clauza scop) sau numai in membrul
drept al unei reguli, nu si in membrul ei stang, sunt cuantificate existential, asadar 
fiecare dintre interogarile urmatoare:
?- member(P,[false,true]), echiv(not(not(P)),P).
?- demgresitadublaneg.
semnifica: exista P in lista [false,true] a valorilor de adevar pentru logica clasica
care satisface echiv(not(not(P)),P)?
Pentru a demonstra principiul dublei negatii (non non p <=> p), ne folosim de faptul ca 
Prolog-ul satisface o negatie incercand mai intai sa satisfaca argumentul sau, si de 
negarea enunturilor cuantificate: orice P din in lista [false,true] satisface
echiv(not(not(P)),P) ddaca nu exista P in lista [false,true] care sa nu satisfaca
echiv(not(not(P)),P), i.e. nu exista P in lista [false,true] care sa satisfaca negatia lui
echiv(not(not(P)),P): */

demcorectadublaneg :- not((member(P,[false,true]), not(echiv(not(not(P)),P)))).

% Sau, cu verificarea faptului ca Prolog-ul testeaza ambele valori booleene:

demdublaneg :- not((member(P,[false,true]), write(P), nl, not(echiv(not(not(P)),P)))).

/* Interogati:
?- demcorectadublaneg.
?- demdublaneg.
Desigur, a trebuit sa incadrez argumentul primului not din regula de definitie a
predicatului zeroar demcorectadublaneg intr-o pereche suplimentara de paranteze, pentru ca
Prolog-ul sa recunoasca virgula dintre member(P,[false,true]) si not(echiv(not(not(P)),P))
ca si conjunctie; altfel ar fi crezut ca aceasta virgula ar fi separator de argumente si ca
as fi folosit un predicat binar not in locul celui unar predefinit.
La fel, argumentul primului not din regula de definitie a predicatului zeroar demdublaneg
a trebuit incadrat intr-o pereche suplimentara de paranteze, pentru ca Prolog-ul sa 
recunoasca virgulele dintre member(P,[false,true]), write(P), nl, not(echiv(not(not(P)),P))
ca si conjunctii, nu separatori de argumente, intrucat predicatul predefinit not este unar,
nu de aritate 4. */

% Sa demonstram principiul reduderii la absurd: (p=>q) <=> (non q => non p):

demcorectaredabs :- not((member(P,[false,true]), member(Q,[false,true]),
		not(echiv(implica(P,Q),implica(not(Q),not(P)))))).

% Sau, cu verificarea faptului ca Prolog-ul testeaza toate perechile de valori booleene:

demredabs :- not((member(P,[false,true]), member(Q,[false,true]), write((P,Q)), nl,
		not(echiv(implica(P,Q),implica(not(Q),not(P)))))).

/* Predicatul predefinit write este unar, asa ca am avut nevoie de o pereche suplimentara
de paranteze care sa-i incadreze argumentul dat de perechea (P,Q).
Interogati:
?- demcorectaredabs.
?- demredabs.
*/

/* Sa demonstram ca negatia unei disjunctii este echivalenta cu conjunctia negatiilor:
non(p sau q) <=> (non p si non q)
iar negatia unei conjunctii este echivalenta cu disjunctia negatiilor:
non(p si q) <=> (non p sau non q)
Atentie la conjunctiile care trebuie incadrate in paranteze, ca mai sus! */

demnegdisj :- not((member(P,[false,true]), member(Q,[false,true]), write((P,Q)), nl,
		not(echiv(not(P;Q),(not(P),not(Q)))))).

demnegconj :- not((member(P,[false,true]), member(Q,[false,true]), write((P,Q)), nl,
		not(echiv(not((P,Q)),not(P);not(Q))))).

% Sa demonstram tranzitivitatea implicatiei: [(p=>q) si (q=>r)] => (p=>r):

demtranzimplic :- not((member(P,[false,true]), member(Q,[false,true]), member(R,[false,true]),
	 write((P,Q,R)), nl, not(implica((implica(P,Q),implica(Q,R)),implica(P,R))))).

/* Interogati:
?- setof(X, (member(Y,[0,5]), member(Z,[10,100]), X is Y*Z), L).
?- bagof(X, (member(Y,[0,5]), member(Z,[10,100]), X is Y*Z), L).
Pentru a determina lista L a elementelor X egale cu valoarea expresiei aritmetice Y*Z
pentru Y element al listei [0,5] si Z element al listei [10,100], interogam astfel:
?- findall(X, (member(Y,[0,5]), member(Z,[10,100]), X is Y*Z), L).
sau astfel: care e lista elementelor X pentru care exista un element Y in lista [0,5] si un
element Z in lista [10,100] astfel incat X este egal cu valoarea expresiei aritmetice Y*Z:
?- bagof(X, (Y,Z)^(member(Y,[0,5]), member(Z,[10,100]), X is Y*Z), L).
Pentru a determina multimea L a elementelor X egale cu valoarea expresiei aritmetice Y*Z
pentru Y element al listei [0,5] si Z element al listei [10,100], interogam astfel: care 
e multimea elementelor X pentru care exista un element Y in lista [0,5] si un element Z
in lista [10,100] astfel incat X este egal cu valoarea expresiei aritmetice Y*Z:
?- setof(X, (Y,Z)^(member(Y,[0,5]), member(Z,[10,100]), X is Y*Z), L).
Interogati:
?- setof(Y, (member(X,[0,5]), member(Y,[0,10]), member(Z,[0,100]), X=<Y, Y=<Z), L).
?- bagof(Y, (member(X,[0,5]), member(Y,[0,10]), member(Z,[0,100]), X=<Y, Y=<Z), L).
?- findall(Y, (member(X,[0,5]), member(Y,[0,10]), member(Z,[0,100]), X=<Y, Y=<Z), L).
?- setof(Y, (X,Z)^(member(X,[0,5]), member(Y,[0,10]), member(Z,[0,100]), X=<Y, Y=<Z), L).
?- bagof(Y, (X,Z)^(member(X,[0,5]), member(Y,[0,10]), member(Z,[0,100]), X=<Y, Y=<Z), L).
Interogati:
?- setof(Y, (member(X,[0,5]), member(Y,[1,2,3,4,5,6,7,8,9,10]), member(Z,[2,7]), X=<Y, Y=<Z), L).
?- bagof(Y, (member(X,[0,5]), member(Y,[1,2,3,4,5,6,7,8,9,10]), member(Z,[2,7]), X=<Y, Y=<Z), L).
?- findall(Y, (member(X,[0,5]), member(Y,[1,2,3,4,5,6,7,8,9,10]), member(Z,[2,7]), X=<Y, Y=<Z), L), write(L).
?- setof(Y, (X,Z)^(member(X,[0,5]), member(Y,[1,2,3,4,5,6,7,8,9,10]), member(Z,[2,7]), X=<Y, Y=<Z), L).
?- bagof(Y, (X,Z)^(member(X,[0,5]), member(Y,[1,2,3,4,5,6,7,8,9,10]), member(Z,[2,7]), X=<Y, Y=<Z), L), write(L).
In ultima si antepenultima interogare de mai sus (interogari echivalente) am cerut explicit
afisarea listei L, pentru ca lista respectiva este suficient de lunga pentru ca Prolog-ul
sa o afiseze trunchiat ca valoare de variabila (calculata de primul predicat din acele
scopuri compuse: findall(...), respectiv bagof(...)). */

% Putem folosi urmatorul predicat pentru "liniarizarea" unei liste de liste?

liniarizare-partiala1nivel(LL,L) :- findall(X, (member(M,LL), member(X,M)), L).

/* Da, pentru liste care contin numai liste, si pentru un singur nivel de liste in liste:
?- liniarizare-partiala1nivel([[],[1,2,3],[a,b],[],[f(a)]],L).
?- liniarizare-partiala1nivel([[],[1,2,3],[X,Y],[],[f(X)]],L).
Din pacate, variabilele X,Y sunt inlocuite de Prolog cu variabile temporare.
Dar atentie la aceasta interogare:
?- liniarizare-partiala1nivel([[],a,[1,2,f([1,2,3],g(X,[X]))],b,h(a,b),[X,[1,2],[[a]]],c,[[]],[f(X)]],L), write(L).
E mai usor de urmarit daca inlocuim variabila X cu constanta x:
?- liniarizare-partiala1nivel([[],a,[1,2,f([1,2,3],g(x,[x]))],b,h(a,b),[x,[1,2],[[a]]],c,[[]],[f(x)]],L), write(L).
Observati ca s-a "liniarizat" un singur nivel (listele care sunt membri de liste care sunt
membri ai listei au fost lasate ca atare), iar elementele care nu sunt liste ale listei au
fost sterse.
Cum putem face "liniarizare" completa si fara stergerea elementelor care nu sunt liste?
Predicatul unar predefinit is_list determina daca argumentul sau e lista. */

liniarizare([],[]).
liniarizare([H|T],L) :- is_list(H), !, liniarizare(H,L1), liniarizare(T,L2), append(L1,L2,L).
liniarizare([H|T],[H|L]) :- liniarizare(T,L).

/* Interogati:
?- liniarizare([[],a,[1,2,f([1,2,3],g(x,[x]))],b,h(a,b),[x,[1,2],[[a]]],c,[[]],[f(x)]],L), write(L).
*/

% Predicat echivalent cu predicatul predefinit is_list:

e-lista(V) :- var(V), !, fail.
e-lista([]).
e-lista([_|T]) :- e-lista(T).

% Cum putem liniariza inclusiv listele care apar ca argumente in termeni care nu sunt liste?

liniarizare-completa(V,V) :- var(V), !.
liniarizare-completa([],[]) :- !.
liniarizare-completa([H|T],L) :- is_list(H), !, liniarizare-completa(H,L1),
			liniarizare-completa(T,L2), append(L1,L2,L).
liniarizare-completa([H|T],[HL|TL]) :- liniarizare-completa(H,HL), !,
				liniarizare-completa(T,TL).
liniarizare-completa(Termen,Termen) :- Termen=..[_], !.
liniarizare-completa(Termen,Term) :- Termen=..[Op|LArg], liniarizare-completa(LArg,L),
					Term=..[Op|L].

/* Interogati:
?- liniarizare-completa([[],a,[1,2,f([1,2,3],g(x,[x]))],b,h(a,b),[x,[1,2],[[a]]],c,[[]],[f(x)]],L), write(L).
?- liniarizare-completa([[],a,[1,2,f([1,2,3],g(X,[X]))],b,h(a,b),[X,[1,2],[[a]]],c,[[]],[f(X)]],L), write(L).
*/

/* Amintesc ca, pentru satisfacerea fiecarui scop, Prolog-ul testeaza clauzele din baza de
cunostinte (fisierul .pl) de sus in jos. Exemplu in care interschimbarea clauzelor de
definitie ale unui predicat produce eroare: calculul factorialului: */

factorial(0,1) :- !.
factorial(N,F) :- P is N-1, factorial(P,G), F is G*N.

% versus:

fact(N,F) :- P is N-1, fact(P,G), F is G*N.
fact(0,1) :- !.

/* Interogati:
?- factorial(4,CatE4Factorial).
?- fact(4,Cat).
La a doua interogare tastati la un moment dat a (abort), pentru a intrerupe executia.
Putem da trace pentru a vedea pasii fiecarei executii, dar, pentru a-i urmari mai usor,
sa adaugam o serie de afisari la definitiile predicatelor de mai sus: */

factorial-cu-afisare(0,1) :- !.
factorial-cu-afisare(N,F) :- write('Calculez '), write(N), write(' factorial:'), nl,
	P is N-1, factorial-cu-afisare(P,G), write(P), write('!='), write(G), nl, F is G*N.

% versus:

fact-cu-afis(N,F) :- write('Calculez '), write(N), write(' factorial:'), nl,
	P is N-1, fact-cu-afis(P,G), write(P), write('!='), write(G), nl, F is G*N.
fact-cu-afis(0,1) :- !.

/* Interogati:
?- factorial-cu-afisare(4,_4factorial).
?- fact-cu-afis(4,Cat).
La a doua interogare, inchideti fereastra interpretorului de Prolog cand va plictisiti sa
urmariti executia. */


