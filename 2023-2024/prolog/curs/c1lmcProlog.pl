% Comentariu pe un rand.
/* Comentariu pe
	mai multe
	randuri. */

% Conjunctie: ,
% Disjunctie: ;

% Variabilele incep cu litera mare sau underscore.
% Ce incepe cu litera mica e constanta sau operator cu argumente, folosit in termeni compusi.

are(ana,mere).
are(ana,pere).
are(ionel,mere).
are(vali,Fructe) :- are(ana,Fructe), are(ionel,Fructe).
are(vera,Fructe) :- are(ana,Fructe); are(ionel,Fructe).

/* Interogati:
?- are(vali,Ce).
?- are(vera,Ce).
?- are(Cine,Ce).
*/

/* Liste in Prolog:
lista vida: []
lista nevida: [Head|Tail]
Operatorul [|] este binar.
Primul sau argument, Head, este capul listei, i.e. primul element din lista.
Al doilea argument al sau, Tail, este coada listei, care este 
	tot o lista: lista restului de elemente din lista.
A se vedea in suportul pentru laborator alte scrieri pentru liste:
 enumerarea intre [] a tuturor elementelor separate prin virgula;
 enumerarea intre [] a primelor cateva elemente separate prin virgula, apoi |, apoi coada listei.
*/

/* Predicat predefinit: =..
Se foloseste sub forma: Termen=..[OperatorDominantTermen|ListaArgumenteOperatorDominantTermen]
Interogati:
?- ct=..L.
?- ct=..[Op|LA].
?- f(X,10,g(c,V))=..L.
?- f(X,10,g(c,V))=..[Op|LA].
?- T=..[ct].
?- T=..[f,X,10,g(c,V)].
?- T=..L.
?- [1,2,3]=..L.
?- [1,2,3]=..[Op|LA].
?- [2,3]=..[Op|LA].
?- [3]=..[Op|LA].
?- []=..[Op|LA].
*/

/* Unificare: =
Unificare cu testarea ocurentelor (i.e. aparitiilor) variabilelor in termeni: unify_with_occurs_check
Calcul de expresie aritmetica: is
Interogati:
?- X=10.
?- X=10+1.
?- X=2573**10000.
?- X is 10+1.
?- X is 2573**10000.
?- X is 2573**P.
?- X=2573**P.
*/

lung([],0).
lung([_|T],N) :- lung(T,K), N=K+1.

lungime([],0).
lungime([_|T],N) :- lungime(T,K), N is K+1.

/* Interogati:
?- lung([1,2,3,4,5],N).
?- lungime([1,2,3,4,5],N).
*/

% Predicat predefinit echivalent cu lungime: length.

nrcifre(Nr,1) :- Nr<10.
nrcifre(Nr,NC) :- Nr>=10, N is Nr div 10, nrcifre(N,NCf), NC is NCf+1.

numarcifre(Nr,NC) :- integer(Nr), (Nr>=0, nrcifre(Nr,NC); Nr<0, N is -Nr, nrcifre(N,NC)).

% Echivalent, cu predicatul predefinit cut (!), care taie backtracking-ul:

nrulcifre(Nr,1) :- Nr<10, !.
nrulcifre(Nr,NC) :- N is Nr div 10, nrulcifre(N,NCf), NC is NCf+1.

numarulcifre(Nr,NC) :- integer(Nr), (Nr>=0, !, nrulcifre(Nr,NC); N is -Nr, nrulcifre(N,NC)).

/* Interogati:
?- numarcifre(102,NC).
?- numarulcifre(102,NC).
?- numarcifre(-102,NC).
?- numarulcifre(-102,NC).
?- numarcifre(0,NC).
?- Nr is 2573**10000, numarcifre(Nr,NC).
?- numarcifre(2573**10000,NC).
*/

stelute(0).
stelute(N) :- N>0, write('* '), P is N-1, stelute(P).

linie(K,N) :- tab(K), stelute(N).

bradut(_,0).
bradut(K,N) :- N>0, S is K+1, P is N-1, bradut(S,P), nl, linie(K,N).

brad(N) :- bradut(0,N).

% Putem pune intr-un fisier un output mare (told inchide fisierul deschis pentru scriere):

bradmare(N) :- tell('d:/tempwork/bradmare.txt'), brad(N), told.

/* Interogati:
?- bradmare(100).
Vedeti output-ul in fisierul bradmare.txt din folderul tempwork de pe drive-ul d.
*/



