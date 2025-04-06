% Vedeti si bazele de cunostinte scrise la lectiile seriei 14.

% are(ioana,OriceFruct).
are(ana,mere). % are(ana,mere) este adevarat: predicatul binar are e satisfacut cu primul argument ana si al doilea argument mere
are(alex,pere). % are(alex,mere) este adevarat
are(ana,Fructe) :- are(alex,Fructe). % are(alex,Fructe) => are(ana,Fructe)
% are(vali,cirese).
% are(ana,cirese) :- are(Cineva,cirese), not(are(Cineva,mere)).

/*   are
    /   \
  ana   mere
     are
    /   \
  alex  pere
     are
    /   \
  ana  Fructe
     are
    /   \
  alex Fructe
Interogati:
?- are(ana,mere).
     are
    /   \
  ana   mere
     are
    /   \
  alex  mere
?- are(ana,pere).
?- are(ana,cirese).
?- are(elena,mere).
?- are(ana,Ce).
?- are(alex,Ce).
?- are(Cine,mere).
?- are(Cine,pere).
?- are(Cine,cirese).
     are
    /   \
  Cine cirese
     are
    /   \
  alex cirese
?- are(elena,Ce).
?- are(Cine,Ce).
     are
    /   \
  Cine  Ce
     are
    /   \
  alex  Ce
Cu predicatul (adica operatorul boolean) "are" definit ca infixat, de precedenta 500
(precedentele sunt opusul prioritatilor: cu cat un operator are precedenta mai mare,
el are prioritatea mai mica; de exemplu, constantele, expresiile incadrate in paranteze,
termenii de forma operator(argumentul1,argumentul2,...,argumentuln) au precedenta 0, deci
prioritatea cea mai mare, intrucat valorile precedentelor sunt numere naturale):
-> baza de cunostinte:

:- op(500,xfx,are).

ana are mere.
alex are pere.
ana are Fructe :- alex are Fructe.

-> interogarile:
?- ana are mere.
?- ana are pere.
?- ana are cirese.
?- elena are mere.
?- ana Ce.
?- alex are Ce.
?- Cine are mere.
?- Cine are pere.
?- Cine are cirese.
?- elena are Ce.
?- Cine are Ce.
*/

determinaCineareCe :- are(Cine,Ce), write(Cine), tab(1), write(are), tab(1), write(Ce).

determinaCineareCefaraafisare :- are(_,_).

/* Interogati:
?- determinaCineareCe.
*/

numaraExemplele(N) :- see('d:/tempwork/exMace.rtf'), citesteExemple(L), length(L,N), seen.

citesteExemple(L) :- read(Termen), (Termen=end_of_file, L=[], ! ;
				citesteExemple(Restul), L=[Termen|Restul]).

varsaListaExemple :- see('d:/tempwork/exMace.rtf'), tell('d:/tempwork/listaExMace.rtf'),
				citesteExemple(L), write(L), told, seen.

prelucreazaListaExemple :- see('d:/tempwork/exMace.rtf'), 
			tell('d:/tempwork/listaExMacePrelucrate.rtf'),
			citesteExemple(L), scriere-lista-exemple(L), told, seen.

scriere-lista-exemple([]).
scriere-lista-exemple([H|T]) :- scriere-exemplu(H), nl, scriere-lista-exemple(T).

scriere-exemplu(interpretation(NumarElemente,_,
	[function(si(_,_),TabelSi),function(v(_,_),TabelSau),
	function(complement(_),TabelComplement)])) :- write('numarul de elemente = '),
	write(NumarElemente), nl, write('conjunctia: '), write(TabelSi), nl,
	write('disjunctia: '), write(TabelSau), nl,
	write('complementul: '), write(TabelComplement), nl.

% Predicat echivalent cu predicatul predefinit length:

lungime([],0).
lungime([_|T],N) :- lungime(T,K), N is K+1.

numarcf(Nr,NrCf) :- integer(Nr),
	(Nr>=0, !, nrcifre(Nr,NrCf) ; AbsNr is -Nr, nrcifre(AbsNr,NrCf)).

% Varianta:

numarcifre(Nr,NrCf) :- integer(Nr), Nr>=0, nrcifre(Nr,NrCf).
numarcifre(Nr,NrCf) :- integer(Nr), Nr<0, AbsNr is -Nr, nrcifre(AbsNr,NrCf).

nrcifre(Nr,1) :- Nr<10, !.
nrcifre(Nr,NrCf) :- N is Nr div 10, nrcifre(N,NC), NrCf is NC+1.

/* scrie-matrice-ca-tabel(NumarLinii,NumarColoane,Lista),
	scrielinie(NumarColoane,Lista,CoadaListei)
Doresc ca interogarea:
?- scrie-matrice-ca-tabel(2,3,[1,2,3,4,5,6]).
sa produca afisarea:
1 2 3
4 5 6
iar interogarea:
?- scrie-matrice-ca-tabel(2,3,[1,2,3,4,5]).
sa produca afisarea:
1 2 3
4 5
iar interogarea:
?- scrie-matrice-ca-tabel(2,3,[1,2,3,4,5,6,7]).
sa produca afisarea:
1 2 3
4 5 6
*/

scrie-matrice-ca-tabel(_,_,[]) :- !.
scrie-matrice-ca-tabel(0,_,_) :- nl, !.
scrie-matrice-ca-tabel(NrLinii,NrCol,Lista) :- scrielinie(NrCol,Lista,Coada),
		NL is NrLinii-1, scrie-matrice-ca-tabel(NL,NrCol,Coada).

scrielinie(_,[],[]) :- nl, !. 
scrielinie(0,Lista,Lista) :- nl, !.
scrielinie(Nr,[H|T],Coada) :- write(H), tab(1), P is Nr-1, scrielinie(P,T,Coada).

scrie-matrice-ca-tabel-dreapta(_,NrCol,Lista) :- length(Lista,N), N<NrCol, !,
	K is 2*(NrCol-N)+1, tab(K), scrielinie(NrCol,Lista,_).
scrie-matrice-ca-tabel-dreapta(_,_,[]) :- !.
scrie-matrice-ca-tabel-dreapta(0,_,_) :- nl, !.
scrie-matrice-ca-tabel-dreapta(NrLinii,NrCol,Lista) :- scrielinie(NrCol,Lista,Coada),
		NL is NrLinii-1, scrie-matrice-ca-tabel-dreapta(NL,NrCol,Coada).

prelucreazaAltfelListaExemple :- see('d:/tempwork/exMace.rtf'), 
			tell('d:/tempwork/listaExMacePrelucrateAltfel.rtf'),
			citesteExemple(L), scriere-altfel-lista-exemple(L), told, seen.

scriere-altfel-lista-exemple([]).
scriere-altfel-lista-exemple([H|T]) :- scriere-altfel-exemplu(H), nl,
				scriere-altfel-lista-exemple(T).

scriere-altfel-exemplu(interpretation(NumarElemente,_,
	[function(si(_,_),TabelSi),function(v(_,_),TabelSau),
	function(complement(_),TabelComplement)])) :- write('numarul de elemente = '),
write(NumarElemente), nl, write('conjunctia:'), nl, scrietabel(NumarElemente,TabelSi), nl,
	write('disjunctia:'), nl, scrietabel(NumarElemente,TabelSau), nl,
write('complementul: '), scrie-matrice-ca-tabel(1,NumarElemente,TabelComplement), nl.

scrietabel(NumarElemente,Tabel) :- scrie-matrice-ca-tabel(NumarElemente,NumarElemente,Tabel).

nrLiniiMemorat(3).
nrColMemorat(4).
listaMemorata([1,2,3,4,5,6,7,8,9]).

listaCalculata(N,L) :- listaCalc(N,M), reverse(M,L).

listaCalc(0,[]) :- !.
listaCalc(N,[N|L]) :- P is N-1, listaCalc(P,L).

fori1nafisi(N) :- integer(N), N>=0, auxfor(N).

auxfor(0) :- !.
auxfor(N) :- P is N-1, auxfor(P), tab(1), write(N).

/* factorial(Nr,Nr !); factorial(-Nr,+NrFactorial): conventie privind reprezentarea
argumentelor predicatelor din documentatia online a limbajului Prolog, de pe site-ul
SWI-Prolog-ului:
argumentele precedate de "-" trebuie furnizate in interogari;
argumentele precedate de "+" sunt calculate de predicatele respective in interogari;
argumentele precedate de "?" pot avea ambele roluri de mai sus. */

factorial(0,1) :- !.
factorial(Nr,Fact) :- N is Nr-1, factorial(N,F), Fact is F*Nr.

fori1nafis(N,OperatorUnar) :- integer(N), N>=0, auxforafis(N,OperatorUnar).

auxforafis(0,_) :- !.
auxforafis(N,OperatorUnar) :- P is N-1, auxforafis(P,OperatorUnar), tab(1),
		Termen=..[OperatorUnar,N], write(Termen).

afisarestelute(0) :- !.
afisarestelute(N) :- P is N-1, write('* '), afisarestelute(P).

fori1nexec(N,PredicatUnar) :- integer(N), N>=0, auxforexec(N,PredicatUnar).

auxforexec(0,_) :- !.
auxforexec(N,PredicatUnar) :- P is N-1, auxforexec(P,PredicatUnar), nl,
		Termen=..[PredicatUnar,N], Termen.

/* Interogarea:
?- bradut(5).
produce afisarea:
    * 
   * * 
  * * * 
 * * * * 
* * * * * 
*/

bradut(N) :- brad(N,0).

brad(0,_) :- !.
brad(N,K) :- P is N-1, S is K+1, brad(P,S), nl, tab(K), afisarestelute(N).

% Predicat echivalent cu predicatul ternar predefinit append: concat(?L,?M,?C)

concat([],L,L).
concat([H|T],L,[H|M]) :- concat(T,L,M).

% Predicat echivalent cu predicatul binar predefinit reverse: inversa(?L,?I)

inversa([],[]) :- !.
inversa([H|T],L) :- inversa(T,U), concat(U,[H],L).

/* Predicate ternare predefinite (vedeti mai sus conventia din documentatia Progului
privind scrierea argumentelor predicatelor):
setof(-Termen, -Conditie, +MultimeaTermenilorCareSatisfacConditia)
bagof(-Termen, -Conditie, +ListaTermenilorCareSatisfacConditia)
findall(-Termen, -Conditie, +ListaTermenilorCareSatisfacConditia)
Prin multime inteleg lista fara duplicate.
Interogati:
?- setof((Ce,CuCe), concat(Ce,CuCe,[1,2,3]), L).
?- bagof((Ce,CuCe), concat(Ce,CuCe,[1,2,3]), L).
?- findall((Ce,CuCe), concat(Ce,CuCe,[1,2,3]), L).
*/

elimdupllistanevida(L,M) :- setof(X, member(X,L), M).

prodcart(L,M,P) :- setof((X,Y), (member(X,L), member(Y,M)), P).

prodcartlist(L,M,P) :- bagof((X,Y), (member(X,L), member(Y,M)), P).

prodcartliste(L,M,P) :- findall((X,Y), (member(X,L), member(Y,M)), P).

% Eliminarea duplicatelor dintr-o lista (vida sau nevida):

elimdup([],[]).
elimdup([H|T],M) :- member(H,T), !, elimdup(T,M).
elimdup([H|T],[H|M]) :- elimdup(T,M).

% Produsul cartezian de multimi vide sau nevide:

prodcartmult(L,M,Prod) :- findall((X,Y), (member(X,L), member(Y,M)), P), elimdup(P,Prod).

% Predicat echivalent cu predicatul predefinit member:

membru(_,[]) :- fail. % fapt echivalent cu aceasta regula: not(membru(_,[])).
membru(H,[H|_]).
membru(X,[_|T]) :- membru(X,T).

apartine(_,[]) :- fail. % fapt echivalent cu aceasta regula: not(apartine(_,[])).
apartine(H,[H|_]) :- !.
apartine(X,[_|T]) :- apartine(X,T).

% Predicat echivalent cu membru (si cu member):

memb(_,[]) :- fail.
memb(X,[H|_]) :- X=H.
memb(X,[_|T]) :- memb(X,T).

% Predicat echivalent cu apartine:

apart(_,[]) :- fail.
apart(X,[H|_]) :- X=H, !.
apart(X,[_|T]) :- apart(X,T).

% Cu literal identitate in loc de unificare:

membrulitid(_,[]) :- fail.
membrulitid(X,[H|_]) :- X==H.
membrulitid(X,[_|T]) :- membrulitid(X,T).

apartinelitid(_,[]) :- fail.
apartinelitid(X,[H|_]) :- X==H, !.
apartinelitid(X,[_|T]) :- apartinelitid(X,T).

/* In logica clasica singurele valori de adevar sunt fals si adevarat, si fals=/=adevarat.
Asadar toate enunturile la care ne vom referi vor fi fie false, fie adevarate, dar
niciodata ambele.
Fie p, q, r enunturi (propozitii).
Conectorul logic unar, anume negatia (non sau not), il vom considera mai prioritar decat
cei binari: sau, si, =>, <=>, xor etc.. Asadar enuntul non p sau q este echivalent cu
(non p) sau q si nu cu enuntul: non (p sau q).
Conectorii logici predefiniti in Prolog:
si (conjunctia): ","
sau (disjunctia): ";"
non (negatia): "not" sau "\+"
Implicatia o putem defini prin: (p=>q) <=> (non p sau q).
Vom demonstra distributivitatea disjunctiei fata de conjunctie:
[p sau (q si r)] <=> [(p sau q) si (p sau r)]
Aceasta e echivalenta cu distributivitatea reuniunii fata de intersectie:
fie A, B, C multimi arbitrare, fixate; fie x arbitrar, fixat.
Notam reuniunea cu U si intersectia cu ^.
Distributivitatea reuniunii fata de intersectie: A U (B ^ C) = (A U B) ^ (A U C).
Aceasta egalitate este echivalenta cu:
(oricare ar fi y)(y apartine lui A U (B ^ C) <=> y apartine lui (A U B) ^ (A U C)).
Asadar, pentru a demonstra ca A U (B ^ C) = (A U B) ^ (A U C), este suficient sa
demonstram, pentru x arbitrar:
x apartine lui A U (B ^ C) <=> x apartine lui (A U B) ^ (A U C).
Consideram variabilele in Prolog A, B, C, care vor reprezenta proprietatile a, b, c,
respectiv, unde:
a (reprezentata in Prolog de variabila A): x apartine lui A
b (reprezentata in Prolog de variabila B): x apartine lui B
c (reprezentata in Prolog de variabila C): x apartine lui C
Conform definitiei (din acest cadru naiv a) reuniunii si intersectiei de multimi, avem
proprietatile:
[x apartine lui A U (B ^ C)] <=> [a sau (b si c)]
[x apartine lui (A U B) ^ (A U C)] <=> [(a sau b) si (a sau c)]
Avem de demonstrat exact distributivitatea disjunctiei fata de conjunctie aplicata
proprietatilor a, b, c: [a sau (b si c)] <=> [(a sau b) si (a sau c)]. */

implica(P,Q) :- not(P) ; Q. /* echivalent cu:
   implica(P,Q) :- not(P).
   implica(P,Q) :- Q.
*/

echiv(P,Q) :- implica(P,Q), implica(Q,P).

distribreunfdinters(A,B,C) :- echiv(A;(B,C),((A;B),(A;C))).

distribreunfdinters :- not((member(A,[false,true]), member(B,[false,true]),
	member(C,[false,true]), write((A,B,C)), nl, not(distribreunfdinters(A,B,C)))).

/* Distributivitatea intersectiei fata de reuniune: A ^ (B U C) = (A ^ B) U (A ^ C),
se transcrie in distributivitatea conjunctiei fata de disjunctie:
[a si (b sau c)] <=> [(a si b) sau (a si c)]. */

distribintersfdreun(A,B,C) :- echiv((A,(B;C)),(A,B;A,C)).

distribintersfdreun :- not((member(A,[false,true]), member(B,[false,true]),
	member(C,[false,true]), write((A,B,C)), nl, not(distribintersfdreun(A,B,C)))).

/* A este inclus in B <=> (oricare ar fi y)(y apartine lui A => y apartine lui B),
asadar incluziunea lui A in B se transcrie in: a => b.
Tranzitivitatea incluziunii: A inclus in B inclus in C => A inclus in C, se transcrie
in tranzitivitatea implicatiei: [(a => b) si (b => c)] => (a => c), sau, scris
prescurtat: (a => b => c) => (a => c). */

tranzimplic(A,B,C) :- implica((implica(A,B),implica(B,C)),implica(A,C)).

tranzimplic :- not((member(A,[false,true]), member(B,[false,true]), member(C,[false,true]),
		write((A,B,C)), nl, not(tranzimplic(A,B,C)))).

/* Proprietatea x apartine multimii vide este falsa.
Sa demonstram ca singura parte a multimii vide este multimea vida.
Reprezentam incluziunea nestricta intre multimi prin <=.
Dupa cum am vazut, acest lucru este echivalent cu faptul ca:
(oricare ar fi multimea M)(M<=multimea vida <=> M=multimea vida).
Asadar acest lucru se transcrie in: A<=multimea vida <=> A=multimea vida,
asadar in: (a => false) <=> (a <=> false). */

partimultvide(A) :- echiv(implica(A,false),echiv(A,false)).

partimultvide :- not((member(A,[false,true]), write(A), nl, not(partimultvide(A)))).
