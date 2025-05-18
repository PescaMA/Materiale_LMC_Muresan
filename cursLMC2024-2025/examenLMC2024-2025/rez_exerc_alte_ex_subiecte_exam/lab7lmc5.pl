implica(P,Q) :- not(P) ; Q.
echiv(P,Q) :- implica(P,Q) , implica(Q,P).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Logica propozitionala clasica:

/* Amintesc din materialul PDF pentru acest laborator ca am notat cu
f:L2->{false,true}, definita prin: f(0)=false, f(1)=true.
Consider o interpretare arbitrara h:V->L2={0,1}.
Fie enunturile fi, psi, hi.
Notez cu: Fi=f(h~(fi)), Psi=f(h~(psi)), Hi=f(h~(hi)).
Cu aceste notatii, enunt(Fi,Psi,Hi) va fi f(h~(alfa)), pentru enuntul alfa 
din exercitiul/pg.8/Seminarul VI, partea a 5-a:
*/

enunt(Fi,Psi,Hi) :- echiv(implica(Fi, not(implica(not(Psi), Hi))),
			(implica(Psi, not(Fi)), implica(Hi, not(Fi)))).

demenunt :- dem(enunt).

/* Demonstratia oricarei proprietati care depinde de 3 valori booleene -
a se vedea mai jos cazul general pentru N valori booleene: */

dem(Proprietate) :- not((member(Fi,[false,true]), member(Psi,[false,true]), 
		member(Hi,[false,true]), write((Fi,Psi,Hi)), nl,
		Termen=..[Proprietate,Fi,Psi,Hi], not(Termen))).

/* Cu notatiile de mai sus, deductia din exercitiul de pe 
verso-ul paginii 1 din Seminarul VI, partea a 4-a: */

deductie(Fi,Psi,Hi) :- implica((Fi, implica(Fi, implica(Psi, Hi)), 
						not(Hi)), not(Psi)).

demdeductie :- dem(deductie).

/* Notand, ca mai sus, cu: P=f(h(p)), Q=f(h(q)), R=f(h(r)), deductia 
formulata in limbaj natural din exercitiul/pg.6/Seminarul VI, partea a 2-a: */

deductialbjnat(P,Q,R) :- implica((implica(not(P),implica(Q,not(R))), 
				implica(not(P),Q), R), P).

demdeductialbjnat :- dem(deductialbjnat).

/* Notand, ca mai sus, cu: A=f(h(a)), B=f(h(b)), C=f(h(c)), enunturile 
rostite de bastinasii A, B, C, respectiv, din exercitiul/pg.1/Seminarul VI, 
partea a 6-a: */

enuntA(_,B,C) :- echiv((B,C), C).
enuntB(A,B,C) :- implica((A,C), not(implica((B,C), A))).
enuntC(A,B,_) :- echiv(not(B), (A;B)).

% Determinarea bastinasilor care spun adevarul si a celor care mint:

bastinasi(A,B,C) :- member(A,[false,true]), member(B,[false,true]), 
	member(C,[false,true]), % write('verific '), write((A,B,C)), nl,
echiv(enuntA(A,B,C),A), echiv(enuntB(A,B,C),B), echiv(enuntC(A,B,C),C).

% Afisarea triburilor din care fac parte bastinasii:

scrietrib(true) :- write(' face parte din tribul Tu').
scrietrib(false) :- write(' face parte din tribul Fa').

triburi(A,B,C) :- bastinasi(A,B,C), 
		write('A'), scrietrib(A), nl,
		write('B'), scrietrib(B), nl,
		write('C'), scrietrib(C), nl.

/* Pentru urmatoarea demonstratie a regulii de deductie din exercitiul/pg.13/
Seminarul VI, partea a 5-a, consider o interpretare arbitrara h:V->L2={0,1} 
care satisface multimea Gama de enunturi, si notez cu: Fi=f(h~(fi)), 
Psi=f(h~(psi)) si Gama=f(h~(gama)): */

regded(Fi,Psi,Gama) :- implica((implica(Fi, Gama), implica(Psi, Gama)), 
					implica((Fi ; Psi), Gama)).

demregded :- dem(regded).

/* Pentru urmatoarea rezolvare semantica pentru exercitiul/pg.23/Seminarul VI,
partea a 5-a, consider o interpretare arbitrara h:V->L2={0,1} si notez cu: 
P=f(h~(p)), Q=f(h~(q)), R=f(h~(r)) si S=f(h~(s)), astfel ca predicatul de mai
jos enunt(P,Q,R,S)=f(h~(fi^psi^hi^gama^p)), cu notatiile din rezolvarea 
acestui exercitiu; acesta este un predicat de aritate 4, deci nu va fi 
confundat de Prolog cu predicatul ternar enunt de mai sus. Folosesc faptul ca 
multimea {fi,psi,hi,gama,p} e consistenta ddaca e satisfiabila ddaca enuntul 
fi^psi^hi^gama^p e satisfiabil. Predicatul zeroar enuntsatisf e satisfacut 
ddaca enuntul fi^psi^hi^gama^p e satisfiabil, iar predicatul zeroar 
enuntnesatisf e satisfacut ddaca enuntul fi^psi^hi^gama^p e nesatisfiabil 
ddaca acest enunt e inconsistent ddaca multimea {fi,psi,hi,gama,p} e 
inconsistenta: */

enunt(P,Q,R,S) :- implica((not(Q),P), not(R)), implica(Q, not(P)), 
			implica(S, R), implica(not(R), S), P.

enuntsatisf :- member(P,[false,true]), member(Q,[false,true]), 
	member(R,[false,true]), member(S,[false,true]), write((P,Q,R,S)), nl,
	enunt(P,Q,R,S).

enuntnesatisf :- not((member(P,[false,true]), member(Q,[false,true]), 
	member(R,[false,true]), member(S,[false,true]), write((P,Q,R,S)), nl,
	enunt(P,Q,R,S))).

% Demonstratie pentru o proprietate depinzand de N valori booleene:

demNvalbool(N,Proprietate) :- not((listaNvalbool(N,Lista), write(Lista), nl,
		Termen=..[Proprietate|Lista], not(Termen))).

/* Test pentru o proprietate depinzand de N valori booleene, i.e. cautarea
unui N-uplu de valori booleene care satisface acea proprietate: */

testNvalbool(N,Proprietate) :- listaNvalbool(N,Lista), write(Lista), nl,
		Termen=..[Proprietate|Lista], Termen.

% Variante pentru demonstratii de mai sus:

demptenunt :- demNvalbool(3,enunt).

demptdeductie :- demNvalbool(3,deductie).

demptdeductialbjnat :- demNvalbool(3,deductialbjnat).

demptregded :- demNvalbool(3,regded).

verifenuntsatisf :- testNvalbool(4,enunt).

negenunt(P,Q,R,S) :- not(enunt(P,Q,R,S)).

verifenuntnesatisf :- demNvalbool(4,negenunt).

condbastinasi(A,B,C) :- echiv(enuntA(A,B,C),A), 
	echiv(enuntB(A,B,C),B), echiv(enuntC(A,B,C),C).

detbastinasi :- testNvalbool(3,condbastinasi).

/* Interogarea:
?- detbastinasi.
cu cerere de solutii multiple cu ";"/"Next", produce raspunsul:
[false,false,false]
[false,false,true]
[false,true,false]
[false,true,true]
[true,false,false]
[true,false,true]
[true,true,false]
true ;
[true,true,true]
false.
Asadar singura solutie pentru condbastinasi(A,B,C) este:
[A,B,C]=[true,true,false], adica: A=B=true, C=false. */

% Generarea unei liste de N valori booleene arbitrare:

listaNvalbool(0,[]).
listaNvalbool(N,[H|T]) :- N>0, member(H,[false,true]),
			K is N-1, listaNvalbool(K,T).

% Exemplu de proprietate care depinde de 4 valori booleene:

propr(A,B,C,D) :- echiv(((not(A) ; B), C), D).

/* Testarea satisfiabilitatii unei proprietati Propr care depinde de N valori 
booleene, de exemplu a unui enunt in componenta caruia apar N variabile
propozitionale; listele de valori booleene care preceda afisarea cate unui 
raspuns true la o interogare cu acest predicat reprezinta N-uplurile de 
valori booleene care satisfac proprietatea Propr: */

satisfNarg(N,Propr) :- listaNvalbool(N,L), write(L), nl,
			T=..[Propr|L], T.

/* Determinarea N-uplurilor de valori booleene care satisfac o proprietate
intr-un al treilea argument al predicatului: */

detNvalbool(N,Propr,L) :- listaNvalbool(N,L), T=..[Propr|L], T.

% Interogati: ?- detNvalbool(4,propr,L).

/* Testarea satisfiabilitatii negatiei unei proprietati Propr care depinde de
N valori booleene, cu acelasi tip de afisare ca pentru predicatul satisfNarg: */

satisfnegNarg(N,Propr) :- listaNvalbool(N,L), write(L), nl,
			T=..[Propr|L], not(T).

% Demonstrarea unei proprietati Propr care depinde de N valori booleene:

demNarg(N,Propr) :- not(satisfnegNarg(N,Propr)).

% Demonstrarea negatiei unei proprietati Propr care depinde de N valori booleene:

demnegNarg(N,Propr) :- not(satisfNarg(N,Propr)).

/* Cu procedeul descris mai sus, rezolvarile Exercitiilor 1-8 din 
suportul teoretic pentru exercitiile de logica clasica din laborator: */ 

proprex1(A,B,C) :- implica(A,implica(implica(B,C),
			implica(implica(C,not(A)),(not(B),not(C))))).

rezex1 :- demNarg(3,proprex1).

proprex2(A,B,C,D,E) :- implica(A,implica(C,B)), implica(A,implica(B,D)),
			implica(E,A), implica(E,C), E, not(D).

rezex2 :- demnegNarg(5,proprex2).

proprex3(P,Q,R,S) :- implica((not(Q),P),not(R)), implica(Q,not(P)), 
			implica(S,R), implica(not(R),S), P.

rezex3 :- demnegNarg(4,proprex3).

proprex4(F,P,G) :- implica((implica(F,G),implica(P,G)),implica((F;P),G)).

rezex4 :- demNarg(3,proprex4).

proprex5(F,P,H) :- implica((implica(F,P),implica((P,H),F),implica(P,H)),
			echiv(F,(P,H))).

rezex5 :- demNarg(3,proprex5).

proprex6(A,B,C) :- implica((implica((A;B),C),implica(not(A),not(C))),
			echiv(A,C)).

rezex6 :- demNarg(3,proprex6).

propr1ex7(A,B,C,D) :- implica(A,B), implica(B,(C,D)), implica(not(B),C),
				implica(C,A), implica(D,not(A)).

rez1ex7 :- demnegNarg(4,propr1ex7).

propr2ex7(A,B,C,D) :- implica(A,B), implica(B,(C,D)), 
			implica(C,A), implica(D,not(A)).

/* Predicate care testeaza daca o lista (instantiata, nu variabila; va 
amintesc ca predicatul binar predefinit =.. nu functioneaza cu variabile in
ambele argumente) L de valori booleene satisface proprietatea Propr, de 
aritate egala cu lungimea lui L, respectiv negatia proprietatii Propr: */

satisf(Propr,L) :- T=..[Propr|L], T.

satisfneg(Propr,L) :- T=..[Propr|L], not(T).

proprmare2ex7ver1(A,B,C,D) :- implica((A;B;C),not(propr2ex7(A,B,C,D))).

proprmare2ex7ver2(A,B,C,D) :- implica((A;B;C),satisfneg(propr2ex7,[A,B,C,D])).

rez2ex7 :- demNarg(4,proprmare2ex7ver1).

altarez2ex7 :- demNarg(4,proprmare2ex7ver2).

% Multiplicarea unei valori Val intr-o lista formata din N copii ale lui Val:

listaNvalegale(0,_,[]).
listaNvalegale(N,Val,[Val|Lista]) :- N>0, K is N-1, 
					listaNvalegale(K,Val,Lista).

% Obtinerea unei liste de N valori booleene egale (toate false sau toate true):

listaNvalboolegale(N,L) :- member(Val,[false,true]), 
			listaNvalegale(N,Val,L).

rez3ex7 :- listaNvalboolegale(4,L), write(L), nl, satisf(propr2ex7,L).

/* Prin tabel semantic, nu aplicand regula rezolutiei, ca in cerinta acestui 
punct (4) al Exercitiului 7; pentru aplicari ale regulii rezolutiei pentru 
forme clauzale, a se vedea MATERIALUL FACULTATIV cu algoritmul Davis-Putnam;
sigur ca este vorba de afisarea pasilor de rezolutie propozitionala pentru
liste de liste de literali ai logicii propozitionale clasice, nu de aplicarea
regulii rezolutiei in logica clasica a predicatelor pentru cazul particular
al rezolutiei SLD (rezolutie selectiva liniara pe clauze definite) care este
efectuata de interpretorul Prolog-ului in maniera backtracking pentru 
rezolvarea oricarei interogari (puteti vedea, orientativ, algoritmul 
Backward Chaining pe care se bazeaza functionarea interpretorului de Prolog
in suportul teoretic pentru intregul laborator din acest semestru; acest
algoritm va fi, insa, studiat la cursul de Programare Logica din anul II): */

rez4ex7 :- demNarg(4,propr2ex7).

proprex8(P,Q) :- P,Q ; not(implica(P,Q)) ; not(implica(Q,P)) ; not(P),not(Q).

rezex8 :- demNarg(2,proprex8).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Rezolvare pentru Exercitiul 9, din logica clasica a predicatelor:

f(a,b).
f(b,c).
f(c,d).
f(d,a).

r([(a,b),(b,c),(c,b),(c,d)]).

/* Pentru fiecare j, predicatul zeroar satisfAenuntj e satisfacut ddaca
structura algebrica A satisface enuntul epsilon j: */

% Predicat unar corespunzator formulei fara cuantificatori alfa:

propr(X) :- f(X,FX), r(R), member((X,FX),R), member((FX,X),R).

satisfAenunt0 :- not((member(X,[a,b,c,d]), not(propr(X)))).

satisfAenunt1 :- member(X,[a,b,c,d]), propr(X), write(X).

% Predicat binar corespunzator formulei fara cuantificatori beta:

propr(X,Y) :- f(X,FX), f(FX,FFX), r(R), (member((Y,FFX),R); member((FX,Y),R)).

satisfAenunt2 :- member(X,[a,b,c,d]), 
		 not((member(Y,[a,b,c,d]), not(propr(X,Y)))), write(X).

satisfAenunt3 :- not((member(X,[a,b,c,d]), member(Y,[a,b,c,d]), not(propr(X,Y)))).

satisfAenunt4 :- not((member(X,[a,b,c,d]), 
		 not((member(Y,[a,b,c,d]), propr(X,Y))))).

satisfAenunt5 :- member(X,[a,b,c,d]), member(Y,[a,b,c,d]), 
		 propr(X,Y), write((X,Y)), nl.

/* Satisfacerea unui enunt cu o singura variabila cuantificata 
universal, respectiv existential: */

enuntovar(univ,Mult,Propr) :- not((member(X,Mult), T=..[Propr,X], not(T))).

enuntovar(exist,Mult,Propr) :- member(X,Mult), T=..[Propr,X], T, write(X), nl.

/* Satisfacerea unui enunt arbitrar in forma prenex, i.e. constand dintr-o
succesiune de cuantificatori urmata de o formula fara cuantificatori avand ca
variabile libere exact pe cele de sub incidenta cuantificatorilor care o 
preceda; pe masura ce aplicam cate un cuantificator, transmitem mai departe 
valoarea curenta a variabilei de sub incidenta acelui cuantificator: */

enuntmmvar([univ],ListaValori,Mult,Propr) :- not((member(X,Mult),
	append(ListaValori,[X],ListaCompletaValori),
	T=..[Propr|ListaCompletaValori], not(T), 
	write(ListaCompletaValori), nl)).
enuntmmvar([exist],ListaValori,Mult,Propr) :- member(X,Mult),
	append(ListaValori,[X],ListaCompletaValori), 
	T=..[Propr|ListaCompletaValori], T, write(ListaCompletaValori), nl.
enuntmmvar([univ,Cuantif|ListaCuantif],ListaValori,Mult,Propr) :- 
	not((member(X,Mult), append(ListaValori,[X],NouaListaValori),
	not(enuntmmvar([Cuantif|ListaCuantif],NouaListaValori,Mult,Propr)))).
enuntmmvar([exist,Cuantif|ListaCuantif],ListaValori,Mult,Propr) :- 
	member(X,Mult), append(ListaValori,[X],NouaListaValori),
	enuntmmvar([Cuantif|ListaCuantif],NouaListaValori,Mult,Propr).	

/* Predicat ternar care il apeleaza pe cel de aritate 4 de mai sus pentru
lista initiala de valori ale variabilelor cuantificate egala cu []: */ 

enuntmmvar(ListaCuantif,Mult,Propr) :- enuntmmvar(ListaCuantif,[],Mult,Propr).

/* Pentru fiecare j, predicatul zeroar satisfAenuntj este echivalent cu
totsatisfAenuntj, cu exceptia afisarii pentru unele valori ale lui j, iar, in
cazul in care j=0 sau j=1, si cu satisfAtotenuntj, cu exceptia afisarii: */

totsatisfAenunt0 :- enuntovar(univ,[a,b,c,d],propr).

totsatisfAenunt1 :- enuntovar(exist,[a,b,c,d],propr).

satisfAtotenunt0 :- enuntmmvar([univ],[a,b,c,d],propr).

satisfAtotenunt1 :- enuntmmvar([exist],[a,b,c,d],propr).

totsatisfAenunt2 :- enuntmmvar([exist,univ],[a,b,c,d],propr).

totsatisfAenunt3 :- enuntmmvar([univ,univ],[a,b,c,d],propr).

totsatisfAenunt4 :- enuntmmvar([univ,exist],[a,b,c,d],propr).

totsatisfAenunt5 :- enuntmmvar([exist,exist],[a,b,c,d],propr).

