/* Vom folosi predicatele din baza de cunostinte c2lmcID2prolog.pl, asadar o includem aici,
plasand-o in acelasi folder cu aceasta baza de cunostinte si folosind urmatoarea directiva,
care poate fi modificata pentru includerea unor baze de cunostinte din alte foldere, cu
sintaxa pentru incarcarea bazelor de cunostinte in interpretorul de Prolog desktop: */

:- [c2lmcID2prolog].

/* Predicatul poset(+MultElem,+Succ,-Ord) calculeaza relatia de ordine Ord a unui
poset finit cu multimea suport MultElem si relatia de succesiune Succ: */

poset(A,Succ,Ord) :- orddinsucc(Succ,A,Ord).

% Lanturile cu exact 2, respectiv 4 elemente:

lant2([0,1],Ord) :- poset([0,1],[(0,1)],Ord).

lant4([0,a,b,1],Ord) :- poset([0,a,b,1],[(0,a),(a,b),(b,1)],Ord).

/* Exemplul de poset din curs cu diagrama Hasse in forma de stea cu 3 colturi, unul jos
(minimul posetului) si doua sus (elementele maximale ale acestui poset): */

exdincurs([a,b,c,d],Ord) :- poset([a,b,c,d],[(a,b),(b,c),(b,d)],Ord).

% Rombul, diamantul, respectiv pentagonul:

romb([0,a,b,1],Ord) :- poset([0,a,b,1],[(0,a),(0,b),(a,1),(b,1)],Ord).

m3([0,a,b,c,1],Ord) :- poset([0,a,b,c,1],[(0,a),(0,b),(0,c),(a,1),(b,1),(c,1)],Ord).

n5([0,x,y,z,1],Ord) :- poset([0,x,y,z,1],[(0,x),(0,y),(y,z),(x,1),(z,1)],Ord).

% Suma ordinala a rombului cu lantul cu (exact) 2 elemente:

rombplusL2([0,a,b,c,1],Ord) :- poset([0,a,b,c,1],[(0,a),(0,b),(a,c),(b,c),(c,1)],Ord).

/* Exemplul din curs de poset marginit care nu e latice cu diagrama Hasse in forma de 
hexagon cu doua diagonale: */

hexagoncudiag(A,Ord) :- A=[0,a,b,c,d,1], poset(A,[(0,a),(0,b),(a,c),(a,d),(b,c),(b,d),(c,1),(d,1)],Ord).

/* Sa scriem si un predicat pentru afisarea unei liste de poseturi cu multimi suport 
arbitrare (nu toate cu aceeasi multime suport, ca in cazul predicatului afisareposeturi din
baza de cunostinte c2lmcID2prolog.pl): */

afisposeturi([]).
afisposeturi([(P,Ord)|T]) :- afisareposet(P,Ord), nl, write('----------------'), nl,
				afisposeturi(T).

/* Interogati:
?- lant2(L2,OrdL2), lant4(L4,OrdL4), exdincurs(A,OrdA), romb(R,OrdR), m3(M3,OrdM3), n5(N5,OrdN5), rombplusL2(RsumL2,OrdRsumL2), hexagoncudiag(H,OrdH), afisposeturi([(L2,OrdL2),(L4,OrdL4),(A,OrdA),(R,OrdR),(M3,OrdM3),(N5,OrdN5),(RsumL2,OrdRsumL2),(H,OrdH)]).
*/

/* In predicatele urmatoare S va fi o submultime a (multimii suport P a) unui poset cu
multimea suport P si relatia de ordine Ord. Predicatele de mai jos care determina elemente
intorc false daca nu exista astfel de elemente, iar predicatele care determina multimi 
intorc lista vida in acest caz. */

% Determinarea minorantilor M (si a listei acestora LM) ai submultimii S in posetul (P,Ord):

minorant(M,S,P,Ord) :- member(M,P), minoreaza(M,S,Ord).

minoreaza(M,S,Ord) :- not((member(X,S), not(member((M,X),Ord)))).

minorantii(S,P,Ord,LM) :- setof(M, minorant(M,S,P,Ord), LM), !.
minorantii(_,_,_,[]).

% Determinarea majorantilor M (si a listei acestora LM) ai submultimii S in posetul (P,Ord):

majorant(M,S,P,Ord) :- member(M,P), majoreaza(M,S,Ord).

majoreaza(M,S,Ord) :- not((member(X,S), not(member((X,M),Ord)))).

majorantii(S,P,Ord,LM) :- setof(M, majorant(M,S,P,Ord), LM), !.
majorantii(_,_,_,[]).

/* Determinarea elementelor minimale, respectiv maximale M (si a listelor acestora LM) ale
submultimii S in posetul (P,Ord); desigur, nu are importanta daca in locul acestuia
consideram subposetul sau (S,Ord^(SxS)) cu multimea suport S si ordinea indusa pe multimea
S de ordinea Ord de pe multimea P, rezultatele vor fi aceleasi: */

elemminimal(M,S,Ord) :- member(M,S), not((member(X,S), member((X,M),Ord), M\=X)).

elementeleminimale(S,Ord,LM) :- setof(M, elemminimal(M,S,Ord), LM), !.
elementeleminimale(_,_,[]).

elemmaximal(M,S,Ord) :- member(M,S), not((member(X,S), member((M,X),Ord), M\=X)).

elementelemaximale(S,Ord,LM) :- setof(M, elemmaximal(M,S,Ord), LM), !.
elementelemaximale(_,_,[]).

/* Determinarea minimului, maximului, infimumului, respectiv supremumului lui S in posetul
(P,Ord); desigur, pentru minim si maxim nu are importanta daca in locul acestuia consideram 
subposetul sau (S,Ord^(SxS)), rezultatele vor fi aceleasi: */

minim(M,S,Ord) :- minorant(M,S,S,Ord).

maxim(M,S,Ord) :- majorant(M,S,S,Ord).

inf(M,S,P,Ord) :- minorantii(S,P,Ord,L), maxim(M,L,Ord).

sup(M,S,P,Ord) :- majorantii(S,P,Ord,L), minim(M,L,Ord).

/* Interogati:
?- exdincurs(P,Ord), minorantii([c,d],P,Ord,LMinor), majorantii([c,d],P,Ord,LMajor), elementeleminimale(P,Ord,LMinPoset), elementelemaximale(P,Ord,LMaxPoset).
?- exdincurs(P,Ord), minim(MinPoset,P,Ord).
?- exdincurs(P,Ord), maxim(MaxPoset,P,Ord). 
?- exdincurs(P,Ord), inf(Inf,[c,d],P,Ord).
?- exdincurs(P,Ord), sup(Sup,[c,d],P,Ord).
*/

% Predicatul urmator testeaza daca un poset (P,Ord) este latice:

latice(P,Ord) :- not((member(X,P), member(Y,P), 
		not((inf(_,[X,Y],P,Ord), sup(_,[X,Y],P,Ord))))).

% Calculul produsului cartezian (P,OrdP) a doua poseturi (A,OrdA) si (B,OrdB):

prodcartposeturi(A,OrdA,B,OrdB,P,OrdP) :- prodcart(A,B,P), prodcartrelbin(OrdA,OrdB,OrdP).

% Rombul ca produs cartezian al lantului cu (exact - se subintelege) 2 elemente cu el insusi:

rombul(R,OrdR) :- lant2(L2,OrdL2), prodcartposeturi(L2,OrdL2,L2,OrdL2,R,OrdR).

/* Determinarea izomorfismelor de poseturi F (si a listei lor LF) de la un poset (A,OrdA) 
la un poset (B,OrdB): */

izomposeturi(F,A,OrdA,B,OrdB) :- fct(F,A,B), inj(A), surj(F,B), cresc(F,OrdA,OrdB),
				invrel(F,InvF), cresc(InvF,OrdB,OrdA).

izomorfismeleposeturi(A,OrdA,B,OrdB,LF) :- setof(F, izomposeturi(F,A,OrdA,B,OrdB), LF), !.
izomorfismeleposeturi(_,_,_,_,[]).

% Predicatul urmator testeaza daca doua poseturi (A,OrdA) si (B,OrdB) sunt izomorfe:

poseturiizomorfe(A,OrdA,B,OrdB) :- izomposeturi(_,A,OrdA,B,OrdB).

% varianta:

poseturiizom(A,OrdA,B,OrdB) :- izomorfismeleposeturi(A,OrdA,B,OrdB,[_|_]).

/* Determinarea morfismelor de latici F (si a listei lor LF) de la o latice Ore (A,OrdA) la 
o latice Ore (B,OrdB): */

morflat(F,A,OrdA,B,OrdB) :- fct(F,A,B), pastrdisjconj(F,A,OrdA,B,OrdB).

morfismelelatici(A,OrdA,B,OrdB,LF) :- setof(F, morflat(F,A,OrdA,B,OrdB), LF), !.
morfismelelatici(_,_,_,_,[]).

pastrdisjconj(F,A,OrdA,B,OrdB) :- not((member(X,A), member(Y,A), 
		member((X,FX),F), member((Y,FY),F), 
		inf(XsiY,[X,Y],A,OrdA), sup(XsauY,[X,Y],A,OrdA),
		member((XsiY,FXsiY),F), member((XsauY,FXsauY),F),
	not((inf(FXsiY,[FX,FY],B,OrdB), sup(FXsauY,[FX,FY],B,OrdB))))).

/* Interogati:
?- romb(R,OrdR), rombul(L2xL2,OrdL2xL2), poseturiizomorfe(R,OrdR,L2xL2,OrdL2xL2).
?- romb(R,OrdR), rombul(L2xL2,OrdL2xL2), poseturiizom(R,OrdR,L2xL2,OrdL2xL2).
?- m3(M3,OrdM3), n5(N5,OrdN5), poseturiizomorfe(M3,OrdM3,N5,OrdN5).
?- m3(M3,OrdM3), n5(N5,OrdN5), poseturiizom(M3,OrdM3,N5,OrdN5).
?- romb(R,OrdR), rombul(L2xL2,OrdL2xL2), izomorfismeleposeturi(R,OrdR,L2xL2,OrdL2xL2,LF), scrielista(LF), length(LF,NrIzomOrd).
?- romb(R,OrdR), rombul(L2xL2,OrdL2xL2), morfismelelatici(R,OrdR,L2xL2,OrdL2xL2,LF), scrielista(LF), length(LF,NrMorfLat).
*/

/* Determinarea sublaticilor S (si a listei lor LS, care nu va fi niciodata vida, pentru ca
intotdeauna va contine laticea vida) ale unei latici Ore (L,OrdL): */

sublatice(S,L,OrdL) :- sublista(S,L), inchdisjconj(S,L,OrdL).

inchdisjconj(S,L,OrdL) :- not((member(X,S), member(Y,S), 
	inf(XsiY,[X,Y],L,OrdL), sup(XsauY,[X,Y],L,OrdL),
	not((inf(XsiY,[X,Y],S,OrdL), sup(XsauY,[X,Y],S,OrdL))))).

sublaticile(L,OrdL,LS) :- setof(S, sublatice(S,L,OrdL), LS).

% Suma ordinala a lantului cu 2 elemente cu rombul si cu inca o copie a lantului cu 2 elemente:

l2plusrombplusL2(L,Ord) :- L=[0,a,b,x,y,1], poset(L,[(0,a),(a,x),(a,y),(x,b),(y,b),(b,1)],Ord).

/* Interogati:
?- romb(L,OrdL), sublaticile(L,OrdL,LS), scrielista(LS), length(LS,NrSublatici).
?- l2plusrombplusL2(L,OrdL), sublaticile(L,OrdL,LS), scrielista(LS), length(LS,NrSublatici).
*/

/* Predicatul nuplu([Val1,Val2,...,ValN]) determina in argumentul sau fiecare lista de N
valori booleene: */

nuplu([]).
nuplu([H|T]) :- member(H,[false,true]), nuplu(T).

% Determinarea tripletelor de valori booleene:

triplet(P,Q,R) :- member(P,[false,true]), member(Q,[false,true]),
	 	member(R,[false,true]), write((P,Q,R)), nl.

% varianta:

triplu(P,Q,R) :- nuplu([P,Q,R]), write((P,Q,R)), nl.

% Determinarea cvadrupletelor de valori booleene:

cvadruplet(P,Q,R,S) :- member(P,[false,true]), member(Q,[false,true]),
	 	member(R,[false,true]), member(S,[false,true]), write((P,Q,R,S)), nl.

% varianta:

cvadruplu(P,Q,R,S) :- nuplu([P,Q,R,S]), write((P,Q,R,S)), nl.

/* Fie f:L2->{false,true}, f(0)=false, f(1)=true. => f transforma operatiile booleene ale
lui L2 in conectorii logici aplicati valorilor booleene din {false,true}. */

/* Cu notatiile din seminar, luand o interpretare arbitrara h:V->L2, variabilele de mai jos
vor lua ca valori valorile (booleene ale) lui foh in aceste variabile propozitionale:
P=f(h(p)), Q=f(h(q)), R=f(h(r)), S=f(h(s)).
Voi nota conectorul logic de negatie, aici, in mod text, cu -|. */

alfa(P,Q,R) :- implica((not(Q),P),not(R)). % f(h~(alfa)), unde alfa = (-|q ^ p) -> -|r

beta(P,Q) :- implica(Q,not(P)). % f(h~(beta)), unde beta = q -> -|p

gama(R,S) :- implica(S,R). % f(h~(gama)), unde gama = s->r

delta(R,S) :- implica(not(R),S). % f(h~(delta)), unde delta = -|r -> s

epsilon(P) :- P. % f(h~(epsilon))=f(h~(p))=f(h(p)), unde epsilon = p

/* Predicat care testeaza daca multimea de enunturi {alfa,beta,gama,delta,epsilon} e
inconsistenta, verificand, in mod echivalent, daca e nesatisfiabila: */

multinconsist :- not((cvadruplet(P,Q,R,S), alfa(P,Q,R), beta(P,Q),
		 gama(R,S), delta(R,S), epsilon(P))).

/* Cu notatiile din seminar, luand o interpretare arbitrara h:V->L2, variabilele de mai jos
vor lua ca valori valorile (booleene ale) lui foh in aceste variabile propozitionale:
A=f(h(a)), B=f(h(b)), C=f(h(c)). */

bastinasA(B,C) :- echiv((B,C),C). % f(h~(alfa))

veriditateA(A,B,C) :- echiv(bastinasA(B,C),A). % f(h~(alfa<->a))

bastinasB(A,B,C) :- implica((A,C),not(implica((B,C),A))). % f(h~(beta))

veriditateB(A,B,C) :- echiv(bastinasB(A,B,C),B). % f(h~(beta<->b))

bastinasC(A,B) :- echiv(not(B),(A;B)). % f(h~(gama))

veriditateC(A,B,C) :- echiv(bastinasC(A,B),C). % f(h~(gama<->c))

% Predicat pentru rezolvarea problemei cu triburile Tu si Fa:

carespuneadev(A,B,C) :- triplet(A,B,C), veriditateA(A,B,C),
			veriditateB(A,B,C), veriditateC(A,B,C).

/* Consideram o interpretare (evaluare, semantica) h:V->L2 care satisface reuniunea
Gama1 U Gama2 U Gama3, arbitrara. Notam cu Fi, Psi, Gama valorile lui foh~ in enunturile
fi, psi, gama, respectiv: Fi=f(h~(fi)), Psi=f(h~(psi)), Gama=f(h~(gama)).
Predicatul urmator demonstreaza regula de deductie:
Gama1 |- fi v psi, Gama2 |- fi->gama, Gama3 |- psi->gama
---------------------------------------------------------
           Gama1 U Gama2 U Gama3 |- gama
*/

regded :- not((triplet(Fi,Psi,Gama), (Fi;Psi), implica(Fi,Gama), implica(Psi,Gama), not(Gama))).

/* Algebra (A,f,R) din exercitiul din setul de cursuri cu logica clasica a predicatelor:
A=[a,b,c,d], f:A->A definita ca mai jos si R={(a,b),(b,c),(c,b),(c,d)}:
 x  | a b c d
--------------
f(x)| b c d a
*/

multAelem([a,b,c,d]).

fctF(a,b).
fctF(b,c).
fctF(c,d).
fctF(d,a).

% varianta: fctF([(a,b),(b,c),(c,d),(d,a)]).

relR([(a,b),(b,c),(c,b),(c,d)]).

/* Predicat care testeaza daca algebra (A,f,R) de mai sus satisface enuntul
(exista x)(R(x,f(x))^R(f(x),x)): */

algAsatisfEnunt1 :- multAelem(A), relR(R), member(X,A),
		fctF(X,FX), member((X,FX),R), member((FX,X),R).

/* Predicat care gaseste, pentru algebra (A,f,R) de mai sus, valorile x din A pentru care 
are loc R(x,f(x))^R(f(x),x), adica perechile (x,f(x)) si (f(x),x) apartin lui R: */

ptCeXsatisfEnunt1(X) :- multAelem(A), relR(R), member(X,A),
		fctF(X,FX), member((X,FX),R), member((FX,X),R).

/* Predicat care testeaza daca algebra (A,f,R) de mai sus satisface enuntul
(exista x)(oricare ar fi y)(R(y,f(f(x))) v R(f(x),y)): */

algAsatisfEnunt2 :- multAelem(A), relR(R), member(X,A), fctF(X,FX), fctF(FX,FFX), 
		not((member(Y,A), not(member((Y,FFX),R) ; member((FX,Y),R)))).

% Predicat pentru verificarea (computer-aided a) corectitudinii predicatului anterior:

verifAsatisfEnunt2 :- multAelem(A), relR(R), write(R), nl, write('----------'), nl,
		member(X,A), fctF(X,FX), fctF(FX,FFX),
		write('(x,f(x),f(f(x))='), write((X,FX,FFX)), write(', '), nl,
		not((member(Y,A), tab(3), write('y='), write(Y), nl,
		tab(3), write('(y,f(f(x))='), write((Y,FFX)), write(', '),
		write('(f(x),y)='), write((FX,Y)), nl,
		not(member((Y,FFX),R) ; member((FX,Y),R)))).













