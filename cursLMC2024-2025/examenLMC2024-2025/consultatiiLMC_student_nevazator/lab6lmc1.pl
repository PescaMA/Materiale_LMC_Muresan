:- [lab5lmc1].

cub(B,Ord) :- B=[0,a,b,c,x,y,z,1],
orddinsucc([(0,a),(0,b),(0,c),(a,x),(a,y),(b,x),(b,z),(c,y),(c,z),(x,1),(y,1),(z,1)],B,Ord).

/* Interogati:
?- m3(M3,OrdM3), n5(N5,OrdN5), morflatmarg(F,M3,OrdM3,N5,OrdN5).
?- m3(M3,OrdM3), n5(N5,OrdN5), morfismelelatmarg(M3,OrdM3,N5,OrdN5,LF), scrielista(LF), length(LF,Nr).
?- m3(M3,OrdM3), n5(N5,OrdN5), morfismelelatmarg(N5,OrdN5,M3,OrdM3,LF), scrielista(LF), length(LF,Nr).
?- cub(C,OrdC), rombul(R,OrdR), morfismelelatmarg(C,OrdC,R,OrdR,LF), scrielista(LF), length(LF,Nr).
Sa comparam si timpii de executie pentru urmatoarele interogari:
?- cub(B,Ord), Init is cputime, izomorfismeleord(B,Ord,B,Ord,LF), Fin is cputime, Dif is Fin-Init, scrielista(LF), length(LF,Nr), write(Dif), write(' secunde').
?- cub(B,Ord), Init is cputime, izomorfismeleposeturi(B,Ord,B,Ord,LF), Fin is cputime, Dif is Fin-Init, scrielista(LF), length(LF,Nr), write(Dif), write(' secunde').
?- cub(B,Ord), Init is cputime, setof(F, (fctbij(F,B,B), pastrdisjconj(F,B,Ord,B,Ord)), LF), Fin is cputime, Dif is Fin-Init, scrielista(LF), length(LF,Nr), write(Dif), write(' secunde').
?- cub(B,Ord), Init is cputime, setof(F, (morflat(F,B,Ord,B,Ord), inj(F), surj(F,B)), LF), Fin is cputime, Dif is Fin-Init, scrielista(LF), length(LF,Nr), write(Dif), write(' secunde').
*/

/* Determinarea complementilor unui element X intr-o latice marginita avand laticea Ore 
subiacenta (L,Ord): */

complementeunulaltuia(X,Y,L,Ord,Zero,Unu) :- inf(Zero,[X,Y],L,Ord), sup(Unu,[X,Y],L,Ord).

complement(Y,X,L,Ord,Zero,Unu) :- member(Y,L), complementeunulaltuia(X,Y,L,Ord,Zero,Unu).

complementi(X,L,Ord,Zero,Unu,ComplemX) :- setof(Y, complement(Y,X,L,Ord,Zero,Unu), ComplemX), !.
complementi(_,_,_,[]).

complementii(X,L,Ord,ComplemX) :- minim(Zero,L,Ord), maxim(Unu,L,Ord), 
				complementi(X,L,Ord,Zero,Unu,ComplemX).

/* Determinarea elementelor complementate ale unei latici marginite avand laticea Ore 
subiacenta (L,Ord): */

complementat(X,L,Ord,Zero,Unu) :- complementi(X,L,Ord,Zero,Unu,[_|_]).

elemcomplementat(X,L,Ord,Zero,Unu) :- member(X,L), complementat(X,L,Ord,Zero,Unu).

elemcomplementate(L,Ord,ElemComplementate) :- minim(Zero,L,Ord), maxim(Unu,L,Ord), 
			setof(X, elemcomplementat(X,L,Ord,Zero,Unu), ElemComplementate), !.
elemcomplementate(_,_,[]).

/* Pentru testarea complementarii unei latici marginite avand laticea Ore subiacenta (L,Ord)
nu putem proceda astfel:
latmargcomplementata(L,Ord) :- elemcomplementate(L,Ord,L).
din cauza sortarii efectuate de predicatul setof. Observati rezultatele interogarilor:
?- cub(B,Ord), elemcomplementate(B,Ord,B).
?- cub(B,Ord), elemcomplementate(B,Ord,L).
Asadar vom proceda astfel: */

latmargcomplementata(L,Ord) :- minim(Zero,L,Ord), maxim(Unu,L,Ord), 
		not((member(X,L), not(complementat(X,L,Ord,Zero,Unu)))).

/* Interogati:
?- cub(B,Ord), latmargcomplementata(B,Ord).
*/

/* Determinarea subalgebrelor Boole S ale unei algebre Boole avand laticea Ore subiacenta 
(B,Ord), si a listei LS a acestor subalgebre, care va fi nevida, pentru ca intotdeauna va 
contine algebra {0,1}: */

subalgBoole(S,B,Ord) :- sublatice(S,B,Ord), S\=[], pastrcomplem(S,B,Ord).

pastrcomplem(S,B,Ord) :- minim(Zero,B,Ord), maxim(Unu,B,Ord), 
	not((member(X,S), complement(Y,X,B,Ord,Zero,Unu), not(member(Y,S)))).

subalgebreleBoole(B,Ord,LS) :- setof(S, subalgBoole(S,B,Ord), LS).

% varianta:

subalgbool(S,B,Ord) :- sublaticemarg(S,B,Ord), pastrcompl(S,B,Ord).

pastrcompl(S,B,Ord) :- minim(Zero,B,Ord), maxim(Unu,B,Ord), 
	not((member(X,S), not(complement(_,X,S,Ord,Zero,Unu)))).

subalgebrelebool(B,Ord,LS) :- setof(S, subalgbool(S,B,Ord), LS).

/* Interogati:
?- cub(B,Ord), subalgebreleBoole(B,Ord,LS), scrielista(LS), length(LS,NrSubalgBoole).
?- cub(B,Ord), subalgebrelebool(B,Ord,LS), scrielista(LS), length(LS,NrSubalgBoole).
*/

implica(P,Q) :- not(P) ; Q.
echiv(P,Q) :- implica(P,Q), implica(Q,P).

% Generarea unui N-uplu de valori booleene sub forma de lista:

auxnuplu([]).
auxnuplu([H|T]) :- member(H,[false,true]), auxnuplu(T).

nuplu(L) :- auxnuplu(L), write(L), nl.

% Asadar generarea unui cvadruplet de valori booleene poate fi efectuata astfel:

cvadruplet(P,Q,R,S) :- member(P,[false,true]), member(Q,[false,true]),
			member(R,[false,true]), member(S,[false,true]), 
			write((P,Q,R,S)), nl.

% dar si astfel:

cvadruplu(P,Q,R,S) :- nuplu([P,Q,R,S]).

/* Consideram variabilele propozitionale p, q, r, s si enunturile: 
alfa = (-|q ^ p) -> -|r, beta = q -> -|p, gama = s->r, delta = -|r -> s, epsilon = p,
unde am notat prin -| conectorul logic de negatie.
Putem demonstra prin tabel semantic, cu ajutorul Prolog-ului, ca multimea de enunturi
{alfa, beta, gama, delta, epsilon} e inconsistenta, ca mai jos. Vom vedea notiunile  
teoretice de mai jos in urmatoarele cursuri si seminarii.
Notam cu f:L2->{false,true} functia definita prin: f(0)=false, f(1)=true. Intrucat f este 
bijectiva si transforma operatiile booleene ale algebrei Boole standard L2 in conectorii 
logici aplicati valorilor booleene din {false,true}, care determina pe multimea {false,true}
o structura de algebra Boole, rezulta ca f este izomorfism boolean intre L2 si algebra 
Boole astfel definita cu multimea suport {false,true}.
Consideram o interpretare arbitrara h:V->L2 si variabilele Prolog P, Q, R, S, ale caror 
valori booleene vor reprezenta valorile compunerii foh in aceste variabile propozitionale:
P=f(h(p)), Q=f(h(q)), R=f(h(r)), S=f(h(s)). Atunci valorile booleene ale predicatelor de 
mai jos vor fi valorile compunerii foh~ in aceste enunturi, unde h~:E->L2 este unica 
prelungire a lui h la multimea E a enunturilor care transforma conectorii logici in operatii
booleene: alfa(P,Q,R)=f(h~(alfa)), beta(P,Q)=f(h~(beta)), gama(R,S)=f(h~(gama)), 
delta(R,S)=f(h~(delta)), epsilon(P)=f(h~(epsilon))=f(h~(p))=f(h(p))=P. */

alfa(P,Q,R) :- implica((not(Q),P),not(R)).

beta(P,Q) :- implica(Q,not(P)).

gama(R,S) :- implica(S,R).

delta(R,S) :- implica(not(R),S).

epsilon(P) :- P.

textinconsist :- not((cvadruplet(P,Q,R,S), alfa(P,Q,R), beta(P,Q), gama(R,S), delta(R,S), epsilon(P))).

% varianta:

textcontrad :- not((nuplu([P,Q,R,S]), alfa(P,Q,R), beta(P,Q), gama(R,S), delta(R,S), epsilon(P))).

/* Vom pastra notatia de mai sus pentru izomorfismul boolean f.
Vom reprezenta, peste tot in mod plain text:
	prin -| conectorul logic de negatie, 
	prin |- simbolul pentru adevarurile sintactice (i.e. teoremele formale) si 
deductia sintactica,
	prin |= simbolul pentru adevarurile semantice (i.e. enunturile universal adevarate,
tautulogiile) si deductia semantica.
Desigur: conform Teoremei de completitudine, adevarurile sintactice coincid cu cele 
semantice, iar, conform Teoremei de completitudine tare, deductia sintactica, coincide cu 
cea semantica. */

/* Consideram variabilele propozitionale p, q, r si enunturile:
alfa1 = -|p -> (r -> -|q), beta1 = -|p -> r, gama1 = q si delta1 = p.
Sa demonstram, ca mai sus, prin tabel semantic, ca are loc deductia semantica: 
	{alfa1,beta1,gama1} |= delta1.
Fie h:V->L2 o interpretare arbitrara.
Prin variabilele P, Q, R in Prolog vom reprezenta: P=f(h(p)), Q=f(h(q)) si R=f(h(r)).
Asadar valorile predicatelor de mai jos vor fi date de: alfa1(P,Q,R)=f(h~(alfa1)),
beta1(P,R)=f(h~(beta1)), gama1(Q)=f(h~(gama1))=f(h(q)) si delta1(P)=f(h~(delta1))=f(h(p)).
*/

alfa1(P,Q,R) :- implica(not(P),implica(R,not(Q))).

beta1(P,R) :- implica(not(P),R).

gama1(Q) :- Q.

delta1(P) :- P.

deductie(P,Q,R) :- implica((alfa1(P,Q,R), beta1(P,R), gama1(Q)), delta1(P)).

demdeductie :- not((nuplu([P,Q,R]), not(deductie(P,Q,R)))).

/* Sa demonstram, prin tabel semantic, ca, pentru orice enunturi fi, psi, hi, are loc 
deductia sintactica: {fi, fi->(psi->hi), -|hi} |- -|psi, sau, in mod echivalent, deductia 
semantica: {fi, fi->(psi->hi), -|hi} |= -|psi.
Fie h:V->L2 o interpretare arbitrara. Prin variabilele Fi, Psi, Hi in Prolog vom reprezenta:
Fi=f(h~(fi)), Psi=f(h~(psi)) si Hi=f(h~(hi)). */

deductia(Fi,Psi,Hi) :- implica((Fi, implica(Fi,implica(Psi,Hi)), not(Hi)), not(Psi)).

demdeductia :- not((nuplu([Fi,Psi,Hi]), not(deductia(Fi,Psi,Hi)))).

/* Pentru problema cu triburile, vom considera o interpretare arbitrara h:V->L2 si vom 
reprezenta prin variabilele A, B, C in Prolog: A=f(h(a)), B=f(h(b)) si C=f(h(c)). */

adevA(A,B,C) :- echiv(echiv((B,C),C),A).

adevB(A,B,C) :- echiv(implica((A,C),not(implica((B,C),A))),B).

adevC(A,B,C) :- echiv(echiv(not(B),A;B),C).

dettriburi(A,B,C) :- nuplu([A,B,C]), adevA(A,B,C), adevB(A,B,C), adevC(A,B,C).

scrietriburi :- dettriburi(A,B,C), write('A'), scrietrib(A), 
	write('B'), scrietrib(B), write('C'), scrietrib(C).

scrie :- write(' face parte din tribul ').

scrietrib(V) :- scrie, dentrib(V), nl.

dentrib(false) :- write('Fa').
dentrib(true) :- write('Tu').

% varianta:

determintriburi(A,B,C) :- auxnuplu([A,B,C]), adevA(A,B,C), adevB(A,B,C), adevC(A,B,C).

scrieretriburi :- determintriburi(A,B,C), write('A'), scrietrib(A), 
	write('B'), scrietrib(B), write('C'), scrietrib(C).

/* Interogati:
?- dettriburi(A,B,C).
?- scrietriburi.
?- scrieretriburi.
*/
