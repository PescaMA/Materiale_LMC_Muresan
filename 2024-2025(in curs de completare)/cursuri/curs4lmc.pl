/* Fie multimile A,B,C arbitrare, fixate.
Fie x arbitrar, fixat.
Notam cu variabilele A,B,C (am putea folosi _a,_b,_c,_d respectiv) proprietatile:
A: x apartine lui A
B: x apartine lui B
C: x apartine lui C
Sa demonstram idempotenta reuniunii: AUA=A.
Avem de demonstrat: x apartine lui AUA <=> x apartine A, adica:
(x apartine lui A sau x apartine lui A) <=> x apartine lui A, adica:
A ; A <=> A, adica:
pentru orice A membru al multimii [false,true], A ; A <=> A, adica A ; A are aceeasi valoare de adevar ca si A.
*/

:- op(300,xfx,xor).

implica(P,Q) :- not(P); Q.
echiv(P,Q) :- implica(P,Q), implica(Q,P).
implicstr(P,Q) :- implica(P,Q), not(echiv(P,Q)).
P xor Q :- P,not(Q) ; Q,not(P).

idempreun(A) :- echiv(A;A, A).
idempinters(A) :- echiv((A,A), A).

demidempreun :- not((member(A,[false,true]), write(A), nl, not(idempreun(A)))).
demidempinters :- not((member(A,[false,true]), write(A), nl, not(idempinters(A)))).

comutreun(A,B) :- echiv(A;B, B;A).
comutinters(A,B) :- echiv((A,B), (B,A)).
comutdifsim(A,B) :- echiv(A xor B, B xor A).

demcomutreun :- not((member(A,[false,true]), member(B,[false,true]), write((A,B)), nl, 			not(comutreun(A,B)))).
demcomutinters :- not((member(A,[false,true]), member(B,[false,true]), write((A,B)), nl, 			not(comutinters(A,B)))).
demcomutdifsim :- not((member(A,[false,true]), member(B,[false,true]), write((A,B)), nl, 			not(comutdifsim(A,B)))).

asocreun(A,B,C) :- echiv(A;(B;C), (A;B);C).
asocinters(A,B,C) :- echiv((A,(B,C)), ((A,B),C)).
asocdifsim(A,B,C) :- echiv(A xor (B xor C), (A xor B) xor C).

demasocreun :- not((member(A,[false,true]), member(B,[false,true]), 
		member(C,[false,true]), write((A,B,C)), nl, not(asocreun(A,B,C)))).
demasocinters :- not((member(A,[false,true]), member(B,[false,true]), 
		member(C,[false,true]), write((A,B,C)), nl, not(asocinters(A,B,C)))).
demasocdifsim :- not((member(A,[false,true]), member(B,[false,true]), 
		member(C,[false,true]), write((A,B,C)), nl, not(asocdifsim(A,B,C)))).

/* Reprezint:
incluziunea nestricta prin <=, iar cea stricta prin <
intersectia prin ^
diferenta simetrica prin /\
multimea vida prin 0
Observam ca: A<B <=> (A<=B si non(A=B)) <=>
<=> implicstr(x apartine lui A, x apartine lui B)
<=> implicstr(A,B), cu notatiile de mai sus pentru variabilele A,B.
*/

% A<=AUB si A^B<=A:

reuninclterm(A,B) :- implica(A, A;B).
intersinclinterm(A,B) :- implica((A,B), A).

demreuninclterm :- not((member(A,[false,true]), member(B,[false,true]), write((A,B)), nl, 			not(reuninclterm(A,B)))).
demintersinclinterm :- not((member(A,[false,true]), member(B,[false,true]), write((A,B)), 			nl, not(intersinclinterm(A,B)))).

% 0<=A:

vidainclorice(A) :- implica(false,A).

demvidainclorice :- not((member(A,[false,true]), write(A), nl, not(vidainclorice(A)))).

% A<=A si non(A<A):

incleainsasi(A) :- implica(A,A).
noninclstreainsasi(A) :- not(implicstr(A,A)).

demincleainsasi :- not((member(A,[false,true]), write(A), nl, not(incleainsasi(A)))).
demnoninclstreainsasi :- not((member(A,[false,true]), write(A), nl,
			 not(noninclstreainsasi(A)))).

% A<=0 <=> A=0:

sgpartevide(A) :- echiv(implica(A,false), echiv(A,false)).

demsgpartevide :- not((member(A,[false,true]), write(A), nl, not(sgpartevide(A)))).

% (A<=B si B<=C) => A<=C:

tranzincl(A,B,C) :- implica((implica(A,B), implica(B,C)), implica(A,C)).

demtranzincl :- not((member(A,[false,true]), member(B,[false,true]), 
		member(C,[false,true]), write((A,B,C)), nl, not(tranzincl(A,B,C)))).

% A<=B => A^C<=B^C:

intersambiim(A,B,C) :- implica(implica(A,B), implica((A,C), (B,C))).

demintersambiim :- not((member(A,[false,true]), member(B,[false,true]), 
		member(C,[false,true]), write((A,B,C)), nl, not(intersambiim(A,B,C)))).
