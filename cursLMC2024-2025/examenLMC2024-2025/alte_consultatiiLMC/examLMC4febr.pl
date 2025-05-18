:- [lab6lmc1].

% Exercitiul 1:

l2xl2plusl2(A,OrdStrA,OrdA) :- A=[0,a,b,c,1], ordstrdinsucc([(0,a),(0,b),(a,c),(b,c),(c,1)],OrdStrA),
				orddinordstr(OrdStrA,A,OrdA).

l4(B,OrdStrB,OrdB) :- B=[0,p,q,1], ordstrdinsucc([(0,p),(p,q),(q,1)],OrdStrB), 
			orddinordstr(OrdStrB,B,OrdB).

/* E util (sigur ca nu si obligatoriu) sa pastram in aceste predicate si relatia de ordine, 
si pe cea de ordine stricta. */

fctL2xL2plusL2laL4(ListaFctStrCresc) :- l2xl2plusl2(A,OrdStrA,_), l4(B,OrdStrB,_),
			functiilecresc(A,OrdStrA,B,OrdStrB,ListaFctStrCresc).

/* Predicatul cresc din Laboratorul 5 testeaza, de fapt, pastrarea unei relatii binare arbitrare 
(nu neaparat de ordine) de catre o functie; cand e aplicat pentru relatii de ordine stricta, acesta
testeaza proprietatea unei functii de a fi strict crescatoare. Sigur ca nu e obligatoriu sa 
implementam astfel predicatul fctL2xL2plusL2laL4. */

toatesurj :- fctL2xL2plusL2laL4(ListaFctStrCresc), l4(B,_,_), toatesurj(ListaFctStrCresc,B).

toatesurj([],_).
toatesurj([F|LF],B) :- surj(F,B), toatesurj(LF,B).

niciunamorflat :- l2xl2plusl2(A,_,OrdA), l4(B,_,OrdB), fctL2xL2plusL2laL4(ListaFctStrCresc),
			niciunamorflat(ListaFctStrCresc,A,OrdA,B,OrdB).

niciunamorflat([],_,_,_,_).
niciunamorflat([F|LF],A,OrdA,B,OrdB) :- not(morflat(F,A,OrdA,B,OrdB)), 
			niciunamorflat(LF,A,OrdA,B,OrdB).

% Exercitiul 2:

fi(Alfa,Beta) :- implica(echiv(Alfa,Beta), not(Alfa;Beta)).

condfi(Alfa,Beta) :- echiv(fi(Alfa,Beta), not((Alfa,Beta))).

fisatisf :- not((nuplu([Alfa,Beta]), not(condfi(Alfa,Beta)))).

% Exercitiul 3:

multime([a,b,c]).

detf(Fctf) :- multime(A), fct(Fctf,A,A), orddinsucc([(a,b),(b,c)],A,Ord), preordgen(Fctf,A,P), 
		permutare(Ord,P).

detR(RelR) :- ordstrdinsucc([(a,b),(b,c)],RelR).

formula(X,Y) :- detf(F), detR(R), member((X,FX),F), member((FX,FFX),F), member((Y,FY),F), 
		implica(FFX=FY, member((X,Y),R)).

verifAsatepsilon :- multime(A), not((member(X,A), member(Y,A), not(formula(X,Y)))).
