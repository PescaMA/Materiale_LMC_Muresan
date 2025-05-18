:- [lab6lmc1].

% Exercitiul 1:

l2xl2(A,OrdA) :- A=[0,a,b,1], orddinsucc([(0,a),(0,b),(a,1),(b,1)],A,OrdA).

l4(B,OrdB) :- B=[0,p,q,1], orddinsucc([(0,p),(p,q),(q,1)],B,OrdB).

morfL2xL2laL4(ListaMorf) :- l2xl2(A,OrdA), l4(B,OrdB),
		morfismelelatmarg(A,OrdA,B,OrdB,ListaMorf).

niciunainj :- morfL2xL2laL4(ListaMorf), niciunainj(ListaMorf).

niciunainj([]).
niciunainj([F|LF]) :- not(inj(F)), niciunainj(LF).

% Exercitiul 2:

fi(Alfa,Beta) :- echiv(implica(Alfa,Beta), Alfa;Beta).

condfi(Alfa,Beta) :- echiv(fi(Alfa,Beta), Beta).

fisatisf :- not((nuplu([Alfa,Beta]), not(condfi(Alfa,Beta)))).

% Exercitiul 3:

multime([a,b,c]).

detf(Fctf) :- multime(A), fct(Fctf,A,A), inj(Fctf), inclusa([(a,b),(b,c)],Fctf).

inclusa([],_).
inclusa([H|T],L) :- member(H,L), inclusa(T,L).

detR(RelR) :- invrel([(a,b),(b,c)],RelR).

formula(X,Y) :- detf(F), detR(R), member((X,FX),F), member((Y,FY),F), member((FY,FFY),F),
		implica(member((X,Y),R), member((FX,FFY),R)).

verifAsatepsilon :- multime(A), not((member(X,A), not((member(Y,A), formula(X,Y))))).
