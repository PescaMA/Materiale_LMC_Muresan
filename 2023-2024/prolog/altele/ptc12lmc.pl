:- [c2lmcID2prolog].

cvadruplet(P,Q,R,S) :- member(P,[false,true]), member(Q,[false,true]),
			member(R,[false,true]), member(S,[false,true]), 
			write((P,Q,R,S)), nl.

auxnuplu([]).
auxnuplu([H|T]) :- member(H,[false,true]), auxnuplu(T).

nuplu(L) :- auxnuplu(L), write(L), nl.

alfa(P,Q,R) :- implica((not(Q),P),not(R)).

beta(P,Q) :- implica(Q,not(P)).

gama(R,S) :- implica(S,R).

delta(R,S) :- implica(not(R),S).

epsilon(P) :- P.

textinconsist :- not((cvadruplet(P,Q,R,S), alfa(P,Q,R), beta(P,Q), gama(R,S), delta(R,S), epsilon(P))).

% varianta:

textcontrad :- not((nuplu([P,Q,R,S]), alfa(P,Q,R), beta(P,Q), gama(R,S), delta(R,S), epsilon(P))).


