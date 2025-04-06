reun([],[],[]).
reun(A,B,AUB) :- setof(X, (member(X,A) ; member(X,B)), AUB).

diag([],[]).
diag([H|T],[(H,H)|U]) :- diag(T,U).

inchrefl(R,A,Q) :- diag(A,D), reun(D,R,Q).

comp(R,S,SoR) :- setof((X,Z), Y^(member((X,Y),R), member((Y,Z),S)), SoR), !.
comp(_,_,[]).

tranz(R) :- not((member((X,Y),R), member((Y,Z),R), not(member((X,Z),R)))).

inchtranz(R,T) :- auxinchtranz(R,R,T).

auxinchtranz(_,T,T) :- tranz(T), !.
auxinchtranz(R,Tn,T) :- comp(R,Tn,C), reun(R,C,Tsn), auxinchtranz(R,Tsn,T).

preordgen(R,A,P) :- inchtranz(R,T), inchrefl(T,A,P).

orddinsucc(Succ,A,Ord) :- preordgen(Succ,A,Ord).

% poset(+MultElem,+Succ,-Ord)

poset(A,Succ,Ord) :- orddinsucc(Succ,A,Ord).

lant2([0,1],Ord) :- poset([0,1],[(0,1)],Ord).

romb([0,a,b,1],Ord) :- poset([0,a,b,1],[(0,a),(0,b),(a,1),(b,1)],Ord).

cub([0,a,b,c,x,y,z,1],Ord) :- poset([0,a,b,c,x,y,z,1],[(0,a),(0,b),(0,c),(a,x),(a,y),(b,x),(b,z),(c,y),(c,z),(x,1),(y,1),(z,1)],Ord).

minorant(M,S,P,Ord) :- member(M,P), minoreaza(M,S,Ord).

minoreaza(M,S,Ord) :- not((member(X,S), not(member((M,X),Ord)))).

minorantii(S,P,Ord,LM) :- setof(M, minorant(M,S,P,Ord), LM), !.
minorantii(_,_,_,[]).

majorant(M,S,P,Ord) :- member(M,P), majoreaza(M,S,Ord).

majoreaza(M,S,Ord) :- not((member(X,S), not(member((X,M),Ord)))).

majorantii(S,P,Ord,LM) :- setof(M, majorant(M,S,P,Ord), LM), !.
majorantii(_,_,_,[]).

elemminimal(M,S,Ord) :- member(M,S), not((member(X,S), member((X,M),Ord), M\=X)).

elemmaximal(M,S,Ord) :- member(M,S), not((member(X,S), member((M,X),Ord), M\=X)).

minim(M,S,Ord) :- minorant(M,S,S,Ord).

maxim(M,S,Ord) :- majorant(M,S,S,Ord).

inf(M,S,P,Ord) :- minorantii(S,P,Ord,L), maxim(M,L,Ord).

sup(M,S,P,Ord) :- majorantii(S,P,Ord,L), minim(M,L,Ord).

latice(P,Ord) :- not((member(X,P), member(Y,P), 
		not((inf(_,[X,Y],P,Ord), sup(_,[X,Y],P,Ord))))).

sublatice(S,L,OrdL) :- sublista(S,L), inchdisjconj(S,L,OrdL).

inchdisjconj(S,L,OrdL) :- not((member(X,S), member(Y,S), 
	inf(XsiY,[X,Y],L,OrdL), sup(XsauY,[X,Y],L,OrdL),
	not((inf(XsiY,[X,Y],S,OrdL), sup(XsauY,[X,Y],S,OrdL))))).

invrel([],[]).
invrel([(X,Y)|T],[(Y,X)|U]) :- invrel(T,U).

inj(R) :- not((member((X,U),R), member((Y,U),R), X\=Y)).

surj(R,B) :- not((member(U,B), not(member((_,U),R)))).

fct([],[],_).
fct([(H,FH)|U],[H|T],B) :- member(FH,B), fct(U,T,B).

cresc(F,OrdA,OrdB) :- not((member((X,Y),OrdA), member((X,FX),F), member((Y,FY),F),
			not(member((FX,FY),OrdB)))).

izomposeturi(F,A,OrdA,B,OrdB) :- fct(F,A,B), inj(F), surj(F,B), cresc(F,OrdA,OrdB),
				invrel(F,InvF), cresc(InvF,OrdB,OrdA).

morflat(F,A,OrdA,B,OrdB) :- fct(F,A,B), pastrdisjconj(F,A,OrdA,B,OrdB).

pastrdisjconj(F,A,OrdA,B,OrdB) :- not((member(X,A), member(Y,A), 
		member((X,FX),F), member((Y,FY),F), 
		inf(XsiY,[X,Y],A,OrdA), sup(XsauY,[X,Y],A,OrdA),
		member((XsiY,FXsiY),F), member((XsauY,FXsauY),F),
	not((inf(FXsiY,[FX,FY],B,OrdB), sup(FXsauY,[FX,FY],B,OrdB))))).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%

implica(P,Q) :- not(P) ; Q.

echiv(P,Q) :- implica(P,Q), implica(Q,P).

auxnuplu([]).
auxnuplu([H|T]) :- member(H,[false,true]), auxnuplu(T).

nuplu(L) :- auxnuplu(L), write(L), nl.
