:- [lab5lmc2].

% Multime suport pentru lantul cu N elemente:

lN(0,[]).
lN(N,[N|T]) :- N>0, PN is N-1, lN(PN,T).

% Relatia de succesiune a lantului cu N elemente cu aceasta multime suport:

succLN(0,[]).
succLN(1,[]).
succLN(N,[(PN,N)|T]) :- N>1, PN is N-1, succLN(PN,T).

% Lantul cu N elemente, construit ca fiind posetul (LN,OrdLN):

lantN(N,LN,OrdLN) :- lN(N,LN), succLN(N,SuccLN), orddinsucc(SuccLN,LN,OrdLN).

% Lista primelor N lanturi finite nevide, o varianta de constructie:

lanturiN(0,[]).
lanturiN(N,[(LN,OrdLN)|Lanturi]) :- N>0, lantN(N,LN,OrdLN),
			PN is N-1, lanturiN(PN,Lanturi).

% si o varianta mai avantajoasa, fara recalculari:

lanturileN(0,[]) :- !.
lanturileN(N,Lanturi) :- lantN(1,L1,OrdL1),
			auxlanturileN(1,N,L1,[],[(L1,OrdL1)],Lanturi).

auxlanturileN(N,N,_,_,Lanturi,Lanturi).
auxlanturileN(K,N,LK,SuccLK,L,Lanturi) :- K<N, SK is K+1,
	LSK=[SK|LK], SuccLSK=[(K,SK)|SuccLK], orddinsucc(SuccLSK,LSK,OrdLSK),
	auxlanturileN(SK,N,LSK,SuccLSK,[(LSK,OrdLSK)|L],Lanturi).

% Produsul direct a doua poseturi (P,OrdP) si (Q,OrdQ):

prodposet(P,OrdP,Q,OrdQ,Prod,OrdProd) :- prodcartmult(P,Q,Prod),
					prodrel(OrdP,OrdQ,OrdProd).

% Lista produselor directe de poseturi din doua liste de poseturi:

prodposetsgl(_,[],[]).
prodposetsgl((P,OrdP),[(Q,OrdQ)|T],[(Prod,OrdProd)|L]) :- 
	prodposet(P,OrdP,Q,OrdQ,Prod,OrdProd), prodposetsgl((P,OrdP),T,L).

prodlistposet([],_,[]).
prodlistposet([(P,OrdP)|T],L,ListaProd) :- prodposetsgl((P,OrdP),L,M),
		prodlistposet(T,L,LP), append(M,LP,ListaProd).

% Lista produselor de K lanturi nevide de cardinale cel mult N:

prodlanturi(1,N,L) :- lanturileN(N,L).
prodlanturi(K,N,LPK) :- K>1, PK is K-1, prodlanturi(PK,N,LPPK),
		lanturileN(N,L), prodlistposet(L,LPPK,LPK).