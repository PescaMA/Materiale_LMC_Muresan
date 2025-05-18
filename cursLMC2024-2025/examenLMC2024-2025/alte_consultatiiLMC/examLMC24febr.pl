:- [lab6lmc1].

% Exercitiul 1:

l2xl3(A,OrdA) :- A=[0,a,b,c,d,1],   % a,b vor fi atomii, iar c,d coatomii, unde avb=c
	orddinsucc([(0,a),(0,b),(a,c),(b,c),(b,d),(c,1),(d,1)],A,OrdA).

% Atom = succesor al lui 0; coatom=predecesor al lui 1.

l2(B,OrdB) :- B=[0,1], orddinsucc([(0,1)],B,OrdB).

fctcrescsurj(A,OrdA,B,OrdB,L) :- setof(F, (fctcresc(F,A,OrdA,B,OrdB), surj(F,B)), L), !.
fctcrescsurj(_,_,_,_,[]).

fctL2xL3laL2(ListaFctCrescSurj) :- l2xl3(A,OrdA), l2(B,OrdB), 
				fctcrescsurj(A,OrdA,B,OrdB,ListaFctCrescSurj).

preimagsgl(Rel,Elem,Preimag) :- setof(X, member((X,Elem), Rel), Preimag), !.
preimagsgl(_,_,[]).

selcondpreimag(ListaFct,Elem1,Elem2,ListaFctCondPreimag) :- findall(F, (member(F,ListaFct),
	(preimagsgl(F,Elem1,[_]) ; preimagsgl(F,Elem2,[_]))), ListaFctCondPreimag).

/* Putem elimina duplicatele din ListaFctCondPreimag obtinuta mai sus, dar in cele ce 
urmeaza selcondpreimag va fi aplicat unei liste fara duplicate ListaFct, colectate cu setof.
Observati ca setof in locul lui findall mai sus, din cauza modului in care setof colecteaza
termenii, ar obtine una singura dintre cele doua functii care satisfac:
   fctL2xL3laL2(ListaFctCrescSurj), selcondpreimag(ListaFctCrescSurj,0,1,ListaFiltrata).
O eroare precum folosirea lui setof in loc de findall aici nu se depuncteaza, la fel ca 
omiterea utilizarii predicatului permutare in predicatul detf mai jos. */

niciunamorflatmarg([],_,_,_,_).
niciunamorflatmarg([F|LF],A,OrdA,B,OrdB) :- not(morflatmarg(F,A,OrdA,B,OrdB)),
				niciunamorflatmarg(LF,A,OrdA,B,OrdB).

/* Putem folosi metoda cu negatie (nu exista membru al listei a.i....) in loc de recursie. 
Putem testa doar nesatisfacerea simultana a pastrarii disjunctiei si conjunctiei si a lui 
0 si 1, intrucat toti membrii acelei liste vor fi functii la apelul din urmatorul predicat.*/

niciunamorflatmarg :- fctL2xL3laL2(ListaFctCrescSurj), 
	selcondpreimag(ListaFctCrescSurj,0,1,ListaFiltrata), 
	l2xl3(A,OrdA), l2(B,OrdB), niciunamorflatmarg(ListaFiltrata,A,OrdA,B,OrdB).

% Exercitiul 2:

fi(Alfa,Beta) :- implica(implica(Alfa,Beta), echiv(Alfa,Beta)).

fisatisf :- nuplu([Alfa,Beta]), fi(Alfa,Beta).

finesatisf :- not((nuplu([Alfa,Beta]), not(Alfa), Beta, fi(Alfa,Beta))).

% Exercitiul 3:

multime([a,b,c]).

detR(RelR) :- ordstrdinsucc([(a,b)],R), inchsim(R,RelR).

detf(Fctf) :- multime(A), orddinsucc([(a,b)],A,Ord), detrelfcttot(Fctf,A,Ord).

detrelfcttot(F,P,OrdP) :- fct(F,P,P), inchrefl(F,P,R), permutare(R,OrdP).

verifAsatepsilon :- multime(A), detf(F), detR(R), 
	not((member(X,A), member((X,FX),F), member((FX,FFX),F), 
	member(Y,A), member((Y,FY),F), member((FY,FFY),F), 
	not(echiv(FX=FFY, member((FFX,FY),R))))).

testAnusatepsilon :- multime(A), detf(F), detR(R), member(X,A), write('x='), write(X),
	write(', f(x)='), member((X,FX),F), write(FX),
	write(', f(f(x))='), member((FX,FFX),F), write(FFX), nl,
	not((member(Y,A), write('y='), write(Y), 
	write(', f(y)='), member((Y,FY),F), write(FY), 
	write(', f(f(y))='), member((FY,FFY),F), write(FFY), nl,
	echiv(FX=FFY, member((FFX,FY),R)))).


