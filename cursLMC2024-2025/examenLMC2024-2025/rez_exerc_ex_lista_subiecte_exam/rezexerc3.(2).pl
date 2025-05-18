:- [lab7lmc5].

f(a,b).
f(b,c).
f(c,a).

r([(a,a),(a,b),(a,c),(b,a),(b,b),(b,c)]).

formula(X,Y) :- r(R), implica(f(X,Y),member((X,Y),R)).

verifAlgSatFormula :- not((member(X,[a,b,c]), member(Y,[a,b,c]), 
			not(formula(X,Y)))).

% Varianta:

verificAlgSatisfFormula :- enuntmmvar([univ,univ],[a,b,c],formula).



