:- [lab7lmc5].

ipoteza(A,B,C,D) :- implica(A,implica(B,implica(C,D))).

concluzia(A,B,C,D) :- not(not(implica(not(D),not((A,B,C))))).

proprietatea(A,B,C,D) :- implica(ipoteza(A,B,C,D),concluzia(A,B,C,D)).

demExercLogProp :- demNarg(4,proprietatea).

%%% Si observatia:

phi(A,B,C,D) :- not(implica(not(D),not((A,B,C)))).

enunt(A,B,C,D) :- ipoteza(A,B,C,D), phi(A,B,C,D).

observatia :- not(satisfNarg(4,enunt)).

varobservatia :- demnegNarg(4,enunt).



