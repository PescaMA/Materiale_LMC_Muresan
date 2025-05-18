:- [lab7lmc5].

ipoteza(A,B,P,Q) :- implica(A,implica(P,echiv(implica(true,Q),B))).

concluzia(A,B,P,Q) :- implica((A,B),implica(P,Q)).

proprietatea(A,B,P,Q) :- implica(ipoteza(A,B,P,Q),concluzia(A,B,P,Q)).

demExercLogProp :- demNarg(4,proprietatea).
