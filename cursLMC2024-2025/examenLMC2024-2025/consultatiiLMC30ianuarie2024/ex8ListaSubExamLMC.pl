:- [lab6lmc1].

/* Avem izomofismul boolean f:L2->{false,true}, f(0)=false, f(1)=true.
Fie h:V-L2, arbitrara.
Notam cu: Alfa=f(h~(alfa)), Beta=f(h~(beta)), Gama=f(h~(gama)) si vom calcula 
fi(Alfa,Beta,Gama)=f(h~(fi)), psi(Alfa,Beta,Gama)=f(h~(psi)), unde:
fi = (alfa->beta)<->gama, psi = gama->(alfa^-|beta).
Am notat cu -| negatia logica. Pastrez restul notatiilor de pana acum. */

fi(Alfa,Beta,Gama) :- echiv(implica(Alfa,Beta),Gama).

psi(Alfa,Beta,Gama) :- implica(Gama,(Alfa,not(Beta))).

propr1 :- not((nuplu([Alfa,Beta,Gama]), fi(Alfa,Beta,Gama), psi(Alfa,Beta,Gama), Gama)).

% prescurtat, e ok:

propr1v :- not((nuplu([Alfa,Beta]), fi(Alfa,Beta,true), psi(Alfa,Beta,true))).

% naiv:

propr1inutil :- not((nuplu([Alfa,Beta,true]), fi(Alfa,Beta,true), psi(Alfa,Beta,true))).

% propr2 se poate scrie exact ca propr1:

propr2v :- not((nuplu([Alfa,Beta,Gama]), fi(Alfa,Beta,Gama), psi(Alfa,Beta,Gama), Gama)).

% sau sub forma:

propr2 :- not((nuplu([Alfa,Beta,Gama]), 
	not(implica((fi(Alfa,Beta,Gama), psi(Alfa,Beta,Gama)), not(Gama))))).
