:- [lab6lmc1].

/* Ca in laborator, folosim izomofismul boolean f:L2->{false,true}, f(0)=false, f(1)=true.
=> f pastreaza operatiile booleene (le duce pe cele de pe L2 in cele de pe {false,true}).
Fie h:V-L2, arbitrara. => h~:E->L2 transforma conectorii logici in operatii booleene pe L2.
=> foh~:E->{false,true} transforma conectorii logici in operatii booleene pe {false,true}.
Notam cu: Alfa=foh~(alfa)=f(h~(alfa)), Beta=foh~(beta)=f(h~(beta)) si vom calcula f(h~(fi))=
=f(valoarea de adevar a enuntului fi in interpretarea h) cu un predicat binar fi(Alfa,Beta),
deci fi(Alfa,Beta)=foh~(fi)=f(h~(fi)).
fi = [(alfa ^ beta) -> beta] -> (alfa ^ beta) =>
fi(Alfa,Beta) = f(h~(fi)) = f(h~([(alfa ^ beta) -> beta] -> (alfa ^ beta)))
= f([(h~(alfa) ^ h~(beta)) -> h~(beta)] -> (h~(alfa) ^ h~(beta)))
= [(f(h~(alfa)) ^ f(h~(beta))) -> f(h~(beta))] -> (f(h~(alfa)) ^ f(h~(beta)))
= [(Alfa ^ Beta) -> Beta] -> (Alfa ^ Beta).
*/

fi(Alfa,Beta) :- implica(implica((Alfa,Beta), Beta), (Alfa,Beta)).

/* Atunci cand alfa,beta apartin lui V, => Alfa,Beta pot lua orice valoare booleana din
{false,true}, dar nu neaparat valori booleene distincte.
Daca alfa, beta ar fi variabile propozitionale distincte, atunci am putea scrie predicatul
zeroar propr1 astfel:
propr1 :- nuplu([Alfa,Beta]), fi(Alfa,Beta), tab(3), write((Alfa,Beta)).
Dar, pentru ca nu avem si ipoteza ca variabilele propozitionale alfa, beta ar fi distincte,
avem urmatoarele variante de scriere ale lui propr1, cu afisarea de la final optionala:
*/

propr1 :- member(V,[false,true]), Alfa=V, Beta=V, fi(Alfa,Beta), tab(3), write((Alfa,Beta)).

propr1v :- nuplu([Alfa,Beta]), Alfa=Beta, fi(Alfa,Beta), tab(3), write((Alfa,Beta)).

/* Pentru a doua proprietate, avem de demonstrat ca, daca nu exista interpretari care sa 
satisfaca multimea {alfa,beta}, atunci nu exista interpretari care sa satisfaca pe fi, 
adica: daca Alfa,Beta nu pot lua ambele valoarea true, atunci nici fi(Alfa,Beta) nu poate
lua valoarea true, adica enuntul fi e satisfacut cel mult in cazul in care e satisfacuta 
multimea de enunturi {alfa,beta}, si in orice alt caz trebuie ca fi sa nu fie satisfacut,
deci avem de demonstrat ca, pentru orice pereche de valori booleene pentru Alfa,Beta, daca 
Alfa,Beta nu sunt ambele true, atunci fi(Alfa,Beta) nu e true, adica nu exista pereche de 
valori booleene pentru Alfa,Beta care sa nu satisfaca aceasta implicatie, adica nu exista
pereche de valori booleene pentru Alfa,Beta care sa nu satisfaca disjunctia: Alfa,Beta 
sunt ambele true sau fi(Alfa,Beta) nu e true, adica nu exista pereche de valori booleene 
pentru Alfa,Beta care sa satisfaca conjunctia: Alfa,Beta nu sunt ambele true si 
fi(Alfa,Beta) e true: */

propr2 :- not((nuplu([Alfa,Beta]), not((Alfa, Beta)), fi(Alfa,Beta))).

propr2v :- not((nuplu([Alfa,Beta]), not(implica(not((Alfa, Beta)), not(fi(Alfa,Beta)))))).

