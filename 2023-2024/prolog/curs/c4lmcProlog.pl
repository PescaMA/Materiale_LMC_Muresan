/* Amintesc ca, in clauzele dintr-o baza de cunostinte Prolog (un fisier .pl):
-> variabilele din fapte si membrii stangi ai regulilor sunt cuantificate universal;
-> variabilele din interogari (in general variabilele din clauzele scop care apar in orice
etapa a rezolvarii/satisfacerii unei interogari) si variabilele din membrii drepti ai
regulilor care nu apar in membrii stangi ai acelorasi reguli sunt cuantificate existential.
Exemplul pe care l-am dat in curs nu este cel mai adecvat: */

are(vali,mere).
are(ana,pere).
are(ioana,mere) :- !.
%are(ana,_).
are(maria,Ceva) :- are(ana,Ceva), !.
/* are(alina,Ceva) :- are(Persoana,Ceva), are(AltaPersoana,Ceva), Persoana\=AltaPersoana,
		not(member(Persoana,[ana,maria])), not(member(AltaPersoana,[ana,maria])).
*/
are(alina,Ceva) :- are(Persoana,Ceva), are(AltaPersoana,Ceva), Persoana\=AltaPersoana.

/* De exemplu, in fiecare dintre urmatoarele doua reguli, ambele variabile, P si Q, apar in
membrii stangi ai regulii, asadar aceste variabile sunt cuantificate universal: */

implica(P,Q) :- not(P) ; Q. /* Adica: pentru orice P si Q, implica(P,Q) e satisfacuta daca
	e satisfacuta disjunctia not(P) ; Q. Si, cum aceasta este singura clauza din
	definitia predicatului binar implica, inseamna ca "daca" devine "ddaca":
	implica(P,Q) e satisfacuta ddaca e satisfacuta disjunctia not(P) ; Q. */

echiv(P,Q) :- implica(P,Q) , implica(Q,P). /* Adica: pentru orice P si Q, echiv(P,Q) e
	satisfacuta daca e satisfacuta conjunctia implica(P,Q) , implica(Q,P). Si, cum
	aceasta este singura clauza din definitia predicatului binar echiv, inseamna ca
	aceasta regula semnifica: echiv(P,Q) e satisfacuta ddaca e satisfacuta conjunctia
	implica(P,Q) , implica(Q,P).
La fel mai jos: simbolurile neck (:-), semnificand "daca", devin "ddaca" in regulile
urmatoare, care sunt unicele clauze din definitiile predicatelor urmatoare, adica nu exista
in aceasta baza de cunostinte fapte continand predicatele urmatoare (ca operatori dominanti)
si nu exista alte reguli avand in membrii stangi predicatele urmatoare. */

/* Dar, in fiecare dintre urmatoarele doua reguli, variabilele P si Q apar numai in
membrul drept, asadar aceste variabile sunt cuantificate existential: */

valori-satisf-implic :- member(P,[false,true]), member(Q,[false,true]),
			implica(P,Q), write((P,Q)). /* Adica: predicatul zeroar
	valori-satisf-implic e satisfacut daca (conform celor de mai sus, chiar ddaca)
	exista P, Q care sa satisfaca: member(P,[false,true]), member(Q,[false,true]),
	implica(P,Q), write((P,Q)). Si toate perechile de valori pentru variabilele P, Q
	care satisfac aceasta conjunctie dau satisfaceri diferite pentru acest predicat;
	insa interogarea:
?- valori-satisf-implic.
nu contine variabile, asadar intoarce doar true pentru fiecare satisfacere diferita; de
aceea, pentru a vedea si perechile de valori pentru P, Q care satisfac aceasta clauza, am
adaugat afisarea perechii (P,Q) pentru fiecare astfel de pereche care satisface conjunctia:
member(P,[false,true]), member(Q,[false,true]), implica(P,Q). Desigur, ca toate predicatele
de scriere, write((P,Q)) isi face efectul pe ecran si apoi intoarce true, deci e satisfacut.
*/

valori-nu-satisf-implic :- member(P,[false,true]), member(Q,[false,true]),
			not(implica(P,Q)), write((P,Q)). /* Adica: predicatul zeroar
	valori-nu-satisf-implic e satisfacut daca (conform celor de mai sus, chiar ddaca)
	exista P, Q care sa satisfaca: member(P,[false,true]), member(Q,[false,true]),
	not(implica(P,Q)), write((P,Q)). Si toate perechile de valori pentru variabilele P,
	Q care satisfac aceasta conjunctie dau satisfaceri diferite pentru acest predicat.*/

/* Determinarea valorilor booleene care satisfac implicatia se poate face
cu oricare dintre interogarile:
?- member(P,[false,true]), member(Q,[false,true]), implica(P,Q).
?- valori-satisf-implic.
Dupa fiecare solutie/satisfacere trebuie sa dam ;/Next pentru a o vedea pe urmatoarea.
Iar valorile booleene care nu satisfac implicatia pot fi determinate
cu oricare dintre interogarile:
?- member(P,[false,true]), member(Q,[false,true]), not(implica(P,Q)).
?- valori-nu-satisf-implic.
*/

% Pentru a demonstra principiul reducerii la absurd:

princredabs(P,Q) :- echiv(implica(P,Q),implica(not(Q),not(P))).

/* trebuie sa folosim negatia, intrucat variabilele P, Q din membrul drept al urmatoarei
reguli nu apar in membrul stang, asadar sunt cuantificate existential: */

demprincredabs :- not((member(P,[false,true]), member(Q,[false,true]),
			write((P,Q)), nl, not(princredabs(P,Q)))).

/* Deci, pentru a demonstra principiul reducerii la absurd, adica faptul ca, indiferent ce
valori booleene iau P si Q, este satisfacut princredabs(P,Q), demonstram ca nu exista valori
booleene pentru P si Q astfel incat princredabs(P,Q) sa nu fie satisfacut (adica sa fie
satisfacuta negatia lui: not(princredabs(P,Q))).
Scopul de sub primul not din regula anterioara:
?- member(P,[false,true]), member(Q,[false,true]), write((P,Q)), nl, not(princredabs(P,Q)).
este evaluat la false dupa parcurgerea tuturor celor 4 perechi de valori booleene pentru
(P,Q), asadar:
?- demprincredabs.
parcurge toate aceste 4 perechi de valori booleene, apoi se evalueaza la true.
Amintesc ca Prologul:
-> satisface/evalueaza o negatie incercand mai intai sa satisfaca argumentul acelei negatii;
-> satisface/evalueaza o conjunctie de la stanga la dreapta, iar, in momentul in care
intalneste un termen fals/nesatisfacut al acelei conjunctii, atunci intoarce false fara a
mai evalua si restul conjunctiei; de aceea are importanta unde plasam afisari precum cea de
mai sus: write((P,Q)), nl. */



		
