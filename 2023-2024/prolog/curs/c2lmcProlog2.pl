/* Semnificatia unei interogari:
?- p(...,Var,....).
este: pentru ce valori ale variabilelor Var... este satisfacut
(adica intoarce true) predicatul p?
Predicatul dintr-o interogare se numeste scop si poate fi compus:
?- p(...), q(...) ; r(....).
Evaluarea unui scop compus se face de la stanga la dreapta.
Satisfacerea unui scop de tipul:
?- not(p(...)).
se face satisfacand mai intai scopul p(...), apoi evaluand scopul compus not(p(...)).
Satisfacerea unui scop se face prin unificarea acestuia cu:
-> predicatul dintr-un fapt, caz in care rezultatul este true sau este dat de 
valorile variabilelor pentru care s-a realizat acea unificare;
-> membrul stang al unei reguli, caz in care se intra in backtracking, cautand sa se
satisfaca membrul drept al acelei reguli pentru valorile variabilelor pentru care s-a
facut unificarea.
*/

/* Interogati:
?- member(3,[1,2,3,4,5]).
?- member(3,[1,3,2,3,3,4,3,5]).
?- member(X,[1,2,3,4,5]).
si dati ;/Next pentru a cere succesiv solutii.
Predicatele predefinite write, tab, nl isi fac efectul pe ecran, apoi se evalueaza la true.
Interogati:
?- member(X,[1,2,3,4,5]), write(X), nl, fail.
?- not((member(X,[1,2,3,4,5]), write(X), nl, fail)).
Predicatul not este unar, asadar conjunctia de mai sus trebuie incadrata intr-un set
suplimentar de paranteze, altfel Prologul confunda operatorul "," de conjunctie cu
separatorul de argumente.
La fel mai jos la predicatul unar write.
?- member(P,[false,true]), member(Q,[false,true]), member(R,[false,true]), write((P,Q,R)), nl, fail.
?- not((member(P,[false,true]), member(Q,[false,true]), member(R,[false,true]), write((P,Q,R)), nl, fail)).
*/

% Predicat echivalent cu predicatul binar predefinit member:

membru(_,[]) :- fail. /* echivalent: not(membru(_,[]))., intrucat "daca" (neck: :-) din 
	aceasta regula devine "ddaca", pt. ca aceasta e singura regula cu membrul stang (al 
	lui :- ) avand ca operator dominant predicatul binar membru, iar ca al doilea 
	argument al acestuia lista vida [], deci va fi singura regula care se va putea 
	aplica pentru satisfacerea unui scop de tipul: ?- membru(Ceva,[]). */
membru(H,[H|_]). % echivalent: membru(X,[H|_]) :- X=H.
membru(X,[_|T]) :- membru(X,T).

/* Variabilele nedenumite (_) specifica doar locatia unui argument.
In clauzele respective nu avem nevoie de valoarea acelui argument.
Ca mai sus:
membru(_,[]) :- fail. % nimeni nu e membru al listei vide
membru(H,[H|_]). % H e membru intr-o lista cu capul H, indiferent cine e coada listei
membru(X,[_|T]) :- membru(X,T). % X e membru al unei liste daca e membru al cozii listei,
				% indiferent cine e capul listei
*/

apartine(_,[]) :- fail.
apartine(H,[H|_]) :- !.
apartine(X,[_|T]) :- apartine(X,T).

/* Interogati:
?- membru(3,[1,2,3,4,5]).
?- membru(3,[1,3,2,3,3,4,3,5]).
?- membru(X,[1,2,3,4,5]).
?- apartine(3,[1,2,3,4,5]).
?- apartine(3,[1,3,2,3,3,4,3,5]).
?- apartine(X,[1,2,3,4,5]).
*/

implica(P,Q) :- not(P) ; Q.
echiv(P,Q) :- implica(P,Q) , implica(Q,P).

/* Putem observa ca doua proprietati p si q sunt echivalente ddaca au aceeasi valoare de
adevar, interogand: pentru ce perechi de valori booleene e satisfacut predicatul binar echiv:
?- member(P,[false,true]), member(Q,[false,true]), echiv(P,Q).
si dand ;/Next pentru a vedea toate solutiile.
*/

/* Sa demonstram distributivitatea disjunctiei fata de conjunctie:
	[p sau (q si r)] <=> [(p sau q) si (p sau r)]
prin tabel semantic, i.e tabel de valori de adevar. */

ms-distrib-sau-fata-de-si(P,Q,R) :- P ; Q , R.

md-distrib-sau-fata-de-si(P,Q,R) :- (P ; Q) , (P ; R).

distrib-sau-fata-de-si(P,Q,R) :- echiv(ms-distrib-sau-fata-de-si(P,Q,R),md-distrib-sau-fata-de-si(P,Q,R)).

distrib-sau-fata-de-si :- not((member(P,[false,true]), member(Q,[false,true]), member(R,[false,true]), 
				write((P,Q,R)), nl, not(distrib-sau-fata-de-si(P,Q,R)))).

/* Pentru orice valori booleene ale variabilelor P,Q,R este adevarata proprietatea
distrib-sau-fata-de-si(P,Q,R) (anume [P sau (Q si R)] <=> [(P sau Q) si (P sau R)]) ddaca
nu exista triplet de valori booleene care sa nu satisfaca aceasta proprietate.
Putem interoga: ce triplete de valori booleene satisfac proprietatea distrib-sau-fata-de-si:
?- member(P,[false,true]), member(Q,[false,true]), member(R,[false,true]), distrib-sau-fata-de-si(P,Q,R).
si sa dam ;/Next pentru a parcurge toate aceste triplete, sau direct: sa se demonstreze
aceasta proprietate, adica faptul ca proprietatea e satisfacuta pentru toate tripletele de
valori booleene:
?- distrib-sau-fata-de-si.
*/

/* La fel pentru distributivitatea conjunctiei fata de disjunctie:
	[p si (q sau r)] <=> [(p si q) sau (p si r)] */

ms-distrib-si-fata-de-sau(P,Q,R) :- P , (Q ; R).

md-distrib-si-fata-de-sau(P,Q,R) :- P , Q ; P , R.

distrib-si-fata-de-sau(P,Q,R) :- echiv(ms-distrib-si-fata-de-sau(P,Q,R),md-distrib-si-fata-de-sau(P,Q,R)).

distrib-si-fata-de-sau :- not((member(P,[false,true]), member(Q,[false,true]), member(R,[false,true]), 
				write((P,Q,R)), nl, not(distrib-si-fata-de-sau(P,Q,R)))).




 

