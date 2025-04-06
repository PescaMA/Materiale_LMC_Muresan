/* Sa demonstram in Prolog, prin tabele de adevar, proprietatile operatiilor si relatiilor
intre multimi din prima parte a primului seminar. Vom vedea ca demonstrarea acestor
proprietati de calcul cu multimi prin intermediul proprietatilor analoge ale conectorilor
logici sta la baza algebrizarii logicii propozitionale clasice.
Conectorul logic unar, anume negatia (non sau not), il vom considera mai prioritar decat
cei binari: sau, si, =>, <=>, xor etc.. Asadar, pentru p, q enunturi arbitrare: enuntul
non p sau q este echivalent cu (non p) sau q si nu cu enuntul: non (p sau q).
Fie A, B, C, D multimi arbitrare, fixate. Fie x arbitrar, fixat.
In cele ce urmeaza, vom reprezenta prin variabilele A, B, C, D in Prolog proprietatile
a, b, c, d de mai jos:
a: x apartine lui A;
b: x apartine lui B;
c: x apartine lui C;
d: x apartine lui D.
In continuare voi reprezenta principalele operatii si relatii intre multimi astfel:
reuniunea: U
intersectia: ^
diferenta: \
diferenta simetrica: /\
incluziunea nestricta: <=  (si in sens invers: >=)
incluziunea stricta: <  (si in sens invers: >)
nonegalitatea: =/=
Iar multimea partilor unei multimi M o voi nota cu P(M).
Conform definitiilor acestor operatii cu multimi si notatiilor de mai sus:
x apartine lui AUB <=> a sau b
x apartine lui A^B <=> a si b
x apartine lui A\B <=> a si non b
x apartine lui A/\B <=> a xor b
Conform definitiilor relatiilor intre multimi:
A=B <=> (oricare ar fi y)(y apartine lui A <=> y apartine lui B)
A<=B <=> (oricare ar fi y)(y apartine lui A => y apartine lui B)
A<B <=> (A<=B si A=/=B)
Cum x este arbitrar, aceste relatii intre multimi se transcriu, respectiv, in:
a <=> b
a => b
(a => b) si non(a <=> b)
Daca reprezentam nonechivalenta prin <=/=>, proprietatea anterioara se scrie:
(a => b) si (a <=/=> b)
Mai precis, de exemplu pentru egalitatea de multimi:
daca A=B, atunci a<=>b;
pentru a demonstra ca A=B, este suficient sa aratam ca a<=>b, adica:
	x apartine lui A <=> x apartine lui B,
intrucat x este arbitrar.
La fel pentru incluziunea nestricta si incluziunea stricta.
Amintesc ca multimea vida este unica multime care satisface:
(oricare ar fi y)(y nu apartine multimii vide), adica:
(oricare ar fi y)(y apartine multimii vide este fals), adica:
(oricare ar fi y)(non (y apartine multimii vide)), asadar:
	x apartine multimii vide este fals.
Amintesc conectorii logici predefiniti in Prolog:
si (conjunctia): ","
sau (disjunctia): ";"
non (negatia): "not" sau "\+"
Definim implicatia, echivalenta si sau-ul exclusiv: */

implica(P,Q) :- not(P) ; Q.

echiv(P,Q) :- implica(P,Q), implica(Q,P).

% xor(P,Q) :- P,not(Q) ; Q,not(P).

/* Pentru usurinta scrierii, sa definim sau-ul exclusiv ca operator binar infixat; in
urmatoarea declaratie, 500 este precedenta operatorului; precedentele sunt opusul
prioritatilor: cu cat un operator are precedenta mai mare, cu atat acel operator are
prioritatea mai mica; de exemplu, constantele, expresiile incadrate in paranteze, termenii
de forma operator(argumentul1,argumentul2,...,argumentuln) au precedenta 0, deci prioritatea
cea mai mare, intrucat valorile precedentelor sunt numere naturale): */ 

:- op(500,xfx,xor).

P xor Q :- P,not(Q) ; Q,not(P).

/* Conform celor de mai sus:
idempotenta reuniunii: AUA=A, este echivalenta cu idempotenta disjunctiei: (a sau a)<=>a;
idempotenta intersectiei: A^A=A, este echivalenta cu idempotenta conjunctiei: (a si a)<=>a.
Sa demonstram, asadar, semantic (adica prin tabele de adevar) aceste proprietati de calcul
cu multimi, adica sa aratam ca au loc echivalentele de mai sus pentru orice valoare de
adevar a lui a, reprezentata, cum am stabilit mai sus, prin variabila A in Prolog. Dupa
cum am vazut in lectiile anterioare, faptul ca orice enunt, de orice valoare de adevar,
satisface aceste proprietati, este echivalent cu faptul ca nu exista enunt (de o anumita
valoare de adevar) care sa nu satisfaca aceste proprietati.
Pentru a confirma parcurgerea tuturor valorilor booleene, le vom afisa la fiecare pas. */

idempreun :- not((member(A,[false,true]), write(A), nl, not(echiv(A;A,A)))).

idempinters :- not((member(A,[false,true]), write(A), nl, not(echiv((A,A),A)))). /* perechea
	suplimentara de paranteze e necesara pentru a specifica faptul ca acea virgula este
	conjunctie si nu separator de argumente ale lui echiv, la fel ca perechea
	suplimentara de paranteze care incadreaza argumentul primului not */

/* Faptul ca A\A=multimea vida, respectiv A/\A=multimea vida, este echivalent cu:
(a si non a)<=>fals, respectiv (a xor a)<=>fals. */

difvida :- not((member(A,[false,true]), write(A), nl, not(echiv((A,not(A)),false)))).

% difsimvida :- not((member(A,[false,true]), write(A), nl, not(echiv(xor(A,A),false)))).

difsimvida :- not((member(A,[false,true]), write(A), nl, not(echiv(A xor A,false)))).

/* Vom folosi in mod repetat generarea de perechi si triplete de valori booleene, iar, mai
tarziu, si generarea de cvadruplete de valori booleene: */

pereche(A,B) :- member(A,[false,true]), member(B,[false,true]), write((A,B)), nl.

triplet(A,B,C) :- member(A,[false,true]), member(B,[false,true]), member(C,[false,true]),
			write((A,B,C)), nl.

cvadruplet(A,B,C,D) :- member(A,[false,true]), member(B,[false,true]),
		member(C,[false,true]), member(D,[false,true]), write((A,B,C,D)), nl.

comutreun :- not((pereche(A,B), not(echiv(A;B,B;A)))).

comutinters :- not((pereche(A,B), not(echiv((A,B),(B,A))))).

% comutdifsim :- not((pereche(A,B), not(echiv(xor(A,B),xor(B,A))))).

comutdifsim :- not((pereche(A,B), not(echiv(A xor B,B xor A)))).

/* Asociativitatea reuniunii: (AUB)UC=AU(BUC), a intersectiei: (A^B)^C=A^(B^C), respectiv a
diferentei simetrice: (A/\B)/\C=A/\(B/\C), este echivalenta cu asociativitatea disjunctiei:
[(a sau b) sau c]<=>[a sau (b sau c)], a conjunctiei: [(a si b) si c]<=>[a si (b si c)],
respectiv a sau-lui exclusiv: [(a xor b) xor c]<=>[a xor (b xor c)]. */

asocreun :- not((triplet(A,B,C), not(echiv((A;B);C,A;(B;C))))).

asocinters :- not((triplet(A,B,C), not(echiv(((A,B),C),(A,(B,C)))))).

% asocdifsim :- not((triplet(A,B,C), not(echiv(xor(xor(A,B),C),xor(A,xor(B,C)))))).

asocdifsim :- not((triplet(A,B,C), not(echiv((A xor B) xor C,A xor (B xor C))))).

/* Distributivitatea reuniunii fata de intersectie: AU(B^C)=(AUB)^(AUC), respectiv a
intersectiei fata de reuniune: A^(BUC)=(A^B)U(A^C), este echivalenta cu distributivitatea
disjunctiei fata de conjunctie: [a sau (b si c)] <=> [(a sau b) si (a sau c)], respectiv a
conjunctiei fata de disjunctie: [a si (b sau c)] <=> [(a si b) sau (a si c)]. */

distribreunfdinters :- not((triplet(A,B,C), not(echiv(A;(B,C),((A;B),(A;C)))))).

distribintersfdreun :- not((triplet(A,B,C), not(echiv((A,(B;C)),(A,B;A,C))))). /* alte
	paranteze nu sunt necesare, intrucat precedenta disjunctiei in Prolog este mai mare,
	deci prioritatea sa e mai mica decat a conjunctiei */

/* Faptul ca o reuniune (binara sau, mai general, nevida - vom vedea) isi include termenii, 
respectiv o intersectie (la fel) este inclusa in termenii sai este echivalent cu faptul ca
o disjunctie este implicata de fiecare termen al sau, respectiv o conjunctie isi implica
fiecare termen: incluziunea A<=AUB, respectiv A^B<=A este echivalenta cu: a=>(a sau b),
respectiv: (a si b)=>a. */

terminclreun :- not((pereche(A,B), not(implica(A,A;B)))).

intersinclterm :- not((pereche(A,B), not(implica((A,B),A)))).

% Faptul ca AUB=B <=> A<=B <=> A^B=A este echivalent cu: [(a sau b)<=>b]<=>(a=>b)<=>[(a si b)<=>a]:

inclvsreun :- not((pereche(A,B), not(echiv(echiv(A;B,B),implica(A,B))))).

inclvsinters :- not((pereche(A,B), not(echiv(implica(A,B),echiv((A,B),A))))).

/* Faptul ca multimea vida<=A, respectiv A<=A (reflexivitatea incluziunii nestricte), respectiv
non(A<A) (ireflexivitatea incluziunii stricte) este echivalent cu: fals=>a, a=>a, respectiv
non[(a=>a) si non(a<=>a)]: */

vidainclorice :- not((member(A,[false,true]), write(A), nl, not(implica(false,A)))).

reflincl :- not((member(A,[false,true]), write(A), nl, not(implica(A,A)))).

ireflinclstr :- not((member(A,[false,true]), write(A), nl, implica(A,A), not(echiv(A,A)))).

/* Faptul ca unica submultime a multimii vide este multimea vida, i.e. P(multimea vida)={multimea
vida}, adica A<=multimea vida <=> A=multimea vida, este echivalent cu: (a=>fals)<=>(a<=>fals): */

submultvida :- not((member(A,[false,true]), write(A), nl,
		not(echiv(implica(A,false),echiv(A,false))))).

/* Faptul ca AUmultimea vida=A, respectiv A^multimea vida=multimea vida, este echivalent cu:
(a sau fals)<=>a, respectiv (a si fals)<=>fals: */

reuncuvida :- not((member(A,[false,true]), write(A), nl, not(echiv(A;false,A)))).

interscuvida :- not((member(A,[false,true]), write(A), nl, not(echiv((A,false),false)))).

/* Faptul ca A\multimea vida=A, respectiv multimea vida\A=multimea vida, respectiv A/\multimea vida=A,
este echivalent cu: (a si not(fals))<=>a, respectiv (fals si not(a))<=>fals, respectiv
(a xor fals)<=>a: */

difcuvida :- not((member(A,[false,true]), write(A), nl, not(echiv((A,not(false)),A)))).

vidadif :- not((member(A,[false,true]), write(A), nl, not(echiv((false,not(A)),false)))).

difsimcuvida :- not((member(A,[false,true]), write(A), nl, not(echiv(A xor false,A)))).

/* Faptul ca AUB=multimea vida<=>(A=multimea vida si B=multimea vida) este echivalent cu:
[(a sau b)<=>false]<=>[(a<=>false) si (b<=>false)]: */

reunvida :- not((pereche(A,B), not(echiv(echiv(A;B,false),(echiv(A,false),echiv(B,false)))))).

/* Ca mai sus demonstram semantic (i.e. pentru fiecare valoare booleana pentru fiecare
dintre proprietatile a,b,c,d care intervin in proprietatea curenta) proprietatile urmatoare:
*/

% A\B=multimea vida <=> A<=B, iar A/\B=multimea vida <=> A=B:

difvidaincl :- not((pereche(A,B), not(echiv(echiv((A,not(B)),false),implica(A,B))))).

difsimvidaegal :- not((pereche(A,B), not(echiv(echiv(A xor B,false),echiv(A,B))))).

/* Amintesc ca egalitatea A=B, respectiv incluziunea nestricta A<=B, este echivalenta cu
a<=>b, respectiv a=>b, ceea ce, in Prolog, se transcrie in echiv(A,B), respectiv
implica(A,B). Sa definim, asadar, incluziunea stricta A<B prin: */

inclstr(A,B) :- implica(A,B), not(echiv(A,B)).

% A<B <=> (A<=B si non(B<=A)):

inclsstrinclnoninclop :- not((pereche(A,B), 
	not(echiv(inclstr(A,B),(implica(A,B),not(implica(B,A))))))).

% A<B <=> (A<=B si B\A=/=multimea vida):

inclsstrincldifnevida :- not((pereche(A,B), 
	not(echiv(inclstr(A,B),(implica(A,B),not(echiv((B,not(A)),false))))))).

/* Tranzitivitatea incluziunii nestricte: (A<=B si B<=C) => A<=C, scrisa prescurtat A<=B<=C => A<=C,
este echivalenta cu tranzitivitatea implicatiei: [(a=>b) si (b=>c)] => (a=>c), scrisa 
prescurtat (a=>b=>c)=>(a=>c): */

tranzincl :- not((triplet(A,B,C), not(implica((implica(A,B),implica(B,C)),implica(A,C))))).

% (A<B si B<=C) => A<C, scrisa prescurtat A<B<=C => A<C:

inclstrincl :- not((triplet(A,B,C), not(implica((inclstr(A,B),implica(B,C)),inclstr(A,C))))).

% A<=B => C\B<=C\A:

inclcompstgdif :- not((triplet(A,B,C), 
	not(implica(implica(A,B),implica((C,not(B)),(C,not(A))))))).

% (A<=B si C<=D) => C\B<=D\A:

comp2incldif :- not((cvadruplet(A,B,C,D), 
	not(implica((implica(A,B),implica(C,D)),implica((C,not(B)),(D,not(A))))))).

% (A<=C si B<=C) <=> AUB<=C:

reuninclvstermreunincl :- not((triplet(A,B,C), 
	not(echiv((implica(A,C),implica(B,C)),implica(A;B,C))))).

% A\B <= A:

difincl1term :- not((pereche(A,B), not(implica((A,not(B)),A)))).

% A^(A\B) = A\B:

interscudif :- not((pereche(A,B), not(echiv((A,(A,not(B))),(A,not(B)))))).

% A^B=multimea vida <=> A\B=A:

intersvidavsdif :- not((pereche(A,B), not(echiv(echiv((A,B),false),echiv((A,not(B)),A))))).

/* Pentru cele ce urmeaza vom considera o multime T care include multimile A si B, vom nota
cu -M = T\M: complementara lui M fata de T, pentru orice submultime M a lui T, si vom
considera proprietatea:
	t: x apartine lui T,
pe care o vom reprezenta prin variabila T in Prolog.
Pentru a demonstra semantic proprietatile urmatoare, putem proceda in doua moduri:
-> ca mai sus, considerand, in plus, proprietatea t (ca avand o valoare booleana arbitrara)
sau
-> considerand proprietatile a (x apartine lui A) si b (x apartine lui B) pentru un element
x al lui T, deci presupunand, pentru cele ce urmeaza, ca x apartine lui T, adica
proprietatea t este adevarata.
Pentru orice submultime M a lui T, daca notam cu m proprietatea urmatoare:
	m: x apartine lui M,
atunci: x apartine lui -M ddaca x apartine lui T\M ddaca (t si non m), care, in ipoteza ca
t este adevarata, este echivalenta cu non m.
Asadar, pentru x element al lui T, deci in ipoteza ca t este adevarata, avem, de exemplu:
	x apartine lui -A <=> non a;
	x apartine lui -B <=> non b.
Sa nu uitam ca am considerat multimea T ca incluzand pe A si pe B, asadar, daca x apartine
lui A sau lui B, atunci x apartine lui T, adica au loc: (a=>t) si (b=>t), iar acestea pot fi
impuse ca ipoteze in demonstratiile de mai jos; proprietatile care nu au nevoie de aceste
ipoteze pentru a fi adevarate, cum este: A<=B => T\B<=T\A, sunt valabile pentru orice
multime T: nu este nevoie s-o presupunem ca avand A si B drept submultimi.
OBSERVATIE: cum, in cazul in care A<=T si B<=T, avem A^T=A si B^T=B conform unei proprietati
de mai sus (au loc chiar: A<=T <=> A^T=A <=> AUT=T, si la fel pentru B in locul lui A),
rezulta ca, in acest caz, avem: (A=B <=> A^T=B^T), (A<=B <=> A^T<=B^T) si (A<B <=> A^T<B^T),
asadar, pentru a demonstra, de exemplu, incluziunea A<=B, adica faptul ca (oricare ar fi y)
(y apartine lui A => y apartine lui B), ceea ce se poate scrie sub forma a=>b, adica
x apartine lui A => x apartine lui B pentru elementul x arbitrar, avem de demonstrat ca
(oricare ar fi y)(y apartine lui A^T => y apartine lui B^T), adica (oricare ar fi y)
[(y apartine lui A si y apartine lui T) => (y apartine lui B si y apartine lui T)], ceea
ce se poate observa (demonstrand separat fiecare implicatie sau scriind implicatiile p=>q
sub forma echivalenta non p sau q si aplicand faptul ca non(p si q)<=>(non p sau non q) si
cuantificatorul universal este distributiv fata de conjunctie) ca este echivalent cu
(oricare ar fi y)[y apartine lui T => [(y apartine lui A) => (y apartine lui B)]], adica
(oricare ar fi y apartinand lui T)[(y apartine lui A) => (y apartine lui B)], ceea ce se
poate scrie ca a=>b, i.e. x apartine lui A => x apartine lui B, pentru x element al lui T.
Cum A\B <= A, iar A si B sunt multimi arbitrare, rezulta ca -M = T\M <= T pentru orice
multime M cu M<=T: a demonstra acest lucru ar reveni la a redenumi variabilele din regula
de definitie a predicatului difincl1term de mai sus, ceea ce sigur ca nu ar schimba
definitia lui difincl1term.
La fel, faptul ca A<=B => T\B<=T\A (adica -B<=-A pentru A, B submultimi ale lui T) este
proprietatea A<=B => C\B<=C\A de mai sus aplicata pentru C=T.
De asemenea, proprietatea ca A^(T\A)=multimea vida (adica A^-A=multimea vida pentru A
submultime a lui T) este proprietatea A^(B\A)=multimea vida pe care o aveti ca tema
aplicata pentru B=T.
Acum sa demonstram ca -(multimea vida)=T si -T=multimea vida: */

% ca mai sus, pentru proprietatea t avand o valoare booleana arbitrara:

complemmultvida :- not((member(T,[false,true]), write(T), nl,
			not(echiv((T,not(false)),T)))).

complemmulttotala :- not((member(T,[false,true]), write(T), nl,
			not(echiv((T,not(T)),false)))).

% iar cu proprietatea t presupusa adevarata:

complemvida :- echiv(not(false),true).

complemtotala :- echiv(not(true),false).

% Sa demonstram ca --A=A, cu proprietatea t avand o valoare booleana arbitrara:

dublacomplemeid :- not((pereche(A,T), implica(A,T), not(echiv((T,not((T,not(A)))),A)))).
		% (nu exista o astfel de pereche care sa satisfaca acea implicatie si
		% sa nu satisfaca acea echivalenta)

% si acum cu proprietatea t presupusa adevarata:

dublacomplem :- not((member(A,[false,true]), write(A), nl, not(echiv(not(not(A)),A)))).

/* Sa demonstram ca A\B = A^-B, cu proprietatea t avand o valoare booleana arbitrara:
putem observa ca avem nevoie ca A sa fie submultime a lui T, nu neaparat si B (dar nu e
nevoie sa observam acest lucru; daca nu "iese" demonstratia semantica pentru acest caz,
atunci adaugam ipoteza ca B<=T): */

difeinterscucomplem :- not((triplet(A,B,T), implica(A,T),
		not(echiv((A,not(B)),(A,T,not(B)))))).
	% conjunctia, respectiv intersectia, sunt asociative, asadar
	% nu avem nevoie de alte paranteze

/* Conform OBSERVATIEI de mai sus, intrucat A\B<=A<=T si A^-B<=A<=T, pentru a demonstra
egalitatea A\B = A^-B, cu ambii membri inclusi in T, este suficient sa aratam ca x apartine
membrului stang (A\B) ddaca x apartine membrului drept (A^-B) in ipoteza ca proprietatea t
(x apartine lui T) este adevarata, caz in care proprietatea x apartine lui A^-B, adica
x apartine lui A si x apartine lui -B, este echivalenta cu a si non b (x apartine lui A si 
x nu apartine lui B), asadar aceasta varianta de demonstratie devine triviala: */

difinterscomplem :- not((pereche(A,B), not(echiv((A,not(B)),(A,not(B)))))).

% Prima lege a lui De Morgan: -(AUB) = -A^-B, cu t avand o valoare booleana arbitrara:

legea1DeMorgan :- not((triplet(A,B,T), implica(A,T), implica(B,T),
			not(echiv((T,not(A;B)),(T,not(A),T,not(B)))))).
	% ca mai sus, nu am pus alte paranteze, intrucat
	% conjunctia, respectiv intersectia, sunt asociative

% iar cu t presupusa adevarata:

lege1DeMorgan :- not((pereche(A,B), not(echiv(not(A;B),(not(A),not(B)))))).

% A=B <=> -A=-B, cu t avand o valoare booleana arbitrara:

egalvsegalcomplem :- not((triplet(A,B,T), implica(A,T), implica(B,T),
			not(echiv(echiv(A,B),echiv((T,not(A)),(T,not(B))))))).

% si cu t presupusa adevarata:

egalcomplem :- not((pereche(A,B), not(echiv(echiv(A,B),echiv(not(A),not(B)))))).

% AU-A=T, cu t avand o valoare booleana arbitrara:

reuncucomplemtotala :- not((pereche(A,T), implica(A,T), not(echiv((A;T,not(A)),T)))).

% si cu t presupusa adevarata:

reuncucomplem :- not((member(A,[false,true]), write(A), nl, not(echiv((A;not(A)),true)))).

/* A^B=multimea vida <=> A<=-B, cu t avand o valoare booleana arbitrara: putem observa ca
proprietatea A^B=multimea vida <=> A<=T\B are loc pentru A<=T, iar B arbitrara: nu e nevoie
ca T<=B (decat pentru a scrie complementara in prima scriere a acestei echivalente): */

intersvidavsinclcomplem :- not((triplet(A,B,T), implica(A,T),
		not(echiv(echiv((A,B),false),implica(A,(T,not(B))))))).

% si cu t presupusa adevarata:

intersvidainclcomplem :- not((pereche(A,B),
			not(echiv(echiv((A,B),false),implica(A,not(B)))))).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

/* Sa generam functiile intre doua multimi finite (ca sa poata fi reprezentate ca liste in
Prolog) cu un predicat ternar functie(+Domeniu,+Codomeniu,-Grafic).
Identificam fiecare functie f:A->B, f=(A,G,B), cu graficul ei: f=G={(a,f(a)) | a in A}. */

functie([],_,[]).
functie([H|T],B,[(H,FH)|U]) :- member(FH,B), functie(T,B,U).

% Putem genera aceste functii si ca triplete (domeniu,grafic,codomeniu):

functiecatriplet([],B,([],[],B)).
functiecatriplet([H|T],B,([H|T],[(H,FH)|U],B)) :- member(FH,B), functiecatriplet(T,B,(T,U,B)).

functiile(A,B,ListaFct) :- setof(Fct, functie(A,B,Fct), ListaFct).

/* Afisarea acestor functii f:A->B sub forma:
  x | ...elementele a ale lui A...
_______________________________________

f(x)| ...f(a) pentru fiecare a din A...
Exemplu:
  x | 1 2 3
____________

f(x)| a a b
f:{1,2,3}->{a,b}, f(1)=f(2)=a, f(3)=b
*/

scriefunctiile(A,B) :- functiile(A,B,ListaFct), scrielistafct(ListaFct).

scrielistafct([]).
scrielistafct([Fct|ListaFct]) :- scriefct(Fct), nl, nl, scrielistafct(ListaFct).

% scriefct(Fct) 

detdom([],[]).
detdom([(H,_)|U],[H|T]) :- detdom(U,T).

detimag([],[]).
detimag([(_,FH)|U],[FH|T]) :- detimag(U,T).

scrielista([]).
scrielista([H|T]) :- write(H), tab(1), scrielista(T).

scriefct(Fct) :- detdom(Fct,A), detimag(Fct,Im), write('  x | '), scrielista(A), nl,
		length(A,Nr), tragelinie(Nr), nl, nl, write('f(x)| '), scrielista(Im).

tragelinie(0) :- write('__'), !.
tragelinie(Nr) :- write('__'), P is Nr-1, tragelinie(P).

scriefunctiilecunr(A,B) :- functiile(A,B,ListaFct), scrielistafctcunr(ListaFct,0).

scrielistafctcunr([],_).
scrielistafctcunr([Fct|ListaFct],Nr) :- S is Nr+1, write('A '), write(S), write('-a functie:'), nl,
					scriefct(Fct), nl, nl, scrielistafctcunr(ListaFct,S).

%%% Exercitiul cu proprietati ale substantelor din primul material de seminar:

ipoteza1(A,B,C,D) :- implica((A,B),C xor D).
ipoteza2(A,B,C,D) :- implica((B,C),(A,D;not(A),not(D))).
ipoteza3(A,B,C,D) :- implica((not(A),not(B)),(not(C),not(D))).

ipoteza(A,B,C,D) :- ipoteza1(A,B,C,D), ipoteza2(A,B,C,D), ipoteza3(A,B,C,D).

cerinta1(A,B,C) :- implica((not(A),not(B)),not(C)).
cerinta2(A,B,C) :- not((A,B,C)).

rezolvare1 :- not((cvadruplet(A,B,C,D), ipoteza(A,B,C,D), not(cerinta1(A,B,C)))).
rezolvare2 :- not((cvadruplet(A,B,C,D), ipoteza(A,B,C,D), not(cerinta2(A,B,C)))).





