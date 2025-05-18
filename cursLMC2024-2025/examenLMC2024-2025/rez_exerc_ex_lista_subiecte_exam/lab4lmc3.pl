/* Folosim cateva predicate din laboratorul anterior, incepand cu acesta pentru
eliminarea duplicatelor dintr-o lista (transformand-o in multime), cu pastrarea
ultimei aparitii a fiecarei copii a aceluiasi element din acea lista, pentru fiecare
element din lista respectiva: */

elimdup([],[]).
elimdup([H|T],M) :- member(H,T), !, elimdup(T,M).
elimdup([H|T],[H|M]) :- elimdup(T,M).

% Reuniunea a doua multimi:

reun(M,N,R) :- append(M,N,L), elimdup(L,R).

% Intersectia a doua multimi:

inters(_,[],[]).
inters(M,[H|T],[H|L]) :- member(H,M), !, inters(M,T,L).
inters(M,[_|T],L) :- inters(M,T,L).

% Diferenta a doua multimi, prin recurenta dupa descazut:

dif([],_,[]).
dif([H|T],M,D) :- member(H,M), !, dif(T,M,D).
dif([H|T],M,[H|D]) :- dif(T,M,D).

% Diferenta a doua multimi, prin recurenta dupa scazator:

difer(M,[],M).
difer(M,[H|T],D) :- stergetot(H,M,N), difer(N,T,D).

% Diferenta simetrica a doua multimi:

difsim(M,N,D) :- dif(M,N,MminusN), dif(N,M,NminusM), reun(MminusN,NminusM,D).

/* sublista(S,L) e satisfacut ddaca S e sublista a listei L, cu elementele in 
ordinea in care apar in L; genereaza sublistele listei L, iar, daca L e multime,
atunci genereaza submultimile lui L: */

sublista([],_).
sublista([H|T],[H|L]) :- sublista(T,L).
sublista(S,[_|L]) :- sublista(S,L).

% Lista sublistelor, respectiv submultimilor unei liste, respectiv multimi:

listasubliste(L,LS) :- setof(S, sublista(S,L), LS).

/* inclusa(S,M) e satisfacut ddaca S e submultime a lui M, indiferent de ordinea
elementelor sale: */

inclusa([],_).
inclusa([H|T],M) :- member(H,M), inclusa(T,M).

% Stergerea tuturor aparitiilor unui element dintr-o lista:

stergetot(_,[],[]).
stergetot(H,[H|T],L) :- stergetot(H,T,L), !.
stergetot(X,[H|T],[H|L]) :- stergetot(X,T,L).

/* Varianta pentru eliminarea duplicatelor dintr-o lista cu pastrarea primei 
aparitii a fiecarui element in loc de ultima: */

elimindup([],[]).
elimindup([H|T],[H|M]) :- stergetot(H,T,L), elimindup(L,M).

/* Stergerea unei aparitii arbitrare a unui element dintr-o lista; interogati:
?- sterge(Element,[1,2,3,4],ListaRamasa).
Predicatul sterge poate fi folosit si pentru adaugarea unui element pe o pozitie
arbitrara intr-o lista; interogati:
?- sterge(0,DinCeLista,[1,2,3]).
*/

sterge(_,[],[]) :- fail.
sterge(H,[H|T],T).
sterge(X,[H|T],[H|L]) :- sterge(X,T,L).

% permutare(L,P) e satisfacut ddaca P e permutare a listei L:

permutare([],[]).
permutare([H|T],P) :- permutare(T,Q), sterge(H,P,Q).

% Multimea permutarilor unei liste:

listapermutari(L,LP) :- setof(P, permutare(L,P), LP).

% Diagonala unei multimi: diag(MultimeaA,DiagonalaluiA):

diag([],[]).
diag([H|T],[(H,H)|U]) :- diag(T,U).

% Inchiderea reflexiva a unei relatii binare pe o multime:

inchrefl(Rel,Mult,R) :- diag(Mult,Diag), reun(Rel,Diag,R).

% Inversa unei relatii binare:

invrel([],[]).
invrel([(A,B)|T],[(B,A)|R]) :- invrel(T,R).

% Inchiderea simetrica a unei relatii binare pe o multime:

inchsim(R,S) :- invrel(R,Q), reun(R,Q,S).

/* Scriere echivalenta pentru predicatul compun(S,R,Comp) din laboratorul anterior,
care calculeaza in relatia binara Comp compunerea lui S cu R: */

compun(S,R,Comp) :- setof((A,C), B^(member((A,B),R),member((B,C),S)), Comp), !.
compun(_,_,[]).

% Varianta de scriere care nu necesita tratarea separata a cazului Comp=[]:

compunere(S,R,Comp) :- findall((A,C), (member((A,B),R),member((B,C),S)), C),
			elimdup(C,Comp).

% Predicat care testeaza o relatie binara e tranzitiva:

etranz(R) :- compun(R,R,C), inclusa(C,R).

% Inchiderea tranzitiva a unei relatii binare pe o multime:

auxtranz(_,T,T) :- etranz(T), !.
auxtranz(R,Tcurent,T) :- compun(R,Tcurent,Q), reun(R,Q,Turm), auxtranz(R,Turm,T).

inchtranz(R,T) :- auxtranz(R,R,T).

% Produsul cartezian a doua multimi:

prodcart([],_,[]) :- !.
prodcart(_,[],[]) :- !.
prodcart(M,N,P) :- setof((A,B), (member(A,M), member(B,N)), P).

% Scriere echivalenta:

prodcartmult(M,N,P) :- setof((A,B), (member(A,M), member(B,N)), P), ! ; P=[].

% Varianta:

prodcartezmult(M,N,P) :- findall((A,B), (member(A,M), member(B,N)), Q), 
			elimdup(Q,P).

% Produsul cartezian a doua liste:

prodcartlst([],_,[]) :- !.
prodcartlst(_,[],[]) :- !.
prodcartlst(M,N,P) :- bagof((A,B), (member(A,M), member(B,N)), P).

% Varianta:

prodcartezliste(M,N,P) :- findall((A,B), (member(A,M), member(B,N)), P).

% Varianta recursiva, fara metapredicatele setof/bagof/findall:

perechi(_,[],[]).
perechi(A,[H|T],[(A,H)|P]) :- perechi(A,T,P).

prodcartliste([],_,[]).
prodcartliste([H|T],L,P) :- perechi(H,L,Q), prodcartliste(T,L,R), append(Q,R,P).

% Relatia de succesiune Succ asociata unei relatii de ordine Ord:

succord(Succ,Ord) :- setof((A,B), (member((A,B),Ord), A\=B, 
   not((member((A,X),Ord), A\=X, member((X,B),Ord), X\=B))), Succ), ! ; Succ=[].

/* Relatia de succesiune asociata unei ordini totale date de ordonarea elementelor
unei liste [A1,A2,...,An]: A1<A2<...<An; succordtot(Succ,[A1,A2,...,An]) e 
satisfacut ddaca Succ=[(A1,A2),...,(A(n-1),An)]: */

succordtot([],[]).
succordtot([],[_]).
succordtot([(A,B)|R],[A,B|T]) :- succordtot(R,[B|T]).

/* ordtot([A1,A2,...,An],Ord) e satisfacut ddaca Ord e ordinea totala data de 
ordonarea elementelor listei [A1,A2,...,An]: Ord={(Ai,Aj) | 1<=i<=j<=n}: */

ordtot([],[]).
ordtot([H|T],Ord) :- perechi(H,[H|T],P), ordtot(T,O), append(P,O,Ord).

% Relatia de echivalenta asociata unei partitii: eqpart(Echivalenta,Partitie):

eqpart([],[]).
eqpart(Echiv,[Cls|ListaCls]) :- prodcart(Cls,Cls,E), eqpart(Eq,ListaCls),
				append(E,Eq,Echiv).

% Interogati: ?- eqpart(Echiv,[[a,b],[c],[d]]).

/* Lista de relatii de echivalenta asociate partitiilor dintr-o lista de partitii:
leqlpart(ListaEchivalente,ListaPartitii): */

leqlpart([],[]).
leqlpart([E|LE],[P|LP]) :- eqpart(E,P), leqlpart(LE,LP).

/* Interogati: 
?- leqlpart(LEq,[[[a,b],[c],[d]],[[a,b],[c,d]],[[a,b,c],[d]]]), write(LEq).
Cerem explicit scrierea lui LEq, cu predicatul predefinit write, pentru ca LEq 
va fi o lista suficient de lunga incat sa fie afisata truchiat de Prolog ca 
valoare de variabila.
*/

/* Predicat pentru adaugarea unei clase singleton la toate partitiile dintr-o lista
de partitii, obtinand din multimea de partitii a unei multimi finite M, pentru un
element Element care nu se afla in M, multimea de partitii a lui MU{Element} in care
clasa lui Element este singleton, i.e. nu contine ale elemente in afara de Element: 
adclssgl(Element,L,Lmodif) e satisfacut ddaca Lmodif e lista de liste (de liste) 
obtinuta din L prin adaugarea la fiecare lista din L a elementului dat de lista 
singleton [Element]: */

adclssgl(_,[],[]).
adclssgl(A,[P|LP],[[[A]|P]|L]) :- adclssgl(A,LP,L).

/* adfieccls(Element,ListaPartitii,ListaPartitiiModif) obtine din multimea de 
partitii ListaPartitii a unei multimi finite M, pentru un element Element care nu 
se afla in M, multimea de partitii ListaPartitiiModif a lui MU{Element} in care 
clasa lui Element nu este singleton, prin adaugarea lui Element la cate una dintre
clasele fiecarei partitii din ListaPartitii: */

adfiecclspartitie(A,P,M) :- setof([[A|C]|Q], sterge(C,P,Q), M).

adfieccls(_,[],[]).
adfieccls(A,[P|LP],L) :- adfiecclspartitie(A,P,M), adfieccls(A,LP,N), append(M,N,L).

% partitii(Multime,ListaPartitii) calculeaza multimea partitiilor multimii Multime:

partitii([],[]).
partitii([A],[[[A]]]).
partitii([A,B|T],LP) :- partitii([B|T],L), adclssgl(A,L,M), adfieccls(A,L,N),
				append(M,N,LP).

/* echivalente(Multime,ListaEchivalente) calculeaza multimea relatiilor de 
echivalenta pe multimea Multime: */

echivalente(M,LE) :- partitii(M,LP), leqlpart(LE,LP).

% Afisarea fiecarui element al unei liste pe alta linie:

afisare([]).
afisare([H|T]) :- write(H), nl, afisare(T).

/* Interogati:
?- partitii([1,2,3],ListaPartitii), afisare(ListaPartitii).
?- echivalente([1,2,3],ListaEchivalente), afisare(ListaEchivalente).
*/

afispartechiv([]).
afispartechiv([P|LP]) :- write('echivalenta asociata partitiei '), write(P), 
		write(' este '), eqpart(E,P), write(E), nl, afispartechiv(LP).

partechiv(M) :- partitii(M,LP), afispartechiv(LP).

/* Interogati:
?- partechiv([1,2,3]).
*/

% Varianta recursiva, fara setof, pentru predicatul partitii (foloseste adclssgl):

auxadcls(_,[],_,[]).
auxadcls(A,[H|T],Prefix,[P|MP]) :- append(Prefix,[[A|H]|T],P), 
				auxadcls(A,T,[H|Prefix],MP).

adcls(A,Part,MP) :- auxadcls(A,Part,[],MP).

adfiecclasa(_,[],[]).
adfiecclasa(A,[Part|MultPart],MultimePartitii) :- adcls(A,Part,MP), 
	adfiecclasa(A,MultPart,MultP), append(MP,MultP,MultimePartitii).

part([],[]).
part([A],[[[A]]]).
part([A,B|T],MultPart) :- part([B|T],MPart), adclssgl(A,MPart,MP), 
		adfiecclasa(A,MPart,MultP), append(MP,MultP,MultPart).

/* Interogati:
?- part([1,2,3],ListaPartitii), afisare(ListaPartitii).
*/



