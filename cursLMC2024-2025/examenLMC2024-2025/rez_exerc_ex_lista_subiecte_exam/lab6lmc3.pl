:- [lab5lmc7,temele6la10].

/* Multimea morfismelor de latici marginite intre laticile Ore (M1,Ord1) si 
(M2,Ord2); daca acestea sunt latici booleene (algebre Boole), atunci acestea
sunt chiar morfisme booleene: */

morflatmarg(M1,Ord1,M2,Ord2,MultFct) :- 
	colectfct(M1,Ord1,M2,Ord2,critmorflatmarg,MultFct).

/* Multimea morfismelor surjective de latici marginite
intre laticile Ore (M1,Ord1) si (M2,Ord2): */

morfsurjlatmarg(M1,Ord1,M2,Ord2,MultFct) :- 
	colectfct(M1,Ord1,M2,Ord2,critmorfsurjlatmarg,MultFct).

/* Predicat satisfacut ddaca Fct e morfism de latici marginite
intre laticile Ore (M1,Ord1) si (M2,Ord2): */

critmorfsurjlatmarg(M1,Ord1,M2,Ord2,Fct) :- 
	critmorflatmarg(M1,Ord1,M2,Ord2,Fct), esurj(Fct,M2).

% cubul ca latice Ore:

cubL2la3([0,a,b,c,x,y,z,1],Ord) :-  
	ordinedinsucc([(0,a),(0,b),(0,c),(a,x),(a,y),(b,x),(b,z),(c,y),(c,z),(x,1),(y,1),(z,1)],[0,a,b,c,x,y,z,1],Ord).

/* Timpul de executie al urmatoarei interogari este destul de lung, asa ca 
vom afisa pe ecran durata in secunde a determinarii morfismelor booleene,
respectiv a morfismelor booleene surjective de la cub la romb:
?- cubL2la3(A,OrdA), romb(B,OrdB), InitMorf is cputime, morflatmarg(A,OrdA,B,OrdB,MultFct), FinMorf is cputime, TimpMorf is FinMorf-InitMorf, write(TimpMorf), write(' secunde'), nl, scrielistafct(MultFct), nl, InitMorfSurj is cputime, morfsurjlatmarg(A,OrdA,B,OrdB,MultFctSurj), FinMorfSurj is cputime, nl, TimpMorfSurj is FinMorfSurj-InitMorfSurj, write(TimpMorfSurj), write(' secunde'), nl, scrielistafct(MultFctSurj).
*/

/* Multimea filtrelor principale ale unei algebre Boole data prin 
laticea Ore (Mult,Ord) subiacenta ei; la fel vor fi date algebrele Boole 
pentru predicatele de mai jos: */

filtreprinc(Mult,Ord,FiltrePrinc) :- auxfiltreprinc(Mult,Mult,Ord,FiltrePrinc).

auxfiltreprinc([],_,_,[]).
auxfiltreprinc([H|T],Mult,Ord,[FgendeH|ListaFiltre]) :-
	majorantii([H],Mult,Ord,FgendeH),
	auxfiltreprinc(T,Mult,Ord,ListaFiltre).

/* Daca primul argument al predicatului urmator e o submultime a lui Mult,
atunci acest predicat e satisfacut ddaca acest argument e un filtru al
algebrei Boole (Mult,Ord): */

filtru([H|T],Mult,Ord) :- not((member(X,[H|T]), member(Y,[H|T]), 
	member(Z,Mult), inf([X,Y],Mult,Ord,XsiY), member((X,Z),Ord),
	(not(member(XsiY,[H|T])) ; not(member(Z,[H|T]))))).

/* Putem folosi mai jos predicatul sublista(S,L) din lab4lmc3.pl, care e 
inclus in lab5lmc7.pl, care e inclus in aceasta baza de cunostinte, dar vom 
folosi sublist(S,L), care genereaza sublistele S ale listei L fara duplicate: */

sublist([],_).
sublist([H|T],[H|L]) :- sublist(T,L).
sublist([H|T],[_|L]) :- sublist([H|T],L).

% Generarea filtrelor unei algebre Boole (Mult,Ord):

genfiltru(F,Mult,Ord) :- sublist(F,Mult), filtru(F,Mult,Ord).

/* Predicat care testeaza daca F e filtru al algebrei Boole (Mult,Ord), cu
ajutorul predicatului inclusa, pentru care ordinea elementelor din lista F
nu conteaza: */

testfiltru(F,Mult,Ord) :- inclusa(F,Mult), filtru(F,Mult,Ord).

% Multimea filtrelor unei algebre Boole (Mult,Ord):

filtre(Mult,Ord,Filtre) :- setof(F, genfiltru(F,Mult,Ord), Filtre).

% Imaginea unei multimi printr-o functie:

imag([],_,[]).
imag([H|T],Fct,[FdeH|FdeT]) :- member((H,FdeH),Fct), imag(T,Fct,FdeT).

/* Trei variante de scriere a unui predicat care verifica faptul ca imaginea
oricarui filtru al unei algebre Boole (A,OrdA) printr-un morfism boolean de 
la (A,OrdA) la algebra Boole (B,OrdB) este un filtru al lui (B,OrdB); 
putem scrie imfiltru ca mai jos pentru ca inputul (A,OrdA) va fi o algebra 
Boole finita, asadar toate filtrele sale vor fi principale: */

imagfiltru(A,OrdA,B,OrdB) :- morfsurjlatmarg(A,OrdA,B,OrdB,MultFct),
	filtre(A,OrdA,FiltA), not((member(Fct,MultFct), member(F,FiltA),
	imag(F,Fct,G), not(testfiltru(G,B,OrdB)))).

imfiltru(A,OrdA,B,OrdB) :- morfsurjlatmarg(A,OrdA,B,OrdB,MultFct),
	filtreprinc(A,OrdA,FiltA), not((member(Fct,MultFct), member(F,FiltA),
	imag(F,Fct,G), not(testfiltru(G,B,OrdB)))).

imaginefiltru(A,OrdA,B,OrdB) :- not((critmorfsurjlatmarg(A,OrdA,B,OrdB,Fct),
	genfiltru(F,A,OrdA), imag(F,Fct,G), not(testfiltru(G,B,OrdB)))).

testimaginefiltru(A,OrdA,B,OrdB) :- 
	not((critmorfsurjlatmarg(A,OrdA,B,OrdB,Fct), scriefct(Fct), nl,
	genfiltru(F,A,OrdA), write(F), tab(1), imag(F,Fct,G), write(G), nl,
	not(testfiltru(G,B,OrdB)))).

/* Sa interogam, pentru a determina si durata executiei:
?- rombul(M,Ord), Init is cputime, testimaginefiltru(M,Ord,M,Ord), Fin is cputime, Timp is Fin-Init, write(Timp), write(' secunde').
?- cubL2la3(A,OrdA), romb(B,OrdB), Init is cputime, testimaginefiltru(A,OrdA,B,OrdB), Fin is cputime, Timp is Fin-Init, write(Timp), write(' secunde').
*/

% Cele mai mici latici nedistributive: diamantul (M3) si rombul (N5):

diamant([0,a,b,c,1],Ord) :- ordinedinsucc([(0,a),(0,b),(0,c),(a,1),(b,1),(c,1)],[0,a,b,c,1],Ord).

pentagon([0,x,y,z,1],Ord) :- ordinedinsucc([(0,x),(0,y),(y,z),(x,1),(z,1)],[0,x,y,z,1],Ord).

/* Afisarea tuturor morfismelor de latici marginite de la diamant la pentagon 
(nu exista niciunul): */

morfismeM3N5 :- diamant(A,OrdA), pentagon(B,OrdB),
	morflatmarg(A,OrdA,B,OrdB,ListaFct), scrielistafct(ListaFct).

% Afisarea tuturor morfismelor de latici marginite de la romb la pentagon:

morfismerombN5 :- rombul(A,OrdA), pentagon(B,OrdB), 
	morflatmarg(A,OrdA,B,OrdB,ListaFct), scrielistafct(ListaFct).








