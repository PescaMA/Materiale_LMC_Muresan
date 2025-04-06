:- [lab6lmc1].

/* Ca si in baza de cunostinte pentru Laboratorul 6, pe care am inclus-o in cea curenta cu
directiva de mai sus, notam deductia sintactica si faptul de a fi adevar sintactic (i.e. 
teorema formala) prin |-, satisfacerea, deductia semantica si faptul de a fi adevar semantic
(i.e. tautologie, enunt universal adevarat) prin |=, iar negatia logica prin -|.
   La fel ca pana acum, notam cu f:L2->{false,true} functia definita prin: f(0)=false, 
f(1)=true. Intrucat f este bijectiva si transforma operatiile booleene ale algebrei Boole 
standard L2 in conectorii logici aplicati valorilor booleene din {false,true}, care 
determina pe multimea {false,true} o structura de algebra Boole, rezulta ca f este 
izomorfism boolean intre L2 si algebra Boole astfel definita cu multimea suport {false,true}.
   Pana se va mentiona altfel, vom considera o interpretare arbitrara h:V->L2. Cu notatia 
obisnuita, h~:E->L2 va fi prelungirea lui h la multimea E a enunturilor care transforma
conectorii logici (de pe E) in operatii booleene in L2. Cum f pastreaza operatiile booleene, 
compunerea foh~:E->{false,true} transforma conectorii logici (de pe E) in operatii booleene
pe {false,true}.
   Sa ne amintim ca, pentru orice multime Sigma de enunturi si orice enunt epsilon:
   prin definitie, h|=epsilon <=> h~(epsilon)=1, adica, pentru valorile de adevar pe care h
le da variabilelor propozitionale, epsilon e adevarat, i.e. h~ calculeaza valoarea sa de 
adevar ca fiind 1, adica "adevarat"; desigur, singurele valori de adevar care intervin in
calculul lui h~(epsilon) sunt cele ale variabilelor propozitionale p din V(epsilon), adica 
valorile h(p) pentru variabilele propozitionale p care apar in epsilon;
   prin definitie, h|=Sigma <=> (pentru fiecare sigma in Sigma)(h|=sigma);
   conform Teoremei de completitudine, |-epsilon <=> |=epsilon, iar, prin definitie, 
|=epsilon ddaca, (oricare ar fi g:V->L2)(g|=epsilon), adica ddaca epsilon e adevarata 
indiferent ce valori de adevar iau variabilele propozitionale din V(epsilon), i.e. care apar
in epsilon;
   conform Teoremei de completitudine tare, Sigma|-epsilon <=> Sigma|=epsilon, iar, prin 
definitie, Sigma|=epsilon ddaca, (oricare ar fi g:V->L2)(g|=Sigma => g|=epsilon), adica 
ddaca epsilon e adevarata pentru orice valori de adevar pentru variabilele propozitionale 
pentru care toate enunturile din multimea de ipoteze Sigma sunt adevarate.
   Conform celor de mai sus:
h|=epsilon <=> f(h~(epsilon))=true;
h|=Sigma <=> (pentru fiecare sigma in Sigma)(f(h~(sigma))=true);
Sigma|=epsilon <=> (oricare ar fi g:V->L2)((pentru orice sigma in Sigma)(f(g~(sigma))=true)
 => f(g~(epsilon))=true). */

/* Sa demonstram ca, pentru orice multimi de enunturi Sigma1, Sigma2, Sigma3 si orice 
enunturi fi, psi, hi, are loc regula de deductie: 
	Sigma1 U {fi} |- psi, Sigma2 U {psi^hi} |- fi, Sigma3 U {psi} |- hi
	-------------------------------------------------------------------,
		   Sigma1 U Sigma2 U Sigma3 |- fi <-> (psi^hi)
adica, daca multimile de enunturi Sigma1, Sigma2, Sigma3 si enunturile fi, psi, hi satisfac
cele trei ipoteze ale acestei reguli de deductie, anume deductiile sintactice: 
Sigma1 U {fi} |- psi, Sigma2 U {psi^hi} |- fi si Sigma3 U {psi} |- hi, atunci ele satisfac
concluzia acestei reguli de deductie, anume deductia sintactica:
Sigma1 U Sigma2 U Sigma3 |- fi <-> (psi^hi).
   Pentru a demonstra aceasta regula de deductie prin tabel semantic, vom aplica Teorema 
deductiei, apoi Teorema de completitudine tare celor trei ipoteze, astfel:
   Sigma1 U {fi} |- psi <=> Sigma1 |- fi->psi <=> Sigma1 |= fi->psi;
   Sigma2 U {psi^hi} |- fi <=> Sigma2 |- (psi^hi)->fi <=> Sigma2 |= (psi^hi)->fi;
   Sigma3 U {psi} |- hi <=> Sigma3 |- psi->hi <=> Sigma3 |= psi->hi.
   Avem de demonstrat deductia sintactica: Sigma1 U Sigma2 U Sigma3 |- fi <-> (psi^hi), 
care, conform Teoremei de completitudine tare, este echivalenta cu deductia semantica:
Sigma1 U Sigma2 U Sigma3 |= fi <-> (psi^hi). Avem, asadar, de aratat ca, pentru orice
interpretare care satisface multimea Sigma1 U Sigma2 U Sigma3 de ipoteze a acestei deductii
satisface si concluzia ei, enume enuntul fi <-> (psi^hi).
   Sa consideram, asadar, o interpretare h:V->L2 cu proprietatea ca 
h|=Sigma1 U Sigma2 U Sigma3, ceea ce este echivalent cu: h|=Sigma1, h|=Sigma2 si h|=Sigma3,
prin urmare, conform celor trei ipoteze de mai sus si definitiei deductiei semantice, 
h|=fi->psi, h|=(psi^hi)->fi si h|=psi->hi, ceea ce este echivalent cu faptul ca foh~ ia 
valoarea true in fiecare dintre aceste trei enunturi, adica:
   true = f(h~(fi->psi)) = f(h~(fi))->f(h~(psi)),
   true = f(h~((psi^hi)->fi)) = (f(h~(psi))^f(h~(hi)))->f(h~(fi)),
   true = f(h~(psi->hi)) = f(h~(psi))->f(h~(hi)),
unde, in dreapta celui de-al doilea egal, intre valorile lui foh~, avem operatii booleene 
pe multimea {false,true}, definite prin intermediul conectorilor logici; la fel mai jos.
   Avem de demonstrat ca h |= fi<->(psi^hi), adica h~(fi<->(psi^hi))=1, adica 
f(h~(fi<->(psi^hi)))=true, adica f(h~(fi))<->(f(h~(psi))^f(h~(hi)))=true.
   Prin variabilele Prolog Fi, Psi, Hi vom reprezenta valorile booleene: Fi=f(h~(fi)), 
Psi=f(h~(psi)), Hi=f(h~(hi)). */

ipoteza1(Fi,Psi) :- implica(Fi,Psi).

ipoteza2(Fi,Psi,Hi) :- implica((Psi,Hi), Fi).

ipoteza3(Psi,Hi) :- implica(Psi,Hi).

concluzia(Fi,Psi,Hi) :- echiv(Fi, (Psi,Hi)).

reguladeductie(Fi,Psi,Hi) :- 
   implica((ipoteza1(Fi,Psi), ipoteza2(Fi,Psi,Hi), ipoteza3(Psi,Hi)), concluzia(Fi,Psi,Hi)).

demreguladeductie :- not((nuplu([Fi,Psi,Hi]), not(reguladeductie(Fi,Psi,Hi)))).

/* Interogati:
?- demreguladeductie.
*/

% Vom nota cu |=| echivalenta semantica in logica clasica a predicatelor.

/* Algebra (i.e. structura algebrica) (A,f,R) de tip (i.e signatura) (1;2;multimea vida) 
din exercitiul din setul de cursuri cu logica clasica a predicatelor, avand: multimea suport
A={a,b,c,d} (avand |A|=4, deci cu elementele a,b,c,d doua cate doua distincte; le vom 
reprezenta prin constantele a,b,c,d in Prolog), operatia unara f:A->A definita ca mai jos si
relatia binara R={(a,b),(b,c),(c,b),(c,d)} pe multimea A:
 x  | a b c d
--------------
f(x)| b c d a
*/

% Multimea suport A a acestei algebre:

multimeA([a,b,c,d]).

/* Operatia unara f, definita ca relatie binara functionala totala de la A la A, 
prin graficul ei: */

f([(a,b),(b,c),(c,d),(d,a)]).

/* varianta de definitie pentru f, avand in vedere ca aceasta relatie binara este chiar
functie, adica relatie binara functionala totala: */

f(a,b).
f(b,c).
f(c,d).
f(d,a).

/* Prolog-ul permite supraincarcarea operatorilor si nu va face confuzie intre predicatul 
unar f si predicatul binar f de mai sus. */

% Relatia binara R pe multimea A:

r([(a,b),(b,c),(c,b),(c,d)]).

/* Predicat care testeaza daca algebra (A,f,R) de mai sus satisface enuntul:
(exista x)(R(x,f(x))^R(f(x),x)), adica daca exista o valoare pentru x in multimea A pentru
care perechile (x,f(x)) si (f(x),x) apartin relatiei binare R: */

algAsatisfEnunt1 :- multimeA(A), f(F), r(R), member((X,FX),F), member(X,A),
		member((X,FX),R), member((FX,X),R).

% varianta, pentru definitia functiei f prin predicatul binar f:

algAsatisfEnuntul1 :- multimeA(A), r(R), member(X,A), f(X,FX),
		member((X,FX),R), member((FX,X),R).

/* Predicat care testeaza daca algebra (A,f,R) de mai sus satisface enuntul:
(exista x)(oricare ar fi y)(R(y,f(f(x))) v R(f(x),y)), i.e. daca exista x in A astfel incat,
pentru orice y in A, perechea (y,f(f(x))) apartine relatiei binare R sau (f(x),y) apartine
lui R, folosind faptul ca acest enunt este echivalent semantic cu urmatorul enunt avand
ambele variabile cuantificate existential:
(exista x)(oricare ar fi y)(R(y,f(f(x))) v R(f(x),y)) |=| 
(exista x)-|(exista y)-|(R(y,f(f(x))) v R(f(x),y)): */

algAsatisfEnunt2 :- multimeA(A), f(F), r(R), member(X,A), member((X,FX),F),
	member((FX,FFX),F), not((member(Y,A), not(member((Y,FFX),R) ; member((FX,Y),R)))).

% varianta, pentru definitia functiei f prin predicatul binar f:

algAsatisfEnuntul2 :- multimeA(A), r(R), member(X,A), f(X,FX), f(FX,FFX),
		not((member(Y,A), not(member((Y,FFX),R) ; member((FX,Y),R)))).

/* Interogati:
?- algAsatisfEnunt1.
?- algAsatisfEnuntul1.
?- algAsatisfEnunt2.
?- algAsatisfEnuntul2.
Aceasta algebra satisface primul enunt, si vedem ca x=b este singura valoare a variabilei x
pentru care R contine perechile (x,f(x)) si (f(x),x), dar nu satisface al doilea enunt. */

/* Sa notam cu (B,g,S,k) algebra de tip (i.e signatura) (1;2;0) din exercitiul din logica 
clasica a predicatelor de la Seminarul 7, avand: multimea de elemente B={a,b,c} (cu |B|=3),
operatia unara g:B->B definita ca mai jos, relatia binara S egala cu ordinea stricta < a 
lantului cu multimea suport B avand a<b<c, iar constanta k=b:
 x  | a b c
-----------
g(x)| b c a
*/

% Multimea B de elemente:

multimeB([a,b,c]).

% Prima varianta de definitie a lui g:

g([(a,b),(b,c),(c,a)]).

% a doua varianta de definitie pentru g:

g(a,b).
g(b,c).
g(c,a).

/* Relatia binara S={(a,b),(a,c),(b,c)}, dar, presupunand ca exercitiul ne cere s-o 
determinam cu ajutorul unui predicat Prolog, vom proceda astfel: */

s(S) :- ordstrdinsucc([(a,b),(b,c)],S).

% Constanta k:

k(b).

/* Predicat care testeaza daca algebra (B,g,S,k) de mai sus satisface enuntul:
(exista x)(exista y)[g(g(x))=g(y) -> (S(x,k) v -|S(x,g(y)))], i.e. daca exista x si y in B
astfel incat, daca g(g(x))=g(y), atunci perechea (x,k) apartine relatiei binare S sau
perechea (x,g(y)) nu apartine lui S: */

algBsatisfEnunt3 :- multimeB(B), g(G), s(S), k(K), member(X,B), member(Y,B),
	member((X,GX),G), member((GX,GGX),G), member((Y,GY),G),
	implica(GGX=GY, member((X,K),S) ; not(member((X,GY),S))).

% varianta, pentru definitia functiei g prin predicatul binar g:

algBsatisfEnuntul3 :- multimeB(B), s(S), k(K), member(X,B), member(Y,B),
	g(X,GX), g(GX,GGX), g(Y,GY),
	implica(GGX=GY, member((X,K),S) ; not(member((X,GY),S))).

/* Predicat care testeaza daca algebra (B,g,S,k) de mai sus satisface enuntul:
(exista x)(oricare ar fi y)[(S(x,k)^S(k,y)) -> -|S(g(y),g(x))], i.e. daca exista x in B
astfel incat, pentru orice y in B, daca perechile (x,k) si (k,y) apartin relatiei binare S,
atunci perechea (g(y),g(x)) nu apartine lui S, folosind faptul ca acest enunt este 
echivalent semantic cu urmatorul enunt avand ambele variabile cuantificate existential:
(exista x)(oricare ar fi y)[(S(x,k)^S(k,y)) -> -|S(g(y),g(x))] |=|
(exista x)-|(exista y)-|[(S(x,k)^S(k,y)) -> -|S(g(y),g(x))]: */

algBsatisfEnunt4 :- multimeB(B), g(G), s(S), k(K), member(X,B), member((X,GX),G),
	not((member(Y,B), member((Y,GY),G), not(implica((member((X,K),S), member((K,Y),S)),
	not(member((GY,GX),S)))))).

% varianta, pentru definitia functiei g prin predicatul binar g:

algBsatisfEnuntul4 :- multimeB(B), s(S), k(K), member(X,B), g(X,GX),
	not((member(Y,B), g(Y,GY), not(implica((member((X,K),S), member((K,Y),S)),
	not(member((GY,GX),S)))))).

/* Predicat care testeaza daca algebra (B,g,S,k) de mai sus satisface enuntul:
(oricare ar fi x)(exista y)[(S(x,y)) -> (g(x)=k ^ -|(g(y)=x))], i.e. daca, pentru orice x 
in B, exista y in B astfel incat, daca perechea (x,y) apartine relatiei binare S, atunci
g(x)=k si g(y) e diferit de x, folosind faptul ca acest enunt este echivalent semantic cu 
urmatorul enunt avand ambele variabile cuantificate existential:
(oricare ar fi x)(exista y)[(S(x,y)) -> (g(x)=k ^ -|(g(y)=x))] |=|
-|(exista x)-|(exista y)[(S(x,y)) -> (g(x)=k ^ -|(g(y)=x))]: */

algBsatisfEnunt5 :- multimeB(B), g(G), s(S), k(K), not((member(X,B), not((member(Y,B),
	implica(member((X,Y),S), (member((X,K),G), not(member((Y,X),G)))))))).

% varianta:

algBsatisfaceEnunt5 :- multimeB(B), g(G), s(S), k(K), not((member(X,B), member((X,GX),G),
	not((member(Y,B), member((Y,GY),G), implica(member((X,Y),S), (GX=K, GY\=X)))))).

% varianta, pentru definitia functiei g prin predicatul binar g:

algBsatisfEnuntul5 :- multimeB(B), s(S), k(K), not((member(X,B), not((member(Y,B),
	implica(member((X,Y),S), (g(X,K), not(g(Y,X)))))))).

/* Predicat care testeaza daca algebra (B,g,S,k) de mai sus satisface enuntul:
(oricare ar fi x)(oricare ar fi y)(g(x)=g(g(y)) -> S(x,y)), adica inchiderea universala a
formulei g(x)=g(g(y)) -> S(x,y), i.e. daca, pentru orice x si y in B, daca g(x)=g(g(y)), 
atunci perechea (x,y) apartine relatiei binare S, folosind faptul ca acest enunt este 
echivalent semantic cu urmatorul enunt avand ambele variabile cuantificate existential:
(oricare ar fi x)(oricare ar fi y)(g(x)=g(g(y)) -> S(x,y)) |=|
-|(exista x)-|(oricare ar fi y)(g(x)=g(g(y)) -> S(x,y)) |=|
-|(exista x)(exista y)-|(g(x)=g(g(y)) -> S(x,y)) |=|: */

algBsatisfEnunt6 :- multimeB(B), g(G), s(S), not((member(X,B), member((X,GX),G),
	member(Y,B), member((Y,GY),G), member((GY,GGY),G),
	not(implica(GX=GGY, member((X,Y),S))))).

% varianta, pentru definitia functiei g prin predicatul binar g:

algBsatisfEnuntul6 :- multimeB(B), s(S), not((member(X,B), g(X,GX), member(Y,B), 
	g(Y,GY), g(GY,GGY), not(implica(GX=GGY, member((X,Y),S))))).

/* Predicat care testeaza daca algebra (B,g,S,k) de mai sus satisface enuntul:
(exista x)(oricare ar fi y)[(S(g(x),k) v S(k,y)) -> -|S(x,y)], folosind faptul ca:
(exista x)(oricare ar fi y)[(S(g(x),k) v S(k,y)) -> -|S(x,y)] |=|
(exista x)-|(exista y)-|[(S(g(x),k) v S(k,y)) -> -|S(x,y)]: */

algBsatisfEnunt7 :- multimeB(B), g(G), s(S), k(K), member(X,B), member((X,GX),G),
 not((member(Y,B), not(implica(member((GX,K),S) ; member((K,Y),S), not(member((X,Y),S)))))).

% varianta, pentru definitia functiei g prin predicatul binar g:

algBsatisfEnuntul7 :- multimeB(B), s(S), k(K), member(X,B), g(X,GX),
 not((member(Y,B), not(implica(member((GX,K),S) ; member((K,Y),S), not(member((X,Y),S)))))).

/* Predicat care testeaza daca algebra (B,g,S,k) de mai sus satisface enuntul:
(exista x)(oricare ar fi y)[(S(x,g(y)) v g(x)=y) <-> S(x,y)], folosind faptul ca:
(exista x)(oricare ar fi y)[(S(x,g(y)) v g(x)=y) <-> S(x,y)] |=|
(exista x)-|(exista y)-|[(S(x,g(y)) v g(x)=y) <-> S(x,y)]: */

algBsatisfEnunt8 :- multimeB(B), g(G), s(S), member(X,B), member((X,GX),G),
 not((member(Y,B), member((Y,GY),G), not(echiv(member((X,GY),S) ; GX=Y, member((X,Y),S))))).

% varianta, pentru definitia functiei g prin predicatul binar g:

algBsatisfEnuntul8 :- multimeB(B), s(S), member(X,B), g(X,GX), not((member(Y,B), g(Y,GY), 
	not(echiv(member((X,GY),S) ; GX=Y, member((X,Y),S))))).

/* Predicat care testeaza daca algebra (B,g,S,k) de mai sus satisface enuntul:
(oricare ar fi x)(oricare ar fi y)[(g(x)=k ^ S(g(x),g(y))) -> -|S(g(g(x)),g(y))], adica 
inchiderea universala a formulei (g(x)=k ^ S(g(x),g(y))) -> -|S(g(g(x)),g(y)), folosind 
faptul ca: (oricare ar fi x)(oricare ar fi y)[(g(x)=k ^ S(g(x),g(y))) -> -|S(g(g(x)),g(y))]
|=| -|(exista x)-|(oricare ar fi y)[(g(x)=k ^ S(g(x),g(y))) -> -|S(g(g(x)),g(y))]
|=| -|(exista x)(exista y)-|[(g(x)=k ^ S(g(x),g(y))) -> -|S(g(g(x)),g(y))]: */

algBsatisfEnunt9 :- multimeB(B), g(G), s(S), k(K), not((member(X,B), member((X,GX),G),
	member((GX,GGX),G), member(Y,B), member((Y,GY),G),
	not(implica((GX=K, member((GX,GY),S)), not(member((GGX,GY),S)))))).

% varianta, pentru definitia functiei g prin predicatul binar g:

algBsatisfEnuntul9 :- multimeB(B), s(S), k(K), not((member(X,B), g(X,GX), g(GX,GGX), 
   member(Y,B), g(Y,GY), not(implica((GX=K, member((GX,GY),S)), not(member((GGX,GY),S)))))).

/* Predicat care testeaza daca algebra (B,g,S,k) de mai sus satisface enuntul:
(exista x)(oricare ar fi y)[(f(x)=f(f(k)) ^ S(y,k)) -> -|S(x,y)], folosind faptul ca:
(exista x)(oricare ar fi y)[(f(x)=f(f(k)) ^ S(y,k)) -> -|S(x,y)] |=|
(exista x)-|(exista y)-|[(f(x)=f(f(k)) ^ S(y,k)) -> -|S(x,y)]: */

algBsatisfEnunt10 :- multimeB(B), g(G), s(S), k(K), member((K,GK),G), member((GK,GGK),G),
	member(X,B), member((X,GX),G),
	not((member(Y,B), not(implica((GX=GGK, member((Y,K),S)), not(member((X,Y),S)))))).

% varianta, pentru definitia functiei g prin predicatul binar g:

algBsatisfEnuntul10 :- multimeB(B), s(S), k(K), g(K,GK), g(GK,GGK), member(X,B), g(X,GX),
	not((member(Y,B), not(implica((GX=GGK, member((Y,K),S)), not(member((X,Y),S)))))).

/* Predicat care testeaza daca algebra (B,g,S,k) de mai sus satisface enuntul:
(oricare ar fi x)(oricare ar fi y)(S(g(g(x)),y) <-> g(x)=g(y)), adica inchiderea universala
a formulei S(g(g(x)),y) <-> g(x)=g(y), folosind faptul ca: 
(oricare ar fi x)(oricare ar fi y)(S(g(g(x)),y) <-> g(x)=g(y)) |=| 
-|(exista x)-|(oricare ar fi y)(S(g(g(x)),y) <-> g(x)=g(y)) |=|
-|(exista x)(exista y)-|(S(g(g(x)),y) <-> g(x)=g(y)): */

algBsatisfEnunt11 :- multimeB(B), g(G), s(S), k(K), not((member(X,B), member((X,GX),G),
	member((GX,GGX),G), member(Y,B), member((Y,GY),G),
	not(implica((GX=K, member((GX,GY),S)), not(member((GGX,GY),S)))))).

% varianta, pentru definitia functiei g prin predicatul binar g:

algBsatisfEnuntul11 :- multimeB(B), s(S), k(K), not((member(X,B), g(X,GX), g(GX,GGX), 
   member(Y,B), g(Y,GY), not(implica((GX=K, member((GX,GY),S)), not(member((GGX,GY),S)))))).

%%%%%%%%%%%%%%%%%% ADDENDA la Seminarul 7:

/* Sa scriem enunturile de mai sus astfel incat sa putem testa satisfacerea lor de catre
orice algebra de signatura corespunzatoare, anume:
   signatura (1;2;multimea vida) in cazul primelor doua enunturi si acelea dintre 
urmatoarele in care nu apare constanta k;
   signatura (1;2;0) pentru celelalte enunturi: */

enunt1(A,F,R) :- member((X,FX),F), member(X,A), member((X,FX),R), member((FX,X),R).

enunt2(A,F,R) :- member(X,A), member((X,FX),F), member((FX,FFX),F), 
	not((member(Y,A), not(member((Y,FFX),R) ; member((FX,Y),R)))).

% Putem testa daca algebra (A,f,R) satisface primul, respectiv al doilea enunt, astfel:

algebraAsatisfEnunt1 :- multimeA(A), f(F), r(R), enunt1(A,F,R).

algebraAsatisfEnunt2 :- multimeA(A), f(F), r(R), enunt2(A,F,R).

/* De asemenea, putem testa daca algebra (B,g,S) subiacenta algebrei (B,g,S,k) satisface 
aceste enunturi, astfel: */

algebraBsatisfEnunt1 :- multimeB(B), s(S), enunt1(B,g,S).

algebraBsatisfEnunt2 :- multimeB(B), s(S), enunt2(B,g,S).

enunt3(B,G,S,K) :- member(X,B), member(Y,B),
	member((X,GX),G), member((GX,GGX),G), member((Y,GY),G),
	implica(GGX=GY, member((X,K),S) ; not(member((X,GY),S))).

enunt4(B,G,S,K) :- member(X,B), member((X,GX),G),
	not((member(Y,B), member((Y,GY),G), not(implica((member((X,K),S), member((K,Y),S)),
	not(member((GY,GX),S)))))).

enunt5(B,G,S,K) :- not((member(X,B), not((member(Y,B),
	implica(member((X,Y),S), (member((X,K),G), not(member((Y,X),G)))))))).

% varianta:

enunt5v(B,G,S,K) :- not((member(X,B), member((X,GX),G),
	not((member(Y,B), member((Y,GY),G), implica(member((X,Y),S), (GX=K, GY\=X)))))).

% Putem testa daca algebra (B,g,S,k) satisface aceste enunturi, astfel:

algebraBsatisfEnunt3 :- multimeB(B), g(G), s(S), k(K), enunt3(B,G,S,K).

algebraBsatisfEnunt4 :- multimeB(B), g(G), s(S), k(K), enunt4(B,G,S,K).

algebraBsatisfEnunt5 :- multimeB(B), g(G), s(S), k(K), enunt5(B,G,S,K).

algebraBsatisfEnunt5v :- multimeB(B), g(G), s(S), k(K), enunt5(B,G,S,K).

/* De asemenea, putem testa daca algebra (A,f,R,k), de exemplu, cu k=a, satisface aceste 
enunturi, astfel: */

algebraAsatisfEnunt3 :- multimeA(A), f(F), r(R), enunt3(A,F,R,a).

algebraAsatisfEnunt4 :- multimeA(A), f(F), r(R), enunt4(A,F,R,a).

algebraAsatisfEnunt5 :- multimeA(A), f(F), r(R), enunt5(A,F,R,a).

algebraAsatisfEnunt5v :- multimeA(A), f(F), r(R), enunt5v(A,F,R,a).

enunt6(B,G,S) :- not((member(X,B), member((X,GX),G), member(Y,B), member((Y,GY),G), 
	member((GY,GGY),G), not(implica(GX=GGY, member((X,Y),S))))).

/* Putem testa daca algebrele (B,g,S,k) (sau algebra sa subiacenta (B,g,S)), respectiv
(A,f,R) satisfac acest enunt, astfel: */

algebraBsatisfEnunt6 :- multimeB(B), g(G), s(S), enunt6(B,G,S).

algebraAsatisfEnunt6 :- multimeA(A), f(F), r(R), enunt6(A,F,R).

enunt7(B,G,S,K) :- member(X,B), member((X,GX),G), not((member(Y,B), 
	not(implica(member((GX,K),S) ; member((K,Y),S), not(member((X,Y),S)))))).

% Sa testam daca algebra (B,g,S,k), respectiv (A,f,R,k), cu k=a, satisface acest enunt:

algebraBsatisfEnunt7 :- multimeB(B), g(G), s(S), k(K), enunt7(B,G,S,K).

algebraAsatisfEnunt7 :- multimeA(A), f(F), r(R), enunt7(A,F,R,a).

% Procedam la fel ca mai sus, cu aceleasi algebre, pentru enunturile urmatoare:

enunt8(B,G,S) :- member(X,B), member((X,GX),G), not((member(Y,B), member((Y,GY),G), 
	not(echiv(member((X,GY),S) ; GX=Y, member((X,Y),S))))).

algebraBsatisfEnunt8 :- multimeB(B), g(G), s(S), enunt8(B,G,S).

algebraAsatisfEnunt8 :- multimeA(A), f(F), r(R), enunt8(A,F,R).

enunt9(B,G,S,K) :- not((member(X,B), member((X,GX),G),
	member((GX,GGX),G), member(Y,B), member((Y,GY),G),
	not(implica((GX=K, member((GX,GY),S)), not(member((GGX,GY),S)))))).

algebraBsatisfEnunt9 :- multimeB(B), g(G), s(S), k(K), enunt9(B,G,S,K).

algebraAsatisfEnunt9 :- multimeA(A), f(F), r(R), enunt9(A,F,R,a).

enunt10(B,G,S,K) :- member((K,GK),G), member((GK,GGK),G), member(X,B), member((X,GX),G),
	not((member(Y,B), not(implica((GX=GGK, member((Y,K),S)), not(member((X,Y),S)))))).

algebraBsatisfEnunt10 :- multimeB(B), g(G), s(S), k(K), enunt10(B,G,S,K).

algebraAsatisfEnunt10 :- multimeA(A), f(F), r(R), enunt10(A,F,R,a).

enunt11(B,G,S,K) :- not((member(X,B), member((X,GX),G),
	member((GX,GGX),G), member(Y,B), member((Y,GY),G),
	not(implica((GX=K, member((GX,GY),S)), not(member((GGX,GY),S)))))).

algebraBsatisfEnunt11 :- multimeB(B), g(G), s(S), k(K), enunt11(B,G,S,K).

algebraAsatisfEnunt11 :- multimeA(A), f(F), r(R), enunt11(A,F,R,a).

/* Putem scrie enunturile ca mai sus si pentru varianta de definire a functiilor prin 
predicate binare, folosind predicatul predefinit =.. : */

enuntul1(A,OpF,R) :- member(X,A), 
	T=..[OpF,X,FX], T, % formam termenul, apoi impunem sa fie satisfacut
	member((X,FX),R), member((FX,X),R), write(X).

algebraAsatisfEnuntul1 :- multimeA(A), r(R), enuntul1(A,f,R).

algebraBsatisfEnuntul1 :- multimeB(B), s(S), enuntul1(B,g,S).

enuntul2(A,OpF,R) :- member(X,A), T1=..[OpF,X,FX], T1, T2=..[OpF,FX,FFX], T2,
		not((member(Y,A), not(member((Y,FFX),R) ; member((FX,Y),R)))).

algebraAsatisfEnuntul2 :- multimeA(A), r(R), enuntul2(A,f,R).

algebraBsatisfEnuntul2 :- multimeB(B), s(S), enuntul2(B,g,S).

enuntul3(B,OpG,S,K) :- member(X,B), member(Y,B), T1=..[OpG,X,GX], T1, T2=..[OpG,GX,GGX], T2,
	T3=..[OpG,Y,GY], T3, implica(GGX=GY, member((X,K),S) ; not(member((X,GY),S))).

algebraAsatisfEnuntul3 :- multimeA(A), r(R), enuntul3(A,f,R,a).

algebraBsatisfEnuntul3 :- multimeB(B), s(S), k(K), enuntul3(B,g,S,K).

enuntul4(B,OpG,S,K) :- member(X,B), T1=..[OpG,X,GX], T1, not((member(Y,B), T2=..[OpG,Y,GY],
	T2, not(implica((member((X,K),S), member((K,Y),S)), not(member((GY,GX),S)))))).

algebraAsatisfEnuntul4 :- multimeA(A), r(R), enuntul4(A,f,R,a).

algebraBsatisfEnuntul4 :- multimeB(B), s(S), k(K), enuntul4(B,g,S,K).

enuntul5(B,OpG,S,K) :- not((member(X,B), T1=..[OpG,X,K], not((member(Y,B), T2=..[OpG,Y,X],
	implica(member((X,Y),S), (T1, not(T2))))))).

algebraAsatisfEnuntul5 :- multimeA(A), r(R), enuntul5(A,f,R,a).

algebraBsatisfEnuntul5 :- multimeB(B), s(S), k(K), enuntul5(B,g,S,K).

enuntul6(B,OpG,S) :- not((member(X,B), T1=..[OpG,X,GX], T1, member(Y,B), T2=..[OpG,Y,GY], 
	T2, T3=..[OpG,GY,GGY], T3, not(implica(GX=GGY, member((X,Y),S))))).

algebraAsatisfEnuntul6 :- multimeA(A), r(R), enuntul6(A,f,R).

algebraBsatisfEnuntul6 :- multimeB(B), s(S), enuntul6(B,g,S).

enuntul7(B,OpG,S,K) :- member(X,B), T=..[OpG,X,GX], T, not((member(Y,B), 
	not(implica(member((GX,K),S) ; member((K,Y),S), not(member((X,Y),S)))))).

algebraAsatisfEnuntul7 :- multimeA(A), r(R), enuntul7(A,f,R,a).

algebraBsatisfEnuntul7 :- multimeB(B), s(S), k(K), enuntul7(B,g,S,K).

enuntul8(B,OpG,S) :- member(X,B), T1=..[OpG,X,GX], T1, not((member(Y,B), T2=..[OpG,Y,GY], 
	T2, not(echiv(member((X,GY),S) ; GX=Y, member((X,Y),S))))).

algebraAsatisfEnuntul8 :- multimeA(A), r(R), enuntul8(A,f,R).

algebraBsatisfEnuntul8 :- multimeB(B), s(S), enuntul8(B,g,S).

enuntul9(B,OpG,S,K) :- not((member(X,B), T1=..[OpG,X,GX], T1, T2=..[OpG,GX,GGX], T2, 
	member(Y,B), T3=..[OpG,Y,GY], T3, 
	not(implica((GX=K, member((GX,GY),S)), not(member((GGX,GY),S)))))).

algebraAsatisfEnuntul9 :- multimeA(A), r(R), enuntul9(A,f,R,a).

algebraBsatisfEnuntul9 :- multimeB(B), s(S), k(K), enuntul9(B,g,S,K).

enuntul10(B,OpG,S,K) :- T1=..[OpG,K,GK], T1, T2=..[OpG,GK,GGK], T2, 
	member(X,B), T3=..[OpG,X,GX], T3,
	not((member(Y,B), not(implica((GX=GGK, member((Y,K),S)), not(member((X,Y),S)))))).

algebraAsatisfEnuntul10 :- multimeA(A), r(R), enuntul10(A,f,R,a).

algebraBsatisfEnuntul10 :- multimeB(B), s(S), k(K), enuntul10(B,g,S,K).

enuntul11(B,OpG,S,K) :- not((member(X,B), T1=..[OpG,X,GX], T1, T2=..[OpG,GX,GGX], T2, 
	member(Y,B), T3=..[OpG,Y,GY], T3, 
	not(implica((GX=K, member((GX,GY),S)), not(member((GGX,GY),S)))))).

algebraAsatisfEnuntul11 :- multimeA(A), r(R), enuntul11(A,f,R,a).

algebraBsatisfEnuntul11 :- multimeB(B), s(S), k(K), enuntul11(B,g,S,K).
