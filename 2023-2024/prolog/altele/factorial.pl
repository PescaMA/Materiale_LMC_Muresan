factorial(0,1).
factorial(N,Rezultat) :- N>0, N1 is N-1, factorial(N1,Rezultat1), Rezultat is N*Rezultat1.

/*
?- factorial(3,Cat).
Scopul:
     factorial
      /     \
     3      Cat
Faptul:
     factorial
      /     \
     0       1
factorial(3,Cat)\=factorial(0,1), pentru ca 3\=0.
Membrul stang al regulii:
     factorial
      /     \
     N    Rezultat
factorial(3,Cat)=factorial(N,Rezultat), cu N=3 si Rezultat=Cat.
Satisfacerea membrului drept al regulii (acea conjunctie), modificat conform unificarii de mai sus:
   3>0,
   N1 is 3-1, asadar N1=2,
   factorial(N1,Rezultat1), adica factorial(2,Rezultat1) va fi scopul urmator, adica
	va trebui satisfacut acum, dupa care se va satisface ultimul termen al acestei
	conjunctii, anume se va efectua calculul:
   Cat is 3*Rezultat1.
Asadar noul scop este:
?- factorial(2,Rezultat1).
Scopul:
     factorial
      /     \
     2     Rezultat1
Faptul:
     factorial
      /     \
     0       1
factorial(2,Rezultat1)\=factorial(0,1), pentru ca 2\=0.
Membrul stang al regulii:
     factorial
      /     \
     N'   Rezultat'
factorial(2,Rezultat1)=factorial(N',Rezultat'), cu N'=2 si Rezultat'=Rezultat1.
Satisfacerea membrului drept al regulii, modificat conform unificarii de mai sus:
   2>0,
   N2 is 2-1, asadar N2=1,
   factorial(N2,Rezultat2), adica factorial(1,Rezultat2) va fi scopul urmator, adica
	va trebui satisfacut acum, dupa care se va satisface ultimul termen al acestei
	conjunctii, anume se va efectua calculul:
   Rezultat1 is 2*Rezultat2.
Asadar noul scop este:
?- factorial(1,Rezultat2).
Scopul:
     factorial
      /     \
     1     Rezultat2
Faptul:
     factorial
      /     \
     0       1
factorial(1,Rezultat2)\=factorial(0,1), pentru ca 1\=0.
Membrul stang al regulii:
     factorial
      /     \
     N''   Rezultat''
factorial(1,Rezultat2)=factorial(N'',Rezultat''), cu N''=1 si Rezultat''=Rezultat2.
Satisfacerea membrului drept al regulii, modificat conform unificarii de mai sus:
   1>0,
   N3 is 1-1, asadar N3=0,
   factorial(N3,Rezultat3), adica factorial(0,Rezultat3) va fi scopul urmator, adica
	va trebui satisfacut acum, dupa care se va satisface ultimul termen al acestei
	conjunctii, anume se va efectua calculul:
   Rezultat2 is 1*Rezultat3.
Asadar noul scop este:
?- factorial(0,Rezultat3).
Scopul:
     factorial
      /     \
     0     Rezultat3
Faptul:
     factorial
      /     \
     0       1
factorial(0,Rezultat3)=factorial(0,1), cu Rezultat3=1.
Asadar acum revenim din recursie:
   Rezultat2 is 1*Rezultat3, adica 1*1, asadar Rezultat2=1;
   Rezultat1 is 2*Rezultat2, adica 2*1, asadar Rezultat1=2;
   Cat is 3*Rezultat1, adica 3*2, asadar Cat=6.
Avem solutia: Cat=6 pentru interogarea:
?- factorial(3,Cat).
Daca in loc de:
factorial(0,1).
factorial(N,Rezultat) :- N>0, N1 is N-1, factorial(N1,Rezultat1), Rezultat is N*Rezultat1.
as fi scris:
factorial(0,1) :- !.
factorial(N,Rezultat) :- N>0, N1 is N-1, factorial(N1,Rezultat1), Rezultat is N*Rezultat1.
atunci, in momentul in care Prologul a unificat scopul curent: factorial(0,Rezultat3) cu
factorial(0,1), Prologul ar executa cut(!), asadar ar incheia executia cu unica solutie:
Cat=6.
Dar, pentru ca nu am dat cut(!), Prologul are de satisfacut scopul curent, 
factorial(0,Rezultat3), cu faptul: factorial(0,1). sau regula:
factorial(N,Rezultat) :- N>0, N1 is N-1, factorial(N1,Rezultat1), Rezultat is N*Rezultat1.
si a satisfacut scopul factorial(0,Rezultat3) doar cu faptul, asadar acum va incerca sa
satisfaca acest scop cu regula de mai sus, deci va efectua unificarea:
	factorial(N,Rezultat)=factorial(0,Rezultat3),
care consta in: N=0 si Rezultat=Rezultat3, dupa care va trece la satisfacerea membrului 
drept al regulii:
   0>0 e fals, asadar toata conjunctia din membrul drept al acestei reguli este evaluata
	la false, si abia acum se termina executia interogarii initiale, dupa ce fiecare
	scop intermediar a fost satisfacut in toate modurile posibile.
Cum membrul drept al regulii e fals, nu se satisface scopul factorial(0,Rezultat3) si cu
aceasta regula, ci numai cu faptul factorial(0,1), prin urmare solutia Cat=6 este unica.
*/

