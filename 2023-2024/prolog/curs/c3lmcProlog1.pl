concat([],L,L). % faptul: predicatul concat e satisfacut pentru argumente de aceasta forma
concat([H|T],L,[H|U]) :- concat(T,L,U). /* regula: predicatul concat e satisfacut pentru
   argumentele [H|T],L,[H|U] daca predicatul concat e satisfacut pentru argumentele T,L,U */

/* Sa vedem pasii executiei interogarii:
?- concat(Ce,CuCe,[1,2]).
La fiecare pas, Prolog-ul va inlocui variabilele din faptul si regula de mai sus cu
variabile temporare (notate cu underscore urmat de cate un numar natural mare). Vom schimba
notatiile variabilelor din clauzele de mai sus numai unde este nevoie pentru a urmari pasii
acestei executii (si, desigur, le vom nota mai simplu decat o face Prolog-ul).
Scopul curent:
        concat
       /   |   \
     Ce   CuCe [|]
              /   \
             1    [|]
                  / \
                 2  []
este unificat mai intai cu predicatul din faptul de mai sus:
    concat
   /   |  \
 []    L   L
rezultand solutia interogarii:
(1) Ce=[], CuCe=L=[1,2]; (mai cerem solutii)
Apoi acelasi scop este unificat cu membrul stang al regulii de mai sus:
    concat
   /   |  \
 [|]   L  [|]
 / \      / \
H   T    H   U
rezultand solutia unificarii:
Ce=[H|T]=[1|T]
CuCe=L
H=1, U=[2]
Se continua rezolvarea cu membrul drept al regulii, cu
argumentele rezultate din unificarea anterioara:
?- concat(T,CuCe,[2]).
Asadar scopul curent este acum:
    concat
    / |   \
   T CuCe [|]
          / \
         2  []
si va fi unificat mai intai cu predicatul din fapt (inlocuim variabila L cu
variabila temporara L1; la fel procedam mai jos):
    concat
   /  |  \
 []   L1 L1
rezultand a doua solutie a interogarii:
T=[] => (2) Ce=[1|[]]=[1], CuCe=[2]; (mai cerem solutii)
Apoi scopul curent este unificat cu membrul stang al regulii:
    concat
   /   |  \
 [|]  L1  [|]
 / \      / \
H1 T1    H1 U1
iar solutia acestei unificari este:
T=[H1|T1]=[2|T1]
CuCe=L1
H1=2, U1=[]
asadar urmatorul scop curent este membrul drept al regulii, cu aceste argumente:
?- concat(T1,CuCe,[]).
Deci acesta e acum scopul curent:
    concat
    /  |  \
  T1 CuCe []
care va fi unificat mai intai cu predicatul din fapt:
    concat
   /   |  \
 []   L2  L2
rezultand a treia solutie a interogarii:
(3) T1=[]=>T=[2|[]]=[2]=>Ce=[1|[2]]=[1,2], CuCe=[]; (mai cerem solutii)
Acum unificam scopul curent cu membrul stang al regulii:
    concat
   /   |  \
 [|]  L2  [|]
 / \      / \
H2 T2    H2 U2
iar aceasta unificare nu are solutii, pentru ca, pe al treilea argument al lui concat,
[] nu unifica cu [H2|U2].
Asadar acum Prolog-ul intoarce false: nu mai exista solutii (satisfaceri ale scopului).
*/
