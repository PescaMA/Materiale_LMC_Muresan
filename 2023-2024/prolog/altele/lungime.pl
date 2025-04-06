lungime([],0).
lungime([_|T],N) :- lungime(T,P), N is P+1.

/* Imbricarea este permisa, dar produce termeni (expresii), nu calculul aritmetic dorit;
de aceea acest calcul aritmetic trebuie efectuat separat, cu predicatul predefinit is;
daca am scrie:

lungime([],0).
lungime([_|T],P+1) :- lungime(T,P).

atunci la interogarea:
?- lungime([a,b,c],Cat).
am primi solutia: Cat=0+1+1+1.
Sa verificam acest lucru: */

lung([],0).
lung([_|T],P+1) :- lung(T,P).

/* Sa interogam:
?- lungime([a,b,c],Cat).
?- lung([a,b,c],Cat).
In recursie, lungime face calculul aritmetic P+1, iar lung considera termenul P+1 si
continua recursia cu acest termen pe al doilea argument:
     +
    / \
   P   1,
unde subarborele stang al radacinii, pe care l-am reprezentat prin P mai sus, este 
arborele asociat expresiei P intoarse din recursie.
La interogarea de mai sus, in loc de a produce, in recursie, numerele 0,1,2,3, ca predicatul
lungime, predicatul lung formeaza, in al doilea argument al sau (in care ar trebui sa
calculeze lungimea listei), pe rand, termenii reprezentati prin urmatorii arbori:
    0
  
     +
    / \
   0   1

     +
    / \
   +   1
  / \
 0   1

       +
      / \
     +   1
    / \
   +   1
  / \
 0   1

*/





