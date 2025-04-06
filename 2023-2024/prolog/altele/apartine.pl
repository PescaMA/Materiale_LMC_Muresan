apartine(H,[H|_]).
apartine(X,[_|T]) :- apartine(X,T).

