
num(zero).
num(succ(X)) :- num(X).

toNum(zero,0).
toNum(succ(X),Z) :- Z_ is Z-1, toNum(X,Z_),!.

add(zero, Y, Y).
add(succ(X),Y,succ(Z)) :- add(X,Y,Z).

formula(X,S) :- toNum(S_,S), formula_(X,S_).
formula_(X,S) :- formula(X,[],S).

formula(vari(X),L,zero) :- memberchk(X,L).
formula(abst(X,E),L,succ(S)) :- formula(E,[X|L], S).
formula(apl(N,M),L,succ(S))  :- add(S1,S2,S), formula(N,L,S1), formula(M,L,S2).

fsize(vari(_),1).
fsize(abst(_,E),Z) :- fsize(E,S), Z is 1 + S.
fsize(apl(N,M),Z) :- fsize(N,S1), fsize(M,S2), Z is 1+S1+S2.

containsVar(vari(X), X).
containsVar(abst(Y,E), X) :- X \== Y, containsVar(E, X).
containsVar(apl(N,M), X)  :- containsVar(N,X) ; containsVar(M,X).

betared(apl(abst(X,E),Y), T) :- change(X,Y,E,T),!.
betared(X,X).

redLMOM(X,Y,false) :- betared(X,Y), X==Y.
redLMOM(apl(N1,M),apl(N2,M),true) :- redLMOM(N1, N2, true),!.
redLMOM(apl(N,M1),apl(N,M2),true) :- redLMOM(M1, M2, true),!.
redLMOM(X,Y,true) :- betared(X,Y), X \== Y.


change(X,Y,vari(X),Y).
change(X,Y,apl(E11,E12),apl(E21,E22)) :- change(X,Y,E11,E21), change(X,Y,E12,E22).
change(X,_,abst(X,E),abst(X,E)) :- !.
change(X,Y,abst(Z,E1),abst(Z,E2)) :- change(X,Y,E1,E2).
