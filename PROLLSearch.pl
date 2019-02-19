
num(zero).
num(succ(X)) :- num(X).

toNum(zero,0).
toNum(succ(X),Z) :- Z_ is Z-1, toNum(X,Z_),!.

fromNum(X,Y) :- fromNum(X,0,Y).
fromNum(zero,ACC,ACC).
fromNum(succ(X),ACC, ACC_) :- ACCNEW is ACC+1, fromNum(X,ACCNEW,ACC_).

smallerEq_(X,Y) :- toNum(N,Y), smallerEq(X,N).
smallerEq(zero, _).
smallerEq(succ(X), succ(Y)) :- smallerEq(X,Y).

smaller(zero,succ(_)).
smaller(succ(X),succ(Y)) :- smaller(X,Y).

add(zero, Y, Y).
add(succ(X),Y,succ(Z)) :- add(X,Y,Z).

mult(zero, _, zero).
mult(succ(X), Y, Z) :- mult(X,Y,RES), add(Y, RES, Z).

formula(X,S) :- toNum(S_,S), formula_(X,S_).
formula_(X,S) :- formula(X,[],S).

formula(vari(X),L,zero) :- member(X,L).
formula(abst(X,E),L,succ(S)) :- exceeds(X, L), formula(E,[X|L], S).
formula(apl(N,M),L,succ(S))  :- add(S1,S2,S), formula(N,L,S1), formula(M,L,S2).

fsize(vari(_),0).
fsize(abst(_,E),Z) :- fsize(E,S), Z is 1 + S.
fsize(apl(N,M),Z) :- fsize(N,S1), fsize(M,S2), Z is 1+S1+S2.

containsVar(vari(X), X).
containsVar(abst(Y,E), X) :- X \== Y, containsVar(E, X).
containsVar(apl(N,M), X)  :- containsVar(N,X) ; containsVar(M,X).



redLMOM(X,Y) :- redLMOM(X,Y,true), !.
redLMOM(X,X) :- redLMOM(X,X,false), !.

redLMOM(X,Y,false) :- betared(X,Y), X==Y.
redLMOM(apl(N1,M),apl(N2,M),true) :- redLMOM(N1, N2, true),!.
redLMOM(apl(N,M1),apl(N,M2),true) :- redLMOM(M1, M2, true),!.
redLMOM(X,Y,true) :- betared(X,Y), X \== Y.

betared(apl(abst(X,E),Y), T) :- change(X,Y,E,T),!.
betared(X,X).

change(X,Y,vari(X),Y).
change(_,_,vari(Z),vari(Z)).
change(X,Y,apl(E11,E12),apl(E21,E22)) :- change(X,Y,E11,E21), change(X,Y,E12,E22).
change(X,_,abst(X,E),abst(X,E)) :- !.
change(X,Y,abst(Z,E1),abst(Z,E2)) :- change(X,Y,E1,E2).

run(X,Y) :- run(X,Y,_), !.
run(X,Y,succ(S)) :- redLMOM(X,Z,true),!, run(Z,Y,S), !.
run(X,X,S) :- redLMOM(X,X,false), dif(S,zero), !.

/* misc */

alldiff([]).
alldiff([X|XS]) :- notContains(X, XS), alldiff(XS).

notContains(X, XS) :- maplist(dif(X), XS).

notContainsDir(_,[]).
notContainsDir(X,[Y|YS]) :- Y\==X, notContainsDir(X, YS).

exceeds(zero,[]).
exceeds(succ(X),[X]) :- !.
exceeds(X,[Y|YS]) :- smaller(Y,X), exceeds(X,YS),!.
exceeds(succ(Y),[Y|YS]) :- exceeds(succ(Y), YS).

/* lambda calculus functions */

l_id(abst(x,vari(x))).
l_true(abst(x,abst(z,vari(x)))). % :- alldiff([X,Y]), !.
l_false(abst(x,abst(z,vari(z)))).

l_tuple(abst(x,abst(z,abst(f, apl(apl(vari(f), vari(x)), vari(z)) )))).
l_fst(abst(f, apl(vari(f), T))) :- l_true(T), !.
l_snd(abst(f, apl(vari(f), T))) :- l_false(T), !.

llv(X,Y) :- varLST(X, Z), lambdaLST(Z, Y).
lambdaLST([],l_false).
lambdaLST([X|L], T) :- l_tuple(TUP), lambdaLST(L, PREV), run(apl(apl(TUP, X), PREV), T), !.

vapllst(X,Y) :- varLST(X,Z), apllst(Z,Y).
apllst(X,Y) :- reverse(X,Z), apllst_(Z, Y).
apllst_([X],X).
apllst_([X|XS],apl(REST, X)) :- apllst_(XS,REST), !.

varLST([], []).
varLST([X|XS], [vari(X)|XS_]) :- varLST(XS, XS_).

implements(_,_,[]).
implements(F,FAC, [(X,Y) |XS]) :- fsize(X, S), mult(FAC, S, STEPS), run(apl(F,X), Y, STEPS), implements(F,FAC, XS).

implementsApl(_,_,[]). %TODO: neater factor needed
implementsApl(F,FAC, [(X,Y) |XS]) :- apllst([F|X], APL), run(APL, Y, FAC), implementsApl(F,FAC, XS).

% type: [([a],[b])] to transform strings into one another
mtxToLLST([],[]).
mtxToLLST([(A,B)|XS], [(C,D)|XS_]) :- llv(A,C), llv(B,D), mtxToLLST(XS, XS_).

mtxToVLST([],[]).
mtxToVLST([(A,B)|XS], [(C,D)|XS_]) :- varLST(A,C), varLST(B,D), mtxToVLST(XS, XS_).

mtxToAplLST([],[]).
mtxToAplLST([(A,B)|XS], [(C,D)|XS_]) :- apllst(A,C), apllst(B,D), mtxToAplLST(XS, XS_).

%TODO: formula search constrains not kept somewhere...lost in cuts
learningtest :- l_true(T),l_false(F), toNum(FAC, 100),
                MTX = [([F,F],[T])], % ,([F,T],[F]),([T,F],[F]),([T,T],[T])],
                writeln(MTX),
                num(N), fromNum(N,NN),writeln(NN), formula_(FORM, N),
                implementsApl(FORM, FAC, MTX).
test :- display(test), test.
% num(N),writeln(N), toNum(RT, 100), formula_(F, N), apllst([F,vari(0),vari(1)], APL), run(APL, apl(vari(0), vari(0)), RT).
% F = abst(x, abst(z, vari(z))), run(apl(apl(F,vari(0)), vari(1)), vari(1) ).

% apl(abst(x, apl(vari(x), vari(x))), abst(x, apl(vari(x), vari(x))))
