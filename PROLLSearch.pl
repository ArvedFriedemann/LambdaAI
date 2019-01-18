function(X) :- function(X, []).
function(var(X)) :- function(var(X),VARS), member(var(X), VARS).
function(abstraction(var(X),Y), VARS) :- function(Y, ).
function()
