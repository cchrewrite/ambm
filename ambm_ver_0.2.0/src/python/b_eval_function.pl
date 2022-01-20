/*
is_bexp(X,V1,V2,SP):-
  (
      S = bCONJ(bTRUE,bTRUE), X = bTRUE
      ;
      S = bCONJ(bFALSE,bTRUE), X = bFALSE
      ;
      S = bCONJ(bTRUE,bFALSE), X = bFALSE
      ;
      S = bCONJ(bFALSE,bFALSE), X = bFALSE
  ),
  S = bCONJ(V1,V2),
  SP = lambdaexp,
  nl.%,print(V1),nl,print(V2),nl,print(X),nl,read(_).
*/
/*
is_bexp(bTRUE,bTRUE,bTRUE,lambdaexp).
is_bexp(bFALSE,bTRUE,bFALSE,lambdaexp).
is_bexp(bFALSE,bFALSE,bTRUE,lambdaexp).

iso_cond_good(A,B,C) :-
  print(safdjksdajfsak),
  %read(_), 
  is_bexp(C,A,B,lambdaexp),
  nl,print(A),nl,print(B),nl,print(C),nl.%,read(_).
*/

%is_bexp(X,U,V,S) :-
 
is_bexp(X,U,V,S) :- 
  is_bexp_comp(X,U,V,S),
  nl.%,print(U),nl,print(V),nl,print(X),nl,read(_).
is_bexp_comp(X,V1,V2,SP):-
  (
      S = bCONJ(bTRUE,bTRUE)
      ;
      S = bCONJ(bFALSE,bTRUE)
      ;
      S = bCONJ(bTRUE,bFALSE)
      ;
      S = bCONJ(bFALSE,bFALSE)
  ),
  S = bCONJ(V1,V2),
  SP = lambda([P,Q],bCONJ(P,Q)),

  b_eval(S,T),
  %print(X),nl,print(T),nl,print(S),nl,
  %read(U),
  X = T.




/*
is_bexp(X,S):-
  (
      S = bCONJ(bTRUE,bTRUE)
      ;
      S = bCONJ(bFALSE,bTRUE)
      ;
      S = bCONJ(bTRUE,bFALSE)
      ;
      S = bCONJ(bFALSE,bFALSE)
  ),
  b_eval(S,X).
*/

b_eval(X,X):-
  atom(X),
  !.

b_eval(bCONJ(X,Y),Z):-
    b_eval(X,XT),
    b_eval(Y,YT),
    (
      XT = bFALSE,
      Z = bFALSE,
      !
    ;
      YT = bFALSE,
      Z = bFALSE,
      !
    ;
      Z = bTRUE
    ),
    !.

/*
b_eval(bCONJ(bTRUE,bFALSE),bFALSE):-!.
b_eval(bCONJ(bFALSE,bTRUE),bFALSE):-!.
*/
