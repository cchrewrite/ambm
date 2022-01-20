
rule_to_cond(X):-
    conv(X,Y),
    write(Y).

conv(Y,Y):-
  \+ground(Y),
  write("WARNING: Cannot convert, because "),
  write(Y),write(" is not ground."),nl,
  !.

conv(is_bobj(X,Y),Res):-
  conv(X,XT),
  conv(Y,YT),
  atomic_list_concat([XT,"=",YT],' ',Res),
  !.

conv(in_bset(X,Y),Res):-
  conv(X,XT),
  conv(Y,YT),
  atomic_list_concat([XT,":",YT],' ',Res),
  !.

conv(has_bdist(X,Y),Res):-
  conv(X,XT),
  conv(Y,YT),
  atomic_list_concat([YT,":",XT],' ',Res),
  !.

conv(is_bsubset(X,Y),Res):-
  conv(X,XT),
  conv(Y,YT),
  atomic_list_concat([XT,"<:",YT],' ',Res),
  !.


conv(X,Res):-
  is_list(X),
  conv_list(X,XT),
  atomic_list_concat(XT,' , ',P),
  atomic_list_concat(["{",P,"}"],' ',Res),
  !.

conv_list([],[]):-!.
conv_list([X|L],[XT|LT]):-
  conv(X,XT),
  conv_list(L,LT),
  !.
  

conv(X,X):-
  atom(X),
  !.

conv(X,X):-
  write("WARNING: Cannot convert "),
  write(X),nl,
  !.



