MACHINE           Paperround

CONSTANTS      MaxN

PROPERTIES      MaxN = 7

VARIABLES         houseset, magazine

INVARIANT         houseset:POW(1..MaxN) & magazine <: houseset

INITIALISATION    houseset := {} || magazine := {}

OPERATIONS

 add(new) = 
  PRE 
    new:1..MaxN & new/:houseset
  THEN
    houseset := houseset \/ {new}
  END;
 add_magazine(new) = PRE new:houseset THEN
    magazine := magazine \/ {new}
  END;

  ans <-- number =
  BEGIN
    ans := card(houseset)
  END

END