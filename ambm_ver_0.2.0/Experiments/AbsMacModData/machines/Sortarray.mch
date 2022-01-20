MACHINE           Sortarray

CONSTANTS      cap, MaxN

PROPERTIES     cap = 4 & MaxN = 4

VARIABLES         aa

INVARIANT         aa : 1..cap --> 0..MaxN

INITIALISATION    aa :: 1..cap --> 0..MaxN

OPERATIONS

  set(ii,nn) =
  PRE ii : 1..cap & nn : 0..MaxN
  THEN aa(ii) := nn
  END;

nn <-- get(ii) =
  PRE ii : 1..cap
  THEN nn := aa(ii)
  END;

  sort =
  ANY pp
  WHERE pp : 1..cap >->> 1..cap & 
        ! ii . (ii : 1..cap-1 => (pp;aa)(ii) <= (pp;aa)(ii+1))
  THEN aa := (pp;aa)
  END  

END
