MACHINE abz2020_GenericTimersMC
// A variation of GenericTimers for model checking

CONSTANTS
  maxNAT, nTIMERS
PROPERTIES
  maxNAT = 4 &
  nTIMERS = 2

VARIABLES
  curDeadlines

INVARIANT
  curDeadlines : 0..nTIMERS --> -1..maxNAT
  //curDeadlines : POW(0..nTIMERS * 0..maxNAT)

INITIALISATION
  //curDeadlines := {0 |-> 0, 1 |-> 0}
  curDeadlines :: 0..nTIMERS --> {-1}

OPERATIONS
  
  AbsoluteSetDeadline(timer,deadline) = PRE timer:0..nTIMERS & deadline:0..maxNAT THEN
     curDeadlines(timer) := deadline
  END;
  
  AddDeadline(timer,deadline) = PRE timer:0..nTIMERS & deadline:0..maxNAT THEN
     curDeadlines(timer) := deadline
  END;
  
  // Increase time without exceeding a deadline
  IncreaseTime(delta) = SELECT delta:0..maxNAT & 
      ((#(tm).(tm : 0..nTIMERS & curDeadlines(tm) >= 0)) => delta <= min(ran(curDeadlines) - {-1})) THEN
      //(curDeadlines/={} => delta <= min(ran(curDeadlines))) THEN
     curDeadlines := %x.(x:dom(curDeadlines)|max({0,curDeadlines(x)-delta}))
  END;
  
  IncreaseTimeUntilDeadline(timer,delta) =
   SELECT delta:0..maxNAT & 
          timer : dom(curDeadlines) &
          delta = min(ran(curDeadlines) - {-1}) & 
          delta = curDeadlines(timer) &
          delta >= 0 THEN
     curDeadlines := %x.(x:dom(curDeadlines) \ {timer} | max({0,curDeadlines(x)-delta})) \/ {timer |-> -1}
  END;
  
  IncreaseTimeUntilCyclicDeadline(timer,delta,newDelta) =
   SELECT delta:0..maxNAT & 
          timer : dom(curDeadlines) & 
          delta = curDeadlines(timer)  &
          delta = min(ran(curDeadlines) - {-1}) &
          delta >= 0 &
          newDelta : 0..maxNAT
  THEN
     curDeadlines := %x.(x:dom(curDeadlines) \ {timer} | max({0,curDeadlines(x)-delta})) \/ {timer |-> newDelta}
  END

END
  
  
