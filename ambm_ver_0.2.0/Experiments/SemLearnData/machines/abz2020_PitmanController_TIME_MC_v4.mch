MACHINE abz2020_PitmanController_TIME_MC_v4
// v2: uses GenericTimer machine
SETS
  PTIMERS = {blink_deadline, tip_deadline};
  DIRECTIONS = {left_blink,right_blink,neutral_blink};
  SWITCH_STATUS = {switch_on,switch_off};
  PITMAN_POSITION = {Neutral, Downward5, Downward7, Upward5, Upward7};
  KEY_STATE = {NoKeyInserted, KeyInserted,KeyInsertedOnPosition}
CONSTANTS
  maxNAT,
  pitman_direction,
  BLINK_DIRECTION,
  LAMP_STATUS,
  lamp_on,
  lamp_off,
  BLINK_CYCLE_COUNTER,
  cycleMaxLampStatus,
  PITMAN_DIRECTION_BLINKING, 
  PITMAN_TIP_BLINKING

PROPERTIES
  maxNAT = 500 &
  pitman_direction = {Neutral |-> neutral_blink, Downward5 |-> left_blink, Downward7 |-> left_blink,
                      Upward5 |-> right_blink, Upward7 |-> right_blink} &
  BLINK_DIRECTION = {left_blink, right_blink} &
  LAMP_STATUS = {0,100} &
  lamp_off = 0 & lamp_on = 100 &
  BLINK_CYCLE_COUNTER = -1..10 &
  cycleMaxLampStatus : BOOL --> LAMP_STATUS &
  cycleMaxLampStatus = {FALSE |-> lamp_off, TRUE |-> lamp_on}
  &
  PITMAN_DIRECTION_BLINKING = {Downward7, Upward7} &
  PITMAN_TIP_BLINKING = {Downward5, Upward5} 

VARIABLES
  curDeadlines,

  active_blinkers /*@desc "set of active blinkers" */,
  remaining_blinks /*@desc "how many cycles remain" */,
  onCycle /*@desc "TRUE if we are currently in the lamp_on cycle" */,
  
  
  /* ACTUATORS */
  blinkLeft /*@desc "Actuator for left blink lamps (0-100)" */,
  blinkRight /*@desc "Actuator for right blink lamps (0-100)" */,
  
  /* SENSORS */
  hazardWarningSwitchOn /*@desc "Actuator: TRUE when Hazard warning light switch is pressed" */,
  pitmanArmUpDown /*@desc "Actuator: Vertical position of the Pitman Arm" */,
  keyState /*@desc "Actuator: position of the Key (NoKeyInserted, KeyInserted,KeyInsertedOnPosition)" */,
  engineOn /*@desc "Actuator: TRUE when the engine is on" */
 


INVARIANT
  curDeadlines : PTIMERS --> -1..maxNAT &
  /*@label "SAF-H1" */ (hazardWarningSwitchOn = switch_on => active_blinkers=BLINK_DIRECTION) 
  /*@desc "ELS-8: As long as the hazard warning light switch is pressed (active), all
           direction indicators flash synchronously. " */ &
  
   /*@label "SAF-H2" */ (hazardWarningSwitchOn = switch_off & (remaining_blinks = -1)
    => active_blinkers = {pitman_direction(pitmanArmUpDown)} ) &

   /*@label "SAF-H3" */ (pitmanArmUpDown:PITMAN_DIRECTION_BLINKING & engineOn=TRUE 
    => {pitman_direction(pitmanArmUpDown)} <: active_blinkers) &
    
     /*@label "SAF-H4" */ (engineOn=FALSE & hazardWarningSwitchOn = switch_off => active_blinkers={})
    &
 // new invariants required for Rodin Proof:
 
  /*@label "SAF-H0" */ (hazardWarningSwitchOn = switch_on ⇒ remaining_blinks = -1) &
  
  /*@label "SAF-H3b"*/ (pitmanArmUpDown : PITMAN_DIRECTION_BLINKING & engineOn=TRUE
         => remaining_blinks = -1)
 &

  active_blinkers <: BLINK_DIRECTION &
  remaining_blinks : BLINK_CYCLE_COUNTER &

  blinkLeft: LAMP_STATUS & blinkRight : LAMP_STATUS &
  onCycle: BOOL &
  
  /*@label "SAF1" */ ((remaining_blinks=0 & (blinkLeft=lamp_off & blinkRight=lamp_off)) <=> active_blinkers ={}) &
  /*@label "SAF2" */ (blinkRight/=lamp_off => right_blink:active_blinkers) & // strengthened after finding issue with VisB
  /*@label "SAF3" */ (blinkLeft/=lamp_off  => left_blink:active_blinkers) & // ditto
  
  /*@label "SAF4" */ (active_blinkers=BLINK_DIRECTION => blinkLeft=blinkRight) // invariant added after finding issue with VisB
  &
   /*@label "SAF5" */ (onCycle=FALSE => (blinkLeft=lamp_off & blinkRight=lamp_off))
  &
   /*@label "SAF6" */ (onCycle=TRUE & active_blinkers /={} => not(blinkLeft=lamp_off & blinkRight=lamp_off))
&
   hazardWarningSwitchOn : SWITCH_STATUS &
  pitmanArmUpDown : PITMAN_POSITION &
  keyState: KEY_STATE &
  engineOn : BOOL 


ASSERTIONS
  pitman_direction : PITMAN_POSITION --> DIRECTIONS

INITIALISATION
  curDeadlines :: PTIMERS --> {-1} ;
  curDeadlines(blink_deadline) := 500 ||
  active_blinkers := {} ||
  blinkLeft,blinkRight := lamp_off,lamp_off ||
  remaining_blinks := 0 ||
  onCycle := FALSE ||
  hazardWarningSwitchOn := switch_off ||
  pitmanArmUpDown := Neutral ||
  keyState := KeyInsertedOnPosition ||
  engineOn := FALSE


OPERATIONS
  ENV_Pitman_Tip_blinking_start(newPos) = 
  SELECT newPos : PITMAN_TIP_BLINKING &
     newPos /= pitmanArmUpDown THEN
     SELECT newPos : PITMAN_TIP_BLINKING & newPos /= pitmanArmUpDown THEN
         SELECT newPos : PITMAN_TIP_BLINKING &
             newPos /= pitmanArmUpDown  THEN
             pitmanArmUpDown := newPos
         END
         ||
	 IF hazardWarningSwitchOn = switch_off & engineOn = TRUE THEN
                   VAR direction, rem IN
                       direction := pitman_direction(newPos);
                       rem := 3 ;
                       SELECT direction: BLINK_DIRECTION & rem:BLINK_CYCLE_COUNTER & rem /= 0
                       THEN
                         active_blinkers := {direction} ||
                         remaining_blinks := rem ||
                         IF direction=right_blink THEN
                           blinkLeft := lamp_off ||
                           blinkRight := cycleMaxLampStatus(onCycle)
                         ELSE
                           blinkLeft := cycleMaxLampStatus(onCycle) ||
                           blinkRight := lamp_off
                         END
                       END
		   END

         END
     END
     ||
     curDeadlines(tip_deadline) := 500
  END;
  

  RTIME_Tip_blinking_Timeout(delta) =
   SELECT
     /*@label "grdTip" */ delta : 0..500
   THEN
     IF pitmanArmUpDown : PITMAN_TIP_BLINKING & remaining_blinks > 1 &
        active_blinkers = {pitman_direction(pitmanArmUpDown)} THEN
          SELECT pitmanArmUpDown : PITMAN_TIP_BLINKING & remaining_blinks > 1 & active_blinkers = {pitman_direction(pitmanArmUpDown)} THEN
	    SELECT -1:BLINK_CYCLE_COUNTER & -1 /= 0 & remaining_blinks /= 0
            THEN
              remaining_blinks := -1
            END
          END 
     END ||
     SELECT delta:0..maxNAT & 
          tip_deadline : dom(curDeadlines) &
          delta = min(ran(curDeadlines) - {-1}) & 
          delta = curDeadlines(tip_deadline) &
          delta >= 0
     THEN
          curDeadlines := %x.(x:dom(curDeadlines) \ {tip_deadline} | max({0,curDeadlines(x)-delta})) \/ {tip_deadline |-> -1}
     END
 
  END;
  
  RTIME_BlinkerOn(delta) =
   SELECT
     /*@label "grdTip" */ delta : 0..500
   THEN
      SELECT (blinkLeft=lamp_off & blinkRight=lamp_off) & remaining_blinks /= 0 THEN
        onCycle := TRUE ||
        IF left_blink:active_blinkers THEN
          blinkLeft := lamp_on 
        END ||
        IF right_blink:active_blinkers THEN
          blinkRight := lamp_on
        END ||
        IF remaining_blinks>0 THEN
          remaining_blinks := remaining_blinks - 1
        END
      END
      || 
      VAR timer, newDelta IN
        timer := blink_deadline;
        newDelta := 500 ;
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

  END;
  
  RTIME_BlinkerOff(delta) =
   SELECT
     /*@label "grdTip" */ delta : 0..500
   THEN
      SELECT not(blinkLeft=lamp_off & blinkRight=lamp_off) THEN
        blinkLeft,blinkRight := lamp_off, lamp_off ||
        onCycle := FALSE ||
        IF remaining_blinks=0 THEN
          active_blinkers := {}
        END
      END
      ||
      VAR timer, newDelta IN
        timer := blink_deadline;
        newDelta := 500 ;
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

  END;
  
  RTIME_Nothing(delta,newOnCycle) =
   SELECT
     /*@label "grdDelta" */ delta : 0..500 &
     newOnCycle : BOOL
   THEN
      SELECT (blinkLeft=lamp_off & blinkRight=lamp_off) & active_blinkers={} & newOnCycle = FALSE THEN
        onCycle := newOnCycle
      END
      ||
      VAR timer, newDelta IN
        timer := blink_deadline ; 
        newDelta := 100 ;
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

  END;
  
  RTIME_Passes(delta) = SELECT delta : {100} THEN
      SELECT delta:0..maxNAT & ((#(tm).(tm : PTIMERS & curDeadlines(tm) >= 0)) => delta <= min(ran(curDeadlines) - {-1})) THEN
       curDeadlines := %x.(x:dom(curDeadlines)|max({0,curDeadlines(x)-delta}))
      END
  END;

 ENV_Hazard_blinking(newSwitchPos) = SELECT newSwitchPos /= hazardWarningSwitchOn THEN
 // ELS-1, ELS-5
	 SELECT newSwitchPos = switch_on // hazardWarningSwitchOn = switch_off 
	 THEN
		active_blinkers := BLINK_DIRECTION ||
    remaining_blinks := -1 ||
    blinkLeft := cycleMaxLampStatus(onCycle) ||
    blinkRight := cycleMaxLampStatus(onCycle) // if onCyle=TRUE then turn both blinkers on

	  WHEN newSwitchPos = switch_off // hazardWarningSwitchOn = switch_on
	  THEN
		IF pitmanArmUpDown = Neutral or engineOn = FALSE THEN
		   active_blinkers := {} ||
    remaining_blinks := 0 ||
    blinkLeft,blinkRight := lamp_off, lamp_off
		ELSIF  pitmanArmUpDown /: PITMAN_DIRECTION_BLINKING THEN
		   // ELS-12 : When hazard warning is deactivated again, the pitman arm is in
           //  position \direction blinking left" or \direction blinking right" ignition is On, 
           //  the direction blinking cycle should be started (see Req. ELS-1).
		   active_blinkers := {} ||
    remaining_blinks := 0 ||
    blinkLeft,blinkRight := lamp_off, lamp_off
		ELSE
                   VAR direction, rem IN
                       direction := pitman_direction(pitmanArmUpDown);
                       rem := remaining_blinks ;
                       SELECT direction: BLINK_DIRECTION & rem:BLINK_CYCLE_COUNTER & rem /= 0
                       THEN
                         active_blinkers := {direction} ||
                         remaining_blinks := rem ||
                         IF direction=right_blink THEN
                           blinkLeft := lamp_off ||
                           blinkRight := cycleMaxLampStatus(onCycle)
                         ELSE
                           blinkLeft := cycleMaxLampStatus(onCycle) ||
                           blinkRight := lamp_off
                         END
                       END
		   END
	        END
              END ||
                SELECT
                  newSwitchPos : SWITCH_STATUS &
                  newSwitchPos /= hazardWarningSwitchOn
                THEN
                  hazardWarningSwitchOn := newSwitchPos
                END
 END ;


 ENV_Turn_EngineOn =
   BEGIN
 
   SELECT engineOn=FALSE & keyState = KeyInsertedOnPosition THEN
     engineOn := TRUE
   END ||
   IF pitmanArmUpDown :PITMAN_DIRECTION_BLINKING &
      hazardWarningSwitchOn = switch_off THEN
                     VAR direction, rem IN
                       direction := pitman_direction(pitmanArmUpDown);
                       rem := -1 ;
                       SELECT direction: BLINK_DIRECTION & rem:BLINK_CYCLE_COUNTER & rem /= 0
                       THEN
                         active_blinkers := {direction} ||
                         remaining_blinks := rem ||
                         IF direction=right_blink THEN
                           blinkLeft := lamp_off ||
                           blinkRight := cycleMaxLampStatus(onCycle)
                         ELSE
                           blinkLeft := cycleMaxLampStatus(onCycle) ||
                           blinkRight := lamp_off
                         END
                       END
		   END

   END
 END;
 
 ENV_Turn_EngineOff = 
 BEGIN
 
   SELECT engineOn=TRUE THEN
     engineOn := FALSE
   END ||
   IF hazardWarningSwitchOn = switch_off
    /*@desc "ELS-8 As long as the hazard warning light switch is pressed (active), 
             all direction indicators flash synchronously." */
             // TO DO: pluse ratio 1:2 if ignition key is in lock
   THEN
		active_blinkers := {} ||
    remaining_blinks := 0 ||
    blinkLeft,blinkRight := lamp_off, lamp_off
   END
 END;

 
 ENV_Pitman_DirectionBlinking(newPos) = 
 // corresponds to pitmanArmUpDown = 2 or 4 (Upward/Downward7)
 // ELS-1, ELS-5
 PRE newPos /= pitmanArmUpDown THEN
    IF hazardWarningSwitchOn = switch_off & engineOn = TRUE THEN
                VAR direction, rem IN
                       direction := pitman_direction(newPos);
                       rem := -1;
                       SELECT direction: BLINK_DIRECTION & rem:BLINK_CYCLE_COUNTER & rem /= 0
                       THEN
                         active_blinkers := {direction} ||
                         remaining_blinks := rem ||
                         IF direction=right_blink THEN
                           blinkLeft := lamp_off ||
                           blinkRight := cycleMaxLampStatus(onCycle)
                         ELSE
                           blinkLeft := cycleMaxLampStatus(onCycle) ||
                           blinkRight := lamp_off
                         END
                       END
		   END

    END
    ||
    SELECT newPos : PITMAN_DIRECTION_BLINKING &
      newPos /= pitmanArmUpDown THEN
       pitmanArmUpDown := newPos
    END
 END;

 ENV_Pitman_Reset_to_Neutral = 
 // ELS-1, ELS-5
 BEGIN
    SELECT pitmanArmUpDown /= Neutral THEN
    pitmanArmUpDown := Neutral
    END
    ||
    IF hazardWarningSwitchOn = switch_off & (remaining_blinks = -1) THEN
		active_blinkers := {} ||
    remaining_blinks := 0 ||
    blinkLeft,blinkRight := lamp_off, lamp_off
    END
 END 
END

