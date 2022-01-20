MACHINE abz2020_PitmanController_v6



SETS
  DIRECTIONS = {left_blink,right_blink,neutral_blink};
  SWITCH_STATUS = {switch_on,switch_off};
  PITMAN_POSITION = {Neutral, Downward5, Downward7, Upward5, Upward7};
  KEY_STATE = {NoKeyInserted, KeyInserted,KeyInsertedOnPosition}

CONSTANTS
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



ASSERTIONS
 /*@label "thm1" */ pitman_direction : PITMAN_POSITION --> DIRECTIONS

VARIABLES

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

INITIALISATION

  active_blinkers := {} ||
  blinkLeft,blinkRight := lamp_off,lamp_off ||
  remaining_blinks := 0 ||
  onCycle := FALSE ||
  hazardWarningSwitchOn := switch_off ||
  pitmanArmUpDown := Neutral ||
  keyState := KeyInsertedOnPosition ||
  engineOn := FALSE



OPERATIONS

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



   // TIME-PASSING Events; in the ValidationSequences these events happen every 500 ms
  TIME_BlinkerOn = SELECT (blinkLeft=lamp_off & blinkRight=lamp_off) & remaining_blinks /= 0 THEN
    onCycle := TRUE ||
    IF left_blink:active_blinkers THEN
       blinkLeft := lamp_on 
    END ||
    IF right_blink:active_blinkers THEN
       blinkRight := lamp_on
    END ||
    IF remaining_blinks>0 THEN
       remaining_blinks := remaining_blinks - 1
       // for ELS-7 we already decrement here; setting remaining_blinks now to 3 will complete cycle and then do 3 new blinks
    END
 END;
 
 TIME_BlinkerOff = SELECT not(blinkLeft=lamp_off & blinkRight=lamp_off) THEN
    blinkLeft,blinkRight := lamp_off, lamp_off ||
    onCycle := FALSE ||
    IF remaining_blinks=0 THEN
       active_blinkers := {}
    END
 END;
 
 TIME_Nothing(newOnCycle) = SELECT (blinkLeft=lamp_off & blinkRight=lamp_off) & active_blinkers={} & newOnCycle = FALSE THEN
    onCycle := newOnCycle
  END;


/*
 SET_Pitman_Reset_to_Neutral = 
 SELECT pitmanArmUpDown /= Neutral THEN
    pitmanArmUpDown := Neutral
 END;
*/


/* 
 SET_Hazard_blinking(newSwitchPos) = SELECT newSwitchPos : SWITCH_STATUS &
    newSwitchPos /= hazardWarningSwitchOn THEN
		hazardWarningSwitchOn := newSwitchPos 
 END; 
*/

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
 END;
 
 ENV_Pitman_Tip_blinking_short(newPos) = 
 // ELS-2, ELS-5
 PRE newPos : PITMAN_TIP_BLINKING &
     newPos /= pitmanArmUpDown THEN
 
         SELECT newPos : PITMAN_TIP_BLINKING &
             newPos /= pitmanArmUpDown  THEN
             pitmanArmUpDown := newPos
         END

        ||
	   IF hazardWarningSwitchOn = switch_off 
	     
	      & engineOn = TRUE 
		 THEN
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
 END;
 
 TIME_Tip_blinking_Timeout = 
 // after 0.5 seconds a Tip blinking is cancelled and replaced by a continuous blinking
 // ELS-4: If the driver holds the pitman arm for more than 0.5 seconds in position "tip-blinking left", 
 // flashing cycles are initiated for all direction
 // indicators on the left (see Req. ELS-1) until the pitman arm leaves the position "tip-blinking left".
 SELECT pitmanArmUpDown : PITMAN_TIP_BLINKING & remaining_blinks > 1 &
        active_blinkers = {pitman_direction(pitmanArmUpDown)} THEN
	    SELECT -1:BLINK_CYCLE_COUNTER & -1 /= 0 & remaining_blinks /= 0
            THEN
              remaining_blinks := -1
            END

 END 

 
END

