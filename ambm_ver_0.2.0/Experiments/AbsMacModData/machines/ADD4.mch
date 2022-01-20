MACHINE ADD4 
/*" U2B3.6.5d generated this component from Class ADD4 "*/
CONSTANTS
            MaxN
PROPERTIES
            MaxN = 3
VARIABLES
	inpA,
	inpB,
	inpc,
	out,
	outc,
	valid
INVARIANT
	inpA : 0..MaxN &
	inpB : 0..MaxN &
	inpc : 0..1 &
	out : 0..MaxN &
	outc : 0..1 &
	valid : BOOL &
	(valid=TRUE => 
	outc*(MaxN + 1)+out=inpA+inpB+inpc)
INITIALISATION
	inpA := 0 ||
	inpB := 0 ||
	inpc := 0 ||
	out := 0 ||
	outc := 0 ||
	valid := TRUE

OPERATIONS
 calculate  =
BEGIN
	SELECT
		valid=FALSE
	THEN
		out:=(inpA+inpB+inpc) mod (MaxN + 1) ||
		outc:=(inpA+inpB+inpc) / (MaxN + 1) ||
		valid:=TRUE 
		
	END
END
;
 reset  =
BEGIN
	SELECT
		valid=TRUE
	THEN
		valid:=FALSE ||
		ANY ia,ib,ic WHERE ia: 0..MaxN & ib:0..MaxN &ic:0..1
		THEN inpA:=ia || inpB:=ib || inpc:=ic
		END
	END
END
;
 evol0  =
BEGIN
	skip
END
;
 setc1  =
BEGIN
	skip
END
;
 evol1  =
BEGIN
	skip
END
;
 setc2  =
BEGIN
	skip
END
;
 evol2  =
BEGIN
	skip
END
;
 setc3  =
BEGIN
	skip
END
;
 evol3  =
BEGIN
	skip
END
END

