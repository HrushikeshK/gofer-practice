type Variable = String
type Label = String
type State = [(String,Value)]
type Program =[(Label,Statement)]

ctype Aexp where
 Icon : Int -> Aexp 
 Ivar : Variable -> Aexp
 Add, Mul, Sub, Div : Aexp -> Aexp -> Aexp

ctype Bexp where
 Bcon : Bool -> Bexp
 Bvar : Variable -> Bexp
 And, Or : Bexp -> Bexp -> Bexp
 IsEqual : Exp -> Exp -> Bexp
 IsLessE, IsGreatE : Aexp -> Aexp -> Bexp

ctype Exp where
 Arith : Aexp -> Exp
 Boolean : Bexp -> Exp

ctype Statement where
 Abort, Skip : Statement
 Assign : Variable -> Exp -> Statement
 Sequence : Statement -> Statement -> Statement
 While : Bexp -> Statement -> Statement
 If1 : Bexp -> Statement -> Statement
 Ifelse : Bexp -> Statement -> Statement -> Statement
 Jmp : Label -> Program -> Statement
 Jmpe : Exp -> Exp -> Label -> Program -> Statement
 Jmple, Jmpge : Aexp -> Aexp -> Label -> Program -> Statement
 
ctype Value where
 StateI : Int -> Value
 StateB : Bool -> Value


-- Interpret

interpret : (Program, State) -> State
interpret.([],state)          = state
interpret.((all@((_,x)::_)),state) = interpret.(tStmt.x.(all,state))
			
			
opI : Value -> Value -> (Int->Int->Int) -> Int
opI.(StateI.x).(StateI.y).f = f.x.y

opB : Value -> Value -> (Bool->Bool->Bool) -> Bool
opB.(StateB.x).(StateB.y).f = f.x.y

tExp : Exp -> State -> Value
tExp.(Arith.(Icon.x)).env       = StateI.x
tExp.(Arith.(Ivar.x)).env       = lookup.env.x
tExp.(Arith.(Add.x.y)).env      = StateI.(opI.(tExp.(Arith.x).env).(tExp.(Arith.y).env).(+))
tExp.(Arith.(Mul.x.y)).env      = StateI.(opI.(tExp.(Arith.x).env).(tExp.(Arith.y).env).(*))
tExp.(Arith.(Sub.x.y)).env      = StateI.(opI.(tExp.(Arith.x).env).(tExp.(Arith.y).env).(-))
tExp.(Arith.(Div.x.y)).env      = StateI.(opI.(tExp.(Arith.x).env).(tExp.(Arith.y).env).(/))
tExp.(Boolean.(Bcon.x)).env     = StateB.x                     
tExp.(Boolean.(Bvar.x)).env     = lookup.env.x
tExp.(Boolean.(And.x.y)).env    = StateB.(opB.(tExp.(Boolean.x).env).(tExp.(Boolean.y).env).(&&))
tExp.(Boolean.(Or.x.y)).env     = StateB.(opB.(tExp.(Boolean.x).env).(tExp.(Boolean.y).env).(||))

tExp.(Boolean.(IsEqual.(Arith.x).(Arith.y))).env
 				| tExp.(Arith.x).env == tExp.(Arith.y).env    = StateB.True
				| otherwise 	     			      = StateB.False
				
tExp.(Boolean.(IsEqual.(Boolean.x).(Boolean.y))).env
				| tExp.(Boolean.x).env == tExp.(Boolean.y).env    = StateB.True
				| otherwise 	       	  			  = StateB.False
tExp.(Boolean.(IsEqual.(Arith.x).(Boolean.y))).env = error.("Type mismatch in IsEqual : Int -> Bool")
tExp.(Boolean.(IsEqual.(Boolean.x).(Arith.y))).env = error.("Type mismatch in IsEqual : Bool -> Int")

tExp.(Boolean.(IsLessE.x.y)).env
				| tExp.(Arith.x).env <= tExp.(Arith.y).env    = StateB.True
				| otherwise 	       			     = StateB.False
tExp.(Boolean.(IsGreatE.x.y)).env
				| tExp.(Arith.x).env >= tExp.(Arith.y).env    = StateB.True
				| otherwise 	       			     = StateB.False



                     
state   = [ ("x",StateI.10),("y",StateI.2),("z",StateI.3), ("t",StateB.True),("f",StateB.False) ]

program = [ ("l1", Assign."x".l2), ("l2", Assign."y".ly), ("l3", Jmple.(Ivar."x").(Icon.14)."l1".program), ("l4", Assign."t".l10), ("l5",Assign."z".lz) ]

{-
program2 = [ ("l1", Assign."x".l2), ("l2", Assign."y".ly), ("l3", Jmpe.(Ivar."x").(Icon.11)."l5".program), ("l4", Assign."t".l10), ("l5",Assign."z".lz) ]

program3 = [ ("l1", Assign."x".l2), ("l2", Assign."y".ly), ("l3", Jmpge.(Ivar."x").(Icon.14)."l1".program), ("l4", Assign."t".l10), ("l5",Assign."z".lz) ]
-}

lookup : [(Variable,Value)] -> String -> Value
lookup.((x,y)::xs).z
		   | z == x    = y
		   | otherwise = lookup.xs.z	   


tStmt : Statement -> (Program,State) -> (Program,State)

tStmt.Abort.(prog,state) = ([],state)
tStmt.(Assign.x.e).(((_,_)::ms),state) = (ms,cstate.x.(tExp.e.state).state)
tStmt.(Sequence.s1.s2).state = tStmt.s2.(tStmt.s1.state)

tStmt.(Jmp.lab.(all@((x,y)::xs))).(prog,state)
	   | lab == x  = (all,state)
	   | otherwise = tStmt.(Jmp.lab.xs).(prog,state)
	   
tStmt.(Jmpe.exp1.exp2.lab.prog).(rest@((_,_) :: xs),state)
	   | tExp.(Boolean.(IsEqual.exp1.exp2)).state == StateB.True  = tStmt.(Jmp.lab.prog).(rest,state)
	   | otherwise			       		              = (xs,state)

tStmt.(Jmple.exp1.exp2.lab.prog).(rest@((_,_) :: xs),state)
	   | tExp.(Boolean.(IsLessE.exp1.exp2)).state == StateB.True  = tStmt.(Jmp.lab.prog).(rest,state)
	   | otherwise			       		              = (xs,state)

tStmt.(Jmpge.exp1.exp2.lab.prog).(rest@((_,_)::xs),state)
	   | tExp.(Boolean.(IsGreatE.exp1.exp2)).state == StateB.True  = tStmt.(Jmp.lab.prog).(rest,state)
	   | otherwise			       		               = (xs,state)





---- type check and change state ----

cstate : Variable -> Value -> State -> State

cstate.x.(StateB.val).((y,(StateB.z))::xs)
			| x == y    = ((y,(StateB.val))::xs)
			| otherwise = (y,(StateB.z)) :: cstate.x.(StateB.val).xs
			
cstate.x.(StateI.val).((y,(StateI.z))::xs)
			| x == y    = ((y,(StateI.val))::xs)
			| otherwise = (y,(StateI.z)) :: cstate.x.(StateI.val).xs

cstate.x.(StateI.val).((y,(StateB.z))::xs)
			| x == y    = error.("Type Mismatch : Cannot convert Bool to Int")
			| otherwise = (y,(StateB.z)) :: cstate.x.(StateI.val).xs

cstate.x.(StateB.val).((y,(StateI.z))::xs)
			| x == y    = error.("Type Mismatch : Cannot convert Int to Bool")
			| otherwise = (y,(StateI.z)) :: cstate.x.(StateB.val).xs
			
cstate.x.val.[] = error.("No such variable available")			


l0 = Ivar."x"
l1 = Icon.1
l2 = Arith.(Add.l0.l1)

lx = Arith.(Add.l1.(Ivar."x"))
ly = Arith.(Add.l1.(Ivar."y"))
lz = Arith.(Add.l1.(Ivar."z"))

l3 = Ivar."y"
l4 = Ivar."x"
l5 = Arith.(Mul.l3.l4)

l6 = Bcon.True
l7 = Bvar."t"
l8 = Boolean.(And.l6.l7)

l9 = Bcon.False
l10 = Boolean.(And.l6.l9)
