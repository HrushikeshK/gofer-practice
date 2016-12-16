type Variable = String

ctype Aexp where
 Icon : Int -> Aexp 
 Ivar : Variable -> Aexp
 Add, Mul, Sub, Div : Aexp -> Aexp -> Aexp

ctype Bexp where
 Bcon : Bool -> Bexp
 Bvar : Variable -> Bexp
 And, Or : Bexp -> Bexp -> Bexp

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

interpret : [Statement] -> State -> State
interpret.[].state=state
interpret.(x::xs).state=interpret.xs.(tStmt.x.state)

interpret1 : [Program] -> State -> State
interpret1.[].state=state
interpret1.(x::xs).state=interpret.xs.(tStmt.x.state)

ctype Value where
 StateI : Int -> Value
 StateB : Bool -> Value

type State = [(String,Value)]
type Program =[(String,Statement)]
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

                     
state = [("x",StateI.10),("y",StateI.2),("z",StateI.3),("t",StateB.True),("f",StateB.False)]


lookup : [([Char],Value)] -> String -> Value
lookup.((x,(StateI.y))::xs).z
		   | z == x    = StateI.y
		   | otherwise = lookup.xs.z
lookup.((x,(StateB.y))::xs).z
		   | z == x    = StateB.y
		   | otherwise = lookup.xs.z		   


tStmt : Statement -> State -> State
tStmt.(Assign.x.e).state = cstate.x.(tExp.e.state).state
tStmt.(Sequence.s1.s2).state = tStmt.s2.(tStmt.s1.state) 

cstate.x.expr.((y,(StateI.z))::xs)
			| x == y    = ((y,expr)::xs)
			| otherwise = (y,(StateI.z)) :: cstate.x.expr.xs
cstate.x.expr.((y,(StateB.z))::xs)
			| x == y    = ((y,expr)::xs)
			| otherwise = (y,(StateB.z)) :: cstate.x.expr.xs
cstate.x.expr.[] = []			


l0 = Icon.10
l1 = Icon.2
l2 = Add.l0.l1

l3 = Ivar."y"
l4 = Ivar."x"
l5 = Mul.l3.l4

l6 = Bcon.True
l7 = Bvar."t"
l8 = And.l6.l7

