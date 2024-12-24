import Mathlib.Util.Term.Basic

-- On command line, tests format functions with => rather than ↦ without this.
set_option pp.unicode.fun true

/-- info: id (id true) : Bool -/
#guard_msgs in #check id (id true)

/-- info: id true : Bool -/
#guard_msgs in #check delta% id (id true)

/-- info: true : Bool -/
#guard_msgs in #check delta% delta% id (id true)

/-- info: true : Bool -/
#guard_msgs in #check delta% delta% by exact id (id true)

/-- info: let x := true; x : Bool -/
#guard_msgs in #check let x := true; x

/-- info: true : Bool -/
#guard_msgs in #check zeta% let x := true; x

/-- info: let x := true; let y := x; y : Bool -/
#guard_msgs in #check let x := true; let y := x; y

/-- info: true : Bool -/
#guard_msgs in #check zeta% let x := true; let y := x; y

/-- info: true : Bool -/
#guard_msgs in #check zeta% by exact let x := true; let y := x; y

class A where

class B extends A where

class C extends A where

instance c : C :=
  letI : B := {}
  {}

set_option pp.explicit true in
/-- info: @C.mk (@B.toA (@B.mk A.mk)) : C -/
#guard_msgs in #check delta% c

set_option pp.explicit true in
/-- info: @C.mk A.mk : C -/
#guard_msgs in #check reduceProj% delta% c
