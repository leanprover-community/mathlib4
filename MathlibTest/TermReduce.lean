import Mathlib.Util.TermReduce
-- On command line, tests format functions with => rather than ↦ without this.
set_option linter.style.setOption false
set_option pp.unicode.fun true

/-- info: (fun x ↦ x) true : Bool -/
#guard_msgs in #check (fun x => x) true

/-- info: true : Bool -/
#guard_msgs in #check beta% (fun x => x) true

/-- info: (fun x y ↦ (x, y)) true : Bool → Bool × Bool -/
#guard_msgs in #check (fun (x y : Bool) => (x, y)) true

/-- info: fun y ↦ (true, y) : Bool → Bool × Bool -/
#guard_msgs in #check beta% (fun (x y : Bool) => (x, y)) true

/-- info: (fun x ↦ cond x) true 1 : Nat → Nat -/
#guard_msgs in #check (fun (x : Bool) => cond x) true 1

/-- info: cond true 1 : Nat → Nat -/
#guard_msgs in #check beta% (fun (x : Bool) => cond x) true 1

/-- info: ∀ (i : Nat), 0 ≤ i : Prop -/
#guard_msgs in #check ∀ i : Nat, beta% (fun j => 0 ≤ j) i

/-- info: (fun x1 x2 ↦ x1 && x2) true false : Bool -/
#guard_msgs in #check (· && ·) true false

/-- info: true && false : Bool -/
#guard_msgs in #check beta% (· && ·) true false

abbrev reducibleId : Bool → Bool := fun x => x

/-- info: reducibleId true : Bool -/
#guard_msgs in #check reducibleId true

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

set_option pp.all true in
/-- info: @C.mk A.mk : C -/
#guard_msgs in #check delta% c

set_option pp.all true in
/-- info: @C.mk A.mk : C -/
#guard_msgs in #check reduceProj% delta% c
