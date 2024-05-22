import Mathlib.Util.TermBeta
-- On command line, tests format functions with => rather than ↦ without this.
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

/-- info: (fun x x_1 ↦ x && x_1) true false : Bool -/
#guard_msgs in #check (· && ·) true false

/-- info: true && false : Bool -/
#guard_msgs in #check beta% (· && ·) true false

abbrev reducibleId : Bool → Bool := fun x => x

/-- info: reducibleId true : Bool -/
#guard_msgs in #check reducibleId true
