module

public import Mathlib.Tactic.PPWithUniv

universe u

@[pp_with_univ]
def Foo := Sort u

/-- info: Foo.{u} : Type u -/
#guard_msgs in
#check Foo.{u}

/-- info: Foo.{2} : Type 2 -/
#guard_msgs in
#check Foo.{2}

set_option pp.mdata true in
/-- info: Foo.{3} : Type 3 -/
#guard_msgs in
#check Foo.{3}

@[pp_with_univ]
def Bar (n : Nat) := Fin n → Sort u

/-- info: Bar.{u} : Nat → Type u -/
#guard_msgs in
#check Bar.{u}

/-- info: Bar.{u} 13 : Type u -/
#guard_msgs in
#check Bar.{u} 13

/-- info: Bar.{2} : Nat → Type 2 -/
#guard_msgs in
#check Bar.{2}

/-- info: Bar.{2} 9 : Type 2 -/
#guard_msgs in
#check Bar.{2} 9

set_option pp.mdata true in
/-- info: Bar.{3} : Nat → Type 3 -/
#guard_msgs in
#check Bar.{3}

set_option pp.mdata true in
/-- info: Bar.{3} 8 : Type 3 -/
#guard_msgs in
#check Bar.{3} 8
