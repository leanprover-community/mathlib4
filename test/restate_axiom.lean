import Mathlib.Tactic.RestateAxiom

structure A :=
  (x : Nat)
  (a' : x = 1 := by rfl)
  (borp : x = 2 := by rfl)

#check A.a'
restate_axiom A.a'
#check A.a
restate_axiom A.a' foo
#check A.foo
restate_axiom A.borp
#check A.borp_lemma
