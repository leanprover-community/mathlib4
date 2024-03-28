/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Tactic.ITauto

section ITauto₀
variable (p q r : Prop)
variable (h : p ∧ q ∨ p ∧ r)

example : p ∧ p := by itauto

end ITauto₀

section ITauto₃

example (p : Prop) : ¬(p ↔ ¬p) := by itauto
example (p : Prop) : ¬p = ¬p := by itauto
example (p : Prop) : p ≠ ¬p := by itauto

example (p : Prop) : p ∧ True ↔ p := by itauto
example (p : Prop) : p ∨ False ↔ p := by itauto
example (p q : Prop) (h0 : q) : p → q := by itauto
example (p q r : Prop) : p ∨ q ∧ r → (p ∨ q) ∧ (r ∨ p ∨ r) := by itauto
example (p q r : Prop) : p ∨ q ∧ r → (p ∨ q) ∧ (r ∨ p ∨ r) := by itauto
example (p q r : Prop) (h : p) : (p → q ∨ r) → q ∨ r := by itauto
example (p q : Prop) (h : ¬(p ↔ q)) (h' : p) : ¬q := by itauto
example (p q : Prop) (h : ¬(p ↔ q)) (h' : q) : ¬p := by itauto
example (p q : Prop) (h : ¬(p ↔ q)) (h' : ¬q) (h'' : ¬p) : False := by itauto
example (p q r : Prop) (h : p ↔ q) (h' : r ↔ q) (h'' : ¬r) : ¬p := by itauto
example (p q r : Prop) (h : p ↔ q) (h' : r ↔ q) : p ↔ r := by itauto
example (p q : Prop) : Xor' p q → (p ↔ ¬q) := by itauto
example (p q : Prop) : Xor' p q → Xor' q p := by itauto

example (p q r : Prop) (h : ¬(p ↔ q)) (h' : r ↔ q) : ¬(p ↔ r) := by itauto

example (p : Prop) : p → ¬(p → ¬p) := by itauto

example (p : Prop) (em : p ∨ ¬p) : ¬(p ↔ ¬p) := by itauto

example (p : Prop) [Decidable p] : p ∨ ¬p := by itauto *
example (p : Prop) [Decidable p] : ¬(p ↔ ¬p) := by itauto
example (p q r : Prop) [Decidable p] : (p → q ∨ r) → (p → q) ∨ (p → r) := by itauto *
example (p q r : Prop) [Decidable q] : (p → q ∨ r) → (p → q) ∨ (p → r) := by itauto [q]

example (xl yl zl xr yr zr : Prop) :
    (xl ∧ yl ∨ xr ∧ yr) ∧ zl ∨ (xl ∧ yr ∨ xr ∧ yl) ∧ zr ↔
      xl ∧ (yl ∧ zl ∨ yr ∧ zr) ∨ xr ∧ (yl ∧ zr ∨ yr ∧ zl) := by itauto

example : 0 < 1 ∨ ¬0 < 1 := by itauto *
example (p : Prop) (h : 0 < 1 → p) (h2 : ¬0 < 1 → p) : p := by itauto *

example (b : Bool) : ¬b ∨ b := by itauto *
example (p : Prop) : ¬p ∨ p := by itauto! [p]
example (p : Prop) : ¬p ∨ p := by itauto! *

-- failure tests
example (p q r : Prop) : True := by
  haveI : p ∨ ¬p := by (fail_if_success itauto); sorry
  clear this; haveI : ¬(p ↔ q) → ¬p → q := by (fail_if_success itauto); sorry
  clear this; haveI : ¬(p ↔ q) → (r ↔ q) → (p ↔ ¬r) := by (fail_if_success itauto); sorry
  trivial

example (P : Nat → Prop) (n : Nat)
    (h : ¬(n = 7 ∨ n = 0) ∧ P n) : ¬(P n → n = 7 ∨ n = 0) := by itauto

section ModuloSymmetry
variable {p q r : Prop} {α : Type} {x y : α}
variable (h : x = y)
variable (h'' : (p ∧ q ↔ q ∨ r) ↔ (r ∧ p ↔ r ∨ q))
example (h' : ¬x = y) : p ∧ q := by itauto
example : x = y := by itauto
end ModuloSymmetry

end ITauto₃

example (p1 p2 p3 p4 p5 p6 f : Prop)
    (h : (
      (p1 ∧ p2 ∧ p3 ∧ p4 ∧ p5 ∧ p6 ∧ True) ∨
      (((p1 → f) → f) → f) ∨
      (p2 → f) ∨
      (p3 → f) ∨
      (p4 → f) ∨
      (p5 → f) ∨
      (p6 → f) ∨
      False
    ) → f) : f := by itauto
