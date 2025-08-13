import Mathlib.Tactic.Simproc.Apply
import Qq

/-
We test it on a simproc that rewrites `3` to `4`.
-/

axiom three_eq_four : 3 = 4

open Qq Lean.Meta.Simp

def threeFour : Simproc := fun e ↦ do
  let ⟨1, ~q(Nat), ~q(3)⟩ ← inferTypeQ e | return .continue
  let rhs : Q(Nat) := q(4)
  have proof : Q(3 = $rhs) := q(three_eq_four)
  return .visit { expr := rhs, proof? := .some proof }

open Lean.Elab.Tactic Lean.Parser.Tactic

elab "rw_3_4 " loc:(location)? : tactic =>
  Simproc.apply threeFour (loc.map expandLocation)

example (h : 4 = 5) : 3 = 5 := by
  rw_3_4
  exact h

example : 3 = 4 := by
  rw_3_4

example : 4 = 3 := by
  rw_3_4

example : False :=
  absurd (by rw_3_4 : 3 = 4) (by decide)

example (i : Fin 3) : Fin 4 := by
  rw_3_4 at i
  guard_hyp i :ₛ Fin 4
  exact i

set_option linter.unusedVariables false in
example (i : Fin 3) (h : 2 + 3 = 6) : Vector Int 4 := by
  rw_3_4 at i h ⊢
  guard_hyp i :ₛ Fin 4
  guard_hyp h :ₛ 2 + 4 = 6
  guard_target =ₛ Vector Int 4
  exact #v[37, 51, 64, 32]
