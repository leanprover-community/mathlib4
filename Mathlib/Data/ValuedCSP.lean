/-
Copyright (c) 2023 Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvorak
-/
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Data.Bool.Basic
import Mathlib.Tactic.LibrarySearch
import Mathlib.Data.Finset.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!

# General Valued Constraint Satisfaction Problems

-/

/-- A template for a valued CSP problem with costs in `C` which is usually `ℚ≥0` -/
structure ValuedCspTemplate (C : Type) [LinearOrderedAddCommMonoid C] where
  /-- Domain of "labels" -/
  D : Type
  /-- Cost functions `D^k → C` for any `k` -/
  F : List (Σ (k : ℕ), (Fin k → D) → C)

structure ValuedCspTerm {C : Type} [LinearOrderedAddCommMonoid C] (Γ : ValuedCspTemplate C)
    (ι : Type) where
  f : Σ (k : ℕ), (Fin k → Γ.D) → C
  inΓ : f ∈ Γ.F
  app : Fin f.fst → ι

def ValuedCspInstance {C : Type} [LinearOrderedAddCommMonoid C] (Γ : ValuedCspTemplate C)
    (ι : Type) : Type :=
  List (ValuedCspTerm Γ ι)

def ValuedCspTerm.evalSolution {C : Type} [LinearOrderedAddCommMonoid C]
    {Γ : ValuedCspTemplate C} {ι : Type}
    (t : ValuedCspTerm Γ ι) (x : ι → Γ.D) : C :=
  t.f.snd (x ∘ t.app)

def ValuedCspInstance.evalSolution {C : Type} [LinearOrderedAddCommMonoid C]
    {Γ : ValuedCspTemplate C} {ι : Type}
    (I : ValuedCspInstance Γ ι) (x : ι → Γ.D) : C :=
  (I.map (fun t => t.evalSolution x)).sum

def ValuedCspInstance.optimumSolution {C : Type} [LinearOrderedAddCommMonoid C]
    {Γ : ValuedCspTemplate C} {ι : Type}
    (I : ValuedCspInstance Γ ι) (x : ι → Γ.D) : Prop :=
  ∀ y : ι → Γ.D, I.evalSolution x ≤ I.evalSolution y









private def Bool_nsmul_zero (b : Bool) :
  ((fun (n : ℕ) (a : Bool) => a && decide (n > 0)) 0 b) = false :=
by
  simp

private def Bool_nsmul_succ (n : ℕ) (b : Bool) :
  (fun m a ↦ a && decide (m > 0)) (n + 1) b = (b || (fun m a ↦ a && decide (m > 0)) n b) :=
by
  cases b with
  | false => rfl
  | true => simp [Nat.succ_pos n]

private def Bool_add_le_add_left (a b : Bool) :
  (a = false ∨ b = true) → ∀ (c : Bool), (((c || a) = false) ∨ ((c || b) = true)) :=
by
  simp

-- Upside down !!
instance crispCodomain : LinearOrderedAddCommMonoid Bool where
  __ := Bool.linearOrder
  add (a b : Bool) := a || b
  add_assoc := Bool.or_assoc
  zero := false
  zero_add (_ : Bool) := rfl
  add_zero := Bool.or_false
  nsmul (n : ℕ) (a : Bool) := a && (n > 0)
  nsmul_zero := Bool_nsmul_zero
  nsmul_succ := Bool_nsmul_succ
  add_comm := Bool.or_comm
  add_le_add_left := Bool_add_le_add_left

-- example : B ≠ A ≠ C ≠ D ≠ B ≠ C with three available colors

private def exampleEqualit : (Fin 2 → Fin 3) → Bool := fun d => d 0 == d 1

private def exampleEquality : Σ (k : ℕ), (Fin k → Fin 3) → Bool := ⟨2, exampleEqualit⟩

private def exampleCrispCsp : ValuedCspTemplate Bool :=
  ValuedCspTemplate.mk (Fin 3) [exampleEquality]

private def exampleTermAB : ValuedCspTerm exampleCrispCsp (Fin 4) :=
  ValuedCspTerm.mk exampleEquality (by simp [exampleCrispCsp]) ![0, 1]

private def exampleTermBC : ValuedCspTerm exampleCrispCsp (Fin 4) :=
  ValuedCspTerm.mk exampleEquality (by simp [exampleCrispCsp]) ![1, 2]

private def exampleTermCA : ValuedCspTerm exampleCrispCsp (Fin 4) :=
  ValuedCspTerm.mk exampleEquality (by simp [exampleCrispCsp]) ![2, 0]

private def exampleTermBD : ValuedCspTerm exampleCrispCsp (Fin 4) :=
  ValuedCspTerm.mk exampleEquality (by simp [exampleCrispCsp]) ![1, 3]

private def exampleTermCD : ValuedCspTerm exampleCrispCsp (Fin 4) :=
  ValuedCspTerm.mk exampleEquality (by simp [exampleCrispCsp]) ![2, 3]

private def exampleCrispCspInstance : ValuedCspInstance exampleCrispCsp (Fin 4) :=
  [exampleTermAB, exampleTermBC, exampleTermCA, exampleTermBD, exampleTermCD]

private def exampleSolutionCorrect0 : Fin 4 → Fin 3 :=   ![0, 1, 2, 0]
private def exampleSolutionCorrect1 : Fin 4 → Fin 3 :=   ![1, 2, 3, 1]
private def exampleSolutionCorrect2 : Fin 4 → Fin 3 :=   ![2, 0, 1, 2]
private def exampleSolutionCorrect3 : Fin 4 → Fin 3 :=   ![0, 2, 1, 0]
private def exampleSolutionCorrect4 : Fin 4 → Fin 3 :=   ![1, 0, 2, 1]
private def exampleSolutionCorrect5 : Fin 4 → Fin 3 :=   ![1, 0, 2, 1]
private def exampleSolutionIncorrect0 : Fin 4 → Fin 3 := ![0, 0, 0, 0]
private def exampleSolutionIncorrect1 : Fin 4 → Fin 3 := ![1, 0, 0, 0]
private def exampleSolutionIncorrect2 : Fin 4 → Fin 3 := ![0, 2, 0, 0]
private def exampleSolutionIncorrect3 : Fin 4 → Fin 3 := ![0, 1, 0, 2]
private def exampleSolutionIncorrect4 : Fin 4 → Fin 3 := ![2, 2, 0, 1]
private def exampleSolutionIncorrect5 : Fin 4 → Fin 3 := ![0, 1, 2, 1]
private def exampleSolutionIncorrect6 : Fin 4 → Fin 3 := ![1, 0, 0, 1]
private def exampleSolutionIncorrect7 : Fin 4 → Fin 3 := ![2, 2, 0, 2]

#eval exampleCrispCspInstance.evalSolution exampleSolutionCorrect0 -- `false` means SATISFIED here
#eval exampleCrispCspInstance.evalSolution exampleSolutionCorrect1 -- `false` means SATISFIED here
#eval exampleCrispCspInstance.evalSolution exampleSolutionCorrect2 -- `false` means SATISFIED here
#eval exampleCrispCspInstance.evalSolution exampleSolutionCorrect3 -- `false` means SATISFIED here
#eval exampleCrispCspInstance.evalSolution exampleSolutionCorrect4 -- `false` means SATISFIED here
#eval exampleCrispCspInstance.evalSolution exampleSolutionCorrect5 -- `false` means SATISFIED here
#eval exampleCrispCspInstance.evalSolution exampleSolutionIncorrect0 -- `true` means WRONG here
#eval exampleCrispCspInstance.evalSolution exampleSolutionIncorrect1 -- `true` means WRONG here
#eval exampleCrispCspInstance.evalSolution exampleSolutionIncorrect2 -- `true` means WRONG here
#eval exampleCrispCspInstance.evalSolution exampleSolutionIncorrect3 -- `true` means WRONG here
#eval exampleCrispCspInstance.evalSolution exampleSolutionIncorrect4 -- `true` means WRONG here
#eval exampleCrispCspInstance.evalSolution exampleSolutionIncorrect5 -- `true` means WRONG here
#eval exampleCrispCspInstance.evalSolution exampleSolutionIncorrect6 -- `true` means WRONG here
#eval exampleCrispCspInstance.evalSolution exampleSolutionIncorrect7 -- `true` means WRONG here

example : exampleCrispCspInstance.optimumSolution exampleSolutionCorrect0 := by
  unfold ValuedCspInstance.optimumSolution
  intro s
  exact Bool.false_le
