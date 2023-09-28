/-
Copyright (c) 2023 Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvorak
-/
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Data.Bool.Basic
import Mathlib.Tactic.LibrarySearch
import Mathlib.Data.Finset.Basic

/-!

# General Valued Constraint Satisfaction Problems

-/

/-- Type of functions `α^n → β` for a general arity `n : ℕ` -/
def ofArity (α β : Type _) : ℕ → Type
| 0   => β
| n+1 => α → ofArity α β n

def ofArityEval {α β : Type _} {n : ℕ} (f : ofArity α β n) (a : Fin n → α) : β :=
  match n with
  | 0   => sorry
  | n+1 => sorry

/-- A template for a valued CSP problem with costs in `C` which is usually `ℚ≥0` -/
structure ValuedCspTemplate (C : Type) [LinearOrderedAddCommMonoid C] where
  /-- Domain of "labels" -/
  D : Type
  /-- Cost functions `D^k → C` for any `k` -/
  F : List (Σ (k : ℕ), ofArity D C k)

structure ValuedCspTerm {C : Type} [LinearOrderedAddCommMonoid C] (Γ : ValuedCspTemplate C)
    (ι : Type) where
  f : Σ (k : ℕ), ofArity Γ.D C k
  f_in_Γ : f ∈ Γ.F
  app : Fin f.fst → ι

def ValuedCspInstance {C : Type} [LinearOrderedAddCommMonoid C] (Γ : ValuedCspTemplate C)
    (ι : Type) : Type :=
  List (ValuedCspTerm Γ ι)

def ValuedCspTerm.evalSolution {C : Type} [LinearOrderedAddCommMonoid C] {Γ : ValuedCspTemplate C}
    {ι : Type} (t : ValuedCspTerm Γ ι) (x : ι → Γ.D) : C :=
  ofArityEval t.f.snd (x ∘ t.app)

def ValuedCspInstance.evalSolution {C : Type} [LinearOrderedAddCommMonoid C] {Γ : ValuedCspTemplate C}
    {ι : Type} (I : ValuedCspInstance Γ ι) (x : ι → Γ.D) : C :=
  (I.map (fun t => t.evalSolution x)).sum









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
  le := Bool.linearOrder.le
  lt := Bool.linearOrder.lt
  le_refl := Bool.linearOrder.le_refl
  le_trans := Bool.linearOrder.le_trans
  lt_iff_le_not_le := Bool.linearOrder.lt_iff_le_not_le
  le_antisymm := Bool.linearOrder.le_antisymm
  min := Bool.linearOrder.min
  max := Bool.linearOrder.max
  compare := Bool.linearOrder.compare
  le_total := Bool.linearOrder.le_total
  decidableLE := Bool.linearOrder.decidableLE
  decidableEq := Bool.linearOrder.decidableEq
  decidableLT := Bool.linearOrder.decidableLT
  min_def := Bool.linearOrder.min_def
  max_def := Bool.linearOrder.max_def
  compare_eq_compareOfLessAndEq := Bool.linearOrder.compare_eq_compareOfLessAndEq
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

private def exampleEquality : ofArity (Fin 3) Bool 2 := fun a b => a == b

private def exampleEquality' : Σ (k : ℕ), ofArity (Fin 3) Bool k := ⟨2, exampleEquality⟩

private def exampleCrispCsp : ValuedCspTemplate Bool :=
.mk (Fin 3) [exampleEquality']

private def exampleTermAB : ValuedCspTerm exampleCrispCsp (Fin 4) := by
  use exampleEquality'
  · simp [exampleCrispCsp]
  --exact ![1, 2]
  simp [exampleEquality']
  intro i
  match i with
  | 0 => exact 0
  | 1 => exact 1

#print exampleTermAB
