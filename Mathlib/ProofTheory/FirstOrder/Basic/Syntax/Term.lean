/-
Copyright (c) 2024 Shogo Saito. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shogo Saito. Adapted for mathlib by Hunter Monroe
-/
import Mathlib.ProofTheory.Matrix
import Mathlib.ModelTheory.Syntax

/-!
# Terms of first-order logic

This file defines the terms of first-order logic, in greater generality than
`Mathlib.ModelTheory.Syntax`.

The bounded variables are denoted by `&.x` for `x : Fin n`, and free variables are denoted
by `%.x` for `x : α`. `t : L.Semiterm α n` is a (semi-)term of language `L` with bounded variables
of `Fin n` and free variables of `α`.
-/

namespace FirstOrder

/-- A Semiterm is a type plus one of `n` bounded variables -/
abbrev Language.Semiterm (L : Language) (α : Type*) (n : ℕ) := L.Term (α ⊕ Fin n)

/-- `&` prefer for a bounded variable -/
scoped[FirstOrder] prefix:arg "&" => FirstOrder.Language.Term.var ∘ Sum.inr

/-- `SyntacticiSemiterm` is type `ℕ` and one of `n` bounded variables -/
abbrev Language.SyntacticSemiterm (L : Language) (n : ℕ) := L.Semiterm ℕ n

/-- `SyntacticTerm` is a term given by type `ℕ` -/
abbrev Language.SyntacticTerm (L : Language) := L.Term ℕ

namespace Language.Term

universe u u₁ u₂ u₃ v v₁ v₂ v₃

variable
  {L L' : Language.{u}} {L₁ : Language.{u₁}} {L₂ : Language.{u₂}} {L₃ : Language.{u₃}}
  {α α' : Type v} {α₁ : Type v₁} {α₂ : Type v₂} {α₃ : Type v₃}
  {n n₁ n₂ n₃ : ℕ}

section Decidable

variable [(k : ℕ) → DecidableEq (L.Functions k)] [DecidableEq α]

-- This should be included in Mathlib.ModelTheory.Syntax.
/-- Has decidable equality -/
def hasDecEq : (t u : L.Term α) → Decidable (Eq t u)
  | var x,              var y                => by simp; exact decEq x y
  | var _,              func _ _             => isFalse Term.noConfusion
  | func _ _,           var _                => isFalse Term.noConfusion
  | @func L α k₁ f₁ v₁, @func L α k₂ f₂ v₂ => by
      by_cases e : k₁ = k₂
      · rcases e with rfl
        exact match decEq f₁ f₂ with
        | isTrue h => by simp[h]; exact Matrix.decVec _ _ (fun i => hasDecEq (v₁ i) (v₂ i))
        | isFalse h => isFalse (by simp[h])
      · exact isFalse (by simp[e])

instance : DecidableEq (L.Term α) := hasDecEq

end Decidable

section

/-- `bvar` is a bounded variable -/
abbrev bvar (x : Fin n) : L.Semiterm α n := var (Sum.inr x)

/-- Free variable `fvar` is a `Semiterm` give by type `α` -/
abbrev fvar (x : α) : L.Semiterm α n := var (Sum.inl x)

-- These notations are based on https://github.com/leanprover-community/mathlib4/blob/e7991a6bedc97ed0ea667ae44d268634e5dd8815/Mathlib/ModelTheory/Syntax.lean#L260-L260, but I don't think they are good notations.
/-- Prefix notation `%.` for `fvar` -/
scoped[FirstOrder] prefix:max "%." => FirstOrder.Language.Term.fvar

/-- Prefix notation `&.` for `bvar` -/
scoped[FirstOrder] prefix:max "&." => FirstOrder.Language.Term.bvar

variable [DecidableEq α]

/-- Bounded variable `bv` -/
def bv (t : Semiterm L α n) : Finset (Fin n) := Finset.eraseNone <| t.varFinset.image Sum.getRight?

@[simp] lemma bv_bvar (x : Fin n) : (&.x : Semiterm L α n).bv = {x} := rfl

@[simp] lemma bv_fvar (x : α) : (%.x : Semiterm L α n).bv = ∅ := rfl

lemma bv_func {k} (f : L.Functions k) (v : Fin k → Semiterm L α n) :
    (func f v).bv = .biUnion .univ fun i ↦ (v i).bv := by
  simp [bv, Finset.biUnion_image]; ext; simp

@[simp] lemma bv_constant (f : L.Functions 0) (v : Fin 0 → Semiterm L α n) : (func f v).bv = ∅ :=
  rfl

/--`Positive` has positive number of bounded variables -/
def Positive (t : Semiterm L α (n + 1)) : Prop := ∀ x ∈ t.bv, 0 < x

namespace Positive

@[simp] protected lemma bvar (x : Fin n) : Positive (&.x : Semiterm L α (n + 1)) ↔
  (0 : Fin (n+1)) < x := by simp[Positive]

@[simp] protected lemma fvar (x : α) : Positive (%.x : Semiterm L α (n + 1)) := by simp[Positive]

@[simp] protected lemma func {k} (f : L.Functions k) (v : Fin k → Semiterm L α (n + 1)) :
    Positive (func f v) ↔ ∀ i, Positive (v i) := by simp[Positive, bv]; rw [forall_comm]

end Positive

/-- Free variable -/
def fv (t : Semiterm L α n) : Finset α := Finset.eraseNone <| t.varFinset.image Sum.getLeft?

@[simp] lemma fv_bvar (x : Fin n) : (&.x : Semiterm L α n).fv = ∅ := rfl

@[simp] lemma fv_fvar (x : α) : (%.x : Semiterm L α n).fv = {x} := rfl

lemma fv_func {k} (f : L.Functions k) (v : Fin k → Semiterm L α n) :
    (func f v).fv = .biUnion .univ fun i ↦ fv (v i) := by
  simp [fv, Finset.biUnion_image]; ext; simp

@[simp] lemma fv_constant (f : L.Functions 0) (v : Fin 0 → Semiterm L α n) : (func f v).fv = ∅ :=
  rfl

end

end Language.Term

end FirstOrder
