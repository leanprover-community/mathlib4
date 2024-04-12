/-
Copyright (c) 2024 Malvin Gattinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Malvin Gattinger
-/
import Mathlib.Logic.Relation.Basic
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Transitive relations are finite chains

This file provides theorems to convert between transitive relations and finite chains.

Currently only `Relation.ReflTransGen` is covered.
Similar results about `Relation.TransGen` should be added.
-/

variable {α : Type*}

variable {r : α → α → Prop}

variable {a b c : α}

/-- A version of `Relation.ReflTransGen.cases_tail` also giving (in)equalities. -/
-- TODO: make this an iff ↔/
theorem ReflTransGen.cases_tail_eq_neq {r : α → α → Prop} (h : Relation.ReflTransGen r a c) :
    a = c ∨ (a ≠ c ∧ ∃ b, a ≠ b ∧ r a b ∧ Relation.ReflTransGen r b c) := by
  induction h using Relation.ReflTransGen.head_induction_on
  · left
    rfl
  case head a b a_r_b b_r_z IH_b_z =>
    cases Classical.em (a = b)
    case inl a_is_b =>
      subst a_is_b
      cases IH_b_z
      case inl a_is_z =>
        left
        assumption
      case inr IH =>
        right
        assumption
    case inr a_neq_b =>
      cases IH_b_z
      case inl a_is_z =>
        subst a_is_z
        right
        constructor
        · assumption
        · use b
      case inr IH =>
        cases Classical.em (a = c)
        · left
          assumption
        · right
          constructor
          · assumption
          · use b

/-- `∃ x₀ ... xₙ, a = x₀ ∧ r x₀ x₁ ∧ ... ∧ xₙ = b` implies `ReflTransGen r a b` -/
theorem ReflTransGen.to_finitelyManySteps {r : α → α → Prop} (h : Relation.ReflTransGen r a c) :
    ∃ (n : ℕ) (f : Fin n.succ → α),
      a = f 0 ∧ c = f (Fin.last n) ∧ ∀ i : Fin n, r (f i.castSucc) (f i.succ) := by
  induction h using Relation.ReflTransGen.head_induction_on
  case refl =>
    use 0, Function.const _ c
    simp_all
  case head a b a_r_b b_rS_z IH_b_c =>
    rcases IH_b_c with ⟨m, g, b_is_g0, c_is_last, steps⟩
    use m + 1
    use Fin.cons a g
    constructor
    · simp
    · constructor
      · rw [c_is_last]; rfl
      · intro i
        cases i using Fin.induction
        · simp_all
        case succ k IH =>
          simp_all
          apply steps

/-- `ReflTransGen r a b` implies that `∃ x₀ ... xₙ, a = x₀ ∧ r x₀ x₁ ∧ ... ∧ xₙ = b` -/
theorem ReflTransGen.from_finitelyManySteps (r : α → α → Prop) {n : ℕ} :
    ∀ (a c : α) (f : Fin n.succ → α),
      (a = f 0 ∧ c = f (Fin.last n) ∧ ∀ i : Fin n, r (f i.castSucc) (f i.succ))
        → Relation.ReflTransGen r a c := by
  induction n
  case zero =>
    rintro a c f ⟨a_is_head, c_is_last, _⟩
    convert Relation.ReflTransGen.refl
  case succ n IH =>
    rintro a c f ⟨a_is_head, c_is_last, steprel⟩
    let b := f 1 -- WAIT bad, tail may be empty?
    rw [Relation.ReflTransGen.cases_head_iff]
    right
    use b
    constructor
    · specialize steprel 0
      simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one] at steprel
      rw [← a_is_head] at steprel
      convert steprel
    · apply IH b c (Fin.tail f)
      constructor
      · rfl
      constructor
      · simp_all only [] -- ??
        rfl
      · intro i
        specialize steprel i.succ
        induction i
        simp_all only [and_imp, Fin.succ_mk, Fin.castSucc_mk]
        exact steprel

/-- `ReflTransGen r a b` is equivalent to `∃ x₀ ... xₙ, a = x₀ ∧ r x₀ x₁ ∧ ... ∧ r xₙ = b` -/
theorem ReflTransGen.iff_finitelyManySteps (r : α → α → Prop) (x z : α) :
    Relation.ReflTransGen r x z ↔
      ∃ (n : ℕ) (f : Fin n.succ → α),
        x = f 0 ∧ z = f (Fin.last n) ∧ ∀ i : Fin n, r (f i.castSucc) (f (i.succ)) :=
  ⟨ReflTransGen.to_finitelyManySteps,
  fun ⟨_, ys, x_is_head, z_is_last, rhs⟩ =>
    ReflTransGen.from_finitelyManySteps r x z ys ⟨x_is_head, z_is_last, rhs⟩⟩
