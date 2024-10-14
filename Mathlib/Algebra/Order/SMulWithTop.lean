/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.Algebra.Order.AddTorsor
import Mathlib.Order.WithBot

/-!
# Ordered scalar multiplication and vector addition with top
This file has some lemmas for extending ordered vector addition.

## Instances
* VAdd (WithTop G) (WithTop P)
* IsOrderedVAdd (WithTop G) (WithTop P)

## TODO
* multiplicativize

-/

open Function

variable {G P : Type*}

namespace WithTop

variable [VAdd G P] {g : WithTop G} {p : WithTop P}

instance : VAdd (WithTop G) (WithTop P) :=
  ⟨Option.map₂ (· +ᵥ ·)⟩

@[simp]
theorem coe_vAdd (g : G) (p : P) :
    ↑(g +ᵥ p) = ((g : WithTop G) +ᵥ (p : WithTop P)) :=
  rfl

@[simp]
theorem top_vAdd : (⊤ : WithTop G) +ᵥ p = ⊤ :=
  rfl

@[simp]
theorem vAdd_top : g +ᵥ (⊤ : WithTop P) = ⊤ := by cases g <;> rfl

@[simp]
theorem vAdd_eq_top : g +ᵥ p = ⊤ ↔ g = ⊤ ∨ p = ⊤ := by
  match g, p with
  | ⊤, _ => simp
  | _, ⊤ => simp
  | (g : G), (p : P) =>
    simp only [← coe_vAdd, coe_ne_top, or_self, iff_false, ne_eq]

theorem vAdd_ne_top : g +ᵥ p ≠ ⊤ ↔ g ≠ ⊤ ∧ p ≠ ⊤ :=
  vAdd_eq_top.not.trans not_or

theorem vAdd_lt_top [LT G] [LT P] : g +ᵥ p < ⊤ ↔ g < ⊤ ∧ p < ⊤ := by
  simp_rw [WithTop.lt_top_iff_ne_top, vAdd_ne_top]

/-!
theorem vAdd_eq_coe : ∀ {g : WithTop G} {p : WithTop P} {q : P},
    g +ᵥ p = q ↔ ∃ (g' : G) (p' : P), ↑g' = g ∧ ↑p' = p ∧ g' +ᵥ p' = q
  | ⊤, p, q => by simp
  | some g, ⊤, q => by simp
  | some g, some p, q => by
      simp only [exists_and_left]
-/

theorem vAdd_coe_eq_top_iff {p : P} : g +ᵥ (p : WithTop P) = ⊤ ↔ g = ⊤ := by simp

theorem coe_vAdd_eq_top_iff {g : G} : (g : WithTop G) +ᵥ p = ⊤ ↔ p = ⊤ := by simp

instance [LE G] [LE P] [IsOrderedVAdd G P] :
    IsOrderedVAdd (WithTop G) (WithTop P) where
  vadd_le_vadd_left := fun p p' hpp' g => by
    match g, p, p' with
    | ⊤, _, _ => simp
    | (g : G), _, ⊤ => simp
    | (g : G), ⊤, (p' : P) => exact (not_top_le_coe p' hpp').elim
    | (g : G), (p : P), (p' : P) =>
      simp_rw [← WithTop.coe_vAdd, WithTop.coe_le_coe] at *
      exact IsOrderedVAdd.vadd_le_vadd_left p p' hpp' g
  vadd_le_vadd_right := fun g g' hgg' p => by
    match g, g', p with
    | _, _, ⊤ => simp
    | _, ⊤, (p : P) => simp
    | ⊤, (g' : G), _ => exact (not_top_le_coe g' hgg').elim
    | (g : G), (g' : G), (p : P) =>
      simp_rw [← WithTop.coe_vAdd, WithTop.coe_le_coe] at *
      exact IsOrderedVAdd.vadd_le_vadd_right g g' hgg' p

end WithTop
