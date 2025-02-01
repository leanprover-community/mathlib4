/-
Copyright (c) 2025 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.Algebra.Order.AddTorsor
import Mathlib.Order.WithBot

/-!
# Ordered scalar multiplication and vector addition with top
This file has some lemmas for extending ordered scalar multiplication and vector addition to allow
top elements.

## Instances
 * SMul (WithTop G) (WithTop P)
 * VAdd (WithTop G) (WithTop P)
 * IsOrderedSMul (WithTop G) (WithTop P)
 * IsOrderedVAdd (WithTop G) (WithTop P)

-/

open Function

variable {G P : Type*}

namespace WithTop

variable {g : WithTop G} {p : WithTop P}

@[to_additive]
instance [_root_.SMul G P] : SMul (WithTop G) (WithTop P) :=
  ⟨Option.map₂ (· • ·)⟩

@[to_additive] -- global simpNF says simping this runs afoul of WithTop.coe_nsmul
lemma coe_SMul [SMul G P] (g : G) (p : P) :
    ↑(g • p) = (g : WithTop G) • (p : WithTop P) :=
  rfl

@[to_additive (attr := simp)]
lemma top_SMul [SMul G P] : (⊤ : WithTop G) • p = ⊤ :=
  rfl

@[to_additive (attr := simp)]
lemma smul_top [SMul G P] : g • (⊤ : WithTop P) = ⊤ := by cases g <;> rfl

@[to_additive (attr := simp)]
lemma smul_eq_top [SMul G P] : g • p = ⊤ ↔ g = ⊤ ∨ p = ⊤ := by
  match g, p with
  | ⊤, _ => simp
  | _, ⊤ => simp
  | (g : G), (p : P) =>
    simp only [← coe_SMul, coe_ne_top, or_self, iff_false, ne_eq]

@[to_additive]
lemma smul_ne_top [SMul G P] : g • p ≠ ⊤ ↔ g ≠ ⊤ ∧ p ≠ ⊤ :=
  smul_eq_top.not.trans not_or

@[to_additive]
lemma smul_lt_top [LT G] [LT P] [SMul G P] : g • p < ⊤ ↔ g < ⊤ ∧ p < ⊤ := by
  simp_rw [WithTop.lt_top_iff_ne_top, smul_ne_top]

@[to_additive]
lemma smul_coe_eq_top_iff [SMul G P] {p : P} : g • (p : WithTop P) = ⊤ ↔ g = ⊤ := by simp

@[to_additive]
lemma coe_smul_eq_top_iff [SMul G P] {g : G} : (g : WithTop G) • p = ⊤ ↔ p = ⊤ := by simp

@[to_additive]
instance [LE G] [LE P] [SMul G P] [IsOrderedSMul G P] :
    IsOrderedSMul (WithTop G) (WithTop P) where
  smul_le_smul_left := fun p p' hpp' g => by
    match g, p, p' with
    | ⊤, _, _ => simp
    | (g : G), _, ⊤ => simp
    | (g : G), ⊤, (p' : P) => exact (not_top_le_coe p' hpp').elim
    | (g : G), (p : P), (p' : P) =>
      simp_rw [← WithTop.coe_SMul, WithTop.coe_le_coe] at *
      exact IsOrderedSMul.smul_le_smul_left p p' hpp' g
  smul_le_smul_right := fun g g' hgg' p => by
    match g, g', p with
    | _, _, ⊤ => simp
    | _, ⊤, (p : P) => simp
    | ⊤, (g' : G), _ => exact (not_top_le_coe g' hgg').elim
    | (g : G), (g' : G), (p : P) =>
      simp_rw [← WithTop.coe_SMul, WithTop.coe_le_coe] at *
      exact IsOrderedSMul.smul_le_smul_right g g' hgg' p

end WithTop
