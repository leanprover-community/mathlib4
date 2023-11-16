/-
Copyright (c) 2023 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# Bounds for values of Dirichlet characters

We consider Dirichtlet characters `χ` with values in a normed field `F`.

We show that `‖χ a‖ = 1` if `a` is a unit and `‖a‖ ≤ 1` in general.
-/

-- TODO: change to `{F : Type*}` when this is done in `DirichletCharacter.Basic`
variable {F : Type} [NormedField F] {n : ℕ} (χ : DirichletCharacter F n)

namespace DirichletCharacter

/-- The value at a unit of a Dirichlet character with target a normed field has norm `1`. -/
lemma unit_norm_eq_one (a : (ZMod n)ˣ) : ‖χ a‖ = 1 := by
  obtain ⟨e, he₀, he₁⟩ := ZMod.exists_pos_unit_pow_eq_one n
  refine (pow_eq_one_iff_of_nonneg (norm_nonneg _) he₀.ne').mp ?_
  rw [← norm_pow, ← map_pow, ← Units.val_pow_eq_pow_val, he₁ a, Units.val_one, map_one, norm_one]

/-- The values of a Dirichlet character with target a normed field have norm bounded by `1`. -/
lemma norm_le_one (a : ZMod n) : ‖χ a‖ ≤ 1 := by
  by_cases h : IsUnit a
  · exact (χ.unit_norm_eq_one h.unit).le
  · rw [χ.map_nonunit h, norm_zero]
    exact zero_le_one


end DirichletCharacter
