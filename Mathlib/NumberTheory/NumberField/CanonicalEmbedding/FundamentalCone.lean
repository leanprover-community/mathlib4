/-
Copyright (c) 2024 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic

/-!
# Fundamental Cone

Let `K` be a number field of signature `(r₁, r₂)`. We define an action of the units `(𝓞 K)ˣ` on
the mixed space `ℝ^r₁ × ℂ^r₂` via the `mixedEmbedding`.

## Main definitions and results

* `NumberField.mixedEmbedding.unitSMul`: the action of `(𝓞 K)ˣ` on the mixed space defined, for
`u : (𝓞 K)ˣ`, by multiplication component by component with `mixedEmbedding K u`.

## Tags

number field, canonical embedding, units
-/

variable (K : Type*) [Field K]

namespace NumberField.mixedEmbedding

open NumberField NumberField.InfinitePlace

noncomputable section UnitSMul

/-- The action of `(𝓞 K)ˣ` on the mixed space `ℝ^r₁ × ℂ^r₂` defined, for `u : (𝓞 K)ˣ`, by
multiplication component by component with `mixedEmbedding K u`. -/
@[simps]
instance unitSMul : SMul (𝓞 K)ˣ (mixedSpace K) where
  smul u x := mixedEmbedding K u * x

instance : MulAction (𝓞 K)ˣ (mixedSpace K) where
  one_smul := fun _ ↦ by simp_rw [unitSMul_smul, Units.coe_one, map_one, one_mul]
  mul_smul := fun _ _ _ ↦ by simp_rw [unitSMul_smul, Units.coe_mul, map_mul, mul_assoc]

instance : SMulZeroClass (𝓞 K)ˣ (mixedSpace K) where
  smul_zero := fun _ ↦ by simp_rw [unitSMul_smul, mul_zero]

variable {K}

theorem unit_smul_eq_zero (u : (𝓞 K)ˣ) (x : mixedSpace K) :
    u • x = 0 ↔ x = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, smul_zero]⟩
  contrapose! h
  obtain ⟨w, h⟩ := exists_normAtPlace_ne_zero_iff.mpr h
  refine exists_normAtPlace_ne_zero_iff.mp ⟨w, ?_⟩
  rw [unitSMul_smul, map_mul]
  exact mul_ne_zero (by simp) h

variable [NumberField K]

theorem unit_smul_eq_iff_mul_eq {x y : 𝓞 K} {u : (𝓞 K)ˣ} :
    u • mixedEmbedding K x = mixedEmbedding K y ↔ u * x = y := by
  rw [unitSMul_smul, ← map_mul, Function.Injective.eq_iff, ← RingOfIntegers.coe_eq_algebraMap,
    ← map_mul, ← RingOfIntegers.ext_iff]
  exact mixedEmbedding_injective K

theorem norm_unit_smul (u : (𝓞 K)ˣ) (x : mixedSpace K) :
    mixedEmbedding.norm (u • x) = mixedEmbedding.norm x := by
  rw [unitSMul_smul, map_mul, norm_unit, one_mul]

end UnitSMul

end NumberField.mixedEmbedding
