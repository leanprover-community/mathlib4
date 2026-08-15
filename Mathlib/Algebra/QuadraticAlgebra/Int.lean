/-
Copyright (c) 2026 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.Algebra.QuadraticAlgebra.Discr
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Data.Rat.Lemmas

/-!
# Quadratic algebras over `ℤ`

For `a b : ℤ`, `QuadraticAlgebra ℤ a b` is an order in `QuadraticAlgebra ℚ a b`.

## Main results

* `QuadraticAlgebra ℚ a b` is the localization of `QuadraticAlgebra ℤ a b` at the nonzero
  integers and its fraction ring.
* `QuadraticAlgebra.Int.isDomain_iff`: `QuadraticAlgebra ℤ a b` is an integral domain iff
  `discr a b` is not a square.
-/

@[expose] public section

namespace QuadraticAlgebra

open Algebra

namespace Int

variable {a b : ℤ}

noncomputable instance : Algebra (QuadraticAlgebra ℤ a b) (QuadraticAlgebra ℚ a b) :=
  (baseChange ℚ a b).toRingHom.toAlgebra

instance : IsScalarTower ℤ (QuadraticAlgebra ℤ a b) (QuadraticAlgebra ℚ a b) :=
  .of_algHom (baseChange ℚ a b)

theorem algebraMap_eq (x : QuadraticAlgebra ℤ a b) :
    algebraMap (QuadraticAlgebra ℤ a b) (QuadraticAlgebra ℚ a b) x = baseChange ℚ a b x := rfl

@[simp]
theorem algebraMap_re_eq (x : QuadraticAlgebra ℤ a b) :
    (algebraMap (QuadraticAlgebra ℤ a b) (QuadraticAlgebra ℚ a b) x).re = x.re := by
  simp [algebraMap_eq, re_baseChange_apply ℚ]

@[simp]
theorem algebraMap_im_eq (x : QuadraticAlgebra ℤ a b) :
    (algebraMap (QuadraticAlgebra ℤ a b) (QuadraticAlgebra ℚ a b) x).im = x.im := by
  simp [algebraMap_eq, im_baseChange_apply ℚ]

instance : FaithfulSMul (QuadraticAlgebra ℤ a b) (QuadraticAlgebra ℚ a b) :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr <| baseChange_injective ℚ _ _

/-- The discriminant commutes with the coercion `ℤ → ℚ`. -/
theorem discr_intCast :
    discr (a : ℚ) (b : ℚ) = discr a b := by
  simpa using discr_algebraMap (S := ℚ) a b

open scoped nonZeroDivisors

theorem exists_nat_smul_mem (z : QuadraticAlgebra ℚ a b) :
    ∃ n : ℕ, 0 < n ∧ n • z ∈ Set.range (baseChange ℚ a b) := by
  obtain ⟨n, hn, x, y, hx, hy⟩ : ∃ n : ℕ, 0 < n ∧ ∃ x y : ℤ, n * z.re = x ∧ n * z.im = y :=
    ⟨z.re.den * z.im.den, by positivity, z.im.den * z.re.num, z.re.den * z.im.num,
      by push_cast; grind [← Rat.mul_den_eq_num]⟩
  refine ⟨n, hn, x • 1 + y • ω, ?_⟩
  ext <;> simp [re_baseChange_apply ℚ, im_baseChange_apply ℚ, hx, hy]

/-- `QuadraticAlgebra ℚ a b` is the localization of the order `QuadraticAlgebra ℤ a b` at the
nonzero integers. This is not `IsFractionRing` in general: `QuadraticAlgebra ℤ a b` need not be a
domain (see `isDomain_iff`). -/
noncomputable instance :
    IsLocalization (algebraMapSubmonoid (QuadraticAlgebra ℤ a b) ℤ⁰)
      (QuadraticAlgebra ℚ a b) := by
  refine ⟨fun ⟨y, ⟨x, hx, hy⟩⟩ ↦ ?_, fun x ↦ ?_, fun h ↦ ⟨1, by simpa using h⟩⟩
  · dsimp only
    rw [← hy, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply ℤ ℚ]
    exact IsUnit.map _ <| by simpa [isUnit_iff_ne_zero] using hx
  · obtain ⟨n, hn, ⟨w, hw⟩⟩ := exists_nat_smul_mem x
    exact ⟨⟨w, n, ⟨n, by simpa using hn.ne', rfl⟩⟩, by simp [algebraMap_eq, hw, mul_comm]⟩

instance : IsFractionRing (QuadraticAlgebra ℤ a b) (QuadraticAlgebra ℚ a b) := by
  refine IsLocalization.of_le (algebraMapSubmonoid (QuadraticAlgebra ℤ a b) ℤ⁰) _ ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact norm_mem_nonZeroDivisors_iff.mp <| by simpa using hx
  · intro x hx
    rwa [isUnit_iff_norm_isUnit, isUnit_iff_ne_zero, algebraMap_eq, norm_baseChange ℚ a b,
      eq_intCast, Int.cast_ne_zero, ← mem_nonZeroDivisors_iff_ne_zero, norm_mem_nonZeroDivisors_iff]

instance [h : Fact (¬ IsSquare (discr a b))] : Fact (¬ IsSquare (discr (a : ℚ) (b : ℚ))) := by
  rwa [discr_intCast, Rat.isSquare_intCast_iff]

instance [Fact (¬ IsSquare (discr a b))] : IsDomain (QuadraticAlgebra ℤ a b) :=
  .of_faithfulSMul _ (QuadraticAlgebra ℚ a b)

theorem isDomain_iff :
    IsDomain (QuadraticAlgebra ℤ a b) ↔ ¬ IsSquare (discr a b) := by
  simp [IsFractionRing.isDomain_iff_isField (K := QuadraticAlgebra ℚ a b),
    isField_iff_not_isSquare_discr, discr_intCast]

end Int

end QuadraticAlgebra
