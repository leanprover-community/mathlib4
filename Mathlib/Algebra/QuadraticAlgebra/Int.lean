/-
Copyright (c) 2026 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.Algebra.QuadraticAlgebra.Discriminant
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Quadratic algebras over `ℤ`

For `a b : ℤ`, `QuadraticAlgebra ℤ a b` is an order in `QuadraticAlgebra ℚ a b`.

## Main results

* `QuadraticAlgebra ℚ a b` is the localization of `QuadraticAlgebra ℤ a b` at the nonzero
  integers and its fraction ring.
* `QuadraticAlgebra.Int.isDomain_iff`: `QuadraticAlgebra ℤ a b` is an integral domain iff
  `discr a b` is not a square.
-/

public section

namespace QuadraticAlgebra

open Algebra

namespace Int

variable {a b : ℤ}

noncomputable instance : Algebra (QuadraticAlgebra ℤ a b) (QuadraticAlgebra ℚ a b) :=
  QuadraticAlgebra.algebra ℚ a b

instance : IsScalarTower ℤ (QuadraticAlgebra ℤ a b) (QuadraticAlgebra ℚ a b) :=
  .of_algHom (baseChange ℚ a b)

@[simp]
theorem re_algebraMap (x : QuadraticAlgebra ℤ a b) :
    (algebraMap (QuadraticAlgebra ℤ a b) (QuadraticAlgebra ℚ a b) x).re = x.re := rfl

@[simp]
theorem im_algebraMap (x : QuadraticAlgebra ℤ a b) :
    (algebraMap (QuadraticAlgebra ℤ a b) (QuadraticAlgebra ℚ a b) x).im = x.im := rfl

@[simp]
theorem norm_algebraMap_eq (x : QuadraticAlgebra ℤ a b) :
    norm (algebraMap (QuadraticAlgebra ℤ a b) (QuadraticAlgebra ℚ a b) x) = norm x :=
  norm_mapRingHom (algebraMap ℤ ℚ) a b x

@[simp]
theorem trace_algebraMap_eq (x : QuadraticAlgebra ℤ a b) :
    trace (algebraMap (QuadraticAlgebra ℤ a b) (QuadraticAlgebra ℚ a b) x) = trace x :=
  trace_mapRingHom (algebraMap ℤ ℚ) a b x

instance : FaithfulSMul (QuadraticAlgebra ℤ a b) (QuadraticAlgebra ℚ a b) :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr <| baseChange_injective ℚ _ _

open scoped nonZeroDivisors

theorem exists_nat_smul_mem (z : QuadraticAlgebra ℚ a b) :
    ∃ n : ℕ, 0 < n ∧
      n • z ∈ Set.range (algebraMap (QuadraticAlgebra ℤ a b) (QuadraticAlgebra ℚ a b)) := by
  obtain ⟨n, hn, x, y, hx, hy⟩ : ∃ n : ℕ, 0 < n ∧ ∃ x y : ℤ, n * z.re = x ∧ n * z.im = y :=
    ⟨z.re.den * z.im.den, by positivity, z.im.den * z.re.num, z.re.den * z.im.num,
      by push_cast; grind [← Rat.mul_den_eq_num]⟩
  refine ⟨n, hn, x • 1 + y • ω, ?_⟩
  ext <;> simp [hx, hy]

-- TODO: generalize this instance: if `S` is the localization of `R` at `M`, then
-- `QuadraticAlgebra S a b` is the localization of `QuadraticAlgebra R a b` at the image of `M`.
/-- `QuadraticAlgebra ℚ a b` is the localization of the order `QuadraticAlgebra ℤ a b` at the
nonzero integers. -/
noncomputable instance :
    IsLocalization (algebraMapSubmonoid (QuadraticAlgebra ℤ a b) ℤ⁰)
      (QuadraticAlgebra ℚ a b) := by
  refine ⟨fun ⟨y, ⟨x, hx, hy⟩⟩ ↦ ?_, fun x ↦ ?_, fun h ↦ ⟨1, by simpa using h⟩⟩
  · dsimp only
    rw [← hy, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply ℤ ℚ]
    exact IsUnit.map _ <| by simpa [isUnit_iff_ne_zero] using hx
  · obtain ⟨n, hn, ⟨w, hw⟩⟩ := exists_nat_smul_mem x
    exact ⟨⟨w, n, ⟨n, by simpa using hn.ne', rfl⟩⟩, by simp [hw, mul_comm]⟩

instance : IsFractionRing (QuadraticAlgebra ℤ a b) (QuadraticAlgebra ℚ a b) := by
  refine IsLocalization.of_le (algebraMapSubmonoid (QuadraticAlgebra ℤ a b) ℤ⁰) _ ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact norm_mem_nonZeroDivisors_iff.mp <| by simpa using hx
  · intro x hx
    rwa [isUnit_iff_norm_isUnit, isUnit_iff_ne_zero, norm_algebraMap_eq, Int.cast_ne_zero,
      ← mem_nonZeroDivisors_iff_ne_zero, norm_mem_nonZeroDivisors_iff]

theorem isDomain_iff :
    IsDomain (QuadraticAlgebra ℤ a b) ↔ ¬ IsSquare (discr a b) := by
  simp [IsFractionRing.isDomain_iff_isField (K := QuadraticAlgebra ℚ a b),
    isField_iff_not_isSquare_discr, discr_intCast]

instance [Fact (¬ IsSquare (discr a b))] : IsDomain (QuadraticAlgebra ℤ a b) :=
  isDomain_iff.mpr Fact.out

end Int

end QuadraticAlgebra
