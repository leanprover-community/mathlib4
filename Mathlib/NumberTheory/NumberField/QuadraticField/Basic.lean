/-
Copyright (c) 2026 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.Algebra.QuadraticAlgebra.Int
public import Mathlib.Algebra.QuadraticAlgebra.IsQuadraticExtension
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.QuadraticAlgebra

/-!
# Quadratic fields

A quadratic field is a number field of degree `2` over `ℚ`, that is, a field of characteristic
zero which is a quadratic extension of `ℚ` in the sense of `Algebra.IsQuadraticExtension`.

## Main results

* `NumberField.QuadraticField.isFundamentalDiscr_discr`: the discriminant of a quadratic field
  is a fundamental discriminant;
* `NumberField.QuadraticField.nonempty_algEquiv_quadraticAlgebra_discr`: every quadratic field
  is `ℚ(√(discr K))`;
* `NumberField.QuadraticField.nonempty_algEquiv_iff_discr_eq`: the discriminant is a complete
  invariant of quadratic fields.
-/

public section

open NumberField Int

open scoped QuadraticAlgebra

instance NumberField.of_isQuadraticExtension (K : Type*) [Field K] [CharZero K]
    [Algebra.IsQuadraticExtension ℚ K] : NumberField K where

namespace NumberField.QuadraticField

variable (K : Type*) [Field K] [CharZero K] [h : Algebra.IsQuadraticExtension ℚ K]

instance : Algebra.IsQuadraticExtension ℤ (𝓞 K) where
  finrank_eq_two' := by rw [RingOfIntegers.rank, h.finrank_eq_two]

variable {K}

/-- A ring isomorphism between the ring of integers of `K` and `QuadraticAlgebra ℤ a b` extends
to their fraction fields. -/
noncomputable def algEquivOfRingEquiv {a b : ℤ}
    (f : 𝓞 K ≃+* QuadraticAlgebra ℤ a b) :
    K ≃ₐ[ℚ] QuadraticAlgebra ℚ a b :=
  (IsFractionRing.ringEquivOfRingEquiv f).equivRatAlgEquiv _ _

section discr

/-- If the ring of integers of `K` is `QuadraticAlgebra ℤ a b`, the discriminant of `K` is the
discriminant of that quadratic algebra. -/
theorem discr_eq_quadraticAlgebra_discr {a b : ℤ}
    (f : 𝓞 K ≃+* QuadraticAlgebra ℤ a b) :
    discr K = QuadraticAlgebra.discr a b := by
  rw [← discr_eq_discr K ((QuadraticAlgebra.basis a b).map f.toIntAlgEquiv.symm),
    Module.Basis.coe_map, RingEquiv.symm_toIntAlgEquiv, AlgEquiv.coe_toLinearEquiv,
    ← Algebra.discr_eq_discr_of_algEquiv, ← Algebra.discr_quadraticAlgebra]
  rfl

variable (K)

/-- The discriminant of a quadratic field is a fundamental discriminant. -/
theorem isFundamentalDiscr_discr : Int.IsFundamentalDiscr (discr K) := by
  obtain ⟨a, b, ⟨f⟩⟩ :=
    Algebra.IsQuadraticExtension.exists_algEquiv_quadraticAlgebra (R := ℤ) (A := 𝓞 K)
  rw [discr_eq_quadraticAlgebra_discr f.toRingEquiv]
  exact QuadraticAlgebra.Int.isIntegrallyClosed_iff.mp <| IsIntegrallyClosed.of_equiv f.toRingEquiv

/-- The ring of integers of a quadratic field `K` is the quadratic algebra of discriminant
`discr K`, see `Int.IsFundamentalDiscr.discr_ediv_four_emod_four`. -/
theorem nonempty_algEquiv_ringOfIntegers :
    Nonempty (𝓞 K ≃ₐ[ℤ] QuadraticAlgebra ℤ (discr K / 4) (discr K % 4)) := by
  obtain ⟨a, b, ⟨f⟩⟩ :=
    Algebra.IsQuadraticExtension.exists_algEquiv_quadraticAlgebra (R := ℤ) (A := 𝓞 K)
  refine ⟨f.trans (Nonempty.some ?_)⟩
  rw [QuadraticAlgebra.nonempty_algEquiv_int_iff,
    (isFundamentalDiscr_discr K).discr_ediv_four_emod_four,
    discr_eq_quadraticAlgebra_discr f.toRingEquiv]

/-- Every quadratic field is `ℚ(√(discr K))`. -/
theorem nonempty_algEquiv_quadraticAlgebra_discr :
    Nonempty (K ≃ₐ[ℚ] QuadraticAlgebra ℚ (discr K : ℚ) 0) := by
  obtain ⟨a, b, ⟨f⟩⟩ :=
    Algebra.IsQuadraticExtension.exists_algEquiv_quadraticAlgebra (R := ℤ) (A := 𝓞 K)
  exact ⟨(algEquivOfRingEquiv f.toRingEquiv).trans <|
    (QuadraticAlgebra.algEquivDiscrZero (a : ℚ) (b : ℚ)).trans <|
      QuadraticAlgebra.equivOfEq (by rw [QuadraticAlgebra.Int.discr_intCast,
        discr_eq_quadraticAlgebra_discr f.toRingEquiv]) rfl⟩

/-- The discriminant of a quadratic field is not `1`. A more general version is the
Hermite-Minkowski theorem, see `NumberField.abs_discr_gt_two`. -/
theorem discr_ne_one : discr K ≠ 1 := by
  by_contra! h
  obtain ⟨a, b, ⟨f⟩⟩ :=
    Algebra.IsQuadraticExtension.exists_algEquiv_quadraticAlgebra (R := ℤ) (A := 𝓞 K)
  exact QuadraticAlgebra.Int.isDomain_iff.mp (f.symm.toMulEquiv.isDomain _)
    (discr_eq_quadraticAlgebra_discr f.toRingEquiv ▸ h ▸ IsSquare.one)

/-- `√(discr K)` lies in `K`. -/
theorem exists_sq_eq_discr : ∃ x : K, x ^ 2 = discr K := by
  let e := (nonempty_algEquiv_quadraticAlgebra_discr K).some
  exact ⟨e.symm ω, by simp [← map_pow, QuadraticAlgebra.omega_pow_two_eq_add]⟩

/-- The discriminant of a quadratic field is not a square. -/
theorem not_isSquare_discr : ¬ IsSquare (discr K) :=
  (Int.IsFundamentalDiscr.eq_one_of_isSquare (isFundamentalDiscr_discr K)).mt <| discr_ne_one K

/-- **Stickelberger's theorem**, for quadratic fields: the discriminant is congruent to
`0` or `1` modulo `4`. -/
theorem discr_emod_four : discr K % 4 = 0 ∨ discr K % 4 = 1 :=
  (isFundamentalDiscr_discr K).1

variable (F : Type*) [Field F] [CharZero F] [Algebra.IsQuadraticExtension ℚ F]

/-- The discriminant is a complete invariant of quadratic fields. -/
theorem nonempty_algEquiv_iff_discr_eq :
    Nonempty (K ≃ₐ[ℚ] F) ↔ discr K = discr F := by
  refine ⟨fun ⟨e⟩ ↦ discr_eq_discr_of_algEquiv K e, fun h ↦ ?_⟩
  obtain ⟨e₁⟩ := nonempty_algEquiv_ringOfIntegers K
  obtain ⟨e₂⟩ := nonempty_algEquiv_ringOfIntegers F
  exact ⟨(IsFractionRing.ringEquivOfRingEquiv
    ((h ▸ e₁).trans e₂.symm).toRingEquiv).equivRatAlgEquiv _ _⟩

end discr

end NumberField.QuadraticField
