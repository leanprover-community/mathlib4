/-
Copyright (c) 2024 Daniel Weber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Weber
-/
import Mathlib.FieldTheory.PrimitiveElement

/-!
# Simple field extensions

We define a typeclass `SimpleExtension` for one field being a simple extension of another
(this is data because it contains which element was adjoined).

We also define `TranscendentalExtension F K`, and show that it implies that `K` is `F[X]`'s fraction
field.
-/

open Polynomial IntermediateField algebraMap

/--
A typeclass for K being a simple extension of F, F⟮k⟯ = K.
Note that this is data, and contains the value of `k`.
-/
class SimpleExtension (F K : Type*) [CommSemiring F] [Field K] [Algebra F K] where
  /-- The element of K which is adjoined to F. -/
  k : K
  /-- Every value in K is a fraction of two polynomials with coefficients in F, evaluated at k. -/
  is_adjoin' : ∀ (x : K), ∃ (r s : Polynomial F), x = (aeval k) r / (aeval k) s

/--
We can use `Field.exists_primitive_element` to noncomputably create a simple extension.
-/
noncomputable def SimpleExtesion_of_finite_seperable (F K : Type*) [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] [Algebra.IsSeparable F K] : SimpleExtension F K where
  k := (Field.exists_primitive_element F K).choose
  is_adjoin' x := by
    rw [← IntermediateField.mem_adjoin_simple_iff, (Field.exists_primitive_element F K).choose_spec]
    apply IntermediateField.mem_top

section CommSemiring

variable (F K : Type*) [CommSemiring F] [Field K] [Algebra F K] [se : SimpleExtension F K]

instance (priority := 100) toAlgebra : Algebra F[X] K := (aeval se.k).toAlgebra

lemma SimpleExtension.is_adjoin : ∀ (x : K), ∃ (r s : Polynomial F), x = r / s := se.is_adjoin'

lemma algebraMap_eq_aeval : algebraMap F[X] K = aeval (R := F) se.k := rfl

lemma SimpleExtension.X_eq_k : algebraMap F[X] K X = se.k := aeval_X _

end CommSemiring

section Field

variable (F K : Type*) [Field F] [Field K] [Algebra F K]
    [se : SimpleExtension F K]

variable (F K : Type*) [Field F] [Field K] [Algebra F K] [se : SimpleExtension F K]

lemma SimpleExtension.adjoin_eq_top : F⟮se.k⟯ = ⊤ := by
  ext x
  simp only [mem_adjoin_simple_iff, mem_top, iff_true]
  apply SimpleExtension.is_adjoin'

/--
If K is a finite extension of F then it's equivalent to adjoining to F a root of
`minpoly F k`.
-/
noncomputable def SimpleExtension.equivAdjoinRoot [FiniteDimensional F K] :
    AdjoinRoot (minpoly F se.k) ≃ₐ[F] K :=
  IntermediateField.adjoinRootEquivAdjoin F (IsAlgebraic.of_finite ..).isIntegral
  |>.trans <| IntermediateField.equivOfEq (SimpleExtension.adjoin_eq_top F K)
  |>.trans <| IntermediateField.topEquiv

lemma finiteDimensional_iff_isAlgebraic_gen : FiniteDimensional F K ↔ IsAlgebraic F se.k where
  mp h := IsAlgebraic.of_finite ..
  mpr h := by
    have := adjoin.finiteDimensional h.isIntegral
    rw [SimpleExtension.adjoin_eq_top] at this
    apply IntermediateField.topEquiv.toLinearEquiv.finiteDimensional

lemma gen_transcendental [t : Algebra.Transcendental F K] : Transcendental F se.k := fun h ↦
  have := (finiteDimensional_iff_isAlgebraic_gen F K).mpr h
  Algebra.transcendental_iff_not_isAlgebraic.mp t inferInstance

instance (priority := 100) toIsFractionRing [Algebra.Transcendental F K] :
    IsFractionRing F[X] K where
  map_units' := by
    simp only [isUnit_iff_ne_zero, ne_eq, Subtype.forall]
    intro a ha
    change (a : K) ≠ 0
    intro h
    absurd gen_transcendental F K
    exists a
    exact ⟨nonZeroDivisors.ne_zero ha, h⟩
  surj' z := by
    by_cases hz : z = 0
    · exists ⟨0, ⟨1, ?_⟩⟩
      intro
      simp only [mul_one, imp_self]
      simp [hz]
    obtain ⟨r, s, h⟩ := se.is_adjoin z
    have : (s : K) ≠ 0 := fun nh ↦ hz (div_zero (G₀ := K) _ ▸ (nh ▸ h))
    have s0 : s ≠ 0 := fun nh ↦ by rw [nh] at this; simp at this
    exists ⟨r, s, ?_⟩
    · intro _ h
      simp only [mul_eq_zero, s0, or_false] at h
      exact h
    rw [h]
    field_simp
  exists_of_eq {x y h} := by
    exists 1
    simp only [OneMemClass.coe_one, one_mul]
    by_contra! nh
    rw [algebraMap_eq_aeval, RingHom.coe_coe] at h
    exact gen_transcendental F K ⟨x - y, sub_ne_zero_of_ne nh, by simp [h]⟩

end Field
