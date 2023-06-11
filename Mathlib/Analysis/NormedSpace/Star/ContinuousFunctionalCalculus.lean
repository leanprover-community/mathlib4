/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux

! This file was ported from Lean 3 source module analysis.normed_space.star.continuous_functional_calculus
! leanprover-community/mathlib commit 31c24aa72e7b3e5ed97a8412470e904f82b81004
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.NormedSpace.Star.GelfandDuality
import Mathbin.Topology.Algebra.StarSubalgebra

/-! # Continuous functional calculus

In this file we construct the `continuous_functional_calculus` for a normal element `a` of a
(unital) C⋆-algebra over `ℂ`. This is a star algebra equivalence
`C(spectrum ℂ a, ℂ) ≃⋆ₐ[ℂ] elemental_star_algebra ℂ a` which sends the (restriction of) the
identity map `continuous_map.id ℂ` to the (unique) preimage of `a` under the coercion of
`elemental_star_algebra ℂ a` to `A`.

Being a star algebra equivalence between C⋆-algebras, this map is continuous (even an isometry),
and by the Stone-Weierstrass theorem it is the unique star algebra equivalence which extends the
polynomial functional calculus (i.e., `polynomial.aeval`).

For any continuous function `f : spectrum ℂ a →  ℂ`, this makes it possible to define an element
`f a` (not valid notation) in the original algebra, which heuristically has the same eigenspaces as
`a` and acts on eigenvector of `a` for an eigenvalue `λ` as multiplication by `f λ`. This
description is perfectly accurate in finite dimension, but only heuristic in infinite dimension as
there might be no genuine eigenvector. In particular, when `f` is a polynomial `∑ cᵢ Xⁱ`, then
`f a` is `∑ cᵢ aⁱ`. Also, `id a = a`.

This file also includes a proof of the **spectral permanence** theorem for (unital) C⋆-algebras
(see `star_subalgebra.spectrum_eq`)

## Main definitions

* `continuous_functional_calculus : C(spectrum ℂ a, ℂ) ≃⋆ₐ[ℂ] elemental_star_algebra ℂ a`: this
  is the composition of the inverse of the `gelfand_star_transform` with the natural isomorphism
  induced by the homeomorphism `elemental_star_algebra.character_space_homeo`.
* `elemental_star_algebra.character_space_homeo :
  `character_space ℂ (elemental_star_algebra ℂ a) ≃ₜ spectrum ℂ a`: this homeomorphism is defined
  by evaluating a character `φ` at `a`, and noting that `φ a ∈ spectrum ℂ a` since `φ` is an
  algebra homomorphism. Moreover, this map is continuous and bijective and since the spaces involved
  are compact Hausdorff, it is a homeomorphism.

## Main statements

* `star_subalgebra.coe_is_unit`: for `x : S` in a C⋆-subalgebra `S` of `A`, then `↑x : A` is a unit
  if and only if `x` is a unit.
* `star_subalgebra.spectrum_eq`: **spectral_permanence** for `x : S`, where `S` is a C⋆-subalgebra
  of `A`, `spectrum ℂ x = spectrum ℂ (x : A)`.

## Notes

The result we have established here is the strongest possible, but it is likely not the version
which will be most useful in practice. Future work will include developing an appropriate API for
the continuous functional calculus (including one for real-valued functions with real argument that
applies to self-adjoint elements of the algebra). -/


open scoped Pointwise ENNReal NNReal ComplexOrder

open WeakDual WeakDual.characterSpace elementalStarAlgebra

variable {A : Type _} [NormedRing A] [NormedAlgebra ℂ A]

variable [StarRing A] [CstarRing A] [StarModule ℂ A]

instance {R A : Type _} [CommRing R] [StarRing R] [NormedRing A] [Algebra R A] [StarRing A]
    [ContinuousStar A] [StarModule R A] (a : A) [IsStarNormal a] :
    NormedCommRing (elementalStarAlgebra R a) :=
  { SubringClass.toNormedRing (elementalStarAlgebra R a) with mul_comm := mul_comm }

instance {R A : Type _} [NormedField R] [StarRing R] [NormedRing A] [NormedAlgebra R A] [StarRing A]
    [ContinuousStar A] [StarModule R A] (a : A) : NormedAlgebra R (elementalStarAlgebra R a) :=
  StarSubalgebra.toNormedAlgebra (elementalStarAlgebra R a)

instance {R A : Type _} [NormedField R] [StarRing R] [NormedRing A] [NormedAlgebra R A] [StarRing A]
    [ContinuousStar A] [StarModule R A] (a : A) : NormedSpace R (elementalStarAlgebra R a) :=
  NormedAlgebra.toNormedSpace _

-- without this instance type class search causes timeouts
noncomputable instance elementalStarAlgebra.Complex.normedAlgebra (a : A) :
    NormedAlgebra ℂ (elementalStarAlgebra ℂ a) :=
  inferInstance
#align elemental_star_algebra.complex.normed_algebra elementalStarAlgebra.Complex.normedAlgebra

variable [CompleteSpace A] (a : A) [IsStarNormal a] (S : StarSubalgebra ℂ A)

/-- This lemma is used in the proof of `star_subalgebra.is_unit_of_is_unit_of_is_star_normal`,
which in turn is the key to spectral permanence `star_subalgebra.spectrum_eq`, which is itself
necessary for the continuous functional calculus. Using the continuous functional calculus, this
lemma can be superseded by one that omits the `is_star_normal` hypothesis. -/
theorem spectrum_star_mul_self_of_isStarNormal :
    spectrum ℂ (star a * a) ⊆ Set.Icc (0 : ℂ) ‖star a * a‖ :=
  by
  -- this instance should be found automatically, but without providing it Lean goes on a wild
  -- goose chase when trying to apply `spectrum.gelfand_transform_eq`.
  letI := elementalStarAlgebra.Complex.normedAlgebra a
  rcases subsingleton_or_nontrivial A with ⟨⟩
  · simp only [spectrum.of_subsingleton, Set.empty_subset]
  · set a' : elementalStarAlgebra ℂ a := ⟨a, self_mem ℂ a⟩
    refine' (spectrum.subset_starSubalgebra (star a' * a')).trans _
    rw [← spectrum.gelfandTransform_eq (star a' * a'), ContinuousMap.spectrum_eq_range]
    rintro - ⟨φ, rfl⟩
    rw [gelfand_transform_apply_apply ℂ _ (star a' * a') φ, map_mul φ, map_star φ]
    rw [Complex.eq_coe_norm_of_nonneg (star_mul_self_nonneg _), ← map_star, ← map_mul]
    exact
      ⟨Complex.zero_le_real.2 (norm_nonneg _),
        Complex.real_le_real.2 (AlgHom.norm_apply_le_self φ (star a' * a'))⟩
#align spectrum_star_mul_self_of_is_star_normal spectrum_star_mul_self_of_isStarNormal

variable {a}

/-- This is the key lemma on the way to establishing spectral permanence for C⋆-algebras, which is
established in `star_subalgebra.spectrum_eq`. This lemma is superseded by
`star_subalgebra.coe_is_unit`, which does not require an `is_star_normal` hypothesis and holds for
any closed star subalgebra. -/
theorem elementalStarAlgebra.isUnit_of_isUnit_of_isStarNormal (h : IsUnit a) :
    IsUnit (⟨a, self_mem ℂ a⟩ : elementalStarAlgebra ℂ a) :=
  by
  /- Sketch of proof: Because `a` is normal, it suffices to prove that `star a * a` is invertible
    in `elemental_star_algebra ℂ a`. For this it suffices to prove that it is sufficiently close to a
    unit, namely `algebra_map ℂ _ ‖star a * a‖`, and in this case the required distance is
    `‖star a * a‖`. So one must show `‖star a * a - algebra_map ℂ _ ‖star a * a‖‖ < ‖star a * a‖`.
    Since `star a * a - algebra_map ℂ _ ‖star a * a‖` is selfadjoint, by a corollary of Gelfand's
    formula for the spectral radius (`is_self_adjoint.spectral_radius_eq_nnnorm`) its norm is the
    supremum of the norms of elements in its spectrum (we may use the spectrum in `A` here because
    the norm in `A` and the norm in the subalgebra coincide).
  
    By `spectrum_star_mul_self_of_is_star_normal`, the spectrum (in the algebra `A`) of `star a * a`
    is contained in the interval `[0, ‖star a * a‖]`, and since `a` (and hence `star a * a`) is
    invertible in `A`, we may omit `0` from this interval. Therefore, by basic spectral mapping
    properties, the spectrum (in the algebra `A`) of `star a * a - algebra_map ℂ _ ‖star a * a‖` is
    contained in `[0, ‖star a * a‖)`. The supremum of the (norms of) elements of the spectrum must be
    *strictly* less that `‖star a * a‖` because the spectrum is compact, which completes the proof. -/
  /- We may assume `A` is nontrivial. It suffices to show that `star a * a` is invertible in the
    commutative (because `a` is normal) ring `elemental_star_algebra ℂ a`. Indeed, by commutativity,
    if `star a * a` is invertible, then so is `a`. -/
  nontriviality A
  set a' : elementalStarAlgebra ℂ a := ⟨a, self_mem ℂ a⟩
  suffices : IsUnit (star a' * a'); exact (IsUnit.mul_iff.1 this).2
  replace h := (show Commute (star a) a from star_comm_self' a).isUnit_mul_iff.2 ⟨h.star, h⟩
  /- Since `a` is invertible, `‖star a * a‖ ≠ 0`, so `‖star a * a‖ • 1` is invertible in
    `elemental_star_algebra ℂ a`, and so it suffices to show that the distance between this unit and
    `star a * a` is less than `‖star a * a‖`. -/
  have h₁ : (‖star a * a‖ : ℂ) ≠ 0 := complex.of_real_ne_zero.mpr (norm_ne_zero_iff.mpr h.ne_zero)
  set u : Units (elementalStarAlgebra ℂ a) :=
    Units.map (algebraMap ℂ (elementalStarAlgebra ℂ a)).toMonoidHom (Units.mk0 _ h₁)
  refine' ⟨u.unit_of_nearby _ _, rfl⟩
  simp only [Complex.abs_ofReal, map_inv₀, Units.coe_map, Units.val_inv_eq_inv_val,
    RingHom.coe_monoidHom, RingHom.toMonoidHom_eq_coe, Units.val_mk0, Units.coe_map_inv,
    norm_algebraMap', inv_inv, Complex.norm_eq_abs, abs_norm, Subtype.val_eq_coe, coe_coe]
  /- Since `a` is invertible, by `spectrum_star_mul_self_of_is_star_normal`, the spectrum (in `A`)
    of `star a * a` is contained in the half-open interval `(0, ‖star a * a‖]`. Therefore, by basic
    spectral mapping properties, the spectrum of `‖star a * a‖ • 1 - star a * a` is contained in
    `[0, ‖star a * a‖)`. -/
  have h₂ : ∀ z ∈ spectrum ℂ (algebraMap ℂ A ‖star a * a‖ - star a * a), ‖z‖₊ < ‖star a * a‖₊ :=
    by
    intro z hz
    rw [← spectrum.singleton_sub_eq, Set.singleton_sub] at hz 
    have h₃ : z ∈ Set.Icc (0 : ℂ) ‖star a * a‖ :=
      by
      replace hz := Set.image_subset _ (spectrum_star_mul_self_of_isStarNormal a) hz
      rwa [Set.image_const_sub_Icc, sub_self, sub_zero] at hz 
    refine' lt_of_le_of_ne (Complex.real_le_real.1 <| Complex.eq_coe_norm_of_nonneg h₃.1 ▸ h₃.2) _
    · intro hz'
      replace hz' := congr_arg (fun x : ℝ≥0 => ((x : ℝ) : ℂ)) hz'
      simp only [coe_nnnorm] at hz' 
      rw [← Complex.eq_coe_norm_of_nonneg h₃.1] at hz' 
      obtain ⟨w, hw₁, hw₂⟩ := hz
      refine' (spectrum.zero_not_mem_iff ℂ).mpr h _
      rw [hz', sub_eq_self] at hw₂ 
      rwa [hw₂] at hw₁ 
  /- The norm of `‖star a * a‖ • 1 - star a * a` in the subalgebra and in `A` coincide. In `A`,
    because this element is selfadjoint, by `is_self_adjoint.spectral_radius_eq_nnnorm`, its norm is
    the supremum of the norms of the elements of the spectrum, which is strictly less than
    `‖star a * a‖` by `h₂` and because the spectrum is compact. -/
  exact
    ENNReal.coe_lt_coe.1
      (calc
        (‖star a' * a' - algebraMap ℂ _ ‖star a * a‖‖₊ : ℝ≥0∞) =
            ‖algebraMap ℂ A ‖star a * a‖ - star a * a‖₊ :=
          by rw [← nnnorm_neg, neg_sub]; rfl
        _ = spectralRadius ℂ (algebraMap ℂ A ‖star a * a‖ - star a * a) :=
          by
          refine' (IsSelfAdjoint.spectralRadius_eq_nnnorm _).symm
          rw [IsSelfAdjoint, star_sub, star_mul, star_star, ← algebraMap_star_comm, IsROrC.star_def,
            IsROrC.conj_ofReal]
        _ < ‖star a * a‖₊ := spectrum.spectralRadius_lt_of_forall_lt _ h₂)
#align elemental_star_algebra.is_unit_of_is_unit_of_is_star_normal elementalStarAlgebra.isUnit_of_isUnit_of_isStarNormal

/-- For `x : A` which is invertible in `A`, the inverse lies in any unital C⋆-subalgebra `S`
containing `x`. -/
theorem StarSubalgebra.isUnit_coe_inv_mem {S : StarSubalgebra ℂ A} (hS : IsClosed (S : Set A))
    {x : A} (h : IsUnit x) (hxS : x ∈ S) : ↑h.Unit⁻¹ ∈ S :=
  by
  have hx := h.star.mul h
  suffices this : (↑hx.unit⁻¹ : A) ∈ S
  · rw [← one_mul (↑h.unit⁻¹ : A), ← hx.unit.inv_mul, mul_assoc, IsUnit.unit_spec, mul_assoc,
      h.mul_coe_inv, mul_one]
    exact mul_mem this (star_mem hxS)
  refine' le_of_is_closed_of_mem ℂ hS (mul_mem (star_mem hxS) hxS) _
  haveI := (IsSelfAdjoint.star_mul_self x).IsStarNormal
  have hx' := elementalStarAlgebra.isUnit_of_isUnit_of_isStarNormal hx
  convert (↑hx'.unit⁻¹ : elementalStarAlgebra ℂ (star x * x)).Prop using 1
  exact left_inv_eq_right_inv hx.unit.inv_mul (congr_arg coe hx'.unit.mul_inv)
#align star_subalgebra.is_unit_coe_inv_mem StarSubalgebra.isUnit_coe_inv_mem

/-- For a unital C⋆-subalgebra `S` of `A` and `x : S`, if `↑x : A` is invertible in `A`, then
`x` is invertible in `S`. -/
theorem StarSubalgebra.coe_isUnit {S : StarSubalgebra ℂ A} (hS : IsClosed (S : Set A)) {x : S} :
    IsUnit (x : A) ↔ IsUnit x :=
  by
  refine'
    ⟨fun hx => ⟨⟨x, ⟨(↑hx.Unit⁻¹ : A), StarSubalgebra.isUnit_coe_inv_mem hS hx x.prop⟩, _, _⟩, rfl⟩,
      fun hx => hx.map S.subtype⟩
  exacts [Subtype.coe_injective hx.mul_coe_inv, Subtype.coe_injective hx.coe_inv_mul]
#align star_subalgebra.coe_is_unit StarSubalgebra.coe_isUnit

theorem StarSubalgebra.mem_spectrum_iff {S : StarSubalgebra ℂ A} (hS : IsClosed (S : Set A)) {x : S}
    {z : ℂ} : z ∈ spectrum ℂ x ↔ z ∈ spectrum ℂ (x : A) :=
  not_iff_not.2 (StarSubalgebra.coe_isUnit hS).symm
#align star_subalgebra.mem_spectrum_iff StarSubalgebra.mem_spectrum_iff

/-- **Spectral permanence.** The spectrum of an element is invariant of the (closed)
`star_subalgebra` in which it is contained. -/
theorem StarSubalgebra.spectrum_eq {S : StarSubalgebra ℂ A} (hS : IsClosed (S : Set A)) (x : S) :
    spectrum ℂ x = spectrum ℂ (x : A) :=
  Set.ext fun z => StarSubalgebra.mem_spectrum_iff hS
#align star_subalgebra.spectrum_eq StarSubalgebra.spectrum_eq

variable (a)

/-- The natural map from `character_space ℂ (elemental_star_algebra ℂ x)` to `spectrum ℂ x` given
by evaluating `φ` at `x`. This is essentially just evaluation of the `gelfand_transform` of `x`,
but because we want something in `spectrum ℂ x`, as opposed to
`spectrum ℂ ⟨x, elemental_star_algebra.self_mem ℂ x⟩` there is slightly more work to do. -/
@[simps]
noncomputable def elementalStarAlgebra.characterSpaceToSpectrum (x : A)
    (φ : characterSpace ℂ (elementalStarAlgebra ℂ x)) : spectrum ℂ x
    where
  val := φ ⟨x, self_mem ℂ x⟩
  property := by
    simpa only [StarSubalgebra.spectrum_eq (elementalStarAlgebra.isClosed ℂ x)
        ⟨x, self_mem ℂ x⟩] using
      AlgHom.apply_mem_spectrum φ ⟨x, self_mem ℂ x⟩
#align elemental_star_algebra.character_space_to_spectrum elementalStarAlgebra.characterSpaceToSpectrum

theorem elementalStarAlgebra.continuous_characterSpaceToSpectrum (x : A) :
    Continuous (elementalStarAlgebra.characterSpaceToSpectrum x) :=
  continuous_induced_rng.2
    (map_continuous <| gelfandTransform ℂ (elementalStarAlgebra ℂ x) ⟨x, self_mem ℂ x⟩)
#align elemental_star_algebra.continuous_character_space_to_spectrum elementalStarAlgebra.continuous_characterSpaceToSpectrum

theorem elementalStarAlgebra.bijective_characterSpaceToSpectrum :
    Function.Bijective (elementalStarAlgebra.characterSpaceToSpectrum a) :=
  by
  refine'
    ⟨fun φ ψ h =>
      star_alg_hom_class_ext ℂ (map_continuous φ) (map_continuous ψ)
        (by
          simpa only [elementalStarAlgebra.characterSpaceToSpectrum, Subtype.mk_eq_mk,
            ContinuousMap.coe_mk] using h),
      _⟩
  rintro ⟨z, hz⟩
  have hz' :=
    (StarSubalgebra.spectrum_eq (elementalStarAlgebra.isClosed ℂ a) ⟨a, self_mem ℂ a⟩).symm.subst hz
  rw [character_space.mem_spectrum_iff_exists] at hz' 
  obtain ⟨φ, rfl⟩ := hz'
  exact ⟨φ, rfl⟩
#align elemental_star_algebra.bijective_character_space_to_spectrum elementalStarAlgebra.bijective_characterSpaceToSpectrum

/-- The homeomorphism between the character space of the unital C⋆-subalgebra generated by a
single normal element `a : A` and `spectrum ℂ a`. -/
noncomputable def elementalStarAlgebra.characterSpaceHomeo :
    characterSpace ℂ (elementalStarAlgebra ℂ a) ≃ₜ spectrum ℂ a :=
  @Continuous.homeoOfEquivCompactToT2 _ _ _ _ _ _
    (Equiv.ofBijective (elementalStarAlgebra.characterSpaceToSpectrum a)
      (elementalStarAlgebra.bijective_characterSpaceToSpectrum a))
    (elementalStarAlgebra.continuous_characterSpaceToSpectrum a)
#align elemental_star_algebra.character_space_homeo elementalStarAlgebra.characterSpaceHomeo

/-- **Continuous functional calculus.** Given a normal element `a : A` of a unital C⋆-algebra,
the continuous functional calculus is a `star_alg_equiv` from the complex-valued continuous
functions on the spectrum of `a` to the unital C⋆-subalgebra generated by `a`. Moreover, this
equivalence identifies `(continuous_map.id ℂ).restrict (spectrum ℂ a))` with `a`; see
`continuous_functional_calculus_map_id`. As such it extends the polynomial functional calculus. -/
noncomputable def continuousFunctionalCalculus :
    C(spectrum ℂ a, ℂ) ≃⋆ₐ[ℂ] elementalStarAlgebra ℂ a :=
  ((elementalStarAlgebra.characterSpaceHomeo a).compStarAlgEquiv' ℂ ℂ).trans
    (gelfandStarTransform (elementalStarAlgebra ℂ a)).symm
#align continuous_functional_calculus continuousFunctionalCalculus

theorem continuousFunctionalCalculus_map_id :
    continuousFunctionalCalculus a ((ContinuousMap.id ℂ).restrict (spectrum ℂ a)) =
      ⟨a, self_mem ℂ a⟩ :=
  StarAlgEquiv.symm_apply_apply _ _
#align continuous_functional_calculus_map_id continuousFunctionalCalculus_map_id

