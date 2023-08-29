/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Analysis.NormedSpace.Star.GelfandDuality
import Mathlib.Topology.Algebra.StarSubalgebra

#align_import analysis.normed_space.star.continuous_functional_calculus from "leanprover-community/mathlib"@"31c24aa72e7b3e5ed97a8412470e904f82b81004"

/-! # Continuous functional calculus

In this file we construct the `continuousFunctionalCalculus` for a normal element `a` of a
(unital) C⋆-algebra over `ℂ`. This is a star algebra equivalence
`C(spectrum ℂ a, ℂ) ≃⋆ₐ[ℂ] elementalStarAlgebra ℂ a` which sends the (restriction of) the
identity map `ContinuousMap.id ℂ` to the (unique) preimage of `a` under the coercion of
`elementalStarAlgebra ℂ a` to `A`.

Being a star algebra equivalence between C⋆-algebras, this map is continuous (even an isometry),
and by the Stone-Weierstrass theorem it is the unique star algebra equivalence which extends the
polynomial functional calculus (i.e., `Polynomial.aeval`).

For any continuous function `f : spectrum ℂ a → ℂ`, this makes it possible to define an element
`f a` (not valid notation) in the original algebra, which heuristically has the same eigenspaces as
`a` and acts on eigenvector of `a` for an eigenvalue `λ` as multiplication by `f λ`. This
description is perfectly accurate in finite dimension, but only heuristic in infinite dimension as
there might be no genuine eigenvector. In particular, when `f` is a polynomial `∑ cᵢ Xⁱ`, then
`f a` is `∑ cᵢ aⁱ`. Also, `id a = a`.

This file also includes a proof of the **spectral permanence** theorem for (unital) C⋆-algebras
(see `StarSubalgebra.spectrum_eq`)

## Main definitions

* `continuousFunctionalCalculus : C(spectrum ℂ a, ℂ) ≃⋆ₐ[ℂ] elementalStarAlgebra ℂ a`: this
  is the composition of the inverse of the `gelfandStarTransform` with the natural isomorphism
  induced by the homeomorphism `elementalStarAlgebra.characterSpaceHomeo`.
* `elementalStarAlgebra.characterSpaceHomeo` :
  `characterSpace ℂ (elementalStarAlgebra ℂ a) ≃ₜ spectrum ℂ a`: this homeomorphism is defined
  by evaluating a character `φ` at `a`, and noting that `φ a ∈ spectrum ℂ a` since `φ` is an
  algebra homomorphism. Moreover, this map is continuous and bijective and since the spaces involved
  are compact Hausdorff, it is a homeomorphism.

## Main statements

* `StarSubalgebra.coe_isUnit`: for `x : S` in a C⋆-Subalgebra `S` of `A`, then `↑x : A` is a Unit
  if and only if `x` is a unit.
* `StarSubalgebra.spectrum_eq`: **spectral_permanence** for `x : S`, where `S` is a C⋆-Subalgebra
  of `A`, `spectrum ℂ x = spectrum ℂ (x : A)`.

## Notes

The result we have established here is the strongest possible, but it is likely not the version
which will be most useful in practice. Future work will include developing an appropriate API for
the continuous functional calculus (including one for real-valued functions with real argument that
applies to self-adjoint elements of the algebra). -/


open scoped Pointwise ENNReal NNReal ComplexOrder

open WeakDual WeakDual.CharacterSpace elementalStarAlgebra

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]

variable [StarRing A] [CstarRing A] [StarModule ℂ A]

instance {R A : Type*} [CommRing R] [StarRing R] [NormedRing A] [Algebra R A] [StarRing A]
    [ContinuousStar A] [StarModule R A] (a : A) [IsStarNormal a] :
    NormedCommRing (elementalStarAlgebra R a) :=
  { SubringClass.toNormedRing (elementalStarAlgebra R a) with
    mul_comm := mul_comm }

-- porting note: these hack instances no longer seem to be necessary
#noalign elemental_star_algebra.complex.normed_algebra

variable [CompleteSpace A] (a : A) [IsStarNormal a] (S : StarSubalgebra ℂ A)

/-- This lemma is used in the proof of `elementalStarAlgebra.isUnit_of_isUnit_of_isStarNormal`,
which in turn is the key to spectral permanence `StarSubalgebra.spectrum_eq`, which is itself
necessary for the continuous functional calculus. Using the continuous functional calculus, this
lemma can be superseded by one that omits the `IsStarNormal` hypothesis. -/
theorem spectrum_star_mul_self_of_isStarNormal :
    spectrum ℂ (star a * a) ⊆ Set.Icc (0 : ℂ) ‖star a * a‖ := by
  -- this instance should be found automatically, but without providing it Lean goes on a wild
  -- goose chase when trying to apply `spectrum.gelfandTransform_eq`.
  --letI := elementalStarAlgebra.Complex.normedAlgebra a
  rcases subsingleton_or_nontrivial A with ⟨⟩
  -- ⊢ spectrum ℂ (star a * a) ⊆ Set.Icc 0 ↑‖star a * a‖
  · simp only [spectrum.of_subsingleton, Set.empty_subset]
    -- 🎉 no goals
  · set a' : elementalStarAlgebra ℂ a := ⟨a, self_mem ℂ a⟩
    -- ⊢ spectrum ℂ (star a * a) ⊆ Set.Icc 0 ↑‖star a * a‖
    refine' (spectrum.subset_starSubalgebra (star a' * a')).trans _
    -- ⊢ spectrum ℂ (star a' * a') ⊆ Set.Icc 0 ↑‖star a * a‖
    rw [← spectrum.gelfandTransform_eq (star a' * a'), ContinuousMap.spectrum_eq_range]
    -- ⊢ Set.range ↑(↑(gelfandTransform ℂ { x // x ∈ elementalStarAlgebra ℂ a }) (sta …
    rintro - ⟨φ, rfl⟩
    -- ⊢ ↑(↑(gelfandTransform ℂ { x // x ∈ elementalStarAlgebra ℂ a }) (star a' * a') …
    rw [gelfandTransform_apply_apply ℂ _ (star a' * a') φ, map_mul φ, map_star φ]
    -- ⊢ star (↑φ a') * ↑φ a' ∈ Set.Icc 0 ↑‖star a * a‖
    rw [Complex.eq_coe_norm_of_nonneg (star_mul_self_nonneg _), ← map_star, ← map_mul]
    -- ⊢ ↑‖↑φ (star a' * a')‖ ∈ Set.Icc 0 ↑‖star a * a‖
    exact
      ⟨Complex.zero_le_real.2 (norm_nonneg _),
        Complex.real_le_real.2 (AlgHom.norm_apply_le_self φ (star a' * a'))⟩
#align spectrum_star_mul_self_of_is_star_normal spectrum_star_mul_self_of_isStarNormal

variable {a}

/-- This is the key lemma on the way to establishing spectral permanence for C⋆-algebras, which is
established in `StarSubalgebra.spectrum_eq`. This lemma is superseded by
`StarSubalgebra.coe_isUnit`, which does not require an `IsStarNormal` hypothesis and holds for
any closed star subalgebra. -/
theorem elementalStarAlgebra.isUnit_of_isUnit_of_isStarNormal (h : IsUnit a) :
    IsUnit (⟨a, self_mem ℂ a⟩ : elementalStarAlgebra ℂ a) := by
  /- Sketch of proof: Because `a` is normal, it suffices to prove that `star a * a` is invertible
    in `elementalStarAlgebra ℂ a`. For this it suffices to prove that it is sufficiently close to a
    unit, namely `algebraMap ℂ _ ‖star a * a‖`, and in this case the required distance is
    `‖star a * a‖`. So one must show `‖star a * a - algebraMap ℂ _ ‖star a * a‖‖ < ‖star a * a‖`.
    Since `star a * a - algebraMap ℂ _ ‖star a * a‖` is selfadjoint, by a corollary of Gelfand's
    formula for the spectral radius (`IsSelfAdjoint.spectralRadius_eq_nnnorm`) its norm is the
    supremum of the norms of elements in its spectrum (we may use the spectrum in `A` here because
    the norm in `A` and the norm in the subalgebra coincide).

    By `spectrum_star_mul_self_of_isStarNormal`, the spectrum (in the algebra `A`) of `star a * a`
    is contained in the interval `[0, ‖star a * a‖]`, and since `a` (and hence `star a * a`) is
    invertible in `A`, we may omit `0` from this interval. Therefore, by basic spectral mapping
    properties, the spectrum (in the algebra `A`) of `star a * a - algebraMap ℂ _ ‖star a * a‖` is
    contained in `[0, ‖star a * a‖)`. The supremum of the (norms of) elements of the spectrum must
    be *strictly* less that `‖star a * a‖` because the spectrum is compact, which completes the
    proof. -/
  /- We may assume `A` is nontrivial. It suffices to show that `star a * a` is invertible in the
    commutative (because `a` is normal) ring `elementalStarAlgebra ℂ a`. Indeed, by commutativity,
    if `star a * a` is invertible, then so is `a`. -/
  nontriviality A
  -- ⊢ IsUnit { val := a, property := (_ : a ∈ elementalStarAlgebra ℂ a) }
  set a' : elementalStarAlgebra ℂ a := ⟨a, self_mem ℂ a⟩
  -- ⊢ IsUnit a'
  suffices : IsUnit (star a' * a'); exact (IsUnit.mul_iff.1 this).2
  -- ⊢ IsUnit a'
                                    -- ⊢ IsUnit (star a' * a')
  replace h := (show Commute (star a) a from star_comm_self' a).isUnit_mul_iff.2 ⟨h.star, h⟩
  -- ⊢ IsUnit (star a' * a')
  /- Since `a` is invertible, `‖star a * a‖ ≠ 0`, so `‖star a * a‖ • 1` is invertible in
    `elementalStarAlgebra ℂ a`, and so it suffices to show that the distance between this unit and
    `star a * a` is less than `‖star a * a‖`. -/
  have h₁ : (‖star a * a‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr h.ne_zero)
  -- ⊢ IsUnit (star a' * a')
  set u : Units (elementalStarAlgebra ℂ a) :=
    Units.map (algebraMap ℂ (elementalStarAlgebra ℂ a)).toMonoidHom (Units.mk0 _ h₁)
  refine' ⟨u.ofNearby _ _, rfl⟩
  -- ⊢ ‖star a' * a' - ↑u‖ < ‖↑u⁻¹‖⁻¹
  simp only [Units.coe_map, Units.val_inv_eq_inv_val, RingHom.toMonoidHom_eq_coe, Units.val_mk0,
    Units.coe_map_inv, MonoidHom.coe_coe, norm_algebraMap', norm_inv, Complex.norm_eq_abs,
    Complex.abs_ofReal, abs_norm, inv_inv]
    --RingHom.coe_monoidHom,
    -- Complex.abs_ofReal, map_inv₀,
  --rw [norm_algebraMap', inv_inv, Complex.norm_eq_abs, abs_norm]I-
  /- Since `a` is invertible, by `spectrum_star_mul_self_of_isStarNormal`, the spectrum (in `A`)
    of `star a * a` is contained in the half-open interval `(0, ‖star a * a‖]`. Therefore, by basic
    spectral mapping properties, the spectrum of `‖star a * a‖ • 1 - star a * a` is contained in
    `[0, ‖star a * a‖)`. -/
  have h₂ : ∀ z ∈ spectrum ℂ (algebraMap ℂ A ‖star a * a‖ - star a * a), ‖z‖₊ < ‖star a * a‖₊ := by
    intro z hz
    rw [← spectrum.singleton_sub_eq, Set.singleton_sub] at hz
    have h₃ : z ∈ Set.Icc (0 : ℂ) ‖star a * a‖ := by
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
    because this element is selfadjoint, by `IsSelfAdjoint.spectralRadius_eq_nnnorm`, its norm is
    the supremum of the norms of the elements of the spectrum, which is strictly less than
    `‖star a * a‖` by `h₂` and because the spectrum is compact. -/
  exact ENNReal.coe_lt_coe.1
    (calc
      (‖star a' * a' - algebraMap ℂ _ ‖star a * a‖‖₊ : ℝ≥0∞) =
          ‖algebraMap ℂ A ‖star a * a‖ - star a * a‖₊ :=
        by rw [← nnnorm_neg, neg_sub]; rfl
      _ = spectralRadius ℂ (algebraMap ℂ A ‖star a * a‖ - star a * a) := by
        refine' (IsSelfAdjoint.spectralRadius_eq_nnnorm _).symm
        rw [IsSelfAdjoint, star_sub, star_mul, star_star, ← algebraMap_star_comm]
        congr!
        exact IsROrC.conj_ofReal _
      _ < ‖star a * a‖₊ := spectrum.spectralRadius_lt_of_forall_lt _ h₂)
#align elemental_star_algebra.is_unit_of_is_unit_of_is_star_normal elementalStarAlgebra.isUnit_of_isUnit_of_isStarNormal

/-- For `x : A` which is invertible in `A`, the inverse lies in any unital C⋆-subalgebra `S`
containing `x`. -/
theorem StarSubalgebra.isUnit_coe_inv_mem {S : StarSubalgebra ℂ A} (hS : IsClosed (S : Set A))
    {x : A} (h : IsUnit x) (hxS : x ∈ S) : ↑h.unit⁻¹ ∈ S := by
  have hx := h.star.mul h
  -- ⊢ ↑(IsUnit.unit h)⁻¹ ∈ S
  suffices this : (↑hx.unit⁻¹ : A) ∈ S
  -- ⊢ ↑(IsUnit.unit h)⁻¹ ∈ S
  · rw [← one_mul (↑h.unit⁻¹ : A), ← hx.unit.inv_mul, mul_assoc, IsUnit.unit_spec, mul_assoc,
      h.mul_val_inv, mul_one]
    exact mul_mem this (star_mem hxS)
    -- 🎉 no goals
  refine' le_of_isClosed_of_mem ℂ hS (mul_mem (star_mem hxS) hxS) _
  -- ⊢ ↑(IsUnit.unit hx)⁻¹ ∈ elementalStarAlgebra ℂ (star x * x)
  haveI := (IsSelfAdjoint.star_mul_self x).isStarNormal
  -- ⊢ ↑(IsUnit.unit hx)⁻¹ ∈ elementalStarAlgebra ℂ (star x * x)
  have hx' := elementalStarAlgebra.isUnit_of_isUnit_of_isStarNormal hx
  -- ⊢ ↑(IsUnit.unit hx)⁻¹ ∈ elementalStarAlgebra ℂ (star x * x)
  convert (↑hx'.unit⁻¹ : elementalStarAlgebra ℂ (star x * x)).prop using 1
  -- ⊢ ↑(IsUnit.unit hx)⁻¹ = ↑↑(IsUnit.unit hx')⁻¹
  refine left_inv_eq_right_inv hx.unit.inv_mul ?_
  -- ⊢ ↑(IsUnit.unit hx) * ↑↑(IsUnit.unit hx')⁻¹ = 1
  exact (congr_arg ((↑) : _ → A) hx'.unit.mul_inv)
  -- 🎉 no goals
#align star_subalgebra.is_unit_coe_inv_mem StarSubalgebra.isUnit_coe_inv_mem

/-- For a unital C⋆-subalgebra `S` of `A` and `x : S`, if `↑x : A` is invertible in `A`, then
`x` is invertible in `S`. -/
theorem StarSubalgebra.coe_isUnit {S : StarSubalgebra ℂ A} (hS : IsClosed (S : Set A)) {x : S} :
    IsUnit (x : A) ↔ IsUnit x := by
  refine'
    ⟨fun hx => ⟨⟨x, ⟨(↑hx.unit⁻¹ : A), StarSubalgebra.isUnit_coe_inv_mem hS hx x.prop⟩, _, _⟩, rfl⟩,
      fun hx => hx.map S.subtype⟩
  exacts [Subtype.coe_injective hx.mul_val_inv, Subtype.coe_injective hx.val_inv_mul]
  -- 🎉 no goals
#align star_subalgebra.coe_is_unit StarSubalgebra.coe_isUnit

theorem StarSubalgebra.mem_spectrum_iff {S : StarSubalgebra ℂ A} (hS : IsClosed (S : Set A)) {x : S}
    {z : ℂ} : z ∈ spectrum ℂ x ↔ z ∈ spectrum ℂ (x : A) :=
  not_iff_not.2 (StarSubalgebra.coe_isUnit hS).symm
#align star_subalgebra.mem_spectrum_iff StarSubalgebra.mem_spectrum_iff

/-- **Spectral permanence.** The spectrum of an element is invariant of the (closed)
`StarSubalgebra` in which it is contained. -/
theorem StarSubalgebra.spectrum_eq {S : StarSubalgebra ℂ A} (hS : IsClosed (S : Set A)) (x : S) :
    spectrum ℂ x = spectrum ℂ (x : A) :=
  Set.ext fun _z => StarSubalgebra.mem_spectrum_iff hS
#align star_subalgebra.spectrum_eq StarSubalgebra.spectrum_eq

variable (a)

/-- The natural map from `characterSpace ℂ (elementalStarAlgebra ℂ x)` to `spectrum ℂ x` given
by evaluating `φ` at `x`. This is essentially just evaluation of the `gelfandTransform` of `x`,
but because we want something in `spectrum ℂ x`, as opposed to
`spectrum ℂ ⟨x, elementalStarAlgebra.self_mem ℂ x⟩` there is slightly more work to do. -/
@[simps]
noncomputable def elementalStarAlgebra.characterSpaceToSpectrum (x : A)
    (φ : characterSpace ℂ (elementalStarAlgebra ℂ x)) : spectrum ℂ x where
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
    Function.Bijective (elementalStarAlgebra.characterSpaceToSpectrum a) := by
  refine' ⟨fun φ ψ h => starAlgHomClass_ext ℂ _ _ _, _⟩
  · exact (map_continuous φ)
    -- 🎉 no goals
  · exact (map_continuous ψ)
    -- 🎉 no goals
  · simpa only [elementalStarAlgebra.characterSpaceToSpectrum, Subtype.mk_eq_mk,
      ContinuousMap.coe_mk] using h
  · rintro ⟨z, hz⟩
    -- ⊢ ∃ a_1, characterSpaceToSpectrum a a_1 = { val := z, property := hz }
    have hz' := (StarSubalgebra.spectrum_eq (elementalStarAlgebra.isClosed ℂ a)
      ⟨a, self_mem ℂ a⟩).symm.subst hz
    rw [CharacterSpace.mem_spectrum_iff_exists] at hz'
    -- ⊢ ∃ a_1, characterSpaceToSpectrum a a_1 = { val := z, property := hz }
    obtain ⟨φ, rfl⟩ := hz'
    -- ⊢ ∃ a_1, characterSpaceToSpectrum a a_1 = { val := ↑φ { val := a, property :=  …
    exact ⟨φ, rfl⟩
    -- 🎉 no goals
#align elemental_star_algebra.bijective_character_space_to_spectrum elementalStarAlgebra.bijective_characterSpaceToSpectrum

-- porting note: it would be good to understand why and where Lean is having trouble here
set_option synthInstance.maxHeartbeats 40000 in
/-- The homeomorphism between the character space of the unital C⋆-subalgebra generated by a
single normal element `a : A` and `spectrum ℂ a`. -/
noncomputable def elementalStarAlgebra.characterSpaceHomeo :
    characterSpace ℂ (elementalStarAlgebra ℂ a) ≃ₜ spectrum ℂ a :=
  @Continuous.homeoOfEquivCompactToT2 _ _ _ _ _ _
    (Equiv.ofBijective (elementalStarAlgebra.characterSpaceToSpectrum a)
      (elementalStarAlgebra.bijective_characterSpaceToSpectrum a))
    (elementalStarAlgebra.continuous_characterSpaceToSpectrum a)
#align elemental_star_algebra.character_space_homeo elementalStarAlgebra.characterSpaceHomeo

-- porting note: it would be good to understand why and where Lean is having trouble here
set_option maxHeartbeats 350000 in
/-- **Continuous functional calculus.** Given a normal element `a : A` of a unital C⋆-algebra,
the continuous functional calculus is a `StarAlgEquiv` from the complex-valued continuous
functions on the spectrum of `a` to the unital C⋆-subalgebra generated by `a`. Moreover, this
equivalence identifies `(ContinuousMap.id ℂ).restrict (spectrum ℂ a))` with `a`; see
`continuousFunctionalCalculus_map_id`. As such it extends the polynomial functional calculus. -/
noncomputable def continuousFunctionalCalculus :
    C(spectrum ℂ a, ℂ) ≃⋆ₐ[ℂ] elementalStarAlgebra ℂ a :=
  ((elementalStarAlgebra.characterSpaceHomeo a).compStarAlgEquiv' ℂ ℂ).trans
    (gelfandStarTransform (elementalStarAlgebra ℂ a)).symm
#align continuous_functional_calculus continuousFunctionalCalculus

theorem continuousFunctionalCalculus_map_id :
    continuousFunctionalCalculus a ((ContinuousMap.id ℂ).restrict (spectrum ℂ a)) =
      ⟨a, self_mem ℂ a⟩ :=
  (gelfandStarTransform (elementalStarAlgebra ℂ a)).symm_apply_apply _
#align continuous_functional_calculus_map_id continuousFunctionalCalculus_map_id
