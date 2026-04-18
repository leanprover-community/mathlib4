/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
public import Mathlib.Analysis.CStarAlgebra.GelfandDuality
public import Mathlib.Analysis.CStarAlgebra.Unitization
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic

/-! # Continuous functional calculus

In this file we construct the `continuousFunctionalCalculus` for a normal element `a` of a
(unital) C⋆-algebra over `ℂ`. This is a star algebra equivalence
`C(spectrum ℂ a, ℂ) ≃⋆ₐ[ℂ] elemental ℂ a` which sends the (restriction of) the
identity map `ContinuousMap.id ℂ` to the (unique) preimage of `a` under the coercion of
`elemental ℂ a` to `A`.

Being a star algebra equivalence between C⋆-algebras, this map is continuous (even an isometry),
and by the Stone-Weierstrass theorem it is the unique star algebra equivalence which extends the
polynomial functional calculus (i.e., `Polynomial.aeval`).

For any continuous function `f : spectrum ℂ a → ℂ`, this makes it possible to define an element
`f a` (not valid notation) in the original algebra, which heuristically has the same eigenspaces as
`a` and acts on eigenvector of `a` for an eigenvalue `λ` as multiplication by `f λ`. This
description is perfectly accurate in finite dimension, but only heuristic in infinite dimension as
there might be no genuine eigenvector. In particular, when `f` is a polynomial `∑ cᵢ Xⁱ`, then
`f a` is `∑ cᵢ aⁱ`. Also, `id a = a`.

The result we have established here is the strongest possible, but it is not the version which is
most useful in practice. The generic API for the continuous functional calculus can be found in
`Analysis.CStarAlgebra.ContinuousFunctionalCalculus` in the `Unital` and `NonUnital` files. The
relevant instances on C⋆-algebra can be found in the `Instances` file.

## Main definitions

* `continuousFunctionalCalculus : C(spectrum ℂ a, ℂ) ≃⋆ₐ[ℂ] elemental ℂ a`: this
  is the composition of the inverse of the `gelfandStarTransform` with the natural isomorphism
  induced by the homeomorphism `elemental.characterSpaceHomeo`.
* `elemental.characterSpaceHomeo` :
  `characterSpace ℂ (elemental ℂ a) ≃ₜ spectrum ℂ a`: this homeomorphism is defined
  by evaluating a character `φ` at `a`, and noting that `φ a ∈ spectrum ℂ a` since `φ` is an
  algebra homomorphism. Moreover, this map is continuous and bijective and since the spaces involved
  are compact Hausdorff, it is a homeomorphism.
* `IsStarNormal.instContinuousFunctionalCalculus`: the continuous functional calculus for normal
  elements in a unital C⋆-algebra over `ℂ`.
* `CStarAlgebra.instNonnegSpectrumClass`: In a unital C⋆-algebra over `ℂ` which is also a
  `StarOrderedRing`, the spectrum of a nonnegative element is nonnegative.

-/

@[expose] public section


open scoped Pointwise ENNReal NNReal ComplexOrder CStarAlgebra

open WeakDual WeakDual.CharacterSpace

variable {A : Type*}

namespace StarAlgebra.elemental

variable [CStarAlgebra A]

instance {R A : Type*} [CommRing R] [StarRing R] [NormedRing A] [Algebra R A] [StarRing A]
    [ContinuousStar A] [StarModule R A] (a : A) [IsStarNormal a] :
    NormedCommRing (elemental R a) :=
  { SubringClass.toNormedRing (elemental R a) with
    mul_comm := mul_comm }

noncomputable instance (a : A) [IsStarNormal a] : CommCStarAlgebra (elemental ℂ a) where

variable (a : A) [IsStarNormal a]

set_option backward.isDefEq.respectTransparency false in
/-- The natural map from `characterSpace ℂ (elemental ℂ x)` to `spectrum ℂ x` given
by evaluating `φ` at `x`. This is essentially just evaluation of the `gelfandTransform` of `x`,
but because we want something in `spectrum ℂ x`, as opposed to
`spectrum ℂ ⟨x, elemental.self_mem ℂ x⟩` there is slightly more work to do. -/
@[simps]
noncomputable def characterSpaceToSpectrum (x : A)
    (φ : characterSpace ℂ (elemental ℂ x)) : spectrum ℂ x where
  val := φ ⟨x, self_mem ℂ x⟩
  property := by
    simpa only [StarSubalgebra.spectrum_eq (hS := isClosed ℂ x)
      (a := ⟨x, self_mem ℂ x⟩)] using AlgHom.apply_mem_spectrum φ ⟨x, self_mem ℂ x⟩

theorem continuous_characterSpaceToSpectrum (x : A) :
    Continuous (characterSpaceToSpectrum x) :=
  continuous_induced_rng.2
    (map_continuous <| gelfandTransform ℂ (elemental ℂ x) ⟨x, self_mem ℂ x⟩)

set_option backward.isDefEq.respectTransparency false in
theorem bijective_characterSpaceToSpectrum :
    Function.Bijective (characterSpaceToSpectrum a) := by
  refine ⟨fun φ ψ h => starAlgHomClass_ext ℂ ?_ ?_ ?_, ?_⟩
  · exact (map_continuous φ)
  · exact (map_continuous ψ)
  · simpa only [characterSpaceToSpectrum, Subtype.mk_eq_mk,
      ContinuousMap.coe_mk] using h
  · rintro ⟨z, hz⟩
    have hz' := (StarSubalgebra.spectrum_eq (hS := isClosed ℂ a)
      (a := ⟨a, self_mem ℂ a⟩) ▸ hz)
    rw [CharacterSpace.mem_spectrum_iff_exists] at hz'
    obtain ⟨φ, rfl⟩ := hz'
    exact ⟨φ, rfl⟩

set_option backward.isDefEq.respectTransparency false in
/-- The homeomorphism between the character space of the unital C⋆-subalgebra generated by a
single normal element `a : A` and `spectrum ℂ a`. -/
noncomputable def characterSpaceHomeo :
    characterSpace ℂ (elemental ℂ a) ≃ₜ spectrum ℂ a :=
  @Continuous.homeoOfEquivCompactToT2 _ _ _ _ _ _
    (Equiv.ofBijective (characterSpaceToSpectrum a)
      (bijective_characterSpaceToSpectrum a))
    (continuous_characterSpaceToSpectrum a)

end StarAlgebra.elemental

open StarAlgebra elemental


/-- **Continuous functional calculus.** Given a normal element `a : A` of a unital C⋆-algebra,
the continuous functional calculus is a `StarAlgEquiv` from the complex-valued continuous
functions on the spectrum of `a` to the unital C⋆-subalgebra generated by `a`. Moreover, this
equivalence identifies `(ContinuousMap.id ℂ).restrict (spectrum ℂ a))` with `a`; see
`continuousFunctionalCalculus_map_id`. As such it extends the polynomial functional calculus. -/
noncomputable def continuousFunctionalCalculus [CStarAlgebra A] (a : A) [IsStarNormal a] :
    C(spectrum ℂ a, ℂ) ≃⋆ₐ[ℂ] elemental ℂ a :=
  ((characterSpaceHomeo a).compStarAlgEquiv' ℂ ℂ).trans
    (gelfandStarTransform (elemental ℂ a)).symm

theorem continuousFunctionalCalculus_map_id [CStarAlgebra A] (a : A) [IsStarNormal a] :
    continuousFunctionalCalculus a ((ContinuousMap.id ℂ).restrict (spectrum ℂ a)) =
      ⟨a, self_mem ℂ a⟩ :=
  (gelfandStarTransform (elemental ℂ a)).symm_apply_apply _

/-!
### Continuous functional calculus for normal elements
-/

local notation "σₙ" => quasispectrum

section Normal

section Unital

variable [CStarAlgebra A]

theorem IsStarNormal.instContinuousFunctionalCalculus :
    ContinuousFunctionalCalculus ℂ A IsStarNormal where
  predicate_zero := .zero
  spectrum_nonempty a _ := spectrum.nonempty a
  exists_cfc_of_predicate a ha := by
    have : Isometry ((StarAlgebra.elemental ℂ a).subtype.comp <| continuousFunctionalCalculus a :
        C(spectrum ℂ a, ℂ) →⋆ₐ[ℂ] A) :=
      isometry_subtype_coe.comp <| StarAlgEquiv.isometry (continuousFunctionalCalculus a)
    refine ⟨_, this.continuous, this.injective, ?hom_id, ?hom_map_spectrum, ?predicate_hom⟩
    case hom_id => exact congr_arg Subtype.val <| continuousFunctionalCalculus_map_id a
    case hom_map_spectrum =>
      intro f
      simp only [StarAlgHom.comp_apply, StarAlgHom.coe_coe, StarSubalgebra.coe_subtype]
      rw [← StarSubalgebra.spectrum_eq (hS := StarAlgebra.elemental.isClosed ℂ a),
        AlgEquiv.spectrum_eq (continuousFunctionalCalculus a), ContinuousMap.spectrum_eq_range]
    case predicate_hom => exact fun f ↦ ⟨by rw [← map_star]; exact Commute.all (star f) f |>.map _⟩

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

lemma cfcHom_eq_of_isStarNormal (a : A) [ha : IsStarNormal a] :
    cfcHom ha = (StarAlgebra.elemental ℂ a).subtype.comp (continuousFunctionalCalculus a) := by
  refine cfcHom_eq_of_continuous_of_map_id ha _ ?_ ?_
  · exact continuous_subtype_val.comp <|
      (StarAlgEquiv.isometry (continuousFunctionalCalculus a)).continuous
  · simp [continuousFunctionalCalculus_map_id a]

instance IsStarNormal.instIsometricContinuousFunctionalCalculus :
    IsometricContinuousFunctionalCalculus ℂ A IsStarNormal where
  isometric a ha := by
    rw [cfcHom_eq_of_isStarNormal]
    exact isometry_subtype_coe.comp <| StarAlgEquiv.isometry (continuousFunctionalCalculus a)

set_option backward.isDefEq.respectTransparency false in
instance IsSelfAdjoint.instIsometricContinuousFunctionalCalculus :
    IsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint :=
  SpectrumRestricts.isometric_cfc Complex.reCLM Complex.isometry_ofReal (.zero _)
    fun _ ↦ isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts

end Unital

section NonUnital

variable [NonUnitalCStarAlgebra A]

open Unitization

theorem IsStarNormal.instNonUnitalContinuousFunctionalCalculus :
    NonUnitalClosedEmbeddingContinuousFunctionalCalculus ℂ A IsStarNormal :=
  RCLike.nonUnitalContinuousFunctionalCalculusIsClosedEmbedding Unitization.isStarNormal_inr

attribute [local instance] IsStarNormal.instNonUnitalContinuousFunctionalCalculus

open scoped CStarAlgebra in
lemma inr_comp_cfcₙHom_eq_cfcₙAux (a : A) [ha : IsStarNormal a] :
    (inrNonUnitalStarAlgHom ℂ A).comp (cfcₙHom ha) = cfcₙAux (isStarNormal_inr (R := ℂ)) a ha :=
  inrNonUnitalStarAlgHom_comp_cfcₙHom_eq_cfcₙAux isStarNormal_inr a ha

open ContinuousMapZero in
instance IsStarNormal.instNonUnitalIsometricContinuousFunctionalCalculus :
    NonUnitalIsometricContinuousFunctionalCalculus ℂ A IsStarNormal where
  isometric a ha := by
    refine AddMonoidHomClass.isometry_of_norm _ fun f ↦ ?_
    rw [← norm_inr (𝕜 := ℂ), ← inrNonUnitalStarAlgHom_apply, ← NonUnitalStarAlgHom.comp_apply,
      inr_comp_cfcₙHom_eq_cfcₙAux a, cfcₙAux]
    simp only [NonUnitalStarAlgHom.comp_assoc, NonUnitalStarAlgHom.comp_apply,
      toContinuousMapHom_apply, NonUnitalStarAlgHom.coe_coe]
    rw [norm_cfcHom (a : Unitization ℂ A), StarAlgEquiv.norm_map]
    rfl

set_option backward.isDefEq.respectTransparency false in
instance IsSelfAdjoint.instNonUnitalIsometricContinuousFunctionalCalculus :
    NonUnitalIsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint :=
  QuasispectrumRestricts.isometric_cfc Complex.reCLM Complex.isometry_ofReal (.zero _)
    fun _ ↦ isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts

end NonUnital

end Normal

/-!
### The spectrum of a nonnegative element is nonnegative
-/

section SpectrumRestricts

open NNReal ENNReal

variable [CStarAlgebra A]

set_option backward.isDefEq.respectTransparency false in
lemma SpectrumRestricts.nnreal_iff_nnnorm {a : A} {t : ℝ≥0} (ha : IsSelfAdjoint a) (ht : ‖a‖₊ ≤ t) :
    SpectrumRestricts a ContinuousMap.realToNNReal ↔ ‖algebraMap ℝ A t - a‖₊ ≤ t := by
  have : IsSelfAdjoint (algebraMap ℝ A t - a) := IsSelfAdjoint.algebraMap A (.all (t : ℝ)) |>.sub ha
  rw [← ENNReal.coe_le_coe, ← IsSelfAdjoint.spectralRadius_eq_nnnorm,
    ← SpectrumRestricts.spectralRadius_eq (f := Complex.reCLM)] at ht ⊢
  · exact SpectrumRestricts.nnreal_iff_spectralRadius_le ht
  all_goals
    try apply IsSelfAdjoint.spectrumRestricts
    assumption

lemma SpectrumRestricts.nnreal_add {a b : A} (ha₁ : IsSelfAdjoint a)
    (hb₁ : IsSelfAdjoint b) (ha₂ : SpectrumRestricts a ContinuousMap.realToNNReal)
    (hb₂ : SpectrumRestricts b ContinuousMap.realToNNReal) :
    SpectrumRestricts (a + b) ContinuousMap.realToNNReal := by
  rw [SpectrumRestricts.nnreal_iff_nnnorm (ha₁.add hb₁) (nnnorm_add_le a b), NNReal.coe_add,
    map_add, add_sub_add_comm]
  refine nnnorm_add_le _ _ |>.trans ?_
  gcongr
  all_goals rw [← SpectrumRestricts.nnreal_iff_nnnorm] <;> first | rfl | assumption

lemma IsSelfAdjoint.sq_spectrumRestricts {a : A} (ha : IsSelfAdjoint a) :
    SpectrumRestricts (a ^ 2) ContinuousMap.realToNNReal := by
  rw [SpectrumRestricts.nnreal_iff, ← cfc_id (R := ℝ) a, ← cfc_pow .., cfc_map_spectrum ..]
  rintro - ⟨x, -, rfl⟩
  exact sq_nonneg x

open ComplexStarModule

lemma SpectrumRestricts.eq_zero_of_neg {a : A} (ha : IsSelfAdjoint a)
    (ha₁ : SpectrumRestricts a ContinuousMap.realToNNReal)
    (ha₂ : SpectrumRestricts (-a) ContinuousMap.realToNNReal) :
    a = 0 := by
  rw [SpectrumRestricts.nnreal_iff] at ha₁ ha₂
  apply CFC.eq_zero_of_spectrum_subset_zero (R := ℝ) a
  rw [Set.subset_singleton_iff]
  simp only [← spectrum.neg_eq, Set.mem_neg] at ha₂
  peel ha₁ with x hx _
  linarith [ha₂ (-x) ((neg_neg x).symm ▸ hx)]

lemma SpectrumRestricts.smul_of_nonneg {A : Type*} [Ring A] [Algebra ℝ A] {a : A}
    (ha : SpectrumRestricts a ContinuousMap.realToNNReal) {r : ℝ} (hr : 0 ≤ r) :
    SpectrumRestricts (r • a) ContinuousMap.realToNNReal := by
  rw [SpectrumRestricts.nnreal_iff] at ha ⊢
  nontriviality A
  intro x hx
  by_cases hr' : r = 0
  · simp only [hr', zero_smul, spectrum.zero_eq, Set.mem_singleton_iff] at hx ⊢
    exact hx.symm.le
  · lift r to ℝˣ using IsUnit.mk0 r hr'
    rw [← Units.smul_def, spectrum.unit_smul_eq_smul, Set.mem_smul_set_iff_inv_smul_mem] at hx
    refine le_of_smul_le_smul_left ?_ (inv_pos.mpr <| lt_of_le_of_ne hr <| ne_comm.mpr hr')
    simpa [Units.smul_def] using ha _ hx

/-- The `ℝ`-spectrum of an element of the form `star b * b` in a C⋆-algebra is nonnegative.

This is the key result used to establish `CStarAlgebra.instNonnegSpectrumClass`. -/
lemma spectrum_star_mul_self_nonneg {b : A} : ∀ x ∈ spectrum ℝ (star b * b), 0 ≤ x := by
  -- for convenience we'll work with `a := star b * b`, which is selfadjoint.
  set a := star b * b with a_def
  have ha : IsSelfAdjoint a := by simp [a_def]
  -- the key element to consider is `c := b * a⁻`, which satisfies `- (star c * c) = a⁻ ^ 3`.
  set c := b * a⁻
  have h_eq_negPart_a : -(star c * c) = a⁻ ^ 3 := calc
    -(star c * c) = - a⁻ * a * a⁻ := by
      simp only [star_mul, c, mul_assoc, ← mul_assoc (star b), ← a_def, CFC.negPart_def,
        neg_mul, IsSelfAdjoint.cfcₙ (f := (·⁻)).star_eq]
    _ = - a⁻ * (a⁺ - a⁻) * a⁻ :=
      congr(- a⁻ * $(CFC.posPart_sub_negPart a ha) * a⁻).symm
    _ = a⁻ ^ 3 := by simp [mul_sub, pow_succ]
  -- the spectrum of `- (star c * c) = a⁻ ^ 3` is nonnegative, since the function on the right
  -- is nonnegative on the spectrum of `a`.
  have h_c_spec₀ : SpectrumRestricts (-(star c * c)) (ContinuousMap.realToNNReal ·) := by
    simp only [SpectrumRestricts.nnreal_iff, h_eq_negPart_a, CFC.negPart_def]
    rw [cfcₙ_eq_cfc (hf0 := by simp), ← cfc_pow (ha := ha) .., cfc_map_spectrum (ha := ha) ..]
    rintro - ⟨x, -, rfl⟩
    positivity
  -- the spectrum of `c * star c` is nonnegative, since squares of selfadjoint elements have
  -- nonnegative spectrum, and `c * star c = 2 • (ℜ c ^ 2 + ℑ c ^ 2) + (- (star c * c))`,
  -- and selfadjoint elements with nonnegative spectrum are closed under addition.
  have h_c_spec₁ : SpectrumRestricts (c * star c) ContinuousMap.realToNNReal := by
    rw [eq_sub_iff_add_eq'.mpr <| star_mul_self_add_self_mul_star c, sub_eq_add_neg, ← sq, ← sq]
    refine SpectrumRestricts.nnreal_add ?_ ?_ ?_ h_c_spec₀
    · exact .smul (star_trivial _) <| ((ℜ c).prop.pow 2).add ((ℑ c).prop.pow 2)
    · exact .neg <| .star_mul_self c
    · rw [← Nat.cast_smul_eq_nsmul ℝ]
      refine (ℜ c).2.sq_spectrumRestricts.nnreal_add ((ℜ c).2.pow 2) ((ℑ c).2.pow 2)
        (ℑ c).2.sq_spectrumRestricts |>.smul_of_nonneg <| by simp
  -- therefore `- (star c * c) = 0` and so `a⁻ ^ 3 = 0`. By properties of the continuous functional
  -- calculus, `fun x ↦ x⁻ ^ 3` is zero on the spectrum of `a`, `0 ≤ x` for `x ∈ spectrum ℝ a`.
  rw [h_c_spec₁.mul_comm.eq_zero_of_neg (.star_mul_self c) h_c_spec₀, neg_zero, CFC.negPart_def,
    cfcₙ_eq_cfc (hf0 := by simp), ← cfc_pow _ _ (ha := ha), ← cfc_zero a (R := ℝ)] at h_eq_negPart_a
  have h_eqOn := eqOn_of_cfc_eq_cfc (ha := ha) h_eq_negPart_a
  exact fun x hx ↦ negPart_eq_zero.mp <| eq_zero_of_pow_eq_zero (h_eqOn hx).symm

set_option backward.isDefEq.respectTransparency false in
lemma IsSelfAdjoint.coe_mem_spectrum_complex {A : Type*} [TopologicalSpace A] [Ring A]
    [StarRing A] [Algebra ℂ A] [ContinuousFunctionalCalculus ℂ A IsStarNormal]
    {a : A} {x : ℝ} (ha : IsSelfAdjoint a := by cfc_tac) :
    (x : ℂ) ∈ spectrum ℂ a ↔ x ∈ spectrum ℝ a := by
  simp [← ha.spectrumRestricts.algebraMap_image]

end SpectrumRestricts

section NonnegSpectrumClass

variable [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

instance CStarAlgebra.instNonnegSpectrumClass : NonnegSpectrumClass ℝ A :=
  .of_spectrum_nonneg fun a ha ↦ by
    rw [StarOrderedRing.nonneg_iff] at ha
    induction ha using AddSubmonoid.closure_induction with
    | mem x hx =>
      obtain ⟨b, rfl⟩ := hx
      exact spectrum_star_mul_self_nonneg
    | zero =>
      nontriviality A
      simp
    | add x y x_mem y_mem hx hy =>
      rw [← SpectrumRestricts.nnreal_iff] at hx hy ⊢
      rw [← StarOrderedRing.nonneg_iff] at x_mem y_mem
      exact hx.nnreal_add (.of_nonneg x_mem) (.of_nonneg y_mem) hy

set_option backward.isDefEq.respectTransparency false in
open ComplexOrder in
instance CStarAlgebra.instNonnegSpectrumClassComplexUnital : NonnegSpectrumClass ℂ A where
  quasispectrum_nonneg_of_nonneg a ha x := by
    rw [mem_quasispectrum_iff]
    refine (Or.elim · ge_of_eq fun hx ↦ ?_)
    obtain ⟨y, hy, rfl⟩ := (IsSelfAdjoint.of_nonneg ha).spectrumRestricts.algebraMap_image ▸ hx
    simpa using spectrum_nonneg_of_nonneg ha hy

end NonnegSpectrumClass

section SpectralOrder

variable [NonUnitalCStarAlgebra A]

open scoped CStarAlgebra

set_option backward.isDefEq.respectTransparency false in
variable (A) in
/-- The partial order on a C⋆-algebra defined by `x ≤ y` if and only if `y - x` is
selfadjoint and has nonnegative spectrum.

This is not declared as an instance because one may already have a partial order with better
definitional properties. However, it can be useful to invoke this as an instance in proofs. -/
@[reducible]
def CStarAlgebra.spectralOrder : PartialOrder A where
  le x y := IsSelfAdjoint (y - x) ∧ QuasispectrumRestricts (y - x) ContinuousMap.realToNNReal
  le_refl := by
    simp only [sub_self, IsSelfAdjoint.zero, true_and, forall_const]
    rw [quasispectrumRestricts_iff_spectrumRestricts_inr' ℂ, SpectrumRestricts.nnreal_iff]
    nontriviality A
    simp
  le_antisymm x y hxy hyx := by
    rw [← Unitization.isSelfAdjoint_inr (R := ℂ),
      quasispectrumRestricts_iff_spectrumRestricts_inr' ℂ, Unitization.inr_sub ℂ] at hxy hyx
    rw [← sub_eq_zero]
    apply Unitization.inr_injective (R := ℂ)
    rw [Unitization.inr_zero, Unitization.inr_sub]
    exact hyx.2.eq_zero_of_neg hyx.1 (neg_sub (x : A⁺¹) (y : A⁺¹) ▸ hxy.2)
  le_trans x y z hxy hyz := by
    simp +singlePass only [← Unitization.isSelfAdjoint_inr (R := ℂ),
      quasispectrumRestricts_iff_spectrumRestricts_inr' ℂ] at hxy hyz ⊢
    exact ⟨by simpa using hyz.1.add hxy.1, by simpa using hyz.2.nnreal_add hyz.1 hxy.1 hxy.2⟩

set_option backward.isDefEq.respectTransparency false in
variable (A) in
/-- The `CStarAlgebra.spectralOrder` on a C⋆-algebra is a `StarOrderedRing`. -/
lemma CStarAlgebra.spectralOrderedRing : @StarOrderedRing A _ (CStarAlgebra.spectralOrder A) _ :=
  let _ := CStarAlgebra.spectralOrder A
  { le_iff := by
      intro x y
      constructor
      · intro h
        obtain ⟨s, hs₁, _, hs₂⟩ :=
          CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts h.1 h.2
        refine ⟨s * s, ?_, by rwa [eq_sub_iff_add_eq', eq_comm] at hs₂⟩
        exact AddSubmonoid.subset_closure ⟨s, by simp [hs₁.star_eq]⟩
      · rintro ⟨p, hp, rfl⟩
        simp +instances only [spectralOrder, add_sub_cancel_left]
        induction hp using AddSubmonoid.closure_induction with
        | mem x hx =>
          obtain ⟨s, rfl⟩ := hx
          refine ⟨IsSelfAdjoint.star_mul_self s, ?_⟩
          rw [quasispectrumRestricts_iff_spectrumRestricts_inr' ℂ,
            SpectrumRestricts.nnreal_iff, Unitization.inr_mul, Unitization.inr_star]
          exact spectrum_star_mul_self_nonneg
        | zero =>
          rw [quasispectrumRestricts_iff_spectrumRestricts_inr' ℂ, SpectrumRestricts.nnreal_iff]
          simp
        | add x y _ _ hx hy =>
          simp +singlePass only [← Unitization.isSelfAdjoint_inr (R := ℂ),
            quasispectrumRestricts_iff_spectrumRestricts_inr' ℂ] at hx hy ⊢
          rw [Unitization.inr_add]
          exact ⟨hx.1.add hy.1, hx.2.nnreal_add hx.1 hy.1 hy.2⟩ }

end SpectralOrder

section NonnegSpectrumClass

variable [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

set_option backward.isDefEq.respectTransparency false in
open scoped CStarAlgebra in
instance CStarAlgebra.instNonnegSpectrumClass' : NonnegSpectrumClass ℝ A where
  quasispectrum_nonneg_of_nonneg a ha := by
    rw [Unitization.quasispectrum_eq_spectrum_inr' _ ℂ]
    -- should this actually be an instance on the `Unitization`? (probably scoped)
    let _ := CStarAlgebra.spectralOrder A⁺¹
    have := CStarAlgebra.spectralOrderedRing A⁺¹
    apply spectrum_nonneg_of_nonneg
    rw [StarOrderedRing.nonneg_iff] at ha ⊢
    have := AddSubmonoid.mem_map_of_mem (Unitization.inrNonUnitalStarAlgHom ℂ A) ha
    rw [AddMonoidHom.map_mclosure, ← Set.range_comp] at this
    apply AddSubmonoid.closure_mono ?_ this
    rintro _ ⟨s, rfl⟩
    exact ⟨s, by simp⟩

end NonnegSpectrumClass

section cfc_inr

open CStarAlgebra

variable [NonUnitalCStarAlgebra A]

open scoped NonUnitalContinuousFunctionalCalculus in
/-- This lemma requires a lot from type class synthesis, and so one should instead favor the bespoke
versions for `ℝ≥0`, `ℝ`, and `ℂ`. -/
lemma Unitization.cfcₙ_eq_cfc_inr {R : Type*} [Semifield R] [StarRing R] [MetricSpace R]
    [IsTopologicalSemiring R] [ContinuousStar R] [Module R A] [IsScalarTower R A A]
    [SMulCommClass R A A] [Algebra R ℂ] [IsScalarTower R ℂ A]
    {p : A → Prop} {p' : A⁺¹ → Prop} [NonUnitalContinuousFunctionalCalculus R A p]
    [ContinuousFunctionalCalculus R A⁺¹ p']
    [ContinuousMapZero.UniqueHom R (Unitization ℂ A)]
    (hp : ∀ {a : A}, p' (a : A⁺¹) ↔ p a) (a : A) (f : R → R) (hf₀ : f 0 = 0 := by cfc_zero_tac) :
    cfcₙ f a = cfc f (a : A⁺¹) := by
  by_cases h : ContinuousOn f (σₙ R a) ∧ p a
  · obtain ⟨hf, ha⟩ := h
    rw [← cfcₙ_eq_cfc (quasispectrum_inr_eq R ℂ a ▸ hf)]
    exact (inrNonUnitalStarAlgHom ℂ A).map_cfcₙ f a
  · obtain (hf | ha) := not_and_or.mp h
    · rw [cfcₙ_apply_of_not_continuousOn a hf, inr_zero,
        cfc_apply_of_not_continuousOn _ (quasispectrum_eq_spectrum_inr' R ℂ a ▸ hf)]
    · rw [cfcₙ_apply_of_not_predicate a ha, inr_zero,
        cfc_apply_of_not_predicate _ (not_iff_not.mpr hp |>.mpr ha)]

lemma Unitization.complex_cfcₙ_eq_cfc_inr (a : A) (f : ℂ → ℂ) (hf₀ : f 0 = 0 := by cfc_zero_tac) :
    cfcₙ f a = cfc f (a : A⁺¹) :=
  Unitization.cfcₙ_eq_cfc_inr isStarNormal_inr ..

set_option backward.isDefEq.respectTransparency false in
/-- note: the version for `ℝ≥0`, `Unitization.nnreal_cfcₙ_eq_cfc_inr`, can be found in
`Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Order.lean` -/
lemma Unitization.real_cfcₙ_eq_cfc_inr (a : A) (f : ℝ → ℝ) (hf₀ : f 0 = 0 := by cfc_zero_tac) :
    cfcₙ f a = cfc f (a : A⁺¹) :=
  Unitization.cfcₙ_eq_cfc_inr isSelfAdjoint_inr ..

end cfc_inr
