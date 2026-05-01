/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.CStarAlgebra.Unitization
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.Normed.Algebra.GelfandFormula
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Algebra.Star.StarAlgHom

/-! # Spectral properties in C⋆-algebras

In this file, we establish various properties related to the spectrum of elements in C⋆-algebras.
In particular, we show that the spectrum of a unitary element is contained in the unit circle in
`ℂ`, the spectrum of a selfadjoint element is real, the spectral radius of a selfadjoint element
or normal element is its norm, among others.

An essential feature of C⋆-algebras is **spectral permanence**. This is the property that the
spectrum of an element in a closed subalgebra is the same as the spectrum of the element in the
whole algebra. For Banach algebras more generally, and even for Banach ⋆-algebras, this fails.

A consequence of spectral permanence is that one may always enlarge the C⋆-algebra (via a unital
embedding) while preserving the spectrum of any element. In addition, it allows us to make sense of
the spectrum of elements in non-unital C⋆-algebras by considering them as elements in the
`Unitization` of the C⋆-algebra, or indeed *any* unital C⋆-algebra. Of course, one may do this
(that is, consider the spectrum of an element in a non-unital by embedding it in a unital algebra)
for any Banach algebra, but the downside in that setting is that embedding in different unital
algebras results in varying spectra.

In Mathlib, we don't *define* the spectrum of an element in a non-unital C⋆-algebra, and instead
simply consider the `quasispectrum` so as to avoid depending on a choice of unital algebra. However,
we can still establish a form of spectral permanence.

## Main statements

+ `Unitary.spectrum_subset_circle`: The spectrum of a unitary element is contained in the unit
  sphere in `ℂ`.
+ `IsSelfAdjoint.spectralRadius_eq_nnnorm`: The spectral radius of a selfadjoint element is equal
  to its norm.
+ `IsStarNormal.spectralRadius_eq_nnnorm`: The spectral radius of a normal element is equal to
  its norm.
+ `IsSelfAdjoint.mem_spectrum_eq_re`: Any element of the spectrum of a selfadjoint element is real.
* `StarSubalgebra.coe_isUnit`: for `x : S` in a C⋆-Subalgebra `S` of `A`, then `↑x : A` is a Unit
  if and only if `x` is a unit.
* `StarSubalgebra.spectrum_eq`: **spectral permanence** for `x : S`, where `S` is a C⋆-Subalgebra
  of `A`, `spectrum ℂ x = spectrum ℂ (x : A)`.

## TODO

+ prove a variation of spectral permanence using `StarAlgHom` instead of `StarSubalgebra`.
+ prove a variation of spectral permanence for `quasispectrum`.

-/

public section


local notation "σ" => spectrum
local postfix:max "⋆" => star

section

open scoped Topology ENNReal

open Filter ENNReal spectrum CStarRing NormedSpace

section UnitarySpectrum

variable {𝕜 : Type*} [NormedField 𝕜] {E : Type*} [NormedRing E] [StarRing E] [CStarRing E]
  [NormedAlgebra 𝕜 E] [CompleteSpace E]

theorem Unitary.spectrum_subset_circle (u : unitary E) :
    spectrum 𝕜 (u : E) ⊆ Metric.sphere 0 1 := by
  nontriviality E
  refine fun k hk => mem_sphere_zero_iff_norm.mpr (le_antisymm ?_ ?_)
  · simpa only [CStarRing.norm_coe_unitary u] using norm_le_norm_of_mem hk
  · rw [← Unitary.val_toUnits_apply u] at hk
    have hnk := ne_zero_of_mem_of_unit hk
    rw [← inv_inv (Unitary.toUnits u), ← spectrum.map_inv, Set.mem_inv] at hk
    have : ‖k‖⁻¹ ≤ ‖(↑(Unitary.toUnits u)⁻¹ : E)‖ := by
      simpa only [norm_inv] using norm_le_norm_of_mem hk
    simpa using inv_le_of_inv_le₀ (norm_pos_iff.mpr hnk) this

@[deprecated (since := "2025-10-29")] alias unitary.spectrum_subset_circle :=
  Unitary.spectrum_subset_circle

theorem spectrum.subset_circle_of_unitary {u : E} (h : u ∈ unitary E) :
    spectrum 𝕜 u ⊆ Metric.sphere 0 1 :=
  Unitary.spectrum_subset_circle ⟨u, h⟩

theorem spectrum.norm_eq_one_of_unitary {u : E} (hu : u ∈ unitary E)
    ⦃z : 𝕜⦄ (hz : z ∈ spectrum 𝕜 u) : ‖z‖ = 1 := by
  simpa using spectrum.subset_circle_of_unitary hu hz

end UnitarySpectrum

section Quasispectrum

open scoped NNReal in
lemma CStarAlgebra.le_nnnorm_of_mem_quasispectrum {A : Type*} [NonUnitalCStarAlgebra A]
    {a : A} {x : ℝ≥0} (hx : x ∈ quasispectrum ℝ≥0 a) : x ≤ ‖a‖₊ := by
  rw [Unitization.quasispectrum_eq_spectrum_inr' ℝ≥0 ℂ] at hx
  simpa [Unitization.nnnorm_inr] using spectrum.le_nnnorm_of_mem hx

end Quasispectrum

section ComplexScalars

open Complex

variable {A : Type*} [CStarAlgebra A]

local notation "↑ₐ" => algebraMap ℂ A

theorem IsSelfAdjoint.spectralRadius_eq_nnnorm {a : A} (ha : IsSelfAdjoint a) :
    spectralRadius ℂ a = ‖a‖₊ := by
  have hconst : Tendsto (fun _n : ℕ => (‖a‖₊ : ℝ≥0∞)) atTop _ := tendsto_const_nhds
  refine tendsto_nhds_unique ?_ hconst
  convert
    (spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius (a : A)).comp
      (tendsto_pow_atTop_atTop_of_one_lt one_lt_two) using 1
  refine funext fun n => ?_
  rw [Function.comp_apply, ha.nnnorm_pow_two_pow, ENNReal.coe_pow, ← rpow_natCast, ← rpow_mul]
  simp

/-- In a C⋆-algebra, the spectral radius of a self-adjoint element is equal to its norm.
See `IsSelfAdjoint.toReal_spectralRadius_eq_norm` for a version involving
`spectralRadius ℝ a`. -/
lemma IsSelfAdjoint.toReal_spectralRadius_complex_eq_norm {a : A} (ha : IsSelfAdjoint a) :
    (spectralRadius ℂ a).toReal = ‖a‖ := by
  simp [ha.spectralRadius_eq_nnnorm]

theorem IsStarNormal.spectralRadius_eq_nnnorm (a : A) [IsStarNormal a] :
    spectralRadius ℂ a = ‖a‖₊ := by
  refine (ENNReal.pow_right_strictMono two_ne_zero).injective ?_
  have heq :
    (fun n : ℕ => (‖(a⋆ * a) ^ n‖₊ : ℝ≥0∞) ^ (1 / n : ℝ)) =
      (fun x => x ^ 2) ∘ fun n : ℕ => (‖a ^ n‖₊ : ℝ≥0∞) ^ (1 / n : ℝ) := by
    funext n
    rw [Function.comp_apply, ← rpow_natCast, ← rpow_mul, mul_comm, rpow_mul, rpow_natCast, ←
      coe_pow, sq, ← nnnorm_star_mul_self, Commute.mul_pow (star_comm_self' a), star_pow]
  have h₂ :=
    ((ENNReal.continuous_pow 2).tendsto (spectralRadius ℂ a)).comp
      (spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius a)
  rw [← heq] at h₂
  convert tendsto_nhds_unique h₂ (pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius (a⋆ * a))
  rw [(IsSelfAdjoint.star_mul_self a).spectralRadius_eq_nnnorm, sq, nnnorm_star_mul_self, coe_mul]

variable [StarModule ℂ A]

/-- Any element of the spectrum of a selfadjoint is real. -/
theorem IsSelfAdjoint.mem_spectrum_eq_re {a : A} (ha : IsSelfAdjoint a) {z : ℂ}
    (hz : z ∈ spectrum ℂ a) : z = z.re := by
  let +nondep : NormedAlgebra ℚ A := .restrictScalars ℚ ℂ A
  have hu := exp_mem_unitary_of_mem_skewAdjoint (ha.smul_mem_skewAdjoint conj_I)
  let Iu := Units.mk0 I I_ne_zero
  have : NormedSpace.exp (I • z) ∈ spectrum ℂ (NormedSpace.exp (I • a)) := by
    simpa only [Units.smul_def, Units.val_mk0] using
      spectrum.exp_mem_exp (Iu • a) (smul_mem_smul_iff.mpr hz)
  exact Complex.ext (ofReal_re _) <| by
    simpa only [← Complex.exp_eq_exp_ℂ, mem_sphere_zero_iff_norm, norm_exp, Real.exp_eq_one_iff,
      smul_eq_mul, I_mul, neg_eq_zero] using
      spectrum.subset_circle_of_unitary hu this

/-- Any element of the spectrum of a selfadjoint is real. -/
theorem selfAdjoint.mem_spectrum_eq_re (a : selfAdjoint A) {z : ℂ}
    (hz : z ∈ spectrum ℂ (a : A)) : z = z.re :=
  a.prop.mem_spectrum_eq_re hz

/-- Any element of the spectrum of a selfadjoint is real. -/
theorem IsSelfAdjoint.im_eq_zero_of_mem_spectrum {a : A} (ha : IsSelfAdjoint a)
    {z : ℂ} (hz : z ∈ spectrum ℂ a) : z.im = 0 := by
  rw [ha.mem_spectrum_eq_re hz, ofReal_im]

/-- The spectrum of a selfadjoint is real -/
theorem IsSelfAdjoint.val_re_map_spectrum {a : A} (ha : IsSelfAdjoint a) :
    spectrum ℂ a = ((↑) ∘ re '' spectrum ℂ a : Set ℂ) :=
  le_antisymm (fun z hz => ⟨z, hz, (ha.mem_spectrum_eq_re hz).symm⟩) fun z => by
    rintro ⟨z, hz, rfl⟩
    simpa only [(ha.mem_spectrum_eq_re hz).symm, Function.comp_apply] using hz

/-- The spectrum of a selfadjoint is real -/
theorem selfAdjoint.val_re_map_spectrum (a : selfAdjoint A) :
    spectrum ℂ (a : A) = ((↑) ∘ re '' spectrum ℂ (a : A) : Set ℂ) :=
  a.property.val_re_map_spectrum

/-- The complement of the spectrum of a selfadjoint element in a C⋆-algebra is connected. -/
lemma IsSelfAdjoint.isConnected_spectrum_compl {a : A} (ha : IsSelfAdjoint a) :
    IsConnected (σ ℂ a)ᶜ := by
  suffices IsConnected (((σ ℂ a)ᶜ ∩ {z | 0 ≤ z.im}) ∪ (σ ℂ a)ᶜ ∩ {z | z.im ≤ 0}) by
    rw [← Set.inter_union_distrib_left, ← Set.setOf_or] at this
    rw [← Set.inter_univ (σ ℂ a)ᶜ]
    convert this using 2
    exact Eq.symm <| Set.eq_univ_of_forall (fun z ↦ le_total 0 z.im)
  refine IsConnected.union ?nonempty ?upper ?lower
  case nonempty =>
    have := Filter.NeBot.nonempty_of_mem inferInstance <| Filter.mem_map.mp <|
      Complex.isometry_ofReal.antilipschitz.tendsto_cobounded (spectrum.isBounded a |>.compl)
    exact this.image Complex.ofReal |>.mono <| by simp
  case' upper => apply Complex.isConnected_of_upperHalfPlane ?_ <| Set.inter_subset_right
  case' lower => apply Complex.isConnected_of_lowerHalfPlane ?_ <| Set.inter_subset_right
  all_goals
    refine Set.subset_inter (fun z hz hz' ↦ ?_) (fun _ ↦ by simpa using le_of_lt)
    rw [Set.mem_setOf_eq, ha.im_eq_zero_of_mem_spectrum hz'] at hz
    simp_all

namespace StarSubalgebra

variable (S : StarSubalgebra ℂ A) [hS : IsClosed (S : Set A)]

/-- For a unital C⋆-subalgebra `S` of `A` and `x : S`, if `↑x : A` is invertible in `A`, then
`x` is invertible in `S`. -/
lemma coe_isUnit {a : S} : IsUnit (a : A) ↔ IsUnit a := by
  refine ⟨fun ha ↦ ?_, IsUnit.map S.subtype⟩
  have ha₁ := ha.star.mul ha
  have ha₂ := ha.mul ha.star
  have spec_eq {x : S} (hx : IsSelfAdjoint x) : spectrum ℂ x = spectrum ℂ (x : A) :=
    Subalgebra.spectrum_eq_of_isPreconnected_compl S _ <|
      (hx.map S.subtype).isConnected_spectrum_compl.isPreconnected
  rw [← StarMemClass.coe_star, ← MulMemClass.coe_mul, ← spectrum.zero_notMem_iff ℂ, ← spec_eq,
    spectrum.zero_notMem_iff] at ha₁ ha₂
  · have h₁ : ha₁.unit⁻¹ * star a * a = 1 := mul_assoc _ _ a ▸ ha₁.val_inv_mul
    have h₂ : a * (star a * ha₂.unit⁻¹) = 1 := (mul_assoc a _ _).symm ▸ ha₂.mul_val_inv
    exact ⟨⟨a, ha₁.unit⁻¹ * star a, left_inv_eq_right_inv h₁ h₂ ▸ h₂, h₁⟩, rfl⟩
  · exact IsSelfAdjoint.mul_star_self a
  · exact IsSelfAdjoint.star_mul_self a

lemma mem_spectrum_iff {a : S} {z : ℂ} : z ∈ spectrum ℂ a ↔ z ∈ spectrum ℂ (a : A) :=
  not_iff_not.mpr S.coe_isUnit.symm

/-- **Spectral permanence.** The spectrum of an element is invariant of the (closed)
`StarSubalgebra` in which it is contained. -/
lemma spectrum_eq {a : S} : spectrum ℂ a = spectrum ℂ (a : A) :=
  Set.ext fun _ ↦ S.mem_spectrum_iff

end StarSubalgebra

end ComplexScalars

namespace NonUnitalStarAlgHom

variable {F A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
variable [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B]

open Unitization

/-- A non-unital star algebra homomorphism of complex C⋆-algebras is norm contractive. -/
lemma nnnorm_apply_le (φ : F) (a : A) : ‖φ a‖₊ ≤ ‖a‖₊ := by
  have h (ψ : Unitization ℂ A →⋆ₐ[ℂ] Unitization ℂ B) (x : Unitization ℂ A) :
      ‖ψ x‖₊ ≤ ‖x‖₊ := by
    suffices ∀ {s}, IsSelfAdjoint s → ‖ψ s‖₊ ≤ ‖s‖₊ by
      refine nonneg_le_nonneg_of_sq_le_sq zero_le' ?_
      simp_rw [← nnnorm_star_mul_self, ← map_star, ← map_mul]
      exact this <| .star_mul_self x
    intro s hs
    suffices this : spectralRadius ℂ (ψ s) ≤ spectralRadius ℂ s by
      rwa [(hs.map ψ).spectralRadius_eq_nnnorm, hs.spectralRadius_eq_nnnorm, coe_le_coe]
        at this
    exact iSup_le_iSup_of_subset (AlgHom.spectrum_apply_subset ψ s)
  simpa [nnnorm_inr] using h (starLift (inrNonUnitalStarAlgHom ℂ B |>.comp (φ : A →⋆ₙₐ[ℂ] B))) a

/-- A non-unital star algebra homomorphism of complex C⋆-algebras is norm contractive. -/
lemma norm_apply_le (φ : F) (a : A) : ‖φ a‖ ≤ ‖a‖ := by
  exact_mod_cast nnnorm_apply_le φ a

/-- Non-unital star algebra homomorphisms between C⋆-algebras are continuous linear maps.
See note [lower instance priority] -/
lemma instContinuousLinearMapClassComplex : ContinuousLinearMapClass F ℂ A B :=
  { NonUnitalAlgHomClass.instLinearMapClass with
    map_continuous := fun φ =>
      AddMonoidHomClass.continuous_of_bound φ 1 (by simpa only [one_mul] using nnnorm_apply_le φ) }

scoped[CStarAlgebra] attribute [instance] NonUnitalStarAlgHom.instContinuousLinearMapClassComplex

end NonUnitalStarAlgHom

namespace StarAlgEquiv

variable {F A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [EquivLike F A B]
variable [NonUnitalAlgEquivClass F ℂ A B] [StarHomClass F A B]

lemma nnnorm_map (φ : F) (a : A) : ‖φ a‖₊ = ‖a‖₊ :=
  le_antisymm (NonUnitalStarAlgHom.nnnorm_apply_le φ a) <| by
    simpa using NonUnitalStarAlgHom.nnnorm_apply_le (symm (φ : A ≃⋆ₐ[ℂ] B)) ((φ : A ≃⋆ₐ[ℂ] B) a)

lemma norm_map (φ : F) (a : A) : ‖φ a‖ = ‖a‖ :=
  congr_arg NNReal.toReal (nnnorm_map φ a)

lemma isometry (φ : F) : Isometry φ :=
  AddMonoidHomClass.isometry_of_norm φ (norm_map φ)

end StarAlgEquiv

end

namespace WeakDual

open ContinuousMap Complex

open scoped ComplexStarModule

variable {F A : Type*} [CStarAlgebra A] [FunLike F A ℂ] [hF : AlgHomClass F ℂ A ℂ]

/-- This instance is provided instead of `StarHomClass` to avoid type class inference loops.
See note [lower instance priority] -/
noncomputable instance (priority := 100) Complex.instStarHomClass : StarHomClass F A ℂ where
  map_star φ a := by
    suffices hsa : ∀ s : selfAdjoint A, (φ s)⋆ = φ s by
      rw [← realPart_add_I_smul_imaginaryPart a]
      simp only [map_add, map_smul, star_add, star_smul, hsa, selfAdjoint.star_val_eq]
    intro s
    rw [selfAdjoint.mem_spectrum_eq_re s (AlgHom.apply_mem_spectrum φ (s : A))]
    simp

/-- This is not an instance to avoid type class inference loops. See
`WeakDual.Complex.instStarHomClass`. -/
lemma _root_.AlgHomClass.instStarHomClass : StarHomClass F A ℂ :=
  { WeakDual.Complex.instStarHomClass, hF with }

namespace CharacterSpace

noncomputable instance instStarHomClass : StarHomClass (characterSpace ℂ A) A ℂ :=
  { AlgHomClass.instStarHomClass with }

end CharacterSpace

end WeakDual
