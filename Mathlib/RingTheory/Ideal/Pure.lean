/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Flat.Tensor
public import Mathlib.RingTheory.Ideal.IdempotentFG
public import Mathlib.RingTheory.Idempotents
public import Mathlib.RingTheory.Spectrum.Prime.Basic
public import Mathlib.RingTheory.LocalProperties.Basic

/-!
# Pure ideals

An ideal `I` of a ring `R` is called pure if `R ⧸ I` is flat over `R`
(see [Stacks 04PR](https://stacks.math.columbia.edu/tag/04PR)). In this file we show
some properties of such ideals.

## Main results and definitions

- `Ideal.Pure`: An ideal `I` of `R` is pure if `R ⧸ I` is `R`-flat.
- `Ideal.inf_eq_mul_of_pure`: If `I` is pure, `I ⊓ J = I * J` for every ideal `J`.
- `Ideal.Pure.of_inf_eq_mul`: If for any f.g. ideal `J`, the equality `I ⊓ J = I * J` holds, then
  `I` is pure.
- `Ideal.zeroLocus_inj_of_pure`: If `I` and `J` are pure ideals such that `V(I) = V(J)`, then
  `I = J`.
-/

@[expose] public section

variable {R : Type*} [CommRing R]

open TensorProduct PrimeSpectrum

/-- An ideal `I` of `R` is pure if `R ⧸ I` is a flat `R`-module. -/
@[stacks 04PR]
abbrev Ideal.Pure (I : Ideal R) : Prop :=
  Module.Flat R (R ⧸ I)

lemma injective_lTensor_quotient_iff_inf_eq_mul (I J : Ideal R) :
    Function.Injective (J.subtype.lTensor (R ⧸ I)) ↔ I ⊓ J = I * J := by
  let f : J ⧸ (I • ⊤ : Submodule R J) →ₗ[R] R ⧸ I :=
    Submodule.mapQ _ _ J.subtype <| by
      simp [← Submodule.map_le_iff_le_comap, Ideal.mul_le_right]
  have : J.subtype.lTensor (R ⧸ I) =
      (TensorProduct.rid R (R ⧸ I)).symm ∘ₗ f ∘ₗ TensorProduct.quotTensorEquivQuotSMul J I := by
    ext
    simp [f, ← Ideal.Quotient.algebraMap_eq, Algebra.TensorProduct.tmul_one_eq_one_tmul]
  rw [this]
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, EmbeddingLike.comp_injective,
    EquivLike.injective_comp, ← LinearMap.ker_eq_bot, f, Submodule.ker_mapQ,
    ← LinearMap.le_ker_iff_map, Submodule.ker_mkQ,
    ← (Submodule.map_le_map_iff_of_injective J.injective_subtype)]
  simp [inf_comm, le_antisymm_iff, Ideal.mul_le_inf (I := I) (J := J)]

@[stacks 04PS "(1) => (2)"]
lemma Ideal.inf_eq_mul_of_pure (I J : Ideal R) [I.Pure] :
    I ⊓ J = I * J := by
  rw [← injective_lTensor_quotient_iff_inf_eq_mul]
  apply Module.Flat.lTensor_preserves_injective_linearMap
  exact J.injective_subtype

/-- If `I` is pure, `I ^ 2 = I`. The converse holds if `I` is finitely generated, see
`Ideal.Pure.of_isIdempotentElem`. -/
lemma Ideal.isIdempotentElem_of_pure (I : Ideal R) [I.Pure] : IsIdempotentElem I := by
  simp [IsIdempotentElem, ← Ideal.inf_eq_mul_of_pure]

lemma Ideal.Pure.of_isIdempotentElem {I : Ideal R} (h : I.FG) (h' : IsIdempotentElem I) :
    I.Pure := by
  rw [Ideal.isIdempotentElem_iff_of_fg _ h] at h'
  obtain ⟨e, he, rfl⟩ := h'
  have : Module.Flat R ((R ⧸ R ∙ e) × R ⧸ span {1 - e}) :=
    .of_linearEquiv <| AlgEquiv.prodQuotientOfIsIdempotentElem R he he.one_sub (by simp)
      (by grind [IsIdempotentElem]) |>.toLinearEquiv.symm
  apply Module.Flat.of_retract (LinearMap.inl R _ (R ⧸ span {1 - e})) (LinearMap.fst R _ _)
  simp

@[stacks 04PS "(3) => (1)"]
lemma Ideal.Pure.of_inf_eq_mul (I : Ideal R) (H : ∀ ⦃J : Ideal R⦄, J.FG → I ⊓ J = I * J) :
    I.Pure := by
  rw [Pure, Module.Flat.iff_lTensor_injective]
  intro J hJ
  rw [injective_lTensor_quotient_iff_inf_eq_mul]
  exact H hJ

@[stacks 04PS "(1) => (5)"]
lemma Ideal.exists_eq_mul_of_pure {I : Ideal R} [I.Pure] {x : R} (hx : x ∈ I) :
    ∃ y ∈ I, x = x * y := by
  suffices h : x ∈ I * Ideal.span {x} by
    rw [Ideal.mem_mul_span_singleton] at h
    grind
  rw [← I.inf_eq_mul_of_pure]
  exact ⟨hx, subset_span rfl⟩

@[stacks 04PS "(5) => (7)"]
lemma Ideal.le_ker_atPrime_of_forall_exists_eq_mul {I : Ideal R}
    (h : ∀ x ∈ I, ∃ y ∈ I, x = x * y) {p : Ideal R} [p.IsPrime] (hle : I ≤ p) :
    I ≤ RingHom.ker (algebraMap R <| Localization.AtPrime p) := by
  intro x hx
  obtain ⟨y, hy, heq⟩ := h _ hx
  have : IsUnit (algebraMap R (Localization.AtPrime p) (1 - y)) := by
    rw [IsLocalization.algebraMap_isUnit_iff p.primeCompl]
    refine ⟨1 - y, fun hz ↦ p.one_notMem ?_, by simp⟩
    rw [← sub_add_cancel 1 y]
    exact Ideal.add_mem _ hz (hle hy)
  have hzero : x * (1 - y) = 0 := by simp [mul_sub, ← heq]
  simp only [RingHom.mem_ker, ← this.mul_left_eq_zero, ← RingHom.map_mul, hzero, RingHom.map_zero]

lemma Ideal.ker_piRingHom_atPrime_eq_of_pure (I : Ideal R) [I.Pure] :
    RingHom.ker
      (Pi.ringHom fun p : zeroLocus (I : Set R) ↦
        algebraMap R (Localization.AtPrime p.val.asIdeal)) = I := by
  refine le_antisymm ?_ fun x hx ↦ ?_
  · rw [Pi.ker_ringHom]
    refine le_trans ?_ I.iInf_ker_le
    simp only [le_iInf_iff]
    exact fun i hi hle ↦ iInf_le_of_le ⟨⟨i, hi⟩, hle⟩ le_rfl
  · rw [RingHom.mem_ker]
    ext p
    rw [Pi.ringHom_apply, Pi.zero_apply]
    exact Ideal.le_ker_atPrime_of_forall_exists_eq_mul
      (fun x hx ↦ Ideal.exists_eq_mul_of_pure hx) p.2 hx

@[stacks 04PT]
lemma Ideal.zeroLocus_inj_of_pure {I J : Ideal R} [I.Pure] [J.Pure] :
    zeroLocus (I : Set R) = zeroLocus J ↔ I = J := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ rfl⟩
  rw [← I.ker_piRingHom_atPrime_eq_of_pure, ← J.ker_piRingHom_atPrime_eq_of_pure]
  generalize hs : zeroLocus (I : Set R) = s
  generalize ht : zeroLocus (J : Set R) = t
  obtain rfl : s = t := by rw [← hs, ← ht, h]
  rfl
