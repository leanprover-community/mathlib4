/-
Copyright (c) 2025 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity

/-! # Properties of `rpow` and `sqrt` over an algebra with an isometric CFC

This file collects results about `CFC.rpow`, `CFC.nnrpow` and `CFC.sqrt` that use facts that
rely on an isometric continuous functional calculus.

## Main theorems

* Various versions of `‖a ^ r‖ = ‖a‖ ^ r` and `‖CFC.sqrt a‖ = sqrt ‖a‖`.

## Tags

continuous functional calculus, rpow, sqrt
-/

public section

open scoped NNReal UniformConvergence

namespace CFC

section nonunital

variable {A : Type*} [NonUnitalNormedRing A] [StarRing A] [NormedSpace ℝ A] [IsScalarTower ℝ A A]
  [SMulCommClass ℝ A A] [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass ℝ A]
  [NonUnitalIsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint]

lemma nnnorm_nnrpow (a : A) {r : ℝ≥0} (hr : 0 < r) (ha : 0 ≤ a := by cfc_tac) :
    ‖a ^ r‖₊ = ‖a‖₊ ^ (r : ℝ) :=
  NNReal.monotone_nnrpow_const r |>.monotoneOn _ |>.nnnorm_cfcₙ _ _

lemma norm_nnrpow (a : A) {r : ℝ≥0} (hr : 0 < r) (ha : 0 ≤ a := by cfc_tac) :
    ‖a ^ r‖ = ‖a‖ ^ (r : ℝ) :=
  congr(NNReal.toReal $(nnnorm_nnrpow a hr ha))

lemma nnnorm_sqrt (a : A) (ha : 0 ≤ a := by cfc_tac) : ‖sqrt a‖₊ = NNReal.sqrt ‖a‖₊ := by
  rw [sqrt_eq_nnrpow, NNReal.sqrt_eq_rpow]
  exact nnnorm_nnrpow a (by simp) ha

lemma norm_sqrt (a : A) (ha : 0 ≤ a := by cfc_tac) : ‖sqrt a‖ = √‖a‖ := by
  simpa using congr(NNReal.toReal $(nnnorm_sqrt a ha))

variable [ContinuousStar A] [CompleteSpace A]

lemma continuousOn_sqrt : ContinuousOn sqrt {a : A | 0 ≤ a} :=
  continuousOn_id.cfcₙ_nnreal_of_mem_nhdsSet _ Filter.univ_mem

lemma continuousOn_nnrpow (r : ℝ≥0) : ContinuousOn (· ^ r) {a : A | 0 ≤ a} := by
  obtain (rfl | hr) := eq_zero_or_pos r
  · simpa using continuousOn_const
  · exact continuousOn_id.cfcₙ_nnreal_of_mem_nhdsSet _ Filter.univ_mem

attribute [fun_prop] ContinuousWithinAt.prodMap NNReal.continuousAt_rpow

open UniformOnFun Set in
lemma continuousOn_nnrpow_setProd :
    ContinuousOn (fun x : A × ℝ≥0 => x.1 ^ x.2) (Ici 0 ×ˢ Ioi 0) := by
  intro (a, p) hap
  have ha : 0 ≤ a := Set.mem_prod.mp hap |>.1
  have hp : 0 < p := Set.mem_prod.mp hap |>.2
  obtain ⟨K, hK₁, hK₂⟩ := (quasispectrum.isCompact_nnreal a).nhdsSet_basis_isCompact.ex_mem
  let s : Set ℝ≥0 := K ∩ Ici 0
  have hs_compact : IsCompact s := hK₂.inter_right (ClosedIciTopology.isClosed_Ici 0)
  have hs_contains_spec : quasispectrum ℝ≥0 a ⊆ s := by
    refine Set.subset_inter ?_ ?_
    · exact subset_of_mem_nhdsSet hK₁
    · grind [zero_le]
  let s' := {f : ℝ≥0 →ᵤ[{s}] ℝ≥0 | ContinuousOn (toFun {s} f) s ∧ f 0 = 0}
                ×ˢ {a : A | 0 ≤ a ∧ quasispectrum ℝ≥0 a ⊆ s}
  let ssw := {b : A | 0 ≤ b ∧ quasispectrum ℝ≥0 b ⊆ s} ×ˢ Ioi (0 : ℝ≥0)
  let ssws := Ioi (0 : ℝ≥0) ×ˢ {b : A | 0 ≤ b ∧ quasispectrum ℝ≥0 b ⊆ s}
  refine ContinuousWithinAt.mono_of_mem_nhdsWithin (t := ssw) ?_ <| by
    rw [nhdsWithin_prod_eq, Filter.mem_prod_iff]
    refine ⟨{b : A | 0 ≤ b ∧ quasispectrum ℝ≥0 b ⊆ s}, ?_, Ioi 0, self_mem_nhdsWithin, ?_⟩
    · rw [nhdsWithin]
      apply Filter.mem_inf_of_inter (s := {x | (fun x ↦ quasispectrum ℝ≥0 x ⊆ K) x}) (t := Ici 0)
      · exact (upperHemicontinuous_quasispectrum_nnreal A |>.upperHemicontinuousAt a K hK₁ |>.mono
            fun b hb => subset_of_mem_nhdsSet hb)
      · exact Filter.mem_principal_self _
      · exact fun b ⟨hbK, hb_nonneg⟩ => ⟨hb_nonneg, subset_inter hbK (fun x _ => zero_le x)⟩
    · exact prod_subset_prod_iff.mpr (Or.inl ⟨Subset.rfl, Subset.rfl⟩)
  let f₁ : ℝ≥0 → ℝ≥0 →ᵤ[{s}] ℝ≥0 := fun q : ℝ≥0 => ofFun {s} (fun x : ℝ≥0 => x.nnrpow q)
  let f₂ : (ℝ≥0 →ᵤ[{s}] ℝ≥0) × A → A := fun x => cfcₙ (toFun {s} x.1) x.2
  have h₁ : ContinuousWithinAt f₁ (Ioi 0) p := by
    have : CompactSpace s := isCompact_iff_compactSpace.mp hs_compact
    refine ContinuousOn.continuousOn_uniformOnFun_of_uncurry ?_ _ hp
    intro x hx
    apply ContinuousAt.continuousWithinAt
    change ContinuousAt ((fun a => a.1 ^ a.2) ∘ (Prod.map id NNReal.toReal) ∘ Prod.swap) x
    refine ContinuousAt.comp ?_ (by fun_prop)
    apply NNReal.continuousAt_rpow
    simp only [Function.comp_apply, Prod.map_fst, Prod.fst_swap, id_eq, ne_eq, Prod.map_snd,
      Prod.snd_swap, NNReal.coe_pos]
    grind only [= mem_prod, = mem_Ioi]
  have h₁' : ∀ q ∈ Ioi 0, f₁ q 0 = 0 := by
    intro q hq
    simp only [ofFun, NNReal.nnrpow_def, Equiv.coe_fn_mk, NNReal.rpow_eq_left_iff, zero_ne_one,
      NNReal.coe_eq_one, ne_eq, NNReal.coe_eq_zero, true_and, false_or, f₁]
    grind only [= mem_Ioi]
  have hcomp : (fun x : A × ℝ≥0 => x.1 ^ x.2) = f₂ ∘ (Prod.map f₁ id) ∘ Prod.swap := by
    ext
    simp [Prod.map, Prod.swap, f₁, f₂, ofFun, nnrpow_def, toFun]
  rw [hcomp]
  refine ContinuousWithinAt.comp (t := s') ?_ ?_ ?_
  · apply continuousOn_cfcₙ_nnreal_setProd hs_compact
    simp only [Function.comp_apply, Prod.swap_prod_mk, Prod.map_apply, id_eq, mem_prod,
      mem_setOf_eq]
    refine ⟨⟨?_, h₁' _ hp⟩, ha, by grind⟩
    simp only [toFun, NNReal.nnrpow_def, Equiv.symm_apply_apply, f₁]
    fun_prop
  · refine ContinuousWithinAt.comp (t := ssws) ?_ (by fun_prop) (by grind [MapsTo])
    simp only [Prod.swap_prod_mk]
    exact ContinuousWithinAt.prodMap h₁ continuousWithinAt_id
  · intro x hx
    simp only [Function.comp_apply, mem_prod, Prod.map_fst, Prod.fst_swap, mem_setOf_eq,
      Prod.map_snd, Prod.snd_swap, id_eq, s']
    refine ⟨⟨?_, by grind⟩, by grind, by grind⟩
    simp only [toFun, NNReal.nnrpow_def, Equiv.symm_apply_apply, f₁]
    fun_prop

end nonunital

section unital

variable {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra ℝ A]
  [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass ℝ A]
  [IsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint]

lemma nnnorm_rpow (a : A) {r : ℝ} (hr : 0 < r) (ha : 0 ≤ a := by cfc_tac) :
    ‖a ^ r‖₊ = ‖a‖₊ ^ r := by
  lift r to ℝ≥0 using hr.le
  rw [← nnrpow_eq_rpow, ← nnnorm_nnrpow a]
  all_goals simpa

lemma norm_rpow (a : A) {r : ℝ} (hr : 0 < r) (ha : 0 ≤ a := by cfc_tac) :
    ‖a ^ r‖ = ‖a‖ ^ r :=
  congr(NNReal.toReal $(nnnorm_rpow a hr ha))

lemma continuousOn_rpow [ContinuousStar A] [CompleteSpace A] (r : ℝ) :
    ContinuousOn (· ^ r) {a : A | IsStrictlyPositive a} := by
  refine continuousOn_id.cfc_nnreal_of_mem_nhdsSet _ (s := {0}ᶜ) ?_
  simp_rw [nhdsSet_iUnion, Filter.mem_iSup, isOpen_compl_singleton.mem_nhdsSet]
  exact fun a ha ↦ by simpa using spectrum.zero_notMem _ ha.isUnit

end unital

section cstar

variable {A : Type*} [PartialOrder A] [NonUnitalNormedRing A] [StarRing A] [CStarRing A]
    [NormedSpace ℝ A] [SMulCommClass ℝ A A] [IsScalarTower ℝ A A] [StarOrderedRing A]
    [NonUnitalContinuousFunctionalCalculus ℝ A IsSelfAdjoint] [NonnegSpectrumClass ℝ A]

lemma norm_star_mul_mul_self_of_nonneg {a : A} (b : A) (ha : 0 ≤ a := by cfc_tac) :
    ‖star b * a * b‖ = ‖CFC.sqrt a * b‖ ^ 2 := by
  rw [sq, ← CStarRing.norm_star_mul_self, star_mul, (CFC.sqrt_nonneg a).star_eq,
    ← mul_assoc _ (CFC.sqrt a), mul_assoc _ _ (CFC.sqrt a), CFC.sqrt_mul_sqrt_self a]

lemma IsSelfAdjoint.norm_mul_mul_self_of_nonneg {a : A} (b : A)
    (hb : IsSelfAdjoint b := by cfc_tac) (ha : 0 ≤ a := by cfc_tac) :
    ‖b * a * b‖ = ‖CFC.sqrt a * b‖ ^ 2 := by
  simpa [hb.star_eq] using norm_star_mul_mul_self_of_nonneg b ha

lemma norm_mul_mul_star_self_of_nonneg {a : A} (b : A) (ha : 0 ≤ a := by cfc_tac) :
    ‖b * a * star b‖ = ‖b * CFC.sqrt a‖ ^ 2 := by
  conv_rhs => rw [← (CFC.sqrt_nonneg a).star_eq, ← star_star b, ← star_mul, norm_star,
    ← norm_star_mul_mul_self_of_nonneg _ ha, star_star]

lemma IsSelfAdjoint.norm_mul_mul_self_of_nonneg' {a : A} (b : A)
    (hb : IsSelfAdjoint b := by cfc_tac) (ha : 0 ≤ a := by cfc_tac) :
    ‖b * a * b‖ = ‖b * CFC.sqrt a‖ ^ 2 := by
  simpa [hb.star_eq] using norm_mul_mul_star_self_of_nonneg b ha

end cstar

end CFC
