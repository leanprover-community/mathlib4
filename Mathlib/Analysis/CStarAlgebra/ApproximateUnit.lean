/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow

/-! # Positive contractions in a C⋆-algebra form an approximate unit

This file will show (although it does not yet) that the collection of positive contractions (of norm
strictly less than one) in a possibly non-unital C⋆-algebra form an approximate unit. The key step
is to show that this set is directed using the continuous functional calculus applied with the
functions `fun x : ℝ≥0, 1 - (1 + x)⁻¹` and `fun x : ℝ≥0, x * (1 - x)⁻¹`, which are inverses on
the interval `{x : ℝ≥0 | x < 1}`.

## Main declarations

+ `CFC.monotoneOn_one_sub_one_add_inv`: the function `f := fun x : ℝ≥0, 1 - (1 + x)⁻¹` is
  *operator monotone* on `Set.Ici (0 : A)` (i.e., `cfcₙ f` is monotone on `{x : A | 0 ≤ x}`).
+ `Set.InvOn.one_sub_one_add_inv`: the functions `f := fun x : ℝ≥0, 1 - (1 + x)⁻¹` and
  `g := fun x : ℝ≥0, x * (1 - x)⁻¹` are inverses on `{x : ℝ≥0 | x < 1}`.
+ `CStarAlgebra.directedOn_nonneg_ball`: the set `{x : A | 0 ≤ x} ∩ Metric.ball 0 1` is directed.

## TODO

+ Prove the approximate identity result by following Ken Davidson's proof in
  "C*-Algebras by Example"

-/

variable {A : Type*} [NonUnitalNormedRing A] [StarRing A] [CStarRing A] [CompleteSpace A]
  [NormedSpace ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] [StarModule ℂ A]

local notation "σₙ" => quasispectrum
local notation "σ" => spectrum

variable (a : A) [ha : IsStarNormal a]

open Unitization NNReal
open scoped CStarAlgebra

-- need a non-unital version of this too, where should it go?
theorem cfc_tsub {A : Type*} [TopologicalSpace A] [Ring A] [PartialOrder A] [StarRing A]
    [StarOrderedRing A] [Algebra ℝ A] [TopologicalRing A]
    [ContinuousFunctionalCalculus ℝ (IsSelfAdjoint : A → Prop)]
    [UniqueContinuousFunctionalCalculus ℝ A] [NonnegSpectrumClass ℝ A] (f g : ℝ≥0 → ℝ≥0)
    (a : A) (hfg : ∀ x ∈ spectrum ℝ≥0 a, g x ≤ f x) (ha : 0 ≤ a := by cfc_tac)
    (hf : ContinuousOn f (spectrum ℝ≥0 a) := by cfc_cont_tac)
    (hg : ContinuousOn g (spectrum ℝ≥0 a) := by cfc_cont_tac) :
    cfc (fun x ↦ f x - g x) a = cfc f a - cfc g a := by
  have ha' := SpectrumRestricts.nnreal_of_nonneg ha
  have : (σ ℝ a).EqOn (fun x ↦ ((f x.toNNReal - g x.toNNReal : ℝ≥0) : ℝ))
      (fun x ↦ f x.toNNReal - g x.toNNReal) :=
    fun x hx ↦ NNReal.coe_sub <| hfg _ <| ha'.apply_mem hx
  rw [cfc_nnreal_eq_real, cfc_nnreal_eq_real, cfc_nnreal_eq_real, cfc_congr this]
  refine cfc_sub _ _ a ?_ ?_
  all_goals
    exact continuous_subtype_val.comp_continuousOn <|
      ContinuousOn.comp ‹_› continuous_real_toNNReal.continuousOn <| ha'.image ▸ Set.mapsTo_image ..

variable [PartialOrder A] [StarOrderedRing A]

lemma CFC.monotoneOn_one_sub_one_add_inv :
    MonotoneOn (cfcₙ (fun x : ℝ≥0 ↦ 1 - (1 + x)⁻¹)) (Set.Ici (0 : A)) := by
  intro a ha b hb hab
  simp only [Set.mem_Ici] at ha hb
  rw [← Unitization.inr_le_iff .., Unitization.nnreal_cfcₙ_eq_cfc_inr a _,
    Unitization.nnreal_cfcₙ_eq_cfc_inr b _]
  have h1_add {x : ℝ≥0} : 1 + (x : ℝ) ≠ 0 := by positivity
  have h1_add_inv_le (x : ℝ≥0) : (1 + x)⁻¹ ≤ 1 := by simp
  have h_cfc_one_sub (c : A⁺¹) (hc : 0 ≤ c := by cfc_tac) :
      cfc (fun x : ℝ≥0 ↦ 1 - (1 + x)⁻¹) c = 1 - cfc (·⁻¹ : ℝ≥0 → ℝ≥0) (1 + c) := by
    rw [cfc_tsub _ _ _ (fun x _ ↦ by simp) (hg := by fun_prop (disch := intro _ _; positivity)),
      cfc_const_one ℝ≥0 c]
    rw [cfc_comp' (·⁻¹) (1 + ·) c ?_, cfc_add .., cfc_const_one ℝ≥0 c, cfc_id' ℝ≥0 c]
    refine continuousOn_id.inv₀ ?_
    rintro - ⟨x, -, rfl⟩
    simp only [id_def]
    positivity
  rw [← inr_le_iff a b (.of_nonneg ha) (.of_nonneg hb)] at hab
  rw [← inr_nonneg_iff] at ha hb
  rw [h_cfc_one_sub (a : A⁺¹), h_cfc_one_sub (b : A⁺¹)]
  gcongr
  rw [← CFC.rpow_neg_one_eq_cfc_inv, ← CFC.rpow_neg_one_eq_cfc_inv]
  exact CStarAlgebra.rpow_neg_one_le_rpow_neg_one (add_nonneg zero_le_one ha) (by gcongr) <|
    CStarAlgebra.isUnit_of_le isUnit_one zero_le_one <| le_add_of_nonneg_right ha


lemma Set.InvOn.one_sub_one_add_inv : Set.InvOn (fun x ↦ 1 - (1 + x)⁻¹) (fun x ↦ x * (1 - x)⁻¹)
    {x : ℝ≥0 | x < 1} {x : ℝ≥0 | x < 1} := by
  have h1_add {x : ℝ≥0} : 0 < 1 + (x : ℝ) := by positivity
  have : (fun x : ℝ≥0 ↦ x * (1 + x)⁻¹) = fun x ↦ 1 - (1 + x)⁻¹ := by
    ext x
    field_simp
    simp [sub_mul, inv_mul_cancel₀ h1_add.ne']
  rw [← this]
  constructor
  all_goals intro x (hx : x < 1); have : 0 < 1 - x := tsub_pos_of_lt hx
  · field_simp [tsub_add_cancel_of_le hx.le, tsub_tsub_cancel_of_le hx.le]
  · field_simp [mul_tsub]

lemma norm_cfcₙ_one_sub_one_add_inv_lt_one (a : A) (ha : 0 ≤ a) :
    ‖cfcₙ (fun x : ℝ≥0 ↦ 1 - (1 + x)⁻¹) a‖ < 1 := by
  have : ContinuousOn (fun x ↦ (1 + x)⁻¹) (σₙ ℝ≥0 a) :=
    ContinuousOn.inv₀ (by fun_prop) (by intro _ _; positivity)
  obtain ⟨y, -, hy'⟩ := And.left <| IsGreatest.nnnorm_cfcₙ_nnreal (fun x : ℝ≥0 ↦ 1 - (1 + x)⁻¹) a
    (continuousOn_const.sub this)
  calc ‖cfcₙ (fun x : ℝ≥0 ↦ 1 - (1 + x)⁻¹) a‖₊ = 1 - (1 + y)⁻¹ := hy'.symm
    _ < 1 := tsub_lt_self zero_lt_one (by positivity)

omit [StarModule ℂ A] in
lemma CStarAlgebra.le_nnnorm_of_mem_quasispectrum {a : A} {x : ℝ≥0} (hx : x ∈ σₙ ℝ≥0 a) :
    x ≤ ‖a‖₊ := by
  rw [quasispectrum_eq_spectrum_inr' ℝ≥0 ℂ] at hx
  simpa [nnnorm_inr] using spectrum.le_nnnorm_of_mem hx

lemma CStarAlgebra.directedOn_nonneg_ball :
    DirectedOn (· ≤ ·) ({x : A | 0 ≤ x} ∩ Metric.ball 0 1) := by
  let f : ℝ≥0 → ℝ≥0 := fun x => 1 - (1 + x)⁻¹
  let g : ℝ≥0 → ℝ≥0 := fun x => x * (1 - x)⁻¹
  suffices ∀ a b : A, 0 ≤ a → 0 ≤ b → ‖a‖ < 1 → ‖b‖ < 1 →
      a ≤ cfcₙ f (cfcₙ g a + cfcₙ g b) by
    rintro a ⟨(ha₁ : 0 ≤ a), ha₂⟩ b ⟨(hb₁ : 0 ≤ b), hb₂⟩
    simp only [Metric.mem_ball, dist_zero_right] at ha₂ hb₂
    refine ⟨cfcₙ f (cfcₙ g a + cfcₙ g b), ⟨by simp, ?_⟩, ?_, ?_⟩
    · simpa only [Metric.mem_ball, dist_zero_right] using
        norm_cfcₙ_one_sub_one_add_inv_lt_one _ (by simp [add_nonneg])
    · exact this a b ha₁ hb₁ ha₂ hb₂
    · exact add_comm (cfcₙ g a) (cfcₙ g b) ▸ this b a hb₁ ha₁ hb₂ ha₂
  rintro a b ha₁ - ha₂ -
  calc
    a = cfcₙ (f ∘ g) a := by
      conv_lhs => rw [← cfcₙ_id ℝ≥0 a]
      refine cfcₙ_congr (Set.InvOn.one_sub_one_add_inv.1.eqOn.symm.mono fun x hx ↦ ?_)
      exact lt_of_le_of_lt (CStarAlgebra.le_nnnorm_of_mem_quasispectrum hx) ha₂
    _ = cfcₙ f (cfcₙ g a) := by
      rw [cfcₙ_comp f g a ?_ (by simp [f]) ?_ (by simp [g]) ha₁]
      · fun_prop (disch := intro _ _; positivity)
      · have (x) (hx : x ∈ σₙ ℝ≥0 a) :  1 - x ≠ 0 := by
          refine tsub_pos_of_lt ?_ |>.ne'
          exact lt_of_le_of_lt (CStarAlgebra.le_nnnorm_of_mem_quasispectrum hx) ha₂
        fun_prop (disch := assumption)
    _ ≤ cfcₙ f (cfcₙ g a + cfcₙ g b) := by
      have hab' : cfcₙ g a ≤ cfcₙ g a + cfcₙ g b := le_add_of_nonneg_right cfcₙ_nonneg_of_predicate
      exact CFC.monotoneOn_one_sub_one_add_inv cfcₙ_nonneg_of_predicate
        (cfcₙ_nonneg_of_predicate.trans hab') hab'
