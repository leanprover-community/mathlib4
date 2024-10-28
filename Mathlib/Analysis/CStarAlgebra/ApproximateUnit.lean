/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.PosPart
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow
import Mathlib.Topology.ApproximateUnit

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

variable {A : Type*} [NonUnitalCStarAlgebra A]

local notation "σₙ" => quasispectrum
local notation "σ" => spectrum

open Unitization NNReal CStarAlgebra

variable [PartialOrder A] [StarOrderedRing A]

lemma CFC.monotoneOn_one_sub_one_add_inv :
    MonotoneOn (cfcₙ (fun x : ℝ≥0 ↦ 1 - (1 + x)⁻¹)) (Set.Ici (0 : A)) := by
  intro a ha b hb hab
  simp only [Set.mem_Ici] at ha hb
  rw [← inr_le_iff .., nnreal_cfcₙ_eq_cfc_inr a _, nnreal_cfcₙ_eq_cfc_inr b _]
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
  exact rpow_neg_one_le_rpow_neg_one (add_nonneg zero_le_one ha) (by gcongr) <|
    isUnit_of_le isUnit_one zero_le_one <| le_add_of_nonneg_right ha

lemma Set.InvOn.one_sub_one_add_inv : Set.InvOn (fun x ↦ 1 - (1 + x)⁻¹) (fun x ↦ x * (1 - x)⁻¹)
    {x : ℝ≥0 | x < 1} {x : ℝ≥0 | x < 1} := by
  have h1_add {x : ℝ≥0} : 0 < 1 + (x : ℝ) := by positivity
  have : (fun x : ℝ≥0 ↦ x * (1 + x)⁻¹) = fun x ↦ 1 - (1 + x)⁻¹ := by
    ext x
    field_simp
    simp [sub_mul, inv_mul_cancel₀ h1_add.ne']
  rw [← this]
  constructor
  all_goals intro x (hx : x < 1)
  · have : 0 < 1 - x := tsub_pos_of_lt hx
    field_simp [tsub_add_cancel_of_le hx.le, tsub_tsub_cancel_of_le hx.le]
  · field_simp [mul_tsub]

lemma norm_cfcₙ_one_sub_one_add_inv_lt_one (a : A) :
    ‖cfcₙ (fun x : ℝ≥0 ↦ 1 - (1 + x)⁻¹) a‖ < 1 :=
  nnnorm_cfcₙ_nnreal_lt fun x _ ↦ tsub_lt_self zero_lt_one (by positivity)

-- the calls to `fun_prop` with a discharger set off the linter
set_option linter.style.multiGoal false in
lemma CStarAlgebra.directedOn_nonneg_ball :
    DirectedOn (· ≤ ·) ({x : A | 0 ≤ x} ∩ Metric.ball 0 1) := by
  let f : ℝ≥0 → ℝ≥0 := fun x => 1 - (1 + x)⁻¹
  let g : ℝ≥0 → ℝ≥0 := fun x => x * (1 - x)⁻¹
  suffices ∀ a b : A, 0 ≤ a → 0 ≤ b → ‖a‖ < 1 → ‖b‖ < 1 →
      a ≤ cfcₙ f (cfcₙ g a + cfcₙ g b) by
    rintro a ⟨(ha₁ : 0 ≤ a), ha₂⟩ b ⟨(hb₁ : 0 ≤ b), hb₂⟩
    simp only [Metric.mem_ball, dist_zero_right] at ha₂ hb₂
    refine ⟨cfcₙ f (cfcₙ g a + cfcₙ g b), ⟨by simp, ?_⟩, ?_, ?_⟩
    · simpa only [Metric.mem_ball, dist_zero_right] using norm_cfcₙ_one_sub_one_add_inv_lt_one _
    · exact this a b ha₁ hb₁ ha₂ hb₂
    · exact add_comm (cfcₙ g a) (cfcₙ g b) ▸ this b a hb₁ ha₁ hb₂ ha₂
  rintro a b ha₁ - ha₂ -
  calc
    a = cfcₙ (f ∘ g) a := by
      conv_lhs => rw [← cfcₙ_id ℝ≥0 a]
      refine cfcₙ_congr (Set.InvOn.one_sub_one_add_inv.1.eqOn.symm.mono fun x hx ↦ ?_)
      exact lt_of_le_of_lt (le_nnnorm_of_mem_quasispectrum hx) ha₂
    _ = cfcₙ f (cfcₙ g a) := by
      rw [cfcₙ_comp f g a ?_ (by simp [f, tsub_self]) ?_ (by simp [g]) ha₁]
      · fun_prop (disch := intro _ _; positivity)
      · have (x) (hx : x ∈ σₙ ℝ≥0 a) :  1 - x ≠ 0 := by
          refine tsub_pos_of_lt ?_ |>.ne'
          exact lt_of_le_of_lt (le_nnnorm_of_mem_quasispectrum hx) ha₂
        fun_prop (disch := assumption)
    _ ≤ cfcₙ f (cfcₙ g a + cfcₙ g b) := by
      have hab' : cfcₙ g a ≤ cfcₙ g a + cfcₙ g b := le_add_of_nonneg_right cfcₙ_nonneg_of_predicate
      exact CFC.monotoneOn_one_sub_one_add_inv cfcₙ_nonneg_of_predicate
        (cfcₙ_nonneg_of_predicate.trans hab') hab'

section NormedGroup

variable {E : Type*} [NormedGroup E]

@[to_additive]
theorem eq_one_or_norm_pos (a : E) : a = 1 ∨ 0 < ‖a‖ := by
  by_cases h : a = 1
  · exact Or.inl h
  · apply Or.inr
    simpa [← norm_pos_iff''] using h

@[to_additive]
theorem eq_one_or_nnnorm_pos (a : E) : a = 1 ∨ 0 < ‖a‖₊ :=
  eq_one_or_norm_pos a

end NormedGroup

section SpanNonneg

open Submodule

/-- A C⋆-algebra is spanned by nonnegative elements of norm at most `r` -/
lemma CStarAlgebra.span_nonneg_inter_closedBall {r : ℝ} (hr : 0 < r) :
    span ℂ ({x : A | 0 ≤ x} ∩ Metric.closedBall 0 r) = ⊤ := by
  rw [eq_top_iff, ← span_nonneg, span_le]
  intro x hx
  obtain (rfl | hx_pos) := eq_zero_or_norm_pos x
  · exact zero_mem _
  · suffices (r * ‖x‖⁻¹ : ℂ)⁻¹ • ((r * ‖x‖⁻¹ : ℂ) • x) = x by
      rw [← this]
      refine smul_mem _ _ (subset_span <| Set.mem_inter ?_ ?_)
      · norm_cast
        exact smul_nonneg (by positivity) hx
      · simp [mul_smul, norm_smul, abs_of_pos hr, inv_mul_cancel₀ hx_pos.ne']
    apply inv_smul_smul₀
    norm_cast
    positivity

/-- A C⋆-algebra is spanned by nonnegative elements of norm less than `r`. -/
lemma CStarAlgebra.span_nonneg_inter_ball {r : ℝ} (hr : 0 < r) :
    span ℂ ({x : A | 0 ≤ x} ∩ Metric.ball 0 r) = ⊤ := by
  rw [eq_top_iff, ← span_nonneg_inter_closedBall (half_pos hr)]
  gcongr
  exact Metric.closedBall_subset_ball <| half_lt_self hr

/-- A C⋆-algebra is spanned by nonnegative contractions. -/
lemma CStarAlgebra.span_nonneg_inter_unitClosedBall :
    span ℂ ({x : A | 0 ≤ x} ∩ Metric.closedBall 0 1) = ⊤ :=
  CStarAlgebra.span_nonneg_inter_closedBall zero_lt_one

/-- A C⋆-algebra is spanned by nonnegative strict contractions. -/
lemma CStarAlgebra.span_nonneg_inter_unitBall :
    span ℂ ({x : A | 0 ≤ x} ∩ Metric.ball 0 1) = ⊤ :=
  CStarAlgebra.span_nonneg_inter_ball zero_lt_one

end SpanNonneg

section ApproximateUnit

open Metric

/-- An *increasing approximate unit* in a C⋆-algebra is an approximate unit whose basis consists of
sets in the closed unit ball of nonnegative elements. -/
structure IncreasingApproximateUnit {ι : Type*} (p : ι → Prop) (s : ι → Set A) extends
    ApproximateUnit p s where
  nonneg' (i : ι) (hi : p i) : s i ⊆ {x | 0 ≤ x}
  subset_closedBall (i : ι) (hi : p i) : s i ⊆ closedBall 0 1

open Submodule Filter Topology in
abbrev IncreasingApproximateUnit.of_forall_nonneg_tendsto {ι : Type*} {l : Filter A} {p : ι → Prop}
    {s : ι → Set A} (hl : l.HasBasis p s) (hs : ∀ i, p i → s i ⊆ {x | 0 ≤ x} ∩ closedBall 0 1)
    (hs_nonempty : ∀ i, p i → (s i).Nonempty) (h : ∀ m, 0 ≤ m → ‖m‖ < 1 → Tendsto (· * m) l (𝓝 m)) :
    IncreasingApproximateUnit p s where
  toFilter := l
  toHasBasis := hl
  bounded := ⟨closedBall 0 1, isBounded_closedBall, (hs · · |>.trans Set.inter_subset_right)⟩
  nonneg' i hi := (hs i hi).trans Set.inter_subset_left
  subset_closedBall i hi := (hs i hi).trans Set.inter_subset_right
  neBot := hl.neBot_iff.mpr <| hs_nonempty _
  filter_le := by
    rw [mulLeftRightTendsto.le_iff, forall_and]
    refine and_iff_left_of_imp (fun h_left a ↦ ?_) |>.mpr fun a ↦ ?_
    · apply (star_star a ▸ (continuous_star.tendsto _ |>.comp <| h_left (star a))).congr'
      obtain ⟨i, hi⟩ := hl.ex_mem
      filter_upwards [hl.mem_of_mem hi] with x hx
      simp [IsSelfAdjoint.star_eq (.of_nonneg (hs i hi hx).1)]
    · obtain ⟨n, c, x, rfl⟩ := mem_span_set'.mp <| by
        show a ∈ span ℂ ({x | 0 ≤ x} ∩ ball 0 1)
        simp [CStarAlgebra.span_nonneg_inter_unitBall]
      simp_rw [Finset.mul_sum]
      refine tendsto_finset_sum _ fun i _ ↦ ?_
      simp_rw [mul_smul_comm]
      exact tendsto_const_nhds.smul <| h (x i) (x i).2.1 <| by simpa using (x i).2.2

lemma CStarAlgebra.pow_nonneg
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {a : A} (ha : 0 ≤ a) (n : ℕ) : 0 ≤ a ^ n := by
  rw [← cfc_pow_id (R := ℝ≥0) a]
  exact cfc_nonneg_of_predicate

lemma CStarAlgebra.pow_monotone_of_one_le
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {a : A} (ha : 1 ≤ a) : Monotone (a ^ · : ℕ → A) := by
  have ha' : 0 ≤ a := zero_le_one.trans ha
  intro n m hnm
  simp only
  rw [← cfc_pow_id (R := ℝ) a, ← cfc_pow_id (R := ℝ) a, cfc_le_iff ..]
  rw [CFC.one_le_iff (R := ℝ) a] at ha
  peel ha with x hx _
  exact pow_le_pow_right₀ (ha x hx) hnm

lemma CStarAlgebra.pow_antitone_of_le_one
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {a : A} (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1) : Antitone (a ^ · : ℕ → A) := by
  intro n m hnm
  simp only
  rw [← cfc_pow_id (R := ℝ) a, ← cfc_pow_id (R := ℝ) a, cfc_le_iff ..]
  rw [CFC.le_one_iff (R := ℝ) a] at ha₁
  peel ha₁ with x hx _
  exact pow_le_pow_of_le_one (spectrum_nonneg_of_nonneg ha₀ hx) (ha₁ x hx) hnm

theorem CStarAlgebra.nnnorm_le_nnnorm_of_nonneg_of_le
    {A : Type u_1} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {a : A} {b : A} (ha : 0 ≤ a := by cfc_tac) (hab : a ≤ b) :
    ‖a‖₊ ≤ ‖b‖₊ :=
  norm_le_norm_of_nonneg_of_le ha hab

theorem CStarAlgebra.extracted
    {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (x : A) (hx₁ : 0 ≤ x) (hx₂ : ‖x‖ < 1) (ε : ℝ) (hε : 0 < ε) (b : A) (hb₁ : 0 ≤ b)
    (hb₂ : b ∈ ball 0 1) (hb₃ : cfcₙ (fun y : ℝ≥0 ↦ 1 - (1 + y)⁻¹) (ε⁻¹ ^ 2 • x) ≤ b) :
    ‖star (x : A⁺¹) * ((1 - b) * (1 - b)) * x‖ ≤ ε ^ 2 := by
  set g : ℝ≥0 → ℝ≥0 := fun y ↦ 1 - (1 + y)⁻¹
  have hg : Continuous g := by
    rw [continuous_iff_continuousOn_univ]
    fun_prop (disch := intro _ _; positivity)
  simp only [mem_ball, dist_zero_right] at hb₂
  rw [← norm_inr (𝕜 := ℂ)] at hx₂ hb₂
  rw [← Unitization.inr_le_iff _ _ (.of_nonneg cfcₙ_nonneg_of_predicate) (.of_nonneg hb₁),
    Unitization.nnreal_cfcₙ_eq_cfc_inr _ _ (by simp [g, tsub_self]), inr_smul] at hb₃
  rw [← Unitization.inr_nonneg_iff] at hx₁ hb₁
  generalize (x : A⁺¹) = x, (b : A⁺¹) = b at hx₁ hx₂ hb₁ hb₂ hb₃
  rw [← sq]
  have hx₃ := norm_le_one_iff_of_nonneg x |>.mp hx₂.le
  have hb₄ := norm_le_one_iff_of_nonneg b |>.mp hb₂.le
  rw [← sub_nonneg] at hb₄
  lift ε to ℝ≥0 using hε.le
  rw [← coe_nnnorm]
  norm_cast at hε hb₃ ⊢
  rw [← NNReal.smul_def] at hb₃
  have hg' : ContinuousOn (fun y ↦ (1 + ε⁻¹ ^ 2 * y)⁻¹) (spectrum ℝ≥0 x) :=
    ContinuousOn.inv₀ (by fun_prop) fun _ _ ↦ by positivity
  have : star x * (1 - b) ^ 2 * x ≤ cfc (fun y ↦ y * (1 + ε⁻¹ ^ 2 * y)⁻¹ * y) x := calc
    star x * (1 - b) ^ 2 * x ≤ star x * (1 - b) * x := by
      refine conjugate_le_conjugate ?_ _
      simpa using pow_antitone_of_le_one hb₄ (sub_le_self 1 hb₁) one_le_two
    _ ≤ star x * (1 - cfc g (ε⁻¹ ^ 2 • x)) * x := conjugate_le_conjugate (by gcongr) _
    _ = cfc (fun y ↦ y * (1 + ε⁻¹ ^ 2 * y)⁻¹ * y) x := by
      rw [cfc_mul _ _ x (continuousOn_id' _ |>.mul hg') (continuousOn_id' _),
        cfc_mul _ _ x (continuousOn_id' _) hg', cfc_id' .., IsSelfAdjoint.star_eq (.of_nonneg hx₁)]
      congr
      rw [← cfc_one (R := ℝ≥0) x, ← cfc_comp_smul _ _ _ hg.continuousOn hx₁,
        ← cfc_tsub _ _ x (by simp [g]) hx₁ (by fun_prop) (Continuous.continuousOn <| by fun_prop)]
      refine cfc_congr (fun y _ ↦ ?_)
      simp [g, tsub_tsub_cancel_of_le]
  apply nnnorm_le_nnnorm_of_nonneg_of_le (conjugate_nonneg (pow_nonneg hb₄ 2) x) this |>.trans
  refine nnnorm_cfc_nnreal_le fun y hy ↦ ?_
  field_simp
  calc
    y * ε ^ 2 * y / (ε ^ 2 + y) ≤ ε ^ 2 * 1 := by
      rw [mul_div_assoc]
      gcongr
      · refine mul_le_of_le_one_left (zero_le _) ?_
        rw [← cfc_id' ℝ≥0 x, ← cfc_one (R := ℝ≥0) x,
          cfc_nnreal_le_iff _ _ _ (QuasispectrumRestricts.nnreal_of_nonneg hx₁)] at hx₃
        exact hx₃ y hy
      · exact div_le_one (by positivity) |>.mpr le_add_self
    _ = ε ^ 2 := mul_one _

open Metric Set Unitization in
/-- the approximate unit in a C⋆-algebra consisting of positive contractions of norm strictly
less than 1. -/
def CStarAlgebra.increasingApproximateUnit : IncreasingApproximateUnit
    (· ∈ {x : A | 0 ≤ x} ∩ ball 0 1) ({x | · ≤ x} ∩ ({x | 0 ≤ x} ∩ ball 0 1)) :=
  have basis := directedOn_nonneg_ball (A := A) |>.filterIsBasis ⟨0, by simp⟩ |>.hasBasis
  .of_forall_nonneg_tendsto basis
    (fun _ _ ↦ inter_subset_right.trans <| inter_subset_inter_right _ ball_subset_closedBall)
    (⟨·, Set.mem_inter le_rfl ·⟩) fun x hx₁ hx₂ ↦ by
      rw [basis.tendsto_iff nhds_basis_closedBall]
      intro ε hε
      refine ⟨cfcₙ (fun y : ℝ≥0 ↦ 1 - (1 + y)⁻¹) (ε⁻¹ ^ 2 • x),
        Set.mem_inter cfcₙ_nonneg_of_predicate (by simpa [- inv_pow, mem_closedBall_iff_norm]
          using norm_cfcₙ_one_sub_one_add_inv_lt_one _ (smul_nonneg (by positivity) hx₁)), ?_⟩
      rintro b ⟨(hb₁ : cfcₙ _ _ ≤ _), (hb₂ : 0 ≤ b), hb₃⟩
      rw [mem_closedBall_iff_norm, ← norm_inr (𝕜 := ℂ), inr_sub, inr_mul, norm_sub_rev]
      nth_rw 1 [← one_mul (x : A⁺¹)]
      rw [← sub_mul]
      refine abs_le_of_sq_le_sq' ?_ (by positivity) |>.2
      rw [sq, ← CStarRing.norm_star_mul_self, star_mul, ← mul_assoc, mul_assoc (star _),
        (IsSelfAdjoint.one A⁺¹ |>.sub <| (IsSelfAdjoint.of_nonneg hb₂).inr _).star_eq]
      exact extracted x hx₁ hx₂ ε hε b hb₂ hb₃ hb₁


end ApproximateUnit
