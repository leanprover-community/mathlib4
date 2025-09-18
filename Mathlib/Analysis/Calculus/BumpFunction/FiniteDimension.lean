/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Data.Set.Pointwise.Support
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Bump functions in finite-dimensional vector spaces

Let `E` be a finite-dimensional real normed vector space. We show that any open set `s` in `E` is
exactly the support of a smooth function taking values in `[0, 1]`,
in `IsOpen.exists_smooth_support_eq`.

Then we use this construction to construct bump functions with nice behavior, by convolving
the indicator function of `closedBall 0 1` with a function as above with `s = ball 0 D`.
-/


noncomputable section

open Set Metric TopologicalSpace Function Asymptotics MeasureTheory Module
  ContinuousLinearMap Filter MeasureTheory.Measure Bornology

open scoped Pointwise Topology NNReal Convolution ContDiff

variable {E : Type*} [NormedAddCommGroup E]

section

variable [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- If a set `s` is a neighborhood of `x`, then there exists a smooth function `f` taking
values in `[0, 1]`, supported in `s` and with `f x = 1`. -/
theorem exists_smooth_tsupport_subset {s : Set E} {x : E} (hs : s ∈ 𝓝 x) :
    ∃ f : E → ℝ,
      tsupport f ⊆ s ∧ HasCompactSupport f ∧ ContDiff ℝ ∞ f ∧ range f ⊆ Icc 0 1 ∧ f x = 1 := by
  obtain ⟨d : ℝ, d_pos : 0 < d, hd : Euclidean.closedBall x d ⊆ s⟩ :=
    Euclidean.nhds_basis_closedBall.mem_iff.1 hs
  let c : ContDiffBump (toEuclidean x) :=
    { rIn := d / 2
      rOut := d
      rIn_pos := half_pos d_pos
      rIn_lt_rOut := half_lt_self d_pos }
  let f : E → ℝ := c ∘ toEuclidean
  have f_supp : f.support ⊆ Euclidean.ball x d := by
    intro y hy
    have : toEuclidean y ∈ Function.support c := by
      simpa only [Function.mem_support, Function.comp_apply, Ne] using hy
    rwa [c.support_eq] at this
  have f_tsupp : tsupport f ⊆ Euclidean.closedBall x d := by
    rw [tsupport, ← Euclidean.closure_ball _ d_pos.ne']
    exact closure_mono f_supp
  refine ⟨f, f_tsupp.trans hd, ?_, ?_, ?_, ?_⟩
  · refine isCompact_of_isClosed_isBounded isClosed_closure ?_
    have : IsBounded (Euclidean.closedBall x d) := Euclidean.isCompact_closedBall.isBounded
    refine this.subset (Euclidean.isClosed_closedBall.closure_subset_iff.2 ?_)
    exact f_supp.trans Euclidean.ball_subset_closedBall
  · apply c.contDiff.comp
    exact ContinuousLinearEquiv.contDiff _
  · rintro t ⟨y, rfl⟩
    exact ⟨c.nonneg, c.le_one⟩
  · apply c.one_of_mem_closedBall
    apply mem_closedBall_self
    exact (half_pos d_pos).le

/-- Given an open set `s` in a finite-dimensional real normed vector space, there exists a smooth
function with values in `[0, 1]` whose support is exactly `s`. -/
theorem IsOpen.exists_smooth_support_eq {s : Set E} (hs : IsOpen s) :
    ∃ f : E → ℝ, f.support = s ∧ ContDiff ℝ ∞ f ∧ Set.range f ⊆ Set.Icc 0 1 := by
  /- For any given point `x` in `s`, one can construct a smooth function with support in `s` and
    nonzero at `x`. By second-countability, it follows that we may cover `s` with the supports of
    countably many such functions, say `g i`.
    Then `∑ i, r i • g i` will be the desired function if `r i` is a sequence of positive numbers
    tending quickly enough to zero. Indeed, this ensures that, for any `k ≤ i`, the `k`-th
    derivative of `r i • g i` is bounded by a prescribed (summable) sequence `u i`. From this, the
    summability of the series and of its successive derivatives follows. -/
  rcases eq_empty_or_nonempty s with (rfl | h's)
  · exact
      ⟨fun _ => 0, Function.support_zero, contDiff_const, by
        simp only [range_const, singleton_subset_iff, left_mem_Icc, zero_le_one]⟩
  let ι := { f : E → ℝ // f.support ⊆ s ∧ HasCompactSupport f ∧ ContDiff ℝ ∞ f ∧ range f ⊆ Icc 0 1 }
  obtain ⟨T, T_count, hT⟩ : ∃ T : Set ι, T.Countable ∧ ⋃ f ∈ T, support (f : E → ℝ) = s := by
    have : ⋃ f : ι, (f : E → ℝ).support = s := by
      refine Subset.antisymm (iUnion_subset fun f => f.2.1) ?_
      intro x hx
      rcases exists_smooth_tsupport_subset (hs.mem_nhds hx) with ⟨f, hf⟩
      let g : ι := ⟨f, (subset_tsupport f).trans hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1⟩
      have : x ∈ support (g : E → ℝ) := by
        simp only [g, hf.2.2.2.2, mem_support, Ne, one_ne_zero, not_false_iff]
      exact mem_iUnion_of_mem _ this
    simp_rw [← this]
    apply isOpen_iUnion_countable
    rintro ⟨f, hf⟩
    exact hf.2.2.1.continuous.isOpen_support
  obtain ⟨g0, hg⟩ : ∃ g0 : ℕ → ι, T = range g0 := by
    apply Countable.exists_eq_range T_count
    rcases eq_empty_or_nonempty T with (rfl | hT)
    · simp only [← hT, mem_empty_iff_false, iUnion_of_empty, iUnion_empty, Set.not_nonempty_empty]
        at h's
    · exact hT
  let g : ℕ → E → ℝ := fun n => (g0 n).1
  have g_s : ∀ n, support (g n) ⊆ s := fun n => (g0 n).2.1
  have s_g : ∀ x ∈ s, ∃ n, x ∈ support (g n) := fun x hx ↦ by
    rw [← hT] at hx
    obtain ⟨i, iT, hi⟩ : ∃ i ∈ T, x ∈ support (i : E → ℝ) := by
      simpa only [mem_iUnion, exists_prop] using hx
    grind
  have g_smooth : ∀ n, ContDiff ℝ ∞ (g n) := fun n => (g0 n).2.2.2.1
  have g_comp_supp : ∀ n, HasCompactSupport (g n) := fun n => (g0 n).2.2.1
  have g_nonneg : ∀ n x, 0 ≤ g n x := fun n x => ((g0 n).2.2.2.2 (mem_range_self x)).1
  obtain ⟨δ, δpos, c, δc, c_lt⟩ :
      ∃ δ : ℕ → ℝ≥0, (∀ i : ℕ, 0 < δ i) ∧ ∃ c : NNReal, HasSum δ c ∧ c < 1 :=
    NNReal.exists_pos_sum_of_countable one_ne_zero ℕ
  have : ∀ n : ℕ, ∃ r : ℝ, 0 < r ∧ ∀ i ≤ n, ∀ x, ‖iteratedFDeriv ℝ i (r • g n) x‖ ≤ δ n := by
    intro n
    have : ∀ i, ∃ R, ∀ x, ‖iteratedFDeriv ℝ i (fun x => g n x) x‖ ≤ R := by
      intro i
      have : BddAbove (range fun x => ‖iteratedFDeriv ℝ i (fun x : E => g n x) x‖) := by
        apply ((g_smooth n).continuous_iteratedFDeriv
          (mod_cast le_top)).norm.bddAbove_range_of_hasCompactSupport
        apply HasCompactSupport.comp_left _ norm_zero
        apply (g_comp_supp n).iteratedFDeriv
      rcases this with ⟨R, hR⟩
      exact ⟨R, fun x => hR (mem_range_self _)⟩
    choose R hR using this
    let M := max (((Finset.range (n + 1)).image R).max' (by simp)) 1
    have δnpos : 0 < δ n := δpos n
    have IR : ∀ i ≤ n, R i ≤ M := by
      intro i hi
      refine le_trans ?_ (le_max_left _ _)
      apply Finset.le_max'
      apply Finset.mem_image_of_mem
      simp only [Finset.mem_range]
      omega
    refine ⟨M⁻¹ * δ n, by positivity, fun i hi x => ?_⟩
    calc
      ‖iteratedFDeriv ℝ i ((M⁻¹ * δ n) • g n) x‖ = ‖(M⁻¹ * δ n) • iteratedFDeriv ℝ i (g n) x‖ := by
        rw [iteratedFDeriv_const_smul_apply]
        exact (g_smooth n).contDiffAt.of_le (mod_cast le_top)
      _ = M⁻¹ * δ n * ‖iteratedFDeriv ℝ i (g n) x‖ := by
        rw [norm_smul _ (iteratedFDeriv ℝ i (g n) x), Real.norm_of_nonneg]; positivity
      _ ≤ M⁻¹ * δ n * M := by gcongr; exact (hR i x).trans (IR i hi)
      _ = δ n := by simp [field]
  choose r rpos hr using this
  have S : ∀ x, Summable fun n => (r n • g n) x := fun x ↦ by
    refine .of_nnnorm_bounded δc.summable fun n => ?_
    rw [← NNReal.coe_le_coe, coe_nnnorm]
    simpa only [norm_iteratedFDeriv_zero] using hr n 0 (zero_le n) x
  refine ⟨fun x => ∑' n, (r n • g n) x, ?_, ?_, ?_⟩
  · apply Subset.antisymm
    · intro x hx
      simp only [Pi.smul_apply, Algebra.id.smul_eq_mul, mem_support, Ne] at hx
      contrapose! hx
      have : ∀ n, g n x = 0 := by
        intro n
        contrapose! hx
        exact g_s n hx
      simp only [this, mul_zero, tsum_zero]
    · intro x hx
      obtain ⟨n, hn⟩ : ∃ n, x ∈ support (g n) := s_g x hx
      have I : 0 < r n * g n x := mul_pos (rpos n) (lt_of_le_of_ne (g_nonneg n x) (Ne.symm hn))
      exact ne_of_gt ((S x).tsum_pos (fun i => mul_nonneg (rpos i).le (g_nonneg i x)) n I)
  · refine
      contDiff_tsum_of_eventually (fun n => (g_smooth n).const_smul (r n))
        (fun k _ => (NNReal.hasSum_coe.2 δc).summable) ?_
    intro i _
    simp only [Nat.cofinite_eq_atTop, Filter.eventually_atTop]
    exact ⟨i, fun n hn x => hr _ _ hn _⟩
  · rintro - ⟨y, rfl⟩
    refine ⟨tsum_nonneg fun n => mul_nonneg (rpos n).le (g_nonneg n y), le_trans ?_ c_lt.le⟩
    have A : HasSum (fun n => (δ n : ℝ)) c := NNReal.hasSum_coe.2 δc
    simp only [Pi.smul_apply, smul_eq_mul, NNReal.val_eq_coe, ← A.tsum_eq]
    apply Summable.tsum_le_tsum _ (S y) A.summable
    intro n
    apply (le_abs_self _).trans
    simpa only [norm_iteratedFDeriv_zero] using hr n 0 (zero_le n) y

end

section

namespace ExistsContDiffBumpBase

/-- An auxiliary function to construct partitions of unity on finite-dimensional real vector spaces.
It is the characteristic function of the closed unit ball. -/
def φ : E → ℝ :=
  (closedBall (0 : E) 1).indicator fun _ => (1 : ℝ)

variable [NormedSpace ℝ E] [FiniteDimensional ℝ E]

section HelperDefinitions

variable (E)

theorem u_exists :
    ∃ u : E → ℝ,
      ContDiff ℝ ∞ u ∧ (∀ x, u x ∈ Icc (0 : ℝ) 1) ∧ support u = ball 0 1 ∧ ∀ x, u (-x) = u x := by
  have A : IsOpen (ball (0 : E) 1) := isOpen_ball
  obtain ⟨f, f_support, f_smooth, f_range⟩ :
      ∃ f : E → ℝ, f.support = ball (0 : E) 1 ∧ ContDiff ℝ ∞ f ∧ Set.range f ⊆ Set.Icc 0 1 :=
    A.exists_smooth_support_eq
  have B : ∀ x, f x ∈ Icc (0 : ℝ) 1 := fun x => f_range (mem_range_self x)
  refine ⟨fun x => (f x + f (-x)) / 2, ?_, ?_, ?_, ?_⟩
  · exact (f_smooth.add (f_smooth.comp contDiff_neg)).div_const _
  · intro x
    simp only [mem_Icc]
    constructor
    · linarith [(B x).1, (B (-x)).1]
    · linarith [(B x).2, (B (-x)).2]
  · refine support_eq_iff.2 ⟨fun x hx => ?_, fun x hx => ?_⟩
    · apply ne_of_gt
      have : 0 < f x := by
        apply lt_of_le_of_ne (B x).1 (Ne.symm _)
        rwa [← f_support] at hx
      linarith [(B (-x)).1]
    · have I1 : x ∉ support f := by rwa [f_support]
      have I2 : -x ∉ support f := by
        rw [f_support]
        simpa using hx
      simp only [mem_support, Classical.not_not] at I1 I2
      simp only [I1, I2, add_zero, zero_div]
  · intro x; simp only [add_comm, neg_neg]

variable {E} in
/-- An auxiliary function to construct partitions of unity on finite-dimensional real vector spaces,
which is smooth, symmetric, and with support equal to the unit ball. -/
def u (x : E) : ℝ :=
  Classical.choose (u_exists E) x

theorem u_smooth : ContDiff ℝ ∞ (u : E → ℝ) :=
  (Classical.choose_spec (u_exists E)).1

theorem u_continuous : Continuous (u : E → ℝ) :=
  (u_smooth E).continuous

theorem u_support : support (u : E → ℝ) = ball 0 1 :=
  (Classical.choose_spec (u_exists E)).2.2.1

theorem u_compact_support : HasCompactSupport (u : E → ℝ) := by
  rw [hasCompactSupport_def, u_support, closure_ball (0 : E) one_ne_zero]
  exact isCompact_closedBall _ _

variable {E}

theorem u_nonneg (x : E) : 0 ≤ u x :=
  ((Classical.choose_spec (u_exists E)).2.1 x).1

theorem u_le_one (x : E) : u x ≤ 1 :=
  ((Classical.choose_spec (u_exists E)).2.1 x).2

theorem u_neg (x : E) : u (-x) = u x :=
  (Classical.choose_spec (u_exists E)).2.2.2 x

variable [MeasurableSpace E] [BorelSpace E]

local notation "μ" => MeasureTheory.Measure.addHaar

variable (E) in
theorem u_int_pos : 0 < ∫ x : E, u x ∂μ := by
  refine (integral_pos_iff_support_of_nonneg u_nonneg ?_).mpr ?_
  · exact (u_continuous E).integrable_of_hasCompactSupport (u_compact_support E)
  · rw [u_support]; exact measure_ball_pos _ _ zero_lt_one

/-- An auxiliary function to construct partitions of unity on finite-dimensional real vector spaces,
which is smooth, symmetric, with support equal to the ball of radius `D` and integral `1`. -/
def w (D : ℝ) (x : E) : ℝ :=
  ((∫ x : E, u x ∂μ) * |D| ^ finrank ℝ E)⁻¹ • u (D⁻¹ • x)

theorem w_def (D : ℝ) :
    (w D : E → ℝ) = fun x => ((∫ x : E, u x ∂μ) * |D| ^ finrank ℝ E)⁻¹ • u (D⁻¹ • x) := by
  ext1 x; rfl

theorem w_nonneg (D : ℝ) (x : E) : 0 ≤ w D x := by
  apply mul_nonneg _ (u_nonneg _)
  apply inv_nonneg.2
  apply mul_nonneg (u_int_pos E).le
  norm_cast
  apply pow_nonneg (abs_nonneg D)

theorem w_mul_φ_nonneg (D : ℝ) (x y : E) : 0 ≤ w D y * φ (x - y) :=
  mul_nonneg (w_nonneg D y) (indicator_nonneg (by simp only [zero_le_one, imp_true_iff]) _)

variable (E)

-- see https://github.com/leanprover-community/mathlib4/issues/29041
set_option linter.unusedSimpArgs false in
theorem w_integral {D : ℝ} (Dpos : 0 < D) : ∫ x : E, w D x ∂μ = 1 := by
  simp_rw [w, integral_smul]
  rw [integral_comp_inv_smul_of_nonneg μ (u : E → ℝ) Dpos.le, abs_of_nonneg Dpos.le, mul_comm]
  simp [field, (u_int_pos E).ne']

theorem w_support {D : ℝ} (Dpos : 0 < D) : support (w D : E → ℝ) = ball 0 D := by
  have B : D • ball (0 : E) 1 = ball 0 D := by
    rw [smul_unitBall Dpos.ne', Real.norm_of_nonneg Dpos.le]
  have C : D ^ finrank ℝ E ≠ 0 := by
    norm_cast
    exact pow_ne_zero _ Dpos.ne'
  simp only [w_def, Algebra.id.smul_eq_mul, support_mul, support_inv, univ_inter,
    support_comp_inv_smul₀ Dpos.ne', u_support, B, support_const (u_int_pos E).ne', support_const C,
    abs_of_nonneg Dpos.le]

theorem w_compact_support {D : ℝ} (Dpos : 0 < D) : HasCompactSupport (w D : E → ℝ) := by
  rw [hasCompactSupport_def, w_support E Dpos, closure_ball (0 : E) Dpos.ne']
  exact isCompact_closedBall _ _

variable {E}

/-- An auxiliary function to construct partitions of unity on finite-dimensional real vector spaces.
It is the convolution between a smooth function of integral `1` supported in the ball of radius `D`,
with the indicator function of the closed unit ball. Therefore, it is smooth, equal to `1` on the
ball of radius `1 - D`, with support equal to the ball of radius `1 + D`. -/
def y (D : ℝ) : E → ℝ :=
  w D ⋆[lsmul ℝ ℝ, μ] φ

theorem y_neg (D : ℝ) (x : E) : y D (-x) = y D x := by
  apply convolution_neg_of_neg_eq
  · filter_upwards with x
    simp only [w_def, mul_inv_rev, smul_neg, u_neg, smul_eq_mul]
  · filter_upwards with x
    simp only [φ, indicator, mem_closedBall, dist_zero_right, norm_neg]

theorem y_eq_one_of_mem_closedBall {D : ℝ} {x : E} (Dpos : 0 < D)
    (hx : x ∈ closedBall (0 : E) (1 - D)) : y D x = 1 := by
  change (w D ⋆[lsmul ℝ ℝ, μ] φ) x = 1
  have B : ∀ y : E, y ∈ ball x D → φ y = 1 := by
    have C : ball x D ⊆ ball 0 1 := by
      apply ball_subset_ball'
      simp only [mem_closedBall] at hx
      linarith only [hx]
    intro y hy
    simp only [φ, indicator, mem_closedBall, ite_eq_left_iff, not_le, zero_ne_one]
    intro h'y
    linarith only [mem_ball.1 (C hy), h'y]
  have Bx : φ x = 1 := B _ (mem_ball_self Dpos)
  have B' : ∀ y, y ∈ ball x D → φ y = φ x := by rw [Bx]; exact B
  rw [convolution_eq_right' _ (le_of_eq (w_support E Dpos)) B']
  simp only [lsmul_apply, Algebra.id.smul_eq_mul, integral_mul_const, w_integral E Dpos, Bx,
    one_mul]

theorem y_eq_zero_of_notMem_ball {D : ℝ} {x : E} (Dpos : 0 < D) (hx : x ∉ ball (0 : E) (1 + D)) :
    y D x = 0 := by
  change (w D ⋆[lsmul ℝ ℝ, μ] φ) x = 0
  have B : ∀ y, y ∈ ball x D → φ y = 0 := by
    intro y hy
    simp only [φ, indicator, mem_closedBall_zero_iff, ite_eq_right_iff, one_ne_zero]
    intro h'y
    have C : ball y D ⊆ ball 0 (1 + D) := by
      apply ball_subset_ball'
      rw [← dist_zero_right] at h'y
      linarith only [h'y]
    exact hx (C (mem_ball_comm.1 hy))
  have Bx : φ x = 0 := B _ (mem_ball_self Dpos)
  have B' : ∀ y, y ∈ ball x D → φ y = φ x := by rw [Bx]; exact B
  rw [convolution_eq_right' _ (le_of_eq (w_support E Dpos)) B']
  simp only [lsmul_apply, Algebra.id.smul_eq_mul, Bx, mul_zero, integral_const]

@[deprecated (since := "2025-05-23")] alias y_eq_zero_of_not_mem_ball := y_eq_zero_of_notMem_ball

theorem y_nonneg (D : ℝ) (x : E) : 0 ≤ y D x :=
  integral_nonneg (w_mul_φ_nonneg D x)

theorem y_le_one {D : ℝ} (x : E) (Dpos : 0 < D) : y D x ≤ 1 := by
  have A : (w D ⋆[lsmul ℝ ℝ, μ] φ) x ≤ (w D ⋆[lsmul ℝ ℝ, μ] 1) x := by
    apply
      convolution_mono_right_of_nonneg _ (w_nonneg D) (indicator_le_self' fun x _ => zero_le_one)
        fun _ => zero_le_one
    refine ((w_compact_support E Dpos).convolutionExists_left _ ?_
      (locallyIntegrable_const (1 : ℝ)) x).integrable
    exact continuous_const.mul ((u_continuous E).comp (continuous_id.const_smul _))
  have B : (w D ⋆[lsmul ℝ ℝ, μ] fun _ => (1 : ℝ)) x = 1 := by
    simp only [convolution, mul_one, lsmul_apply, Algebra.id.smul_eq_mul, w_integral E Dpos]
  exact A.trans (le_of_eq B)

theorem y_pos_of_mem_ball {D : ℝ} {x : E} (Dpos : 0 < D) (D_lt_one : D < 1)
    (hx : x ∈ ball (0 : E) (1 + D)) : 0 < y D x := by
  simp only [mem_ball_zero_iff] at hx
  refine (integral_pos_iff_support_of_nonneg (w_mul_φ_nonneg D x) ?_).2 ?_
  · have F_comp : HasCompactSupport (w D) := w_compact_support E Dpos
    have B : LocallyIntegrable (φ : E → ℝ) μ :=
      (locallyIntegrable_const _).indicator measurableSet_closedBall
    have C : Continuous (w D : E → ℝ) :=
      continuous_const.mul ((u_continuous E).comp (continuous_id.const_smul _))
    exact (F_comp.convolutionExists_left (lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ) C B x).integrable
  · set z := (D / (1 + D)) • x with hz
    have B : 0 < 1 + D := by linarith
    have C : ball z (D * (1 + D - ‖x‖) / (1 + D)) ⊆ support fun y : E => w D y * φ (x - y) := by
      intro y hy
      simp only [support_mul, w_support E Dpos]
      simp only [φ, mem_inter_iff, mem_support, Ne, indicator_apply_eq_zero,
        mem_closedBall_zero_iff, one_ne_zero, not_forall, not_false_iff, exists_prop, and_true]
      constructor
      · apply ball_subset_ball' _ hy
        simp only [hz, norm_smul, abs_of_nonneg Dpos.le, abs_of_nonneg B.le, dist_zero_right,
          Real.norm_eq_abs, abs_div]
        field_simp
        simp [div_le_iff₀ B]
      · have ID : ‖D / (1 + D) - 1‖ = 1 / (1 + D) := by
          rw [Real.norm_of_nonpos]
          · simp [field]
          · field_simp
            simp only [sub_add_cancel_right]
            apply div_nonpos_of_nonpos_of_nonneg _ B.le
            linarith only
        rw [← mem_closedBall_iff_norm']
        apply closedBall_subset_closedBall' _ (ball_subset_closedBall hy)
        rw [← one_smul ℝ x, dist_eq_norm, hz, ← sub_smul, one_smul, norm_smul, ID]
        field_simp
        rw [div_le_one_iff]
        exact Or.inl ⟨B, by nlinarith only [hx, D_lt_one]⟩
    apply lt_of_lt_of_le _ (measure_mono C)
    apply measure_ball_pos
    exact div_pos (mul_pos Dpos (by linarith only [hx])) B

variable (E)

theorem y_smooth : ContDiffOn ℝ ∞ (uncurry y) (Ioo (0 : ℝ) 1 ×ˢ (univ : Set E)) := by
  have hs : IsOpen (Ioo (0 : ℝ) (1 : ℝ)) := isOpen_Ioo
  have hk : IsCompact (closedBall (0 : E) 1) := ProperSpace.isCompact_closedBall _ _
  refine contDiffOn_convolution_left_with_param (lsmul ℝ ℝ) hs hk ?_ ?_ ?_
  · rintro p x hp hx
    simp only [w, mul_inv_rev, Algebra.id.smul_eq_mul, mul_eq_zero, inv_eq_zero]
    right
    contrapose! hx
    have : p⁻¹ • x ∈ support u := mem_support.2 hx
    simp only [u_support, norm_smul, mem_ball_zero_iff, Real.norm_eq_abs, abs_inv,
      abs_of_nonneg hp.1.le, ← div_eq_inv_mul, div_lt_one hp.1] at this
    rw [mem_closedBall_zero_iff]
    exact this.le.trans hp.2.le
  · exact (locallyIntegrable_const _).indicator measurableSet_closedBall
  · apply ContDiffOn.mul
    · norm_cast
      refine
        (contDiffOn_const.mul ?_).inv fun x hx =>
          ne_of_gt (mul_pos (u_int_pos E) (pow_pos (abs_pos_of_pos hx.1.1) (finrank ℝ E)))
      apply ContDiffOn.pow
      simp_rw [← Real.norm_eq_abs]
      apply ContDiffOn.norm ℝ
      · exact contDiffOn_fst
      · intro x hx; exact ne_of_gt hx.1.1
    · apply (u_smooth E).comp_contDiffOn
      exact ContDiffOn.smul (contDiffOn_fst.inv fun x hx => ne_of_gt hx.1.1) contDiffOn_snd

theorem y_support {D : ℝ} (Dpos : 0 < D) (D_lt_one : D < 1) :
    support (y D : E → ℝ) = ball (0 : E) (1 + D) :=
  support_eq_iff.2
    ⟨fun _ hx => (y_pos_of_mem_ball Dpos D_lt_one hx).ne', fun _ hx =>
      y_eq_zero_of_notMem_ball Dpos hx⟩

variable {E}

end HelperDefinitions

instance (priority := 100) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] : HasContDiffBump E := by
  refine ⟨⟨?_⟩⟩
  borelize E
  have IR : ∀ R : ℝ, 1 < R → 0 < (R - 1) / (R + 1) := by intro R hR; apply div_pos <;> linarith
  exact
    { toFun := fun R x => if 1 < R then y ((R - 1) / (R + 1)) (((R + 1) / 2)⁻¹ • x) else 0
      mem_Icc := fun R x => by
        simp only [mem_Icc]
        split_ifs with h
        · refine ⟨y_nonneg _ _, y_le_one _ (IR R h)⟩
        · simp only [le_refl, zero_le_one, and_self]
      symmetric := fun R x => by
        split_ifs
        · simp only [y_neg, smul_neg]
        · rfl
      smooth := by
        suffices
          ContDiffOn ℝ ∞
            (uncurry y ∘ fun p : ℝ × E => ((p.1 - 1) / (p.1 + 1), ((p.1 + 1) / 2)⁻¹ • p.2))
            (Ioi 1 ×ˢ univ) by
          apply this.congr
          rintro ⟨R, x⟩ ⟨hR : 1 < R, _⟩
          simp only [hR, uncurry_apply_pair, if_true, Function.comp_apply]
        apply (y_smooth E).comp
        · apply ContDiffOn.prodMk
          · refine
              (contDiffOn_fst.sub contDiffOn_const).div (contDiffOn_fst.add contDiffOn_const) ?_
            rintro ⟨R, x⟩ ⟨hR : 1 < R, _⟩
            apply ne_of_gt
            dsimp only
            linarith
          · apply ContDiffOn.smul _ contDiffOn_snd
            refine ((contDiffOn_fst.add contDiffOn_const).div_const _).inv ?_
            rintro ⟨R, x⟩ ⟨hR : 1 < R, _⟩
            apply ne_of_gt
            dsimp only
            linarith
        · rintro ⟨R, x⟩ ⟨hR : 1 < R, _⟩
          have A : 0 < (R - 1) / (R + 1) := by apply div_pos <;> linarith
          have B : (R - 1) / (R + 1) < 1 := by apply (div_lt_one _).2 <;> linarith
          simp only [prodMk_mem_set_prod_eq, mem_Ioo, mem_univ, and_true, A, B]
      eq_one := fun R hR x hx => by
        have A : 0 < R + 1 := by linarith
        simp only [hR, if_true]
        apply y_eq_one_of_mem_closedBall (IR R hR)
        simp only [norm_smul, inv_div, mem_closedBall_zero_iff, Real.norm_eq_abs, abs_div, abs_two,
          abs_of_nonneg A.le]
        calc
          2 / (R + 1) * ‖x‖ ≤ 2 / (R + 1) := mul_le_of_le_one_right (by positivity) hx
          _ = 1 - (R - 1) / (R + 1) := by field_simp; ring
      support := fun R hR => by
        have A : 0 < (R + 1) / 2 := by linarith
        have C : (R - 1) / (R + 1) < 1 := by apply (div_lt_one _).2 <;> linarith
        simp only [hR, if_true, support_comp_inv_smul₀ A.ne', y_support _ (IR R hR) C,
          _root_.smul_ball A.ne', Real.norm_of_nonneg A.le, smul_zero]
        refine congr (congr_arg ball (Eq.refl 0)) ?_
        field_simp; ring }

end ExistsContDiffBumpBase

end
