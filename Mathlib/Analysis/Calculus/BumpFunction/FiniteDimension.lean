/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.Calculus.Series
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Data.Set.Pointwise.Support

#align_import analysis.calculus.bump_function_findim from "leanprover-community/mathlib"@"fd5edc43dc4f10b85abfe544b88f82cf13c5f844"

/-!
# Bump functions in finite-dimensional vector spaces

Let `E` be a finite-dimensional real normed vector space. We show that any open set `s` in `E` is
exactly the support of a smooth function taking values in `[0, 1]`,
in `IsOpen.exists_smooth_support_eq`.

Then we use this construction to construct bump functions with nice behavior, by convolving
the indicator function of `closedBall 0 1` with a function as above with `s = ball 0 D`.
-/


noncomputable section

open Set Metric TopologicalSpace Function Asymptotics MeasureTheory FiniteDimensional
  ContinuousLinearMap Filter MeasureTheory.Measure

open scoped Pointwise Topology NNReal BigOperators Convolution

variable {E : Type*} [NormedAddCommGroup E]

section

variable [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- If a set `s` is a neighborhood of `x`, then there exists a smooth function `f` taking
values in `[0, 1]`, supported in `s` and with `f x = 1`. -/
theorem exists_smooth_tsupport_subset {s : Set E} {x : E} (hs : s ∈ 𝓝 x) :
    ∃ f : E → ℝ,
      tsupport f ⊆ s ∧ HasCompactSupport f ∧ ContDiff ℝ ⊤ f ∧ range f ⊆ Icc 0 1 ∧ f x = 1 := by
  obtain ⟨d : ℝ, d_pos : 0 < d, hd : Euclidean.closedBall x d ⊆ s⟩ :=
    Euclidean.nhds_basis_closedBall.mem_iff.1 hs
  let c : ContDiffBump (toEuclidean x) :=
    { rIn := d / 2
      rOut := d
      rIn_pos := half_pos d_pos
      rIn_lt_rOut := half_lt_self d_pos }
  let f : E → ℝ := c ∘ toEuclidean
  -- ⊢ ∃ f, tsupport f ⊆ s ∧ HasCompactSupport f ∧ ContDiff ℝ ⊤ f ∧ range f ⊆ Icc 0 …
  have f_supp : f.support ⊆ Euclidean.ball x d := by
    intro y hy
    have : toEuclidean y ∈ Function.support c := by
      simpa only [Function.mem_support, Function.comp_apply, Ne.def] using hy
    rwa [c.support_eq] at this
  have f_tsupp : tsupport f ⊆ Euclidean.closedBall x d := by
    rw [tsupport, ← Euclidean.closure_ball _ d_pos.ne']
    exact closure_mono f_supp
  refine' ⟨f, f_tsupp.trans hd, _, _, _, _⟩
  · refine' isCompact_of_isClosed_bounded isClosed_closure _
    -- ⊢ Metric.Bounded (tsupport f)
    have : Bounded (Euclidean.closedBall x d) := Euclidean.isCompact_closedBall.bounded
    -- ⊢ Metric.Bounded (tsupport f)
    apply this.mono _
    -- ⊢ tsupport f ⊆ Euclidean.closedBall x d
    refine' (IsClosed.closure_subset_iff Euclidean.isClosed_closedBall).2 _
    -- ⊢ support f ⊆ Euclidean.closedBall x d
    exact f_supp.trans Euclidean.ball_subset_closedBall
    -- 🎉 no goals
  · apply c.contDiff.comp
    -- ⊢ ContDiff ℝ ⊤ ↑toEuclidean
    exact ContinuousLinearEquiv.contDiff _
    -- 🎉 no goals
  · rintro t ⟨y, rfl⟩
    -- ⊢ f y ∈ Icc 0 1
    exact ⟨c.nonneg, c.le_one⟩
    -- 🎉 no goals
  · apply c.one_of_mem_closedBall
    -- ⊢ ↑toEuclidean x ∈ closedBall (↑toEuclidean x) c.rIn
    apply mem_closedBall_self
    -- ⊢ 0 ≤ c.rIn
    exact (half_pos d_pos).le
    -- 🎉 no goals
#align exists_smooth_tsupport_subset exists_smooth_tsupport_subset

/-- Given an open set `s` in a finite-dimensional real normed vector space, there exists a smooth
function with values in `[0, 1]` whose support is exactly `s`. -/
theorem IsOpen.exists_smooth_support_eq {s : Set E} (hs : IsOpen s) :
    ∃ f : E → ℝ, f.support = s ∧ ContDiff ℝ ⊤ f ∧ Set.range f ⊆ Set.Icc 0 1 := by
  /- For any given point `x` in `s`, one can construct a smooth function with support in `s` and
    nonzero at `x`. By second-countability, it follows that we may cover `s` with the supports of
    countably many such functions, say `g i`.
    Then `∑ i, r i • g i` will be the desired function if `r i` is a sequence of positive numbers
    tending quickly enough to zero. Indeed, this ensures that, for any `k ≤ i`, the `k`-th
    derivative of `r i • g i` is bounded by a prescribed (summable) sequence `u i`. From this, the
    summability of the series and of its successive derivatives follows. -/
  rcases eq_empty_or_nonempty s with (rfl | h's)
  -- ⊢ ∃ f, support f = ∅ ∧ ContDiff ℝ ⊤ f ∧ range f ⊆ Icc 0 1
  · exact
      ⟨fun _ => 0, Function.support_zero, contDiff_const, by
        simp only [range_const, singleton_subset_iff, left_mem_Icc, zero_le_one]⟩
  let ι := { f : E → ℝ // f.support ⊆ s ∧ HasCompactSupport f ∧ ContDiff ℝ ⊤ f ∧ range f ⊆ Icc 0 1 }
  -- ⊢ ∃ f, support f = s ∧ ContDiff ℝ ⊤ f ∧ range f ⊆ Icc 0 1
  obtain ⟨T, T_count, hT⟩ : ∃ T : Set ι, T.Countable ∧ ⋃ f ∈ T, support (f : E → ℝ) = s := by
    have : ⋃ f : ι, (f : E → ℝ).support = s := by
      refine' Subset.antisymm (iUnion_subset fun f => f.2.1) _
      intro x hx
      rcases exists_smooth_tsupport_subset (hs.mem_nhds hx) with ⟨f, hf⟩
      let g : ι := ⟨f, (subset_tsupport f).trans hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1⟩
      have : x ∈ support (g : E → ℝ) := by
        simp only [hf.2.2.2.2, Subtype.coe_mk, mem_support, Ne.def, one_ne_zero, not_false_iff]
      exact mem_iUnion_of_mem _ this
    simp_rw [← this]
    apply isOpen_iUnion_countable
    rintro ⟨f, hf⟩
    exact hf.2.2.1.continuous.isOpen_support
  obtain ⟨g0, hg⟩ : ∃ g0 : ℕ → ι, T = range g0 := by
    apply Countable.exists_eq_range T_count
    rcases eq_empty_or_nonempty T with (rfl | hT)
    · simp only [iUnion_false, iUnion_empty] at hT
      simp only [← hT, mem_empty_iff_false, iUnion_of_empty, iUnion_empty, Set.not_nonempty_empty]
          at h's
    · exact hT
  let g : ℕ → E → ℝ := fun n => (g0 n).1
  -- ⊢ ∃ f, support f = s ∧ ContDiff ℝ ⊤ f ∧ range f ⊆ Icc 0 1
  have g_s : ∀ n, support (g n) ⊆ s := fun n => (g0 n).2.1
  -- ⊢ ∃ f, support f = s ∧ ContDiff ℝ ⊤ f ∧ range f ⊆ Icc 0 1
  have s_g : ∀ x ∈ s, ∃ n, x ∈ support (g n) := by
    intro x hx
    rw [← hT] at hx
    obtain ⟨i, iT, hi⟩ : ∃ (i : ι) (_ : i ∈ T), x ∈ support (i : E → ℝ) := by
      simpa only [mem_iUnion] using hx
    rw [hg, mem_range] at iT
    rcases iT with ⟨n, hn⟩
    rw [← hn] at hi
    exact ⟨n, hi⟩
  have g_smooth : ∀ n, ContDiff ℝ ⊤ (g n) := fun n => (g0 n).2.2.2.1
  -- ⊢ ∃ f, support f = s ∧ ContDiff ℝ ⊤ f ∧ range f ⊆ Icc 0 1
  have g_comp_supp : ∀ n, HasCompactSupport (g n) := fun n => (g0 n).2.2.1
  -- ⊢ ∃ f, support f = s ∧ ContDiff ℝ ⊤ f ∧ range f ⊆ Icc 0 1
  have g_nonneg : ∀ n x, 0 ≤ g n x := fun n x => ((g0 n).2.2.2.2 (mem_range_self x)).1
  -- ⊢ ∃ f, support f = s ∧ ContDiff ℝ ⊤ f ∧ range f ⊆ Icc 0 1
  obtain ⟨δ, δpos, c, δc, c_lt⟩ :
    ∃ δ : ℕ → ℝ≥0, (∀ i : ℕ, 0 < δ i) ∧ ∃ c : NNReal, HasSum δ c ∧ c < 1
  exact NNReal.exists_pos_sum_of_countable one_ne_zero ℕ
  -- ⊢ ∃ f, support f = s ∧ ContDiff ℝ ⊤ f ∧ range f ⊆ Icc 0 1
  have : ∀ n : ℕ, ∃ r : ℝ, 0 < r ∧ ∀ i ≤ n, ∀ x, ‖iteratedFDeriv ℝ i (r • g n) x‖ ≤ δ n := by
    intro n
    have : ∀ i, ∃ R, ∀ x, ‖iteratedFDeriv ℝ i (fun x => g n x) x‖ ≤ R := by
      intro i
      have : BddAbove (range fun x => ‖iteratedFDeriv ℝ i (fun x : E => g n x) x‖) := by
        apply
          ((g_smooth n).continuous_iteratedFDeriv le_top).norm.bddAbove_range_of_hasCompactSupport
        apply HasCompactSupport.comp_left _ norm_zero
        apply (g_comp_supp n).iteratedFDeriv
      rcases this with ⟨R, hR⟩
      exact ⟨R, fun x => hR (mem_range_self _)⟩
    choose R hR using this
    let M := max (((Finset.range (n + 1)).image R).max' (by simp)) 1
    have δnpos : 0 < δ n := δpos n
    have IR : ∀ i ≤ n, R i ≤ M := by
      intro i hi
      refine' le_trans _ (le_max_left _ _)
      apply Finset.le_max'
      apply Finset.mem_image_of_mem
      -- Porting note: was
      -- simp only [Finset.mem_range]
      -- linarith
      simpa only [Finset.mem_range, Nat.lt_add_one_iff]
    refine' ⟨M⁻¹ * δ n, by positivity, fun i hi x => _⟩
    calc
      ‖iteratedFDeriv ℝ i ((M⁻¹ * δ n) • g n) x‖ = ‖(M⁻¹ * δ n) • iteratedFDeriv ℝ i (g n) x‖ := by
        rw [iteratedFDeriv_const_smul_apply]; exact (g_smooth n).of_le le_top
      _ = M⁻¹ * δ n * ‖iteratedFDeriv ℝ i (g n) x‖ := by
        rw [norm_smul, Real.norm_of_nonneg]; positivity
      _ ≤ M⁻¹ * δ n * M := (mul_le_mul_of_nonneg_left ((hR i x).trans (IR i hi)) (by positivity))
      _ = δ n := by field_simp
  choose r rpos hr using this
  -- ⊢ ∃ f, support f = s ∧ ContDiff ℝ ⊤ f ∧ range f ⊆ Icc 0 1
  have S : ∀ x, Summable fun n => (r n • g n) x := by
    intro x
    refine' summable_of_nnnorm_bounded _ δc.summable fun n => _
    rw [← NNReal.coe_le_coe, coe_nnnorm]
    simpa only [norm_iteratedFDeriv_zero] using hr n 0 (zero_le n) x
  refine' ⟨fun x => ∑' n, (r n • g n) x, _, _, _⟩
  · apply Subset.antisymm
    -- ⊢ (support fun x => ∑' (n : ℕ), (r n • g n) x) ⊆ s
    · intro x hx
      -- ⊢ x ∈ s
      simp only [Pi.smul_apply, Algebra.id.smul_eq_mul, mem_support, Ne.def] at hx
      -- ⊢ x ∈ s
      contrapose! hx
      -- ⊢ ∑' (n : ℕ), r n * ↑(g0 n) x = 0
      have : ∀ n, g n x = 0 := by
        intro n
        contrapose! hx
        exact g_s n hx
      simp only [this, mul_zero, tsum_zero]
      -- 🎉 no goals
    · intro x hx
      -- ⊢ x ∈ support fun x => ∑' (n : ℕ), (r n • g n) x
      obtain ⟨n, hn⟩ : ∃ n, x ∈ support (g n); exact s_g x hx
      -- ⊢ ∃ n, x ∈ support (g n)
                                               -- ⊢ x ∈ support fun x => ∑' (n : ℕ), (r n • g n) x
      have I : 0 < r n * g n x := mul_pos (rpos n) (lt_of_le_of_ne (g_nonneg n x) (Ne.symm hn))
      -- ⊢ x ∈ support fun x => ∑' (n : ℕ), (r n • g n) x
      exact ne_of_gt (tsum_pos (S x) (fun i => mul_nonneg (rpos i).le (g_nonneg i x)) n I)
      -- 🎉 no goals
  · refine'
      contDiff_tsum_of_eventually (fun n => (g_smooth n).const_smul (r n))
        (fun k _ => (NNReal.hasSum_coe.2 δc).summable) _
    intro i _
    -- ⊢ ∀ᶠ (i_1 : ℕ) in Filter.cofinite, ∀ (x : E), ‖iteratedFDeriv ℝ i (fun x => (r …
    simp only [Nat.cofinite_eq_atTop, Pi.smul_apply, Algebra.id.smul_eq_mul,
      Filter.eventually_atTop, ge_iff_le]
    exact ⟨i, fun n hn x => hr _ _ hn _⟩
    -- 🎉 no goals
  · rintro - ⟨y, rfl⟩
    -- ⊢ (fun x => ∑' (n : ℕ), (r n • g n) x) y ∈ Icc 0 1
    refine' ⟨tsum_nonneg fun n => mul_nonneg (rpos n).le (g_nonneg n y), le_trans _ c_lt.le⟩
    -- ⊢ (fun x => ∑' (n : ℕ), (r n • g n) x) y ≤ (fun a => ↑a) c
    have A : HasSum (fun n => (δ n : ℝ)) c := NNReal.hasSum_coe.2 δc
    -- ⊢ (fun x => ∑' (n : ℕ), (r n • g n) x) y ≤ (fun a => ↑a) c
    simp only [Pi.smul_apply, smul_eq_mul, NNReal.val_eq_coe, ← A.tsum_eq, ge_iff_le]
    -- ⊢ ∑' (n : ℕ), r n * ↑(g0 n) y ≤ ∑' (b : ℕ), ↑(δ b)
    apply tsum_le_tsum _ (S y) A.summable
    -- ⊢ ∀ (i : ℕ), (r i • g i) y ≤ ↑(δ i)
    intro n
    -- ⊢ (r n • g n) y ≤ ↑(δ n)
    apply (le_abs_self _).trans
    -- ⊢ |(r n • g n) y| ≤ ↑(δ n)
    simpa only [norm_iteratedFDeriv_zero] using hr n 0 (zero_le n) y
    -- 🎉 no goals
#align is_open.exists_smooth_support_eq IsOpen.exists_smooth_support_eq

end

section

namespace ExistsContDiffBumpBase

/-- An auxiliary function to construct partitions of unity on finite-dimensional real vector spaces.
It is the characteristic function of the closed unit ball. -/
def φ : E → ℝ :=
  (closedBall (0 : E) 1).indicator fun _ => (1 : ℝ)
#align exists_cont_diff_bump_base.φ ExistsContDiffBumpBase.φ

variable [NormedSpace ℝ E] [FiniteDimensional ℝ E]

section HelperDefinitions

variable (E)

theorem u_exists :
    ∃ u : E → ℝ,
      ContDiff ℝ ⊤ u ∧ (∀ x, u x ∈ Icc (0 : ℝ) 1) ∧ support u = ball 0 1 ∧ ∀ x, u (-x) = u x := by
  have A : IsOpen (ball (0 : E) 1) := isOpen_ball
  -- ⊢ ∃ u, ContDiff ℝ ⊤ u ∧ (∀ (x : E), u x ∈ Icc 0 1) ∧ support u = ball 0 1 ∧ ∀  …
  obtain ⟨f, f_support, f_smooth, f_range⟩ :
    ∃ f : E → ℝ, f.support = ball (0 : E) 1 ∧ ContDiff ℝ ⊤ f ∧ Set.range f ⊆ Set.Icc 0 1
  exact A.exists_smooth_support_eq
  -- ⊢ ∃ u, ContDiff ℝ ⊤ u ∧ (∀ (x : E), u x ∈ Icc 0 1) ∧ support u = ball 0 1 ∧ ∀  …
  have B : ∀ x, f x ∈ Icc (0 : ℝ) 1 := fun x => f_range (mem_range_self x)
  -- ⊢ ∃ u, ContDiff ℝ ⊤ u ∧ (∀ (x : E), u x ∈ Icc 0 1) ∧ support u = ball 0 1 ∧ ∀  …
  refine' ⟨fun x => (f x + f (-x)) / 2, _, _, _, _⟩
  · exact (f_smooth.add (f_smooth.comp contDiff_neg)).div_const _
    -- 🎉 no goals
  · intro x
    -- ⊢ (fun x => (f x + f (-x)) / 2) x ∈ Icc 0 1
    simp only [mem_Icc]
    -- ⊢ 0 ≤ (f x + f (-x)) / 2 ∧ (f x + f (-x)) / 2 ≤ 1
    constructor
    -- ⊢ 0 ≤ (f x + f (-x)) / 2
    · linarith [(B x).1, (B (-x)).1]
      -- 🎉 no goals
    · linarith [(B x).2, (B (-x)).2]
      -- 🎉 no goals
  · refine' support_eq_iff.2 ⟨fun x hx => _, fun x hx => _⟩
    -- ⊢ (f x + f (-x)) / 2 ≠ 0
    · apply ne_of_gt
      -- ⊢ 0 < (f x + f (-x)) / 2
      have : 0 < f x := by
        apply lt_of_le_of_ne (B x).1 (Ne.symm _)
        rwa [← f_support] at hx
      linarith [(B (-x)).1]
      -- 🎉 no goals
    · have I1 : x ∉ support f := by rwa [f_support]
      -- ⊢ (f x + f (-x)) / 2 = 0
      have I2 : -x ∉ support f := by
        rw [f_support]
        simpa using hx
      simp only [mem_support, Classical.not_not] at I1 I2
      -- ⊢ (f x + f (-x)) / 2 = 0
      simp only [I1, I2, add_zero, zero_div]
      -- 🎉 no goals
  · intro x; simp only [add_comm, neg_neg]
    -- ⊢ (fun x => (f x + f (-x)) / 2) (-x) = (fun x => (f x + f (-x)) / 2) x
             -- 🎉 no goals
#align exists_cont_diff_bump_base.u_exists ExistsContDiffBumpBase.u_exists

variable {E}

/-- An auxiliary function to construct partitions of unity on finite-dimensional real vector spaces,
which is smooth, symmetric, and with support equal to the unit ball. -/
def u (x : E) : ℝ :=
  Classical.choose (u_exists E) x
#align exists_cont_diff_bump_base.u ExistsContDiffBumpBase.u

variable (E)

theorem u_smooth : ContDiff ℝ ⊤ (u : E → ℝ) :=
  (Classical.choose_spec (u_exists E)).1
#align exists_cont_diff_bump_base.u_smooth ExistsContDiffBumpBase.u_smooth

theorem u_continuous : Continuous (u : E → ℝ) :=
  (u_smooth E).continuous
#align exists_cont_diff_bump_base.u_continuous ExistsContDiffBumpBase.u_continuous

theorem u_support : support (u : E → ℝ) = ball 0 1 :=
  (Classical.choose_spec (u_exists E)).2.2.1
#align exists_cont_diff_bump_base.u_support ExistsContDiffBumpBase.u_support

theorem u_compact_support : HasCompactSupport (u : E → ℝ) := by
  rw [hasCompactSupport_def, u_support, closure_ball (0 : E) one_ne_zero]
  -- ⊢ IsCompact (closedBall 0 1)
  exact isCompact_closedBall _ _
  -- 🎉 no goals
#align exists_cont_diff_bump_base.u_compact_support ExistsContDiffBumpBase.u_compact_support

variable {E}

theorem u_nonneg (x : E) : 0 ≤ u x :=
  ((Classical.choose_spec (u_exists E)).2.1 x).1
#align exists_cont_diff_bump_base.u_nonneg ExistsContDiffBumpBase.u_nonneg

theorem u_le_one (x : E) : u x ≤ 1 :=
  ((Classical.choose_spec (u_exists E)).2.1 x).2
#align exists_cont_diff_bump_base.u_le_one ExistsContDiffBumpBase.u_le_one

theorem u_neg (x : E) : u (-x) = u x :=
  (Classical.choose_spec (u_exists E)).2.2.2 x
#align exists_cont_diff_bump_base.u_neg ExistsContDiffBumpBase.u_neg

variable [MeasurableSpace E] [BorelSpace E]

local notation "μ" => MeasureTheory.Measure.addHaar

variable (E)

theorem u_int_pos : 0 < ∫ x : E, u x ∂μ := by
  refine' (integral_pos_iff_support_of_nonneg u_nonneg _).mpr _
  -- ⊢ Integrable fun i => u i
  · exact (u_continuous E).integrable_of_hasCompactSupport (u_compact_support E)
    -- 🎉 no goals
  · rw [u_support]; exact measure_ball_pos _ _ zero_lt_one
    -- ⊢ 0 < ↑↑μ (ball 0 1)
                    -- 🎉 no goals
#align exists_cont_diff_bump_base.u_int_pos ExistsContDiffBumpBase.u_int_pos

variable {E}
-- porting note: `W` upper case
set_option linter.uppercaseLean3 false

/-- An auxiliary function to construct partitions of unity on finite-dimensional real vector spaces,
which is smooth, symmetric, with support equal to the ball of radius `D` and integral `1`. -/
def w (D : ℝ) (x : E) : ℝ :=
  ((∫ x : E, u x ∂μ) * |D| ^ finrank ℝ E)⁻¹ • u (D⁻¹ • x)
#align exists_cont_diff_bump_base.W ExistsContDiffBumpBase.w

theorem w_def (D : ℝ) :
    (w D : E → ℝ) = fun x => ((∫ x : E, u x ∂μ) * |D| ^ finrank ℝ E)⁻¹ • u (D⁻¹ • x) := by
  ext1 x; rfl
  -- ⊢ w D x = ((∫ (x : E), u x ∂μ) * |D| ^ ↑(finrank ℝ E))⁻¹ • u (D⁻¹ • x)
          -- 🎉 no goals
#align exists_cont_diff_bump_base.W_def ExistsContDiffBumpBase.w_def

theorem w_nonneg (D : ℝ) (x : E) : 0 ≤ w D x := by
  apply mul_nonneg _ (u_nonneg _)
  -- ⊢ 0 ≤ ((∫ (x : E), u x ∂μ) * |D| ^ ↑(finrank ℝ E))⁻¹
  apply inv_nonneg.2
  -- ⊢ 0 ≤ (∫ (x : E), u x ∂μ) * |D| ^ ↑(finrank ℝ E)
  apply mul_nonneg (u_int_pos E).le
  -- ⊢ 0 ≤ |D| ^ ↑(finrank ℝ E)
  norm_cast
  -- ⊢ 0 ≤ |D| ^ finrank ℝ E
  apply pow_nonneg (abs_nonneg D)
  -- 🎉 no goals
#align exists_cont_diff_bump_base.W_nonneg ExistsContDiffBumpBase.w_nonneg

theorem w_mul_φ_nonneg (D : ℝ) (x y : E) : 0 ≤ w D y * φ (x - y) :=
  mul_nonneg (w_nonneg D y) (indicator_nonneg (by simp only [zero_le_one, imp_true_iff]) _)
                                                  -- 🎉 no goals
#align exists_cont_diff_bump_base.W_mul_φ_nonneg ExistsContDiffBumpBase.w_mul_φ_nonneg

variable (E)

theorem w_integral {D : ℝ} (Dpos : 0 < D) : ∫ x : E, w D x ∂μ = 1 := by
  simp_rw [w, integral_smul]
  -- ⊢ ((∫ (x : E), u x ∂μ) * |D| ^ ↑(finrank ℝ E))⁻¹ • ∫ (a : E), u (D⁻¹ • a) ∂μ = 1
  rw [integral_comp_inv_smul_of_nonneg μ (u : E → ℝ) Dpos.le, abs_of_nonneg Dpos.le, mul_comm]
  -- ⊢ (D ^ ↑(finrank ℝ E) * ∫ (x : E), u x ∂μ)⁻¹ • D ^ finrank ℝ E • ∫ (x : E), u  …
  field_simp [(u_int_pos E).ne']
  -- 🎉 no goals
#align exists_cont_diff_bump_base.W_integral ExistsContDiffBumpBase.w_integral

theorem w_support {D : ℝ} (Dpos : 0 < D) : support (w D : E → ℝ) = ball 0 D := by
  have B : D • ball (0 : E) 1 = ball 0 D := by
    rw [smul_unitBall Dpos.ne', Real.norm_of_nonneg Dpos.le]
  have C : D ^ finrank ℝ E ≠ 0 := by
    norm_cast
    exact pow_ne_zero _ Dpos.ne'
  simp only [w_def, Algebra.id.smul_eq_mul, support_mul, support_inv, univ_inter,
    support_comp_inv_smul₀ Dpos.ne', u_support, B, support_const (u_int_pos E).ne', support_const C,
    abs_of_nonneg Dpos.le]
#align exists_cont_diff_bump_base.W_support ExistsContDiffBumpBase.w_support

theorem w_compact_support {D : ℝ} (Dpos : 0 < D) : HasCompactSupport (w D : E → ℝ) := by
  rw [hasCompactSupport_def, w_support E Dpos, closure_ball (0 : E) Dpos.ne']
  -- ⊢ IsCompact (closedBall 0 D)
  exact isCompact_closedBall _ _
  -- 🎉 no goals
#align exists_cont_diff_bump_base.W_compact_support ExistsContDiffBumpBase.w_compact_support

variable {E}

/-- An auxiliary function to construct partitions of unity on finite-dimensional real vector spaces.
It is the convolution between a smooth function of integral `1` supported in the ball of radius `D`,
with the indicator function of the closed unit ball. Therefore, it is smooth, equal to `1` on the
ball of radius `1 - D`, with support equal to the ball of radius `1 + D`. -/
def y (D : ℝ) : E → ℝ :=
  w D ⋆[lsmul ℝ ℝ, μ] φ
#align exists_cont_diff_bump_base.Y ExistsContDiffBumpBase.y

theorem y_neg (D : ℝ) (x : E) : y D (-x) = y D x := by
  apply convolution_neg_of_neg_eq
  -- ⊢ ∀ᵐ (x : E) ∂μ, w D (-x) = w D x
  · apply eventually_of_forall fun x => _
    -- ⊢ ∀ (x : E), w D (-x) = w D x
    simp only [w_def, Real.rpow_nat_cast, mul_inv_rev, smul_neg, u_neg, smul_eq_mul, forall_const]
    -- 🎉 no goals
  · apply eventually_of_forall fun x => _
    -- ⊢ ∀ (x : E), φ (-x) = φ x
    simp only [φ, indicator, mem_closedBall, dist_zero_right, norm_neg, forall_const]
    -- 🎉 no goals
#align exists_cont_diff_bump_base.Y_neg ExistsContDiffBumpBase.y_neg

theorem y_eq_one_of_mem_closedBall {D : ℝ} {x : E} (Dpos : 0 < D)
    (hx : x ∈ closedBall (0 : E) (1 - D)) : y D x = 1 := by
  change (w D ⋆[lsmul ℝ ℝ, μ] φ) x = 1
  -- ⊢ w D ⋆[lsmul ℝ ℝ, x] φ = 1
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
  -- ⊢ w D ⋆[lsmul ℝ ℝ, x] φ = 1
  have B' : ∀ y, y ∈ ball x D → φ y = φ x := by rw [Bx]; exact B
  -- ⊢ w D ⋆[lsmul ℝ ℝ, x] φ = 1
  rw [convolution_eq_right' _ (le_of_eq (w_support E Dpos)) B']
  -- ⊢ ∫ (t : E), ↑(↑(lsmul ℝ ℝ) (w D t)) (φ x) ∂μ = 1
  simp only [lsmul_apply, Algebra.id.smul_eq_mul, integral_mul_right, w_integral E Dpos, Bx,
    one_mul]
#align exists_cont_diff_bump_base.Y_eq_one_of_mem_closed_ball ExistsContDiffBumpBase.y_eq_one_of_mem_closedBall

theorem y_eq_zero_of_not_mem_ball {D : ℝ} {x : E} (Dpos : 0 < D) (hx : x ∉ ball (0 : E) (1 + D)) :
    y D x = 0 := by
  change (w D ⋆[lsmul ℝ ℝ, μ] φ) x = 0
  -- ⊢ w D ⋆[lsmul ℝ ℝ, x] φ = 0
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
  -- ⊢ w D ⋆[lsmul ℝ ℝ, x] φ = 0
  have B' : ∀ y, y ∈ ball x D → φ y = φ x := by rw [Bx]; exact B
  -- ⊢ w D ⋆[lsmul ℝ ℝ, x] φ = 0
  rw [convolution_eq_right' _ (le_of_eq (w_support E Dpos)) B']
  -- ⊢ ∫ (t : E), ↑(↑(lsmul ℝ ℝ) (w D t)) (φ x) ∂μ = 0
  simp only [lsmul_apply, Algebra.id.smul_eq_mul, Bx, mul_zero, integral_const]
  -- 🎉 no goals
#align exists_cont_diff_bump_base.Y_eq_zero_of_not_mem_ball ExistsContDiffBumpBase.y_eq_zero_of_not_mem_ball

theorem y_nonneg (D : ℝ) (x : E) : 0 ≤ y D x :=
  integral_nonneg (w_mul_φ_nonneg D x)
#align exists_cont_diff_bump_base.Y_nonneg ExistsContDiffBumpBase.y_nonneg

theorem y_le_one {D : ℝ} (x : E) (Dpos : 0 < D) : y D x ≤ 1 := by
  have A : (w D ⋆[lsmul ℝ ℝ, μ] φ) x ≤ (w D ⋆[lsmul ℝ ℝ, μ] 1) x := by
    apply
      convolution_mono_right_of_nonneg _ (w_nonneg D) (indicator_le_self' fun x _ => zero_le_one)
        fun _ => zero_le_one
    refine'
      (HasCompactSupport.convolutionExistsLeft _ (w_compact_support E Dpos) _
          (locallyIntegrable_const (1 : ℝ)) x).integrable
    exact continuous_const.mul ((u_continuous E).comp (continuous_id.const_smul _))
  have B : (w D ⋆[lsmul ℝ ℝ, μ] fun _ => (1 : ℝ)) x = 1 := by
    simp only [convolution, ContinuousLinearMap.map_smul, mul_inv_rev, coe_smul', mul_one,
      lsmul_apply, Algebra.id.smul_eq_mul, integral_mul_left, w_integral E Dpos, Pi.smul_apply]
  exact A.trans (le_of_eq B)
  -- 🎉 no goals
#align exists_cont_diff_bump_base.Y_le_one ExistsContDiffBumpBase.y_le_one

theorem y_pos_of_mem_ball {D : ℝ} {x : E} (Dpos : 0 < D) (D_lt_one : D < 1)
    (hx : x ∈ ball (0 : E) (1 + D)) : 0 < y D x := by
  simp only [mem_ball_zero_iff] at hx
  -- ⊢ 0 < y D x
  refine' (integral_pos_iff_support_of_nonneg (w_mul_φ_nonneg D x) _).2 _
  -- ⊢ Integrable fun i => w D i * φ (x - i)
  · have F_comp : HasCompactSupport (w D) := w_compact_support E Dpos
    -- ⊢ Integrable fun i => w D i * φ (x - i)
    have B : LocallyIntegrable (φ : E → ℝ) μ :=
      (locallyIntegrable_const _).indicator measurableSet_closedBall
    have C : Continuous (w D : E → ℝ) :=
      continuous_const.mul ((u_continuous E).comp (continuous_id.const_smul _))
    exact
      (HasCompactSupport.convolutionExistsLeft (lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ) F_comp C B
          x).integrable
  · set z := (D / (1 + D)) • x with hz
    -- ⊢ 0 < ↑↑μ (support fun i => w D i * φ (x - i))
    have B : 0 < 1 + D := by linarith
    -- ⊢ 0 < ↑↑μ (support fun i => w D i * φ (x - i))
    have C : ball z (D * (1 + D - ‖x‖) / (1 + D)) ⊆ support fun y : E => w D y * φ (x - y) := by
      intro y hy
      simp only [support_mul, w_support E Dpos]
      simp only [φ, mem_inter_iff, mem_support, Ne.def, indicator_apply_eq_zero,
        mem_closedBall_zero_iff, one_ne_zero, not_forall, not_false_iff, exists_prop, and_true_iff]
      constructor
      · apply ball_subset_ball' _ hy
        simp only [hz, norm_smul, abs_of_nonneg Dpos.le, abs_of_nonneg B.le, dist_zero_right,
          Real.norm_eq_abs, abs_div]
        simp only [div_le_iff B, field_simps]
        ring_nf
        rfl
      · have ID : ‖D / (1 + D) - 1‖ = 1 / (1 + D) := by
          rw [Real.norm_of_nonpos]
          · simp only [B.ne', Ne.def, not_false_iff, mul_one, neg_sub, add_tsub_cancel_right,
              field_simps]
          · simp only [B.ne', Ne.def, not_false_iff, mul_one, field_simps]
            apply div_nonpos_of_nonpos_of_nonneg _ B.le
            linarith only
        rw [← mem_closedBall_iff_norm']
        apply closedBall_subset_closedBall' _ (ball_subset_closedBall hy)
        rw [← one_smul ℝ x, dist_eq_norm, hz, ← sub_smul, one_smul, norm_smul, ID]
        simp only [B.ne', div_le_iff B, field_simps]
        nlinarith only [hx, D_lt_one]
    apply lt_of_lt_of_le _ (measure_mono C)
    -- ⊢ 0 < ↑↑μ (ball z (D * (1 + D - ‖x‖) / (1 + D)))
    apply measure_ball_pos
    -- ⊢ 0 < D * (1 + D - ‖x‖) / (1 + D)
    exact div_pos (mul_pos Dpos (by linarith only [hx])) B
    -- 🎉 no goals
#align exists_cont_diff_bump_base.Y_pos_of_mem_ball ExistsContDiffBumpBase.y_pos_of_mem_ball

variable (E)

theorem y_smooth : ContDiffOn ℝ ⊤ (uncurry y) (Ioo (0 : ℝ) 1 ×ˢ (univ : Set E)) := by
  have hs : IsOpen (Ioo (0 : ℝ) (1 : ℝ)) := isOpen_Ioo
  -- ⊢ ContDiffOn ℝ ⊤ (uncurry y) (Ioo 0 1 ×ˢ univ)
  have hk : IsCompact (closedBall (0 : E) 1) := ProperSpace.isCompact_closedBall _ _
  -- ⊢ ContDiffOn ℝ ⊤ (uncurry y) (Ioo 0 1 ×ˢ univ)
  refine' contDiffOn_convolution_left_with_param (lsmul ℝ ℝ) hs hk _ _ _
  · rintro p x hp hx
    -- ⊢ w p x = 0
    simp only [w, mul_inv_rev, Algebra.id.smul_eq_mul, mul_eq_zero, inv_eq_zero]
    -- ⊢ (|p| ^ ↑(finrank ℝ E) = 0 ∨ ∫ (x : E), u x ∂μ = 0) ∨ u (p⁻¹ • x) = 0
    right
    -- ⊢ u (p⁻¹ • x) = 0
    contrapose! hx
    -- ⊢ x ∈ closedBall 0 1
    have : p⁻¹ • x ∈ support u := mem_support.2 hx
    -- ⊢ x ∈ closedBall 0 1
    simp only [u_support, norm_smul, mem_ball_zero_iff, Real.norm_eq_abs, abs_inv,
      abs_of_nonneg hp.1.le, ← div_eq_inv_mul, div_lt_one hp.1] at this
    rw [mem_closedBall_zero_iff]
    -- ⊢ ‖x‖ ≤ 1
    exact this.le.trans hp.2.le
    -- 🎉 no goals
  · exact (locallyIntegrable_const _).indicator measurableSet_closedBall
    -- 🎉 no goals
  · apply ContDiffOn.mul
    -- ⊢ ContDiffOn ℝ ⊤ (fun x => ((∫ (x : E), u x ∂μ) * |x.fst| ^ ↑(finrank ℝ E))⁻¹) …
    · norm_cast
      -- ⊢ ContDiffOn ℝ ⊤ (fun x => ((∫ (x : E), u x ∂μ) * |x.fst| ^ finrank ℝ E)⁻¹) (I …
      refine'
        (contDiffOn_const.mul _).inv fun x hx =>
          ne_of_gt (mul_pos (u_int_pos E) (pow_pos (abs_pos_of_pos hx.1.1) (finrank ℝ E)))
      apply ContDiffOn.pow
      -- ⊢ ContDiffOn ℝ ⊤ (fun y => |y.fst|) (Ioo 0 1 ×ˢ univ)
      simp_rw [← Real.norm_eq_abs]
      -- ⊢ ContDiffOn ℝ ⊤ (fun y => ‖y.fst‖) (Ioo 0 1 ×ˢ univ)
      apply @ContDiffOn.norm ℝ
      -- ⊢ ContDiffOn ℝ ⊤ (fun y => y.fst) (Ioo 0 1 ×ˢ univ)
      · exact contDiffOn_fst
        -- 🎉 no goals
      · intro x hx; exact ne_of_gt hx.1.1
        -- ⊢ x.fst ≠ 0
                    -- 🎉 no goals
    · apply (u_smooth E).comp_contDiffOn
      -- ⊢ ContDiffOn ℝ ⊤ (fun x => x.fst⁻¹ • x.snd) (Ioo 0 1 ×ˢ univ)
      exact ContDiffOn.smul (contDiffOn_fst.inv fun x hx => ne_of_gt hx.1.1) contDiffOn_snd
      -- 🎉 no goals
#align exists_cont_diff_bump_base.Y_smooth ExistsContDiffBumpBase.y_smooth

theorem y_support {D : ℝ} (Dpos : 0 < D) (D_lt_one : D < 1) :
    support (y D : E → ℝ) = ball (0 : E) (1 + D) :=
  support_eq_iff.2
    ⟨fun _ hx => (y_pos_of_mem_ball Dpos D_lt_one hx).ne', fun _ hx =>
      y_eq_zero_of_not_mem_ball Dpos hx⟩
#align exists_cont_diff_bump_base.Y_support ExistsContDiffBumpBase.y_support

variable {E}

end HelperDefinitions

instance (priority := 100) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] : HasContDiffBump E := by
  refine' ⟨⟨_⟩⟩
  -- ⊢ ContDiffBumpBase E
  borelize E
  -- ⊢ ContDiffBumpBase E
  have IR : ∀ R : ℝ, 1 < R → 0 < (R - 1) / (R + 1) := by intro R hR; apply div_pos <;> linarith
  -- ⊢ ContDiffBumpBase E
  exact
    { toFun := fun R x => if 1 < R then y ((R - 1) / (R + 1)) (((R + 1) / 2)⁻¹ • x) else 0
      mem_Icc := fun R x => by
        simp only [mem_Icc]
        split_ifs with h
        · refine' ⟨y_nonneg _ _, y_le_one _ (IR R h)⟩
        · simp only [le_refl, zero_le_one, and_self]
      symmetric := fun R x => by
        simp only
        split_ifs
        · simp only [y_neg, smul_neg]
        · rfl
      smooth := by
        suffices
          ContDiffOn ℝ ⊤
            (uncurry y ∘ fun p : ℝ × E => ((p.1 - 1) / (p.1 + 1), ((p.1 + 1) / 2)⁻¹ • p.2))
            (Ioi 1 ×ˢ univ) by
          apply this.congr
          rintro ⟨R, x⟩ ⟨hR : 1 < R, _⟩
          simp only [hR, uncurry_apply_pair, if_true, Function.comp_apply]
        apply (y_smooth E).comp
        · apply ContDiffOn.prod
          · refine'
              (contDiffOn_fst.sub contDiffOn_const).div (contDiffOn_fst.add contDiffOn_const) _
            rintro ⟨R, x⟩ ⟨hR : 1 < R, _⟩
            apply ne_of_gt
            dsimp only
            linarith
          · apply ContDiffOn.smul _ contDiffOn_snd
            refine' ((contDiffOn_fst.add contDiffOn_const).div_const _).inv _
            rintro ⟨R, x⟩ ⟨hR : 1 < R, _⟩
            apply ne_of_gt
            dsimp only
            linarith
        · rintro ⟨R, x⟩ ⟨hR : 1 < R, _⟩
          have A : 0 < (R - 1) / (R + 1) := by apply div_pos <;> linarith
          have B : (R - 1) / (R + 1) < 1 := by apply (div_lt_one _).2 <;> linarith
          simp only [mem_preimage, prod_mk_mem_set_prod_eq, mem_Ioo, mem_univ, and_true_iff, A, B]
      eq_one := fun R hR x hx => by
        have A : 0 < R + 1 := by linarith
        simp only [hR, if_true]
        apply y_eq_one_of_mem_closedBall (IR R hR)
        simp only [norm_smul, inv_div, mem_closedBall_zero_iff, Real.norm_eq_abs, abs_div, abs_two,
          abs_of_nonneg A.le]
        calc
          2 / (R + 1) * ‖x‖ ≤ 2 / (R + 1) * 1 :=
            mul_le_mul_of_nonneg_left hx (div_nonneg zero_le_two A.le)
          _ = 1 - (R - 1) / (R + 1) := by field_simp; ring
      support := fun R hR => by
        have A : 0 < (R + 1) / 2 := by linarith
        have A' : 0 < R + 1 := by linarith
        have C : (R - 1) / (R + 1) < 1 := by apply (div_lt_one _).2 <;> linarith
        simp only [hR, if_true, support_comp_inv_smul₀ A.ne', y_support _ (IR R hR) C,
          _root_.smul_ball A.ne', Real.norm_of_nonneg A.le, smul_zero]
        refine' congr (congr_arg ball (Eq.refl 0)) _
        field_simp; ring }

end ExistsContDiffBumpBase

end
