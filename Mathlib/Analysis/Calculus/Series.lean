/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.ContDiff
import Mathlib.Data.Nat.Cast.WithTop

#align_import analysis.calculus.series from "leanprover-community/mathlib"@"f2ce6086713c78a7f880485f7917ea547a215982"

/-!
# Smoothness of series

We show that series of functions are continuous, or differentiable, or smooth, when each individual
function in the series is and additionally suitable uniform summable bounds are satisfied.

More specifically,
* `continuous_tsum` ensures that a series of continuous functions is continuous.
* `differentiable_tsum` ensures that a series of differentiable functions is differentiable.
* `contDiff_tsum` ensures that a series of smooth functions is smooth.

We also give versions of these statements which are localized to a set.
-/


open Set Metric TopologicalSpace Function Asymptotics Filter

open scoped Topology NNReal BigOperators

variable {α β 𝕜 E F : Type*} [IsROrC 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [CompleteSpace F] {u : α → ℝ}

/-! ### Continuity -/


/-- An infinite sum of functions with summable sup norm is the uniform limit of its partial sums.
Version relative to a set, with general index set. -/
theorem tendstoUniformlyOn_tsum {f : α → β → F} (hu : Summable u) {s : Set β}
    (hfu : ∀ n x, x ∈ s → ‖f n x‖ ≤ u n) :
    TendstoUniformlyOn (fun t : Finset α => fun x => ∑ n in t, f n x) (fun x => ∑' n, f n x) atTop
      s := by
  refine' tendstoUniformlyOn_iff.2 fun ε εpos => _
  -- ⊢ ∀ᶠ (n : Finset α) in atTop, ∀ (x : β), x ∈ s → dist (∑' (n : α), f n x) (∑ n …
  filter_upwards [(tendsto_order.1 (tendsto_tsum_compl_atTop_zero u)).2 _ εpos]with t ht x hx
  -- ⊢ dist (∑' (n : α), f n x) (∑ n in t, f n x) < ε
  have A : Summable fun n => ‖f n x‖ :=
    summable_of_nonneg_of_le (fun n => norm_nonneg _) (fun n => hfu n x hx) hu
  rw [dist_eq_norm, ← sum_add_tsum_subtype_compl (summable_of_summable_norm A) t, add_sub_cancel']
  -- ⊢ ‖∑' (x_1 : { x // ¬x ∈ t }), f (↑x_1) x‖ < ε
  apply lt_of_le_of_lt _ ht
  -- ⊢ ‖∑' (x_1 : { x // ¬x ∈ t }), f (↑x_1) x‖ ≤ ∑' (b : { x // ¬x ∈ t }), u ↑b
  apply (norm_tsum_le_tsum_norm (A.subtype _)).trans
  -- ⊢ ∑' (i : ↑fun x => x ∈ t → False), ‖f (↑i) x‖ ≤ ∑' (b : { x // ¬x ∈ t }), u ↑b
  exact tsum_le_tsum (fun n => hfu _ _ hx) (A.subtype _) (hu.subtype _)
  -- 🎉 no goals
#align tendsto_uniformly_on_tsum tendstoUniformlyOn_tsum

/-- An infinite sum of functions with summable sup norm is the uniform limit of its partial sums.
Version relative to a set, with index set `ℕ`. -/
theorem tendstoUniformlyOn_tsum_nat {f : ℕ → β → F} {u : ℕ → ℝ} (hu : Summable u) {s : Set β}
    (hfu : ∀ n x, x ∈ s → ‖f n x‖ ≤ u n) :
    TendstoUniformlyOn (fun N => fun x => ∑ n in Finset.range N, f n x) (fun x => ∑' n, f n x) atTop
      s :=
  fun v hv => tendsto_finset_range.eventually (tendstoUniformlyOn_tsum hu hfu v hv)
#align tendsto_uniformly_on_tsum_nat tendstoUniformlyOn_tsum_nat

/-- An infinite sum of functions with summable sup norm is the uniform limit of its partial sums.
Version with general index set. -/
theorem tendstoUniformly_tsum {f : α → β → F} (hu : Summable u) (hfu : ∀ n x, ‖f n x‖ ≤ u n) :
    TendstoUniformly (fun t : Finset α => fun x => ∑ n in t, f n x) (fun x => ∑' n, f n x) atTop :=
  by rw [← tendstoUniformlyOn_univ]; exact tendstoUniformlyOn_tsum hu fun n x _ => hfu n x
     -- ⊢ TendstoUniformlyOn (fun t x => ∑ n in t, f n x) (fun x => ∑' (n : α), f n x) …
                                     -- 🎉 no goals
#align tendsto_uniformly_tsum tendstoUniformly_tsum

/-- An infinite sum of functions with summable sup norm is the uniform limit of its partial sums.
Version with index set `ℕ`. -/
theorem tendstoUniformly_tsum_nat {f : ℕ → β → F} {u : ℕ → ℝ} (hu : Summable u)
    (hfu : ∀ n x, ‖f n x‖ ≤ u n) :
    TendstoUniformly (fun N => fun x => ∑ n in Finset.range N, f n x) (fun x => ∑' n, f n x)
      atTop :=
  fun v hv => tendsto_finset_range.eventually (tendstoUniformly_tsum hu hfu v hv)
#align tendsto_uniformly_tsum_nat tendstoUniformly_tsum_nat

/-- An infinite sum of functions with summable sup norm is continuous on a set if each individual
function is. -/
theorem continuousOn_tsum [TopologicalSpace β] {f : α → β → F} {s : Set β}
    (hf : ∀ i, ContinuousOn (f i) s) (hu : Summable u) (hfu : ∀ n x, x ∈ s → ‖f n x‖ ≤ u n) :
    ContinuousOn (fun x => ∑' n, f n x) s := by
  classical
    refine' (tendstoUniformlyOn_tsum hu hfu).continuousOn (eventually_of_forall _)
    intro t
    exact continuousOn_finset_sum _ fun i _ => hf i
#align continuous_on_tsum continuousOn_tsum

/-- An infinite sum of functions with summable sup norm is continuous if each individual
function is. -/
theorem continuous_tsum [TopologicalSpace β] {f : α → β → F} (hf : ∀ i, Continuous (f i))
    (hu : Summable u) (hfu : ∀ n x, ‖f n x‖ ≤ u n) : Continuous fun x => ∑' n, f n x := by
  simp_rw [continuous_iff_continuousOn_univ] at hf ⊢
  -- ⊢ ContinuousOn (fun x => ∑' (n : α), f n x) univ
  exact continuousOn_tsum hf hu fun n x _ => hfu n x
  -- 🎉 no goals
#align continuous_tsum continuous_tsum

/-! ### Differentiability -/

variable [NormedSpace 𝕜 F]

variable {f : α → E → F} {f' : α → E → E →L[𝕜] F} {v : ℕ → α → ℝ} {s : Set E} {x₀ x : E} {N : ℕ∞}

/-- Consider a series of functions `∑' n, f n x` on a preconnected open set. If the series converges
at a point, and all functions in the series are differentiable with a summable bound on the
derivatives, then the series converges everywhere on the set. -/
theorem summable_of_summable_hasFDerivAt_of_isPreconnected (hu : Summable u) (hs : IsOpen s)
    (h's : IsPreconnected s) (hf : ∀ n x, x ∈ s → HasFDerivAt (f n) (f' n x) x)
    (hf' : ∀ n x, x ∈ s → ‖f' n x‖ ≤ u n) (hx₀ : x₀ ∈ s) (hf0 : Summable (f · x₀)) {x : E}
    (hx : x ∈ s) : Summable fun n => f n x := by
  rw [summable_iff_cauchySeq_finset] at hf0 ⊢
  -- ⊢ CauchySeq fun s => ∑ b in s, f b x
  have A : UniformCauchySeqOn (fun t : Finset α => fun x => ∑ i in t, f' i x) atTop s :=
    (tendstoUniformlyOn_tsum hu hf').uniformCauchySeqOn
  -- porting note: Lean 4 failed to find `f` by unification
  refine cauchy_map_of_uniformCauchySeqOn_fderiv (f := fun t x ↦ ∑ i in t, f i x)
    hs h's A (fun t y hy => ?_) hx₀ hx hf0
  exact HasFDerivAt.sum fun i _ => hf i y hy
  -- 🎉 no goals
#align summable_of_summable_has_fderiv_at_of_is_preconnected summable_of_summable_hasFDerivAt_of_isPreconnected

/-- Consider a series of functions `∑' n, f n x` on a preconnected open set. If the series converges
at a point, and all functions in the series are differentiable with a summable bound on the
derivatives, then the series is differentiable on the set and its derivative is the sum of the
derivatives. -/
theorem hasFDerivAt_tsum_of_isPreconnected (hu : Summable u) (hs : IsOpen s)
    (h's : IsPreconnected s) (hf : ∀ n x, x ∈ s → HasFDerivAt (f n) (f' n x) x)
    (hf' : ∀ n x, x ∈ s → ‖f' n x‖ ≤ u n) (hx₀ : x₀ ∈ s) (hf0 : Summable fun n => f n x₀)
    (hx : x ∈ s) : HasFDerivAt (fun y => ∑' n, f n y) (∑' n, f' n x) x := by
  classical
    have A :
      ∀ x : E, x ∈ s → Tendsto (fun t : Finset α => ∑ n in t, f n x) atTop (𝓝 (∑' n, f n x)) := by
      intro y hy
      apply Summable.hasSum
      exact summable_of_summable_hasFDerivAt_of_isPreconnected hu hs h's hf hf' hx₀ hf0 hy
    refine hasFDerivAt_of_tendstoUniformlyOn hs (tendstoUniformlyOn_tsum hu hf')
      (fun t y hy => ?_) A _ hx
    exact HasFDerivAt.sum fun n _ => hf n y hy
#align has_fderiv_at_tsum_of_is_preconnected hasFDerivAt_tsum_of_isPreconnected

/-- Consider a series of functions `∑' n, f n x`. If the series converges at a
point, and all functions in the series are differentiable with a summable bound on the derivatives,
then the series converges everywhere. -/
theorem summable_of_summable_hasFDerivAt (hu : Summable u)
    (hf : ∀ n x, HasFDerivAt (f n) (f' n x) x) (hf' : ∀ n x, ‖f' n x‖ ≤ u n)
    (hf0 : Summable fun n => f n x₀) (x : E) : Summable fun n => f n x := by
  let _ : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 _
  -- ⊢ Summable fun n => f n x
  exact summable_of_summable_hasFDerivAt_of_isPreconnected hu isOpen_univ isPreconnected_univ
    (fun n x _ => hf n x) (fun n x _ => hf' n x) (mem_univ _) hf0 (mem_univ _)
#align summable_of_summable_has_fderiv_at summable_of_summable_hasFDerivAt

/-- Consider a series of functions `∑' n, f n x`. If the series converges at a
point, and all functions in the series are differentiable with a summable bound on the derivatives,
then the series is differentiable and its derivative is the sum of the derivatives. -/
theorem hasFDerivAt_tsum (hu : Summable u) (hf : ∀ n x, HasFDerivAt (f n) (f' n x) x)
    (hf' : ∀ n x, ‖f' n x‖ ≤ u n) (hf0 : Summable fun n => f n x₀) (x : E) :
    HasFDerivAt (fun y => ∑' n, f n y) (∑' n, f' n x) x := by
  let : NormedSpace ℝ E; exact NormedSpace.restrictScalars ℝ 𝕜 _
  -- ⊢ NormedSpace ℝ E
                         -- ⊢ HasFDerivAt (fun y => ∑' (n : α), f n y) (∑' (n : α), f' n x) x
  exact hasFDerivAt_tsum_of_isPreconnected hu isOpen_univ isPreconnected_univ
    (fun n x _ => hf n x) (fun n x _ => hf' n x) (mem_univ _) hf0 (mem_univ _)
#align has_fderiv_at_tsum hasFDerivAt_tsum

/-- Consider a series of functions `∑' n, f n x`. If all functions in the series are differentiable
with a summable bound on the derivatives, then the series is differentiable.
Note that our assumptions do not ensure the pointwise convergence, but if there is no pointwise
convergence then the series is zero everywhere so the result still holds. -/
theorem differentiable_tsum (hu : Summable u) (hf : ∀ n x, HasFDerivAt (f n) (f' n x) x)
    (hf' : ∀ n x, ‖f' n x‖ ≤ u n) : Differentiable 𝕜 fun y => ∑' n, f n y := by
  by_cases h : ∃ x₀, Summable fun n => f n x₀
  -- ⊢ Differentiable 𝕜 fun y => ∑' (n : α), f n y
  · rcases h with ⟨x₀, hf0⟩
    -- ⊢ Differentiable 𝕜 fun y => ∑' (n : α), f n y
    intro x
    -- ⊢ DifferentiableAt 𝕜 (fun y => ∑' (n : α), f n y) x
    exact (hasFDerivAt_tsum hu hf hf' hf0 x).differentiableAt
    -- 🎉 no goals
  · push_neg at h
    -- ⊢ Differentiable 𝕜 fun y => ∑' (n : α), f n y
    have : (fun x => ∑' n, f n x) = 0 := by ext1 x; exact tsum_eq_zero_of_not_summable (h x)
    -- ⊢ Differentiable 𝕜 fun y => ∑' (n : α), f n y
    rw [this]
    -- ⊢ Differentiable 𝕜 0
    exact differentiable_const 0
    -- 🎉 no goals
#align differentiable_tsum differentiable_tsum

theorem fderiv_tsum_apply (hu : Summable u) (hf : ∀ n, Differentiable 𝕜 (f n))
    (hf' : ∀ n x, ‖fderiv 𝕜 (f n) x‖ ≤ u n) (hf0 : Summable fun n => f n x₀) (x : E) :
    fderiv 𝕜 (fun y => ∑' n, f n y) x = ∑' n, fderiv 𝕜 (f n) x :=
  (hasFDerivAt_tsum hu (fun n x => (hf n x).hasFDerivAt) hf' hf0 _).fderiv
#align fderiv_tsum_apply fderiv_tsum_apply

theorem fderiv_tsum (hu : Summable u) (hf : ∀ n, Differentiable 𝕜 (f n))
    (hf' : ∀ n x, ‖fderiv 𝕜 (f n) x‖ ≤ u n) {x₀ : E} (hf0 : Summable fun n => f n x₀) :
    (fderiv 𝕜 fun y => ∑' n, f n y) = fun x => ∑' n, fderiv 𝕜 (f n) x := by
  ext1 x
  -- ⊢ fderiv 𝕜 (fun y => ∑' (n : α), f n y) x = ∑' (n : α), fderiv 𝕜 (f n) x
  exact fderiv_tsum_apply hu hf hf' hf0 x
  -- 🎉 no goals
#align fderiv_tsum fderiv_tsum

/-! ### Higher smoothness -/

/-- Consider a series of smooth functions, with summable uniform bounds on the successive
derivatives. Then the iterated derivative of the sum is the sum of the iterated derivative. -/
theorem iteratedFDeriv_tsum (hf : ∀ i, ContDiff 𝕜 N (f i))
    (hv : ∀ k : ℕ, (k : ℕ∞) ≤ N → Summable (v k))
    (h'f : ∀ (k : ℕ) (i : α) (x : E), (k : ℕ∞) ≤ N → ‖iteratedFDeriv 𝕜 k (f i) x‖ ≤ v k i) {k : ℕ}
    (hk : (k : ℕ∞) ≤ N) :
    (iteratedFDeriv 𝕜 k fun y => ∑' n, f n y) = fun x => ∑' n, iteratedFDeriv 𝕜 k (f n) x := by
  induction' k with k IH
  -- ⊢ (iteratedFDeriv 𝕜 Nat.zero fun y => ∑' (n : α), f n y) = fun x => ∑' (n : α) …
  · ext1 x
    -- ⊢ iteratedFDeriv 𝕜 Nat.zero (fun y => ∑' (n : α), f n y) x = ∑' (n : α), itera …
    simp_rw [iteratedFDeriv_zero_eq_comp]
    -- ⊢ (↑(LinearIsometryEquiv.symm (continuousMultilinearCurryFin0 𝕜 E F)) ∘ fun y  …
    exact (continuousMultilinearCurryFin0 𝕜 E F).symm.toContinuousLinearEquiv.map_tsum
    -- 🎉 no goals
  · have h'k : (k : ℕ∞) < N := lt_of_lt_of_le (WithTop.coe_lt_coe.2 (Nat.lt_succ_self _)) hk
    -- ⊢ (iteratedFDeriv 𝕜 (Nat.succ k) fun y => ∑' (n : α), f n y) = fun x => ∑' (n  …
    have A : Summable fun n => iteratedFDeriv 𝕜 k (f n) 0 :=
      summable_of_norm_bounded (v k) (hv k h'k.le) fun n => h'f k n 0 h'k.le
    simp_rw [iteratedFDeriv_succ_eq_comp_left, IH h'k.le]
    -- ⊢ (↑(continuousMultilinearCurryLeftEquiv 𝕜 (fun x => E) F) ∘ fderiv 𝕜 fun x => …
    rw [fderiv_tsum (hv _ hk) (fun n => (hf n).differentiable_iteratedFDeriv h'k) _ A]
    -- ⊢ (↑(continuousMultilinearCurryLeftEquiv 𝕜 (fun x => E) F) ∘ fun x => ∑' (n :  …
    · ext1 x
      -- ⊢ (↑(continuousMultilinearCurryLeftEquiv 𝕜 (fun x => E) F) ∘ fun x => ∑' (n :  …
      exact (continuousMultilinearCurryLeftEquiv 𝕜
        (fun _ : Fin (k + 1) => E) F).toContinuousLinearEquiv.map_tsum
    · intro n x
      -- ⊢ ‖fderiv 𝕜 (fun x => iteratedFDeriv 𝕜 k (f n) x) x‖ ≤ v (Nat.succ k) n
      simpa only [iteratedFDeriv_succ_eq_comp_left, LinearIsometryEquiv.norm_map, comp_apply]
        using h'f k.succ n x hk
#align iterated_fderiv_tsum iteratedFDeriv_tsum

/-- Consider a series of smooth functions, with summable uniform bounds on the successive
derivatives. Then the iterated derivative of the sum is the sum of the iterated derivative. -/
theorem iteratedFDeriv_tsum_apply (hf : ∀ i, ContDiff 𝕜 N (f i))
    (hv : ∀ k : ℕ, (k : ℕ∞) ≤ N → Summable (v k))
    (h'f : ∀ (k : ℕ) (i : α) (x : E), (k : ℕ∞) ≤ N → ‖iteratedFDeriv 𝕜 k (f i) x‖ ≤ v k i) {k : ℕ}
    (hk : (k : ℕ∞) ≤ N) (x : E) :
    iteratedFDeriv 𝕜 k (fun y => ∑' n, f n y) x = ∑' n, iteratedFDeriv 𝕜 k (f n) x := by
  rw [iteratedFDeriv_tsum hf hv h'f hk]
  -- 🎉 no goals
#align iterated_fderiv_tsum_apply iteratedFDeriv_tsum_apply

/-- Consider a series of functions `∑' i, f i x`. Assume that each individual function `f i` is of
class `C^N`, and moreover there is a uniform summable upper bound on the `k`-th derivative
for each `k ≤ N`. Then the series is also `C^N`. -/
theorem contDiff_tsum (hf : ∀ i, ContDiff 𝕜 N (f i)) (hv : ∀ k : ℕ, (k : ℕ∞) ≤ N → Summable (v k))
    (h'f : ∀ (k : ℕ) (i : α) (x : E), (k : ℕ∞) ≤ N → ‖iteratedFDeriv 𝕜 k (f i) x‖ ≤ v k i) :
    ContDiff 𝕜 N fun x => ∑' i, f i x := by
  rw [contDiff_iff_continuous_differentiable]
  -- ⊢ (∀ (m : ℕ), ↑m ≤ N → Continuous fun x => iteratedFDeriv 𝕜 m (fun x => ∑' (i  …
  constructor
  -- ⊢ ∀ (m : ℕ), ↑m ≤ N → Continuous fun x => iteratedFDeriv 𝕜 m (fun x => ∑' (i : …
  · intro m hm
    -- ⊢ Continuous fun x => iteratedFDeriv 𝕜 m (fun x => ∑' (i : α), f i x) x
    rw [iteratedFDeriv_tsum hf hv h'f hm]
    -- ⊢ Continuous fun x => (fun x => ∑' (n : α), iteratedFDeriv 𝕜 m (f n) x) x
    refine' continuous_tsum _ (hv m hm) _
    -- ⊢ ∀ (i : α), Continuous fun x => iteratedFDeriv 𝕜 m (f i) x
    · intro i
      -- ⊢ Continuous fun x => iteratedFDeriv 𝕜 m (f i) x
      exact ContDiff.continuous_iteratedFDeriv hm (hf i)
      -- 🎉 no goals
    · intro n x
      -- ⊢ ‖iteratedFDeriv 𝕜 m (f n) x‖ ≤ v m n
      exact h'f _ _ _ hm
      -- 🎉 no goals
  · intro m hm
    -- ⊢ Differentiable 𝕜 fun x => iteratedFDeriv 𝕜 m (fun x => ∑' (i : α), f i x) x
    have h'm : ((m + 1 : ℕ) : ℕ∞) ≤ N := by
      simpa only [ENat.coe_add, Nat.cast_withBot, ENat.coe_one] using ENat.add_one_le_of_lt hm
    rw [iteratedFDeriv_tsum hf hv h'f hm.le]
    -- ⊢ Differentiable 𝕜 fun x => (fun x => ∑' (n : α), iteratedFDeriv 𝕜 m (f n) x) x
    have A :
      ∀ n x, HasFDerivAt (iteratedFDeriv 𝕜 m (f n)) (fderiv 𝕜 (iteratedFDeriv 𝕜 m (f n)) x) x :=
      fun n x => (ContDiff.differentiable_iteratedFDeriv hm (hf n)).differentiableAt.hasFDerivAt
    refine differentiable_tsum (hv _ h'm) A fun n x => ?_
    -- ⊢ ‖fderiv 𝕜 (iteratedFDeriv 𝕜 m (f n)) x‖ ≤ v (m + 1) n
    rw [fderiv_iteratedFDeriv, comp_apply, LinearIsometryEquiv.norm_map]
    -- ⊢ ‖iteratedFDeriv 𝕜 (m + 1) (f n) x‖ ≤ v (m + 1) n
    exact h'f _ _ _ h'm
    -- 🎉 no goals
#align cont_diff_tsum contDiff_tsum

/-- Consider a series of functions `∑' i, f i x`. Assume that each individual function `f i` is of
class `C^N`, and moreover there is a uniform summable upper bound on the `k`-th derivative
for each `k ≤ N` (except maybe for finitely many `i`s). Then the series is also `C^N`. -/
theorem contDiff_tsum_of_eventually (hf : ∀ i, ContDiff 𝕜 N (f i))
    (hv : ∀ k : ℕ, (k : ℕ∞) ≤ N → Summable (v k))
    (h'f :
      ∀ k : ℕ,
        (k : ℕ∞) ≤ N →
          ∀ᶠ i in (Filter.cofinite : Filter α), ∀ x : E, ‖iteratedFDeriv 𝕜 k (f i) x‖ ≤ v k i) :
    ContDiff 𝕜 N fun x => ∑' i, f i x := by
  classical
    refine contDiff_iff_forall_nat_le.2 fun m hm => ?_
    let t : Set α :=
      { i : α | ¬∀ k : ℕ, k ∈ Finset.range (m + 1) → ∀ x, ‖iteratedFDeriv 𝕜 k (f i) x‖ ≤ v k i }
    have ht : Set.Finite t :=
      haveI A :
        ∀ᶠ i in (Filter.cofinite : Filter α),
          ∀ k : ℕ, k ∈ Finset.range (m + 1) → ∀ x : E, ‖iteratedFDeriv 𝕜 k (f i) x‖ ≤ v k i := by
        rw [eventually_all_finset]
        intro i hi
        apply h'f
        simp only [Finset.mem_range_succ_iff] at hi
        exact (WithTop.coe_le_coe.2 hi).trans hm
      eventually_cofinite.2 A
    let T : Finset α := ht.toFinset
    have : (fun x => ∑' i, f i x) = (fun x => ∑ i in T, f i x) +
        fun x => ∑' i : { i // i ∉ T }, f i x := by
      ext1 x
      refine' (sum_add_tsum_subtype_compl _ T).symm
      refine' summable_of_norm_bounded_eventually _ (hv 0 (zero_le _)) _
      filter_upwards [h'f 0 (zero_le _)]with i hi
      simpa only [norm_iteratedFDeriv_zero] using hi x
    rw [this]
    apply (ContDiff.sum fun i _ => (hf i).of_le hm).add
    have h'u : ∀ k : ℕ, (k : ℕ∞) ≤ m → Summable (v k ∘ ((↑) : { i // i ∉ T } → α)) := fun k hk =>
      (hv k (hk.trans hm)).subtype _
    refine' contDiff_tsum (fun i => (hf i).of_le hm) h'u _
    rintro k ⟨i, hi⟩ x hk
    dsimp
    simp only [Finite.mem_toFinset, mem_setOf_eq, Finset.mem_range, not_forall, not_le,
      exists_prop, not_exists, not_and, not_lt] at hi
    exact hi k (Nat.lt_succ_iff.2 (WithTop.coe_le_coe.1 hk)) x
#align cont_diff_tsum_of_eventually contDiff_tsum_of_eventually
