/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# Smoothness of series

We show that series of functions are differentiable, or smooth, when each individual
function in the series is and additionally suitable uniform summable bounds are satisfied.

More specifically,
* `differentiable_tsum` ensures that a series of differentiable functions is differentiable.
* `contDiff_tsum` ensures that a series of `C^n` functions is `C^n`.

We also give versions of these statements which are localized to a set.
-/


open Set Metric TopologicalSpace Function Asymptotics Filter

open scoped Topology NNReal

variable {α β 𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [CompleteSpace F] {u : α → ℝ}

/-! ### Differentiability -/

variable [NormedSpace 𝕜 F]
variable {f : α → E → F} {f' : α → E → E →L[𝕜] F} {g : α → 𝕜 → F} {g' : α → 𝕜 → F} {v : ℕ → α → ℝ}
  {s : Set E} {t : Set 𝕜} {x₀ x : E} {y₀ y : 𝕜} {N : ℕ∞}

/-- Consider a series of functions `∑' n, f n x` on a preconnected open set. If the series converges
at a point, and all functions in the series are differentiable with a summable bound on the
derivatives, then the series converges everywhere on the set. -/
theorem summable_of_summable_hasFDerivAt_of_isPreconnected (hu : Summable u) (hs : IsOpen s)
    (h's : IsPreconnected s) (hf : ∀ n x, x ∈ s → HasFDerivAt (f n) (f' n x) x)
    (hf' : ∀ n x, x ∈ s → ‖f' n x‖ ≤ u n) (hx₀ : x₀ ∈ s) (hf0 : Summable (f · x₀))
    (hx : x ∈ s) : Summable fun n => f n x := by
  haveI := Classical.decEq α
  rw [summable_iff_cauchySeq_finset] at hf0 ⊢
  have A : UniformCauchySeqOn (fun t : Finset α => fun x => ∑ i ∈ t, f' i x) atTop s :=
    (tendstoUniformlyOn_tsum hu hf').uniformCauchySeqOn
  refine cauchy_map_of_uniformCauchySeqOn_fderiv (f := fun t x ↦ ∑ i ∈ t, f i x)
    hs h's A (fun t y hy => ?_) hx₀ hx hf0
  exact HasFDerivAt.fun_sum fun i _ => hf i y hy

/-- Consider a series of functions `∑' n, f n x` on a preconnected open set. If the series converges
at a point, and all functions in the series are differentiable with a summable bound on the
derivatives, then the series converges everywhere on the set. -/
theorem summable_of_summable_hasDerivAt_of_isPreconnected (hu : Summable u) (ht : IsOpen t)
    (h't : IsPreconnected t) (hg : ∀ n y, y ∈ t → HasDerivAt (g n) (g' n y) y)
    (hg' : ∀ n y, y ∈ t → ‖g' n y‖ ≤ u n) (hy₀ : y₀ ∈ t) (hg0 : Summable (g · y₀))
    (hy : y ∈ t) : Summable fun n => g n y := by
  simp_rw [hasDerivAt_iff_hasFDerivAt] at hg
  refine summable_of_summable_hasFDerivAt_of_isPreconnected hu ht h't hg ?_ hy₀ hg0 hy
  simpa

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
      ∀ x : E, x ∈ s → Tendsto (fun t : Finset α => ∑ n ∈ t, f n x) atTop (𝓝 (∑' n, f n x)) := by
      intro y hy
      apply Summable.hasSum
      exact summable_of_summable_hasFDerivAt_of_isPreconnected hu hs h's hf hf' hx₀ hf0 hy
    refine hasFDerivAt_of_tendstoUniformlyOn hs (tendstoUniformlyOn_tsum hu hf')
      (fun t y hy => ?_) A hx
    exact HasFDerivAt.fun_sum fun n _ => hf n y hy

/-- Consider a series of functions `∑' n, f n x` on a preconnected open set. If the series converges
at a point, and all functions in the series are differentiable with a summable bound on the
derivatives, then the series is differentiable on the set and its derivative is the sum of the
derivatives. -/
theorem hasDerivAt_tsum_of_isPreconnected (hu : Summable u) (ht : IsOpen t)
    (h't : IsPreconnected t) (hg : ∀ n y, y ∈ t → HasDerivAt (g n) (g' n y) y)
    (hg' : ∀ n y, y ∈ t → ‖g' n y‖ ≤ u n) (hy₀ : y₀ ∈ t) (hg0 : Summable fun n => g n y₀)
    (hy : y ∈ t) : HasDerivAt (fun z => ∑' n, g n z) (∑' n, g' n y) y := by
  simp_rw [hasDerivAt_iff_hasFDerivAt] at hg ⊢
  convert hasFDerivAt_tsum_of_isPreconnected hu ht h't hg ?_ hy₀ hg0 hy
  · exact (ContinuousLinearMap.smulRightL 𝕜 𝕜 F 1).map_tsum <|
      .of_norm_bounded hu fun n ↦ hg' n y hy
  · simpa

/-- Consider a series of functions `∑' n, f n x`. If the series converges at a
point, and all functions in the series are differentiable with a summable bound on the derivatives,
then the series converges everywhere. -/
theorem summable_of_summable_hasFDerivAt (hu : Summable u)
    (hf : ∀ n x, HasFDerivAt (f n) (f' n x) x) (hf' : ∀ n x, ‖f' n x‖ ≤ u n)
    (hf0 : Summable fun n => f n x₀) (x : E) : Summable fun n => f n x := by
  letI : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  let _ : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 _
  exact summable_of_summable_hasFDerivAt_of_isPreconnected hu isOpen_univ isPreconnected_univ
    (fun n x _ => hf n x) (fun n x _ => hf' n x) (mem_univ _) hf0 (mem_univ _)

/-- Consider a series of functions `∑' n, f n x`. If the series converges at a
point, and all functions in the series are differentiable with a summable bound on the derivatives,
then the series converges everywhere. -/
theorem summable_of_summable_hasDerivAt (hu : Summable u)
    (hg : ∀ n y, HasDerivAt (g n) (g' n y) y) (hg' : ∀ n y, ‖g' n y‖ ≤ u n)
    (hg0 : Summable fun n => g n y₀) (y : 𝕜) : Summable fun n => g n y := by
  exact summable_of_summable_hasDerivAt_of_isPreconnected hu isOpen_univ isPreconnected_univ
    (fun n x _ => hg n x) (fun n x _ => hg' n x) (mem_univ _) hg0 (mem_univ _)

/-- Consider a series of functions `∑' n, f n x`. If the series converges at a
point, and all functions in the series are differentiable with a summable bound on the derivatives,
then the series is differentiable and its derivative is the sum of the derivatives. -/
theorem hasFDerivAt_tsum (hu : Summable u) (hf : ∀ n x, HasFDerivAt (f n) (f' n x) x)
    (hf' : ∀ n x, ‖f' n x‖ ≤ u n) (hf0 : Summable fun n => f n x₀) (x : E) :
    HasFDerivAt (fun y => ∑' n, f n y) (∑' n, f' n x) x := by
  letI : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  let A : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 _
  exact hasFDerivAt_tsum_of_isPreconnected hu isOpen_univ isPreconnected_univ
    (fun n x _ => hf n x) (fun n x _ => hf' n x) (mem_univ _) hf0 (mem_univ _)

/-- Consider a series of functions `∑' n, f n x`. If the series converges at a
point, and all functions in the series are differentiable with a summable bound on the derivatives,
then the series is differentiable and its derivative is the sum of the derivatives. -/
theorem hasDerivAt_tsum (hu : Summable u) (hg : ∀ n y, HasDerivAt (g n) (g' n y) y)
    (hg' : ∀ n y, ‖g' n y‖ ≤ u n) (hg0 : Summable fun n => g n y₀) (y : 𝕜) :
    HasDerivAt (fun z => ∑' n, g n z) (∑' n, g' n y) y := by
  exact hasDerivAt_tsum_of_isPreconnected hu isOpen_univ isPreconnected_univ
    (fun n y _ => hg n y) (fun n y _ => hg' n y) (mem_univ _) hg0 (mem_univ _)

/-- Consider a series of functions `∑' n, f n x`. If all functions in the series are differentiable
with a summable bound on the derivatives, then the series is differentiable.
Note that our assumptions do not ensure the pointwise convergence, but if there is no pointwise
convergence then the series is zero everywhere so the result still holds. -/
theorem differentiable_tsum (hu : Summable u) (hf : ∀ n x, HasFDerivAt (f n) (f' n x) x)
    (hf' : ∀ n x, ‖f' n x‖ ≤ u n) : Differentiable 𝕜 fun y => ∑' n, f n y := by
  by_cases h : ∃ x₀, Summable fun n => f n x₀
  · rcases h with ⟨x₀, hf0⟩
    intro x
    exact (hasFDerivAt_tsum hu hf hf' hf0 x).differentiableAt
  · push_neg at h
    have : (fun x => ∑' n, f n x) = 0 := by ext1 x; exact tsum_eq_zero_of_not_summable (h x)
    rw [this]
    exact differentiable_const 0

/-- Consider a series of functions `∑' n, f n x`. If all functions in the series are differentiable
with a summable bound on the derivatives, then the series is differentiable.
Note that our assumptions do not ensure the pointwise convergence, but if there is no pointwise
convergence then the series is zero everywhere so the result still holds. -/
theorem differentiable_tsum' (hu : Summable u) (hg : ∀ n y, HasDerivAt (g n) (g' n y) y)
    (hg' : ∀ n y, ‖g' n y‖ ≤ u n) : Differentiable 𝕜 fun z => ∑' n, g n z := by
  simp_rw [hasDerivAt_iff_hasFDerivAt] at hg
  refine differentiable_tsum hu hg ?_
  simpa

theorem fderiv_tsum_apply (hu : Summable u) (hf : ∀ n, Differentiable 𝕜 (f n))
    (hf' : ∀ n x, ‖fderiv 𝕜 (f n) x‖ ≤ u n) (hf0 : Summable fun n => f n x₀) (x : E) :
    fderiv 𝕜 (fun y => ∑' n, f n y) x = ∑' n, fderiv 𝕜 (f n) x :=
  (hasFDerivAt_tsum hu (fun n x => (hf n x).hasFDerivAt) hf' hf0 _).fderiv

theorem deriv_tsum_apply (hu : Summable u) (hg : ∀ n, Differentiable 𝕜 (g n))
    (hg' : ∀ n y, ‖deriv (g n) y‖ ≤ u n) (hg0 : Summable fun n => g n y₀) (y : 𝕜) :
    deriv (fun z => ∑' n, g n z) y = ∑' n, deriv (g n) y :=
  (hasDerivAt_tsum hu (fun n y => (hg n y).hasDerivAt) hg' hg0 _).deriv

theorem fderiv_tsum (hu : Summable u) (hf : ∀ n, Differentiable 𝕜 (f n))
    (hf' : ∀ n x, ‖fderiv 𝕜 (f n) x‖ ≤ u n) (hf0 : Summable fun n => f n x₀) :
    (fderiv 𝕜 fun y => ∑' n, f n y) = fun x => ∑' n, fderiv 𝕜 (f n) x := by
  ext1 x
  exact fderiv_tsum_apply hu hf hf' hf0 x

theorem deriv_tsum (hu : Summable u) (hg : ∀ n, Differentiable 𝕜 (g n))
    (hg' : ∀ n y, ‖deriv (g n) y‖ ≤ u n) (hg0 : Summable fun n => g n y₀) :
    (deriv fun y => ∑' n, g n y) = fun y => ∑' n, deriv (g n) y := by
  ext1 x
  exact deriv_tsum_apply hu hg hg' hg0 x

/-! ### Higher smoothness -/

/-- Consider a series of `C^n` functions, with summable uniform bounds on the successive
derivatives. Then the iterated derivative of the sum is the sum of the iterated derivative. -/
theorem iteratedFDeriv_tsum (hf : ∀ i, ContDiff 𝕜 N (f i))
    (hv : ∀ k : ℕ, (k : ℕ∞) ≤ N → Summable (v k))
    (h'f : ∀ (k : ℕ) (i : α) (x : E), (k : ℕ∞) ≤ N → ‖iteratedFDeriv 𝕜 k (f i) x‖ ≤ v k i) {k : ℕ}
    (hk : (k : ℕ∞) ≤ N) :
    (iteratedFDeriv 𝕜 k fun y => ∑' n, f n y) = fun x => ∑' n, iteratedFDeriv 𝕜 k (f n) x := by
  induction k with
  | zero =>
    ext1 x
    simp_rw [iteratedFDeriv_zero_eq_comp]
    exact (continuousMultilinearCurryFin0 𝕜 E F).symm.toContinuousLinearEquiv.map_tsum
  | succ k IH =>
    have h'k : (k : ℕ∞) < N := lt_of_lt_of_le (WithTop.coe_lt_coe.2 (Nat.lt_succ_self _)) hk
    have A : Summable fun n => iteratedFDeriv 𝕜 k (f n) 0 :=
      .of_norm_bounded (hv k h'k.le) fun n ↦ h'f k n 0 h'k.le
    simp_rw [iteratedFDeriv_succ_eq_comp_left, IH h'k.le]
    rw [fderiv_tsum (hv _ hk) (fun n => (hf n).differentiable_iteratedFDeriv
        (mod_cast h'k)) _ A]
    · ext1 x
      exact (continuousMultilinearCurryLeftEquiv 𝕜
        (fun _ : Fin (k + 1) => E) F).symm.toContinuousLinearEquiv.map_tsum
    · intro n x
      simpa only [iteratedFDeriv_succ_eq_comp_left, LinearIsometryEquiv.norm_map, comp_apply]
        using h'f k.succ n x hk

/-- Consider a series of smooth functions, with summable uniform bounds on the successive
derivatives. Then the iterated derivative of the sum is the sum of the iterated derivative. -/
theorem iteratedFDeriv_tsum_apply (hf : ∀ i, ContDiff 𝕜 N (f i))
    (hv : ∀ k : ℕ, (k : ℕ∞) ≤ N → Summable (v k))
    (h'f : ∀ (k : ℕ) (i : α) (x : E), (k : ℕ∞) ≤ N → ‖iteratedFDeriv 𝕜 k (f i) x‖ ≤ v k i) {k : ℕ}
    (hk : (k : ℕ∞) ≤ N) (x : E) :
    iteratedFDeriv 𝕜 k (fun y => ∑' n, f n y) x = ∑' n, iteratedFDeriv 𝕜 k (f n) x := by
  rw [iteratedFDeriv_tsum hf hv h'f hk]

/-- Consider a series of functions `∑' i, f i x`. Assume that each individual function `f i` is of
class `C^N`, and moreover there is a uniform summable upper bound on the `k`-th derivative
for each `k ≤ N`. Then the series is also `C^N`. -/
theorem contDiff_tsum (hf : ∀ i, ContDiff 𝕜 N (f i)) (hv : ∀ k : ℕ, (k : ℕ∞) ≤ N → Summable (v k))
    (h'f : ∀ (k : ℕ) (i : α) (x : E), k ≤ N → ‖iteratedFDeriv 𝕜 k (f i) x‖ ≤ v k i) :
    ContDiff 𝕜 N fun x => ∑' i, f i x := by
  rw [contDiff_iff_continuous_differentiable]
  constructor
  · intro m hm
    rw [iteratedFDeriv_tsum hf hv h'f hm]
    refine continuous_tsum ?_ (hv m hm) ?_
    · intro i
      exact ContDiff.continuous_iteratedFDeriv (mod_cast hm) (hf i)
    · intro n x
      exact h'f _ _ _ hm
  · intro m hm
    have h'm : ((m + 1 : ℕ) : ℕ∞) ≤ N := by
      simpa only [ENat.coe_add, ENat.coe_one] using Order.add_one_le_of_lt hm
    rw [iteratedFDeriv_tsum hf hv h'f hm.le]
    have A n x : HasFDerivAt (iteratedFDeriv 𝕜 m (f n)) (fderiv 𝕜 (iteratedFDeriv 𝕜 m (f n)) x) x :=
      (ContDiff.differentiable_iteratedFDeriv (mod_cast hm)
        (hf n)).differentiableAt.hasFDerivAt
    refine differentiable_tsum (hv _ h'm) A fun n x => ?_
    rw [fderiv_iteratedFDeriv, comp_apply, LinearIsometryEquiv.norm_map]
    exact h'f _ _ _ h'm

/-- Consider a series of functions `∑' i, f i x`. Assume that each individual function `f i` is of
class `C^N`, and moreover there is a uniform summable upper bound on the `k`-th derivative
for each `k ≤ N` (except maybe for finitely many `i`s). Then the series is also `C^N`. -/
theorem contDiff_tsum_of_eventually (hf : ∀ i, ContDiff 𝕜 N (f i))
    (hv : ∀ k : ℕ, k ≤ N → Summable (v k))
    (h'f : ∀ k : ℕ, k ≤ N →
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
    have : (fun x => ∑' i, f i x) = (fun x => ∑ i ∈ T, f i x) +
        fun x => ∑' i : { i // i ∉ T }, f i x := by
      ext1 x
      refine (Summable.sum_add_tsum_subtype_compl ?_ T).symm
      refine .of_norm_bounded_eventually (hv 0 (zero_le _)) ?_
      filter_upwards [h'f 0 (zero_le _)] with i hi
      simpa only [norm_iteratedFDeriv_zero] using hi x
    rw [this]
    apply (ContDiff.sum fun i _ => (hf i).of_le (mod_cast hm)).add
    have h'u : ∀ k : ℕ, (k : ℕ∞) ≤ m → Summable (v k ∘ ((↑) : { i // i ∉ T } → α)) := fun k hk =>
      (hv k (hk.trans hm)).subtype _
    refine contDiff_tsum (fun i => (hf i).of_le (mod_cast hm)) h'u ?_
    rintro k ⟨i, hi⟩ x hk
    simp only [t, T, Finite.mem_toFinset, mem_setOf_eq, Finset.mem_range, not_forall, not_le,
      exists_prop, not_exists, not_and, not_lt] at hi
    exact hi k (Nat.lt_succ_iff.2 (WithTop.coe_le_coe.1 hk)) x
