/-
Copyright (c) 2024 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Data.Fintype.Perm

/-!
# The iterated derivative of an analytic function

If a function is analytic, written as `f (x + y) = ∑ pₙ (y, ..., y)` then its `n`-th iterated
derivative at `x` is given by `(v₁, ..., vₙ) ↦ ∑ pₙ (v_{σ (1)}, ..., v_{σ (n)})` where the sum
is over all permutations of `{1, ..., n}`. In particular, it is symmetric.

This generalizes the result of `HasFPowerSeriesOnBall.factorial_smul` giving
`D^n f (v, ..., v) = n! * pₙ (v, ..., v)`.

## Main result

* `HasFPowerSeriesOnBall.iteratedFDeriv_eq_sum` shows that
  `iteratedFDeriv 𝕜 n f x v = ∑ σ : Perm (Fin n), p n (fun i ↦ v (σ i))`,
  when `f` has `p` as power series within the set `s` on the ball `B (x, r)`.
* `ContDiffAt.iteratedFDeriv_comp_perm` proves the symmetry of the iterated derivative of an
  analytic function, in the form `iteratedFDeriv 𝕜 n f x (v ∘ σ) = iteratedFDeriv 𝕜 n f x v`
  for any permutation `σ` of `Fin n`.

Versions within sets are also given.

## Implementation

To prove the formula for the iterated derivative, we decompose an analytic function as
the sum of `fun y ↦ pₙ (y, ..., y)` and the rest. For the former, its iterated derivative follows
from the formula for iterated derivatives of multilinear maps
(see `ContinuousMultilinearMap.iteratedFDeriv_comp_diagonal`). For the latter, we show by
induction on `n` that if the `n`-th term in a power series is zero, then the `n`-th iterated
derivative vanishes (see `HasFPowerSeriesWithinOnBall.iteratedFDerivWithin_eq_zero`).

All these results are proved assuming additionally that the function is analytic on the relevant
set (which does not follow from the fact that the function has a power series, if the target space
is not complete). This makes it possible to avoid all completeness assumptions in the final
statements. When needed, we give versions of some statements assuming completeness and dropping
analyticity, for ease of use.
-/

open scoped ENNReal Topology ContDiff
open Equiv Set

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {f : E → F} {p : FormalMultilinearSeries 𝕜 E F} {s : Set E} {x : E} {r : ℝ≥0∞}

/-- Formal multilinear series associated to the iterated derivative, defined by iterating
`p ↦ p.derivSeries` and currying suitably. It is defined so that, if a function has `p` as a power
series, then its iterated derivative of order `k` has `p.iteratedFDerivSeries k` as a power
series. -/
noncomputable def FormalMultilinearSeries.iteratedFDerivSeries
    (p : FormalMultilinearSeries 𝕜 E F) (k : ℕ) :
    FormalMultilinearSeries 𝕜 E (E [×k]→L[𝕜] F) :=
  match k with
  | 0 => (continuousMultilinearCurryFin0 𝕜 E F).symm
      |>.toContinuousLinearEquiv.toContinuousLinearMap.compFormalMultilinearSeries p
  | (k + 1) => (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (k + 1) ↦ E) F).symm
      |>.toContinuousLinearEquiv.toContinuousLinearMap.compFormalMultilinearSeries
      (p.iteratedFDerivSeries k).derivSeries

/-- If a function has a power series on a ball, then so do its iterated derivatives. -/
protected theorem HasFPowerSeriesWithinOnBall.iteratedFDerivWithin
    (h : HasFPowerSeriesWithinOnBall f p s x r) (h' : AnalyticOn 𝕜 f s)
    (k : ℕ) (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) :
    HasFPowerSeriesWithinOnBall (iteratedFDerivWithin 𝕜 k f s)
      (p.iteratedFDerivSeries k) s x r := by
  induction k with
  | zero =>
    exact (continuousMultilinearCurryFin0 𝕜 E F).symm
      |>.toContinuousLinearEquiv.toContinuousLinearMap.comp_hasFPowerSeriesWithinOnBall h
  | succ k ih =>
    rw [iteratedFDerivWithin_succ_eq_comp_left]
    apply (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (k + 1) ↦ E) F).symm
      |>.toContinuousLinearEquiv.toContinuousLinearMap.comp_hasFPowerSeriesWithinOnBall
        (ih.fderivWithin_of_mem_of_analyticOn (h'.iteratedFDerivWithin hs _) hs hx)

lemma FormalMultilinearSeries.iteratedFDerivSeries_eq_zero {k n : ℕ}
    (h : p (n + k) = 0) : p.iteratedFDerivSeries k n = 0 := by
  induction k generalizing n with
  | zero =>
    ext
    have : p n = 0 := p.congr_zero rfl h
    simp [FormalMultilinearSeries.iteratedFDerivSeries, this]
  | succ k ih =>
    ext
    simp only [iteratedFDerivSeries, Nat.succ_eq_add_one,
      ContinuousLinearMap.compFormalMultilinearSeries_apply,
      ContinuousLinearMap.compContinuousMultilinearMap_coe, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv, Function.comp_apply,
      continuousMultilinearCurryLeftEquiv_symm_apply, ContinuousMultilinearMap.zero_apply,
      ContinuousLinearMap.zero_apply,
      derivSeries_eq_zero _ (ih (p.congr_zero (Nat.succ_add_eq_add_succ _ _).symm h))]

/-- If the `n`-th term in a power series is zero, then the `n`-th derivative of the corresponding
function vanishes. -/
lemma HasFPowerSeriesWithinOnBall.iteratedFDerivWithin_eq_zero
    (h : HasFPowerSeriesWithinOnBall f p s x r) (h' : AnalyticOn 𝕜 f s)
    (hu : UniqueDiffOn 𝕜 s) (hx : x ∈ s) {n : ℕ} (hn : p n = 0) :
    iteratedFDerivWithin 𝕜 n f s x = 0 := by
  have : iteratedFDerivWithin 𝕜 n f s x = p.iteratedFDerivSeries n 0 (fun _ ↦ 0) :=
    ((h.iteratedFDerivWithin h' n hu hx).coeff_zero _).symm
  rw [this, p.iteratedFDerivSeries_eq_zero (p.congr_zero (Nat.zero_add n).symm hn),
    ContinuousMultilinearMap.zero_apply]

lemma ContinuousMultilinearMap.iteratedFDeriv_comp_diagonal
    {n : ℕ} (f : E [×n]→L[𝕜] F) (x : E) (v : Fin n → E) :
    iteratedFDeriv 𝕜 n (fun x ↦ f (fun _ ↦ x)) x v = ∑ σ : Perm (Fin n), f (fun i ↦ v (σ i)) := by
  rw [← sum_comp (Equiv.inv (Perm (Fin n)))]
  let g : E →L[𝕜] (Fin n → E) := ContinuousLinearMap.pi (fun i ↦ ContinuousLinearMap.id 𝕜 E)
  change iteratedFDeriv 𝕜 n (f ∘ g) x v = _
  rw [ContinuousLinearMap.iteratedFDeriv_comp_right _ f.contDiff _ le_rfl, f.iteratedFDeriv_eq]
  simp only [ContinuousMultilinearMap.iteratedFDeriv,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, ContinuousMultilinearMap.sum_apply,
    ContinuousMultilinearMap.iteratedFDerivComponent_apply, Set.mem_range, Pi.compRightL_apply]
  rw [← sum_comp (Equiv.embeddingEquivOfFinite (Fin n))]
  congr with σ
  congr with i
  have A : ∃ y, σ y = i := by
    have : Function.Bijective σ := (Fintype.bijective_iff_injective_and_card _).2 ⟨σ.injective, rfl⟩
    exact this.surjective i
  rcases A with ⟨y, rfl⟩
  simp only [EmbeddingLike.apply_eq_iff_eq, exists_eq, ↓reduceDIte,
    Function.Embedding.toEquivRange_symm_apply_self, ContinuousLinearMap.coe_pi',
    ContinuousLinearMap.coe_id', id_eq, g]
  congr 1
  symm
  simp [coe_fn_mk, inv_apply, Perm.inv_def,
    ofBijective_symm_apply_apply, Function.Embedding.equivOfFiniteSelfEmbedding]

private lemma HasFPowerSeriesWithinOnBall.iteratedFDerivWithin_eq_sum_of_subset
    (h : HasFPowerSeriesWithinOnBall f p s x r) (h' : AnalyticOn 𝕜 f s)
    (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s)
    {n : ℕ} (v : Fin n → E) (h's : s ⊆ EMetric.ball x r) :
    iteratedFDerivWithin 𝕜 n f s x v = ∑ σ : Perm (Fin n), p n (fun i ↦ v (σ i)) := by
  have I : insert x s ∩ EMetric.ball x r = s := by
    rw [Set.insert_eq_of_mem hx]
    exact Set.inter_eq_left.2 h's
  have fcont : ContDiffOn 𝕜 (↑n) f s := by
    apply AnalyticOn.contDiffOn _ hs
    simpa [I] using h'
  let g : E → F := fun z ↦ p n (fun _ ↦ z - x)
  have gcont : ContDiff 𝕜 ω g := by
    apply (p n).contDiff.comp
    exact contDiff_pi.2 (fun i ↦ contDiff_id.sub contDiff_const)
  let q : FormalMultilinearSeries 𝕜 E F := fun k ↦ if h : n = k then (h ▸ p n) else 0
  have A : HasFiniteFPowerSeriesOnBall g q x (n + 1) r := by
    apply HasFiniteFPowerSeriesOnBall.mk' _ h.r_pos
    · intro y hy
      rw [Finset.sum_eq_single_of_mem n]
      · simp [q, g]
      · simp
      · intro i hi h'i
        simp [q, h'i.symm]
    · intro m hm
      have : n ≠ m := by omega
      simp [q, this]
  have B : HasFPowerSeriesWithinOnBall g q s x r :=
    A.toHasFPowerSeriesOnBall.hasFPowerSeriesWithinOnBall
  have J1 : iteratedFDerivWithin 𝕜 n f s x =
      iteratedFDerivWithin 𝕜 n g s x + iteratedFDerivWithin 𝕜 n (f - g) s x := by
    have : f = g + (f - g) := by abel
    nth_rewrite 1 [this]
    rw [iteratedFDerivWithin_add_apply (gcont.of_le le_top).contDiffWithinAt
      (by exact (fcont _ hx).sub (gcont.of_le le_top).contDiffWithinAt) hs hx]
  have J2 : iteratedFDerivWithin 𝕜 n (f - g) s x = 0 := by
    apply (h.sub B).iteratedFDerivWithin_eq_zero (h'.sub ?_) hs hx
    · simp [q]
    · apply gcont.contDiffOn.analyticOn
  have J3 : iteratedFDerivWithin 𝕜 n g s x = iteratedFDeriv 𝕜 n g x :=
    iteratedFDerivWithin_eq_iteratedFDeriv hs (gcont.of_le le_top).contDiffAt hx
  simp only [J1, J3, J2, add_zero]
  let g' : E → F := fun z ↦ p n (fun _ ↦ z)
  have : g = fun z ↦ g' (z - x) := rfl
  rw [this, iteratedFDeriv_comp_sub]
  exact (p n).iteratedFDeriv_comp_diagonal _ v

/-- If a function has a power series in a ball, then its `n`-th iterated derivative is given by
`(v₁, ..., vₙ) ↦ ∑ pₙ (v_{σ (1)}, ..., v_{σ (n)})` where the sum is over all
permutations of `{1, ..., n}`. -/
theorem HasFPowerSeriesWithinOnBall.iteratedFDerivWithin_eq_sum
    (h : HasFPowerSeriesWithinOnBall f p s x r) (h' : AnalyticOn 𝕜 f s)
    (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) {n : ℕ} (v : Fin n → E) :
    iteratedFDerivWithin 𝕜 n f s x v = ∑ σ : Perm (Fin n), p n (fun i ↦ v (σ i)) := by
  have : iteratedFDerivWithin 𝕜 n f s x
      = iteratedFDerivWithin 𝕜 n f (s ∩ EMetric.ball x r) x :=
    (iteratedFDerivWithin_inter_open EMetric.isOpen_ball (EMetric.mem_ball_self h.r_pos)).symm
  rw [this]
  apply HasFPowerSeriesWithinOnBall.iteratedFDerivWithin_eq_sum_of_subset
  · exact h.mono inter_subset_left
  · exact h'.mono inter_subset_left
  · exact hs.inter EMetric.isOpen_ball
  · exact ⟨hx, EMetric.mem_ball_self h.r_pos⟩
  · exact inter_subset_right

/-- If a function has a power series in a ball, then its `n`-th iterated derivative is given by
`(v₁, ..., vₙ) ↦ ∑ pₙ (v_{σ (1)}, ..., v_{σ (n)})` where the sum is over all
permutations of `{1, ..., n}`. -/
theorem HasFPowerSeriesOnBall.iteratedFDeriv_eq_sum
    (h : HasFPowerSeriesOnBall f p x r) (h' : AnalyticOn 𝕜 f univ) {n : ℕ} (v : Fin n → E) :
    iteratedFDeriv 𝕜 n f x v = ∑ σ : Perm (Fin n), p n (fun i ↦ v (σ i)) := by
  simp only [← iteratedFDerivWithin_univ, ← hasFPowerSeriesWithinOnBall_univ] at h ⊢
  exact h.iteratedFDerivWithin_eq_sum h' uniqueDiffOn_univ (mem_univ x) v

/-- If a function has a power series in a ball, then its `n`-th iterated derivative is given by
`(v₁, ..., vₙ) ↦ ∑ pₙ (v_{σ (1)}, ..., v_{σ (n)})` where the sum is over all
permutations of `{1, ..., n}`. -/
theorem HasFPowerSeriesWithinOnBall.iteratedFDerivWithin_eq_sum_of_completeSpace [CompleteSpace F]
    (h : HasFPowerSeriesWithinOnBall f p s x r)
    (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) {n : ℕ} (v : Fin n → E) :
    iteratedFDerivWithin 𝕜 n f s x v = ∑ σ : Perm (Fin n), p n (fun i ↦ v (σ i)) := by
  have : iteratedFDerivWithin 𝕜 n f s x
      = iteratedFDerivWithin 𝕜 n f (s ∩ EMetric.ball x r) x :=
    (iteratedFDerivWithin_inter_open EMetric.isOpen_ball (EMetric.mem_ball_self h.r_pos)).symm
  rw [this]
  apply HasFPowerSeriesWithinOnBall.iteratedFDerivWithin_eq_sum_of_subset
  · exact h.mono inter_subset_left
  · apply h.analyticOn.mono
    rw [insert_eq_of_mem hx]
  · exact hs.inter EMetric.isOpen_ball
  · exact ⟨hx, EMetric.mem_ball_self h.r_pos⟩
  · exact inter_subset_right

/-- If a function has a power series in a ball, then its `n`-th iterated derivative is given by
`(v₁, ..., vₙ) ↦ ∑ pₙ (v_{σ (1)}, ..., v_{σ (n)})` where the sum is over all
permutations of `{1, ..., n}`. -/
theorem HasFPowerSeriesOnBall.iteratedFDeriv_eq_sum_of_completeSpace [CompleteSpace F]
    (h : HasFPowerSeriesOnBall f p x r) {n : ℕ} (v : Fin n → E) :
    iteratedFDeriv 𝕜 n f x v = ∑ σ : Perm (Fin n), p n (fun i ↦ v (σ i)) := by
  simp only [← iteratedFDerivWithin_univ, ← hasFPowerSeriesWithinOnBall_univ] at h ⊢
  exact h.iteratedFDerivWithin_eq_sum_of_completeSpace uniqueDiffOn_univ (mem_univ _) v

/-- The `n`-th iterated derivative of an analytic function on a set is symmetric. -/
theorem AnalyticOn.iteratedFDerivWithin_comp_perm
    (h : AnalyticOn 𝕜 f s) (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) {n : ℕ} (v : Fin n → E)
    (σ : Perm (Fin n)) :
    iteratedFDerivWithin 𝕜 n f s x (v ∘ σ) = iteratedFDerivWithin 𝕜 n f s x v := by
  rcases h x hx with ⟨p, r, hp⟩
  rw [hp.iteratedFDerivWithin_eq_sum h hs hx, hp.iteratedFDerivWithin_eq_sum h hs hx]
  conv_rhs => rw [← Equiv.sum_comp (Equiv.mulLeft σ)]
  simp only [coe_mulLeft, Perm.coe_mul, Function.comp_apply]

theorem AnalyticOn.domDomCongr_iteratedFDerivWithin
    (h : AnalyticOn 𝕜 f s) (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) {n : ℕ} (σ : Perm (Fin n)) :
    (iteratedFDerivWithin 𝕜 n f s x).domDomCongr σ = iteratedFDerivWithin 𝕜 n f s x := by
  ext
  exact h.iteratedFDerivWithin_comp_perm hs hx _ _

/-- The `n`-th iterated derivative of an analytic function on a set is symmetric. -/
theorem ContDiffWithinAt.iteratedFDerivWithin_comp_perm
    (h : ContDiffWithinAt 𝕜 ω f s x) (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) {n : ℕ} (v : Fin n → E)
    (σ : Perm (Fin n)) :
    iteratedFDerivWithin 𝕜 n f s x (v ∘ σ) = iteratedFDerivWithin 𝕜 n f s x v := by
  rcases h.contDiffOn' le_rfl (by simp) with ⟨u, u_open, xu, hu⟩
  rw [insert_eq_of_mem hx] at hu
  have : iteratedFDerivWithin 𝕜 n f (s ∩ u) x = iteratedFDerivWithin 𝕜 n f s x :=
    iteratedFDerivWithin_inter_open u_open xu
  rw [← this]
  exact AnalyticOn.iteratedFDerivWithin_comp_perm hu.analyticOn (hs.inter u_open) ⟨hx, xu⟩ _ _

theorem ContDiffWithinAt.domDomCongr_iteratedFDerivWithin
    (h : ContDiffWithinAt 𝕜 ω f s x) (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) {n : ℕ}
    (σ : Perm (Fin n)) :
    (iteratedFDerivWithin 𝕜 n f s x).domDomCongr σ = iteratedFDerivWithin 𝕜 n f s x := by
  ext
  exact h.iteratedFDerivWithin_comp_perm hs hx _ _

/-- The `n`-th iterated derivative of an analytic function is symmetric. -/
theorem AnalyticOn.iteratedFDeriv_comp_perm
    (h : AnalyticOn 𝕜 f univ) {n : ℕ} (v : Fin n → E) (σ : Perm (Fin n)) :
    iteratedFDeriv 𝕜 n f x (v ∘ σ) = iteratedFDeriv 𝕜 n f x v := by
  rw [← iteratedFDerivWithin_univ]
  exact h.iteratedFDerivWithin_comp_perm uniqueDiffOn_univ (mem_univ x) _ _

theorem AnalyticOn.domDomCongr_iteratedFDeriv (h : AnalyticOn 𝕜 f univ) {n : ℕ} (σ : Perm (Fin n)) :
    (iteratedFDeriv 𝕜 n f x).domDomCongr σ = iteratedFDeriv 𝕜 n f x := by
  rw [← iteratedFDerivWithin_univ]
  exact h.domDomCongr_iteratedFDerivWithin uniqueDiffOn_univ (mem_univ x) _

/-- The `n`-th iterated derivative of an analytic function is symmetric. -/
theorem ContDiffAt.iteratedFDeriv_comp_perm
    (h : ContDiffAt 𝕜 ω f x) {n : ℕ} (v : Fin n → E) (σ : Perm (Fin n)) :
    iteratedFDeriv 𝕜 n f x (v ∘ σ) = iteratedFDeriv 𝕜 n f x v := by
  rw [← iteratedFDerivWithin_univ]
  exact h.iteratedFDerivWithin_comp_perm uniqueDiffOn_univ (mem_univ x) _ _

theorem ContDiffAt.domDomCongr_iteratedFDeriv (h : ContDiffAt 𝕜 ω f x) {n : ℕ} (σ : Perm (Fin n)) :
    (iteratedFDeriv 𝕜 n f x).domDomCongr σ = iteratedFDeriv 𝕜 n f x := by
  rw [← iteratedFDerivWithin_univ]
  exact h.domDomCongr_iteratedFDerivWithin uniqueDiffOn_univ (mem_univ x) _
