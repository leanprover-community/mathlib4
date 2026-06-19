/-
Copyright (c) 2026 Kai Lam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kai Lam
-/

import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Complex.Tietze
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Order.Filter.Cofinite
import Mathlib.Order.Filter.TendstoCofinite
import Mathlib.Algebra.Order.CompleteField
import Mathlib.Order.Interval.Set.OrdConnected
/-!
# Invariance of Domain and partial proof of Brouwer's Fixed Point Theorem

This file contains two parts:

## Part 1: No smooth retraction from the ball to the sphere

We prove that there is no continuously differentiable map `f : E → E` (for a finite‑dimensional
real inner product space `E`) such that `f x` lies on the unit sphere for all `x` with `‖x‖ ≤ 1`
and `f x = x` whenever `‖x‖ = 1`. This is Lemma 2 of the paper:

> Rogers, C. A. “A Less Strange Version of Milnor’s Proof of Brouwer’s Fixed-Point Theorem.”
> *The American Mathematical Monthly* 87, no. 7 (1980): 525–27. https://doi.org/10.2307/2321416.

The proof uses an integral of the determinant of the derivative, showing it would be
simultaneously `0` (for the retraction) and `1` (for the identity), a contradiction.
The result is formalised as `cont_diff_ball_to_sphere_no_fixed`.

This lemma can be used to obtain Brouwer’s fixed point theorem for continuously differentiable
maps, and then for continuous maps via Weierstrass approximation.

## Part 2: Invariance of domain (assuming Brouwer’s fixed point theorem)

Following the exposition by Terry Tao:

> [Brouwer’s fixed point and invariance of domain theorems, and Hilbert’s fifth problem](https://terrytao.wordpress.com/2011/06/13/brouwers-fixed-point-and-invariance-of-domain-theorems-and-hilberts-fifth-problem/#phi-def)

we prove the invariance of domain theorem and some corollaries, under the assumption that
Brouwer’s fixed point theorem holds for the space `E` (i.e. we have an instance of the
type class `BrouwerFixedPoint E`).

### Main definitions

* `BrouwerFixedPoint` – a type class stating that every continuous self‑map of the closed unit
  ball in `E` has a fixed point.
* `Phi` – the retraction of `f(Bⁿ)` onto the set `Σ = Σ₁ ∪ Σ₂` (used in the proof).

### Main statements

* `cont_diff_ball_to_sphere_no_fixed` – a smooth map from the ball to the sphere that fixes
  the sphere pointwise cannot exist.
* `invariance_of_domain_interior` – if `f` is continuous and injective on the closed unit ball,
  then `f(0)` lies in the interior of `f(Bⁿ)`.
* `invariance_of_domain_open_map` – a continuous injective map on an open set is open.
* `dim_le_of_injective_continuous` – if there exists a continuous injective map from
  `E` to `F`, then `dim E ≤ dim F`.
* `invariance_of_dimension` – homeomorphic finite‑dimensional inner product spaces have
  equal dimension.

### Notation

* `E`, `F` – finite‑dimensional real inner product spaces.
* `closedBall 0 1` – the closed unit ball.
* `sphere 0 1` – the unit sphere.

### Implementation details

* The smoothness part uses `ContDiff ℝ 1` (once continuously differentiable) and determinant
  calculations via matrices with respect to an orthonormal basis.
* The invariance of domain proof relies on:
  - Tietze extension theorem to extend the inverse of `f` to a continuous function `G`
    on the whole space.
  - Stone‑Weierstrass theorem (polynomial approximation) to approximate `G` by a
    differentiable map `P` on a compact set.
  - Measure theory to perturb `P` away from zeros on a null set (`Σ₂`).
  - Brouwer’s fixed point theorem (via the `BrouwerFixedPoint` type class) to obtain a
    contradiction in the stability lemma.

### References

* Rogers, C. A. “A Less Strange Version of Milnor’s Proof of Brouwer’s Fixed-Point Theorem.”
  *The American Mathematical Monthly* 87, no. 7 (1980): 525–27. https://doi.org/10.2307/2321416.
* Tao, Terry. “Brouwer’s fixed point and invariance of domain theorems,
  and Hilbert’s fifth problem.”
  *What’s new*, 13 June 2011.
  https://terrytao.wordpress.com/2011/06/13/brouwers-fixed-point-and-invariance-of-domain-theorems-and-hilberts-fifth-problem/#phi-def

### Tags

Brouwer fixed point, invariance of domain, dimension, retraction, smooth map, degree, determinant.
-/

set_option linter.directoryDependency false
open MeasureTheory Metric Set ContinuousLinearMap LinearMap Topology Polynomial

variable {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable (E) in
/-- `BrouwerFixedPoint E` is a typeclass asserting that the Brouwer fixed point theorem holds for
  the closed unit ball in the inner product space `E`.  That is: for every continuous map
  `f : closedBall 0 1 → closedBall 0 1`, there exists `x` such that `f x = x`.
  This is assumed and used to prove invariance of domain. -/
class BrouwerFixedPoint : Prop where
  brouwer_fixed_point (f : (closedBall (0 : E) 1) → (closedBall 0 1))
    (hf : Continuous f) : ∃ x, f x = x


/-- A nonconstant polynomial over a domain is finite‑to‑one: every fibre is finite. -/
lemma TendstoCofinite_of_nonconst_polynomial {R : Type} [CommRing R] [IsDomain R] (p : R[X])
    (hp : p.natDegree ≠ 0) : Filter.TendstoCofinite (fun x : R ↦ p.eval x) := by
  rw [Filter.tendstoCofinite_iff_finite_preimage_singleton]
  intro b
  by_contra! hb
  have := Polynomial.eq_of_infinite_eval_eq p (C b) (by simpa)
  grind [natDegree_C]


/-- A polynomial that is constant on an infinite set (such as an interval) is always constant. -/
lemma polynomial_const_on_infinite {R : Type} [LinearOrder R] [Field R] {s : Set R}
    (hs : s.Infinite) (f : R → R) (P : R[X]) (c : R) (hf : ∀ x ∈ s, f x = P.eval x)
    (h_const : ∀ x ∈ s, f x = c) :
    P.natDegree = 0 := by
  obtain hP_const | hP_nonconst := eq_or_ne P.natDegree 0
  · exact hP_const
  · have h_finite :=
        (TendstoCofinite_of_nonconst_polynomial P hP_nonconst).finite_preimage_singleton _ c
    cases hs.not_finite (h_finite.subset (by grind))


/-- A function is not injective on a set `s` iff there are `a, b ∈ s` with `f a = f b`. -/
theorem not_injOn_iff {α β : Type*} {f : α → β} {s : Set α} :
    ¬ InjOn f s ↔ ∃ a ∈ s, ∃ b ∈ s, f a = f b ∧ a ≠ b := by
  simp only [InjOn, not_forall, exists_prop]

/-- A function that is polynomial and monotone on an order connected set
is either injective or constant on that set. -/
lemma inj_on_or_const_of_monotone {R : Type} [CommRing R] [IsDomain R] [PartialOrder R] [Field R]
    [LinearOrder R] {s : Set R} [OrdConnected s] (f : R → R) (P : R[X])
    (hf : ∀ x ∈ s, f x = P.eval x) (hp : MonotoneOn f s) :
    InjOn f s ∨ ∀ a ∈ s, ∀ b ∈ s, f a = f b  := by
  rw [or_iff_not_imp_left]
  intro hinj x hx y hy
  rw [not_injOn_iff] at hinj
  rcases hinj with ⟨a, ha, b , hb, hab , hne⟩
  have := MonotoneOn.mapsTo_Icc (hp.mono (Set.Icc_subset s ha hb))
  rw [hab] at this
  have hs : (Icc a b).Infinite := by sorry
  have h_const_interval : ∀ x ∈ Icc a b, f x = f b := by
    intro x hx
    rw [MapsTo] at this
    specialize this hx
    rw [Set.Icc_self] at this
    exact mem_singleton_iff.mp this
  have := polynomial_const_on_infinite hs f P (f b) hf h_const_interval

  -- exact polynomial_const_on_infinite hs f P (f b) hf h_const_interval

  -- rw [MapsTo] at this


  -- have := this hx










omit [FiniteDimensional ℝ E] in
/-- If `g` is Lipschitz on the closed unit ball with constant `C`, and `0 ≤ t < 1/C`,
    then the map `x ↦ x + t • g x` is injective on the closed unit ball. -/
lemma injOn_of_lipschitz_lt_one {g : E → E} {C : NNReal}
    (hC : LipschitzOnWith C g (closedBall 0 1))
    {t : ℝ} (ht0 : 0 ≤ t) (htC : t < 1 / C) :
    Set.InjOn (fun x => x + t • g x) (closedBall 0 1) := by
  intro x hx y hy hxy
  have hxy' : x - y = t • (g y - g x) := by grind only [smul_sub]
  have hnorm_eq : ‖x - y‖ = ‖t • g y - t • g x‖ := by rw [hxy', smul_sub]
  have hnorm_le : ‖t • g y - t • g x‖ ≤ t * C * ‖y - x‖ := by
    rw [← smul_sub, norm_smul, Real.norm_of_nonneg ht0]
    nlinarith [LipschitzOnWith.norm_sub_le hC hy hx]
  rcases eq_or_lt_of_le (NNReal.coe_nonneg C) with hC | hC
  · grind only
  · rcases eq_or_lt_of_le (norm_nonneg (x - y)) with hzero | hpos
    · rwa [← dist_eq_norm', zero_eq_dist, eq_comm] at hzero
    · have : t * C * ‖x - y‖ < ‖x - y‖ := by nlinarith [(lt_div_iff₀ hC).mp htC]
      rw [norm_sub_rev] at this
      have : ‖x - y‖ < ‖x - y‖ := calc
        ‖x - y‖ ≤ t * C * ‖y - x‖ := (le_of_eq_of_le hnorm_eq hnorm_le)
        _ < 1 * ‖y - x‖ := by linarith
        _ = ‖x - y‖ := by simp only [one_mul, norm_sub_rev]
      linarith

omit [FiniteDimensional ℝ E] in
/-- For a map `f` that maps the closed unit ball into itself, the convex combination
    `(1-t)x + t f(x)` also lies in the closed unit ball for any `t ∈ [0,1]`. -/
lemma mapsTo_interpolation {f : E → E}
    (hfx : ∀ x ∈ closedBall (0 : E) 1, f x ∈ closedBall 0 1) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Set.MapsTo (fun x => x + t • (f x - x)) (closedBall (0 : E) 1) (closedBall (0 : E) 1) := by
  intro x hx
  simp only [mem_closedBall, dist_zero_right]
  have : (1 - t) • x = x - t • x := by simp [sub_smul]
  rw [smul_sub, add_sub_assoc', add_sub_right_comm, ← this, add_comm]
  have hconvex := convex_closedBall 0 1 (mem_closedBall.mpr (hfx x hx)) hx ht0
    (sub_nonneg_of_le ht1) (by norm_num)
  simp only [mem_closedBall, dist_zero_right] at hconvex
  assumption

/-- The derivative of the interpolation map `x ↦ x + t • g x` at `x` is `id + t • fderiv ℝ g x`. -/
lemma hasFDerivAt_interpolation {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {g : E → E} (hgcont_diff : ContDiff ℝ 1 g)
    (t : ℝ) (x : E) :
    HasFDerivAt (fun x => x + t • g x)
      (ContinuousLinearMap.id ℝ E + t • fderiv ℝ g x) x :=
    HasFDerivAt.fun_add (hasFDerivAt_id x)
    ((hgcont_diff.differentiable (by norm_num)).differentiableAt.hasFDerivAt.const_smul t)

/-- A `C¹` function has a bounded derivative on the closed unit ball. -/
lemma fderiv_bound_of_contDiff {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {g : E → E} (hgcont_diff : ContDiff ℝ 1 g) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ closedBall (0 : E) 1, ‖fderiv ℝ g x‖ ≤ M := by
  have hcont : ContinuousOn (fun x => ‖fderiv ℝ g x‖) (closedBall (0 : E) 1) :=
    (hgcont_diff.continuous_fderiv (by norm_num)).continuousOn.norm
  obtain ⟨x, _, hmax⟩ := (isCompact_closedBall (0 : E) 1).exists_isMaxOn (by simp) hcont
  exact ⟨‖fderiv ℝ g x‖, norm_nonneg _, fun y hy => hmax hy⟩

/-- The diagonal entry `(k,k)` of the matrix `J t x = toMatrix(id + t·fderiv g x)`
    is `1 + t·(A x)ₖₖ`. -/
lemma J_diag {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {g : E → E}
    (b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E)
    (J : ℝ → E → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ)
    (hJ : ∀ t x, J t x = toMatrix b.toBasis b.toBasis
      (ContinuousLinearMap.id ℝ E + t • fderiv ℝ g x))
    (t : ℝ) (x : E) (k : Fin (Module.finrank ℝ E)) :
    J t x k k = 1 + t * (toMatrix b.toBasis b.toBasis (fderiv ℝ g x)) k k := by
  rw [hJ]
  have hid_diag : (toMatrix b.toBasis b.toBasis id) k k = 1 := by
    rw [toMatrix_id_eq_basis_toMatrix, Module.Basis.toMatrix_self b.toBasis]
    exact Matrix.one_apply_eq k
  rw [← hid_diag]
  simp only [coe_id, map_add, toMatrix_id_eq_basis_toMatrix,
    OrthonormalBasis.coe_toBasis, map_smul, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]

/-- The off‑diagonal entry `(k,j)` of `J t x` is `t·(A x)ₖⱼ`. -/
lemma J_offdiag {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {g : E → E}
    (b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E)
    (J : ℝ → E → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ)
    (hJ : ∀ t x, J t x = toMatrix b.toBasis b.toBasis
      (ContinuousLinearMap.id ℝ E + t • fderiv ℝ g x))
    (t : ℝ) (x : E) (k j : Fin (Module.finrank ℝ E)) (hjk : j ≠ k) :
    J t x k j = t * ((toMatrix b.toBasis b.toBasis) (fderiv ℝ g x)) k j := by
  rw [hJ]
  have hid_offdiag :
      (toMatrix b.toBasis b.toBasis id) k j = 0 := by
    simp only [toMatrix_id_eq_basis_toMatrix]
    rw [Module.Basis.toMatrix_self b.toBasis]
    exact Matrix.one_apply_ne' hjk
  simp only [coe_id, map_add, toMatrix_id_eq_basis_toMatrix,
    OrthonormalBasis.coe_toBasis, map_smul, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    add_eq_right]
  rw [← hid_offdiag]
  simp

/-- There exists a uniform bound `M ≥ 0` for all matrix entries of the derivative of `g` on
  the closed ball. -/
lemma A_bound_of_contDiff {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {g : E → E} (hgcont_diff : ContDiff ℝ 1 g)
    (b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ closedBall (0 : E) 1,
      ∀ k j : Fin (Module.finrank ℝ E),
      ‖(toMatrix b.toBasis b.toBasis (fderiv ℝ g x)) k j‖ ≤ M := by
  obtain ⟨M, hM0, hM⟩ := fderiv_bound_of_contDiff hgcont_diff
  refine ⟨M, hM0, fun x hx k j => ?_⟩
  simp only [toMatrix_apply, OrthonormalBasis.coe_toBasis,
    ContinuousLinearMap.coe_coe, OrthonormalBasis.coe_toBasis_repr_apply]
  calc ‖(b.repr ((fderiv ℝ g x) (b.toBasis j))).ofLp k‖
      ≤ ‖b.repr ((fderiv ℝ g x) (b.toBasis j))‖ := PiLp.norm_apply_le _ k
    _ = ‖(fderiv ℝ g x) (b.toBasis j)‖ := b.repr.norm_map _
    _ ≤ ‖fderiv ℝ g x‖ * ‖b.toBasis j‖ := le_opNorm _ _
    _ = ‖fderiv ℝ g x‖ := by simp [OrthonormalBasis.norm_eq_one]
    _ ≤ M := hM x hx

/-- For the row `k`, the sum of absolute off‑diagonal entries of `J t x` is bounded by `t·n·M`. -/
lemma sum_offdiag_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {g : E → E} (b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E)
    (J : ℝ → E → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ)
    (hJ : ∀ t x, J t x = toMatrix b.toBasis b.toBasis
      (ContinuousLinearMap.id ℝ E + t • fderiv ℝ g x))
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ x ∈ closedBall (0 : E) 1,
    ∀ k j : Fin (Module.finrank ℝ E),
    ‖(toMatrix b.toBasis b.toBasis (fderiv ℝ g x)) k j‖ ≤ M)
    {t : ℝ} (ht0 : 0 ≤ t) {x : E} (hx : x ∈ closedBall (0 : E) 1) (k : Fin (Module.finrank ℝ E)) :
    ∑ j ∈ Finset.univ.erase k, ‖J t x k j‖ ≤
      t * Module.finrank ℝ E * M := by
  let n := Module.finrank ℝ E
  have hsum_eq : ∑ j ∈ Finset.univ.erase k, ‖J t x k j‖ =
      ∑ j ∈ Finset.univ.erase k,
      t * ‖((toMatrix b.toBasis b.toBasis) (fderiv ℝ g x)) k j‖ := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [J_offdiag b J hJ t x k j (Finset.mem_erase.mp hj).1, norm_mul, Real.norm_of_nonneg ht0]
  rw [hsum_eq]
  calc ∑ j ∈ Finset.univ.erase k,
        t * ‖((toMatrix b.toBasis b.toBasis) (fderiv ℝ g x)) k j‖
      ≤ ∑ _ ∈ Finset.univ.erase k, t * M := Finset.sum_le_sum
        (fun j _ => mul_le_mul_of_nonneg_left (hM x hx k j) ht0)
    _ = (Finset.univ.erase k).card • (t * M) := by rw [Finset.sum_const]
    _ ≤ t * n * M := by
        have hn : (↑(n - 1) : ℝ) ≤ ↑n := by exact_mod_cast Nat.sub_le n 1
        simp only [Finset.mem_univ, Finset.card_erase_of_mem, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
        nlinarith [mul_nonneg ht0 hM0]

/-- If `t < t0` where `t0 = 1/((n+1)(M+1))`, then `t·n·M < |1 + t·(A x)ₖₖ|`. -/
lemma diag_bound_of_lt {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {g : E → E} (b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E)
    {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ x ∈ closedBall (0 : E) 1, ∀ k j : Fin (Module.finrank ℝ E),
      ‖(toMatrix b.toBasis b.toBasis (fderiv ℝ g x)) k j‖ ≤ M)
    {t0 : ℝ} (ht0_def : t0 = 1 / ((Module.finrank ℝ E + 1) * (M + 1))) {t : ℝ} (ht0 : 0 ≤ t)
    (htC : t < t0) {x : E} (hx : x ∈ closedBall (0 : E) 1) (k : Fin (Module.finrank ℝ E)) :
    let A := fun (_ : ℝ) (x : E) =>
      toMatrix b.toBasis b.toBasis (fderiv ℝ g x)
    t * Module.finrank ℝ E * M < ‖1 + t * A 0 x k k‖ := by
  intro A
  have h1 : 1 - t * M ≤ ‖1 + t * A 0 x k k‖ := by
    have hentry : ‖t * A 0 x k k‖ ≤ t * M := by
      rw [norm_mul, Real.norm_of_nonneg ht0]
      exact mul_le_mul_of_nonneg_left (hM x hx k k) ht0
    linarith [norm_one (α := ℝ), @norm_sub_le_norm_add ℝ _ (1 : ℝ) (t * A 0 x k k)]
  have ht_bound : t * Module.finrank ℝ E * M < 1 - t * M := by
    have : t * ((↑(Module.finrank ℝ E) + 1) * (M + 1)) < 1 :=
      calc t * ((↑(Module.finrank ℝ E) + 1) * (M + 1))
          < t0 * ((↑(Module.finrank ℝ E) + 1) * (M + 1)) := by
              apply mul_lt_mul_of_pos_right htC; positivity
        _ = 1 := by rw [ht0_def]; field_simp
    nlinarith
  linarith

/-- If `t < t0` where `t0 = 1/((n+1)(M+1))`, for each row `k`, the sum of off‑diagonal entries is
  strictly less than the absolute value of the diagonal entry. -/
lemma diag_dom_of_lt {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {g : E → E} (b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E)
    (J : ℝ → E → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ)
    (hJ : ∀ t x, J t x = toMatrix b.toBasis b.toBasis
      (ContinuousLinearMap.id ℝ E + t • fderiv ℝ g x))
    {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ x ∈ closedBall (0 : E) 1, ∀ k j : Fin (Module.finrank ℝ E),
      ‖(toMatrix b.toBasis b.toBasis (fderiv ℝ g x)) k j‖ ≤ M)
    {t0 : ℝ} (ht0_def : t0 = 1 / ((Module.finrank ℝ E + 1) * (M + 1)))
    {t : ℝ} (ht0 : 0 ≤ t) (htC : t < t0) {x : E} (hx : x ∈ closedBall (0 : E) 1)
    (k : Fin (Module.finrank ℝ E)) :
    ∑ j ∈ Finset.univ.erase k, ‖J t x k j‖ < ‖J t x k k‖ := by
  rw [J_diag b J hJ t x k]
  linarith [sum_offdiag_bound b J hJ hM0 hM ht0 hx k,
    diag_bound_of_lt b hM0 hM ht0_def ht0 htC hx k]

/-- If for every row the sum of off‑diagonal entries is less than the absolute diagonal entry,
    then the matrix `J t x` is invertible, hence the corresponding linear map is a unit. -/
lemma isUnit_of_diag_dom {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {g : E → E}
    (b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E)
    (J : ℝ → E → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ)
    (hJ : ∀ t x, J t x = toMatrix b.toBasis b.toBasis
      (ContinuousLinearMap.id ℝ E + t • fderiv ℝ g x)) {t : ℝ} {x : E}
      (hdom : ∀ k : Fin (Module.finrank ℝ E),
      ∑ j ∈ Finset.univ.erase k, ‖J t x k j‖ < ‖J t x k k‖) :
    IsUnit (ContinuousLinearMap.id ℝ E + t • fderiv ℝ g x) := by
  have hmat_unit : IsUnit (J t x) := by
    rw [Matrix.isUnit_iff_isUnit_det]
    simp only [isUnit_iff_ne_zero, ne_eq]
    exact det_ne_zero_of_sum_row_lt_diag hdom
  have hJeq : toMatrix b.toBasis b.toBasis
      (↑(ContinuousLinearMap.id ℝ E + t • fderiv ℝ g x) : E →ₗ[ℝ] E) = J t x := by simp [hJ]
  have hcoe : IsUnit (↑(ContinuousLinearMap.id ℝ E + t • fderiv ℝ g x) : E →ₗ[ℝ] E) := by
    rwa [← isUnit_toMatrix_iff b.toBasis, hJeq]
  exact isUnit_iff_isUnit_toLinearMap.mpr hcoe

/-- If a linear map is a unit (i.e., invertible), its range is the whole space. -/
lemma range_eq_top_of_isUnit {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {g : E → E} {t : ℝ} {x : E}
    (hunit : IsUnit (ContinuousLinearMap.id ℝ E + t • fderiv ℝ g x)) :
    (ContinuousLinearMap.id ℝ E + t • fderiv ℝ g x).range = ⊤ := by
  obtain ⟨u, hu⟩ := hunit
  rw [← hu, range_eq_top]
  exact fun y => ⟨u.inv y, congr_fun (congr_arg DFunLike.coe u.mul_inv) y⟩

/-- Strict differentiability version of `hasFDerivAt_interpolation`. -/
lemma hasStrictFDerivAt_interpolation {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {g : E → E} (hgcont_diff : ContDiff ℝ 1 g) (t : ℝ) (x : E) :
    HasStrictFDerivAt (fun x => x + t • g x)
      (ContinuousLinearMap.id ℝ E + t • fderiv ℝ g x) x :=
  HasStrictFDerivAt.fun_add (hasStrictFDerivAt_id x)
  ((hgcont_diff.hasStrictFDerivAt (n := 1) (by norm_num)).const_smul t)

/-- If a family `f_t` has surjective derivative at every point of the interior of the ball,
    then the image of the interior under `f_t` is open. -/
lemma isOpen_image_interior {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {f_t : ℝ → E → E} {g : E → E} {t : ℝ}
    (hft_strict : ∀ x ∈ closedBall (0 : E) 1,
      HasStrictFDerivAt (f_t t)
        (ContinuousLinearMap.id ℝ E + t • fderiv ℝ g x) x)
    (hft_surj : ∀ x ∈ interior (closedBall (0 : E) 1),
      (ContinuousLinearMap.id ℝ E + t • fderiv ℝ g x).range = ⊤) :
    IsOpen (f_t t '' interior (closedBall (0 : E) 1)) := by
  apply isOpen_iff_mem_nhds.mpr
  intro y ⟨x, hx, hxy⟩
  rw [← hxy, ← (hft_strict x (interior_subset hx)).map_nhds_eq_of_surj (hft_surj x hx)]
  exact Filter.image_mem_map (interior_mem_nhds.mpr (mem_interior_iff_mem_nhds.mp hx))

/-- For an open set `G` in the closed ball, the supremum of parameters for which the line segment
  from `p` to `e` stays in `G` gives a boundary point in the closure. `b` in Roger's paper. -/
lemma sSup_segment_mem_closure_image {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f_t : ℝ → E → E} {t : ℝ} {p e : E} {G : Set E}
    (hG_open : IsOpen G) (hG_sub : G ⊆ f_t t '' closedBall (0 : E) 1)
    (hG_sub_ball : G ⊆ closedBall (0 : E) 1) (hp : p ∈ G) (he_not : e ∉ G)
    (he_ball : e ∈ closedBall (0 : E) 1) (hft_closed : IsClosed (f_t t '' closedBall (0 : E) 1)) :
    let S : Set ℝ := {s ∈ Set.Icc 0 1 | AffineMap.lineMap p e s ∈ G}
    let b := sSup S
    AffineMap.lineMap p e b ∉ G ∧ AffineMap.lineMap p e b ∈ closure G ∧
    (∃ x ∈ closedBall (0 : E) 1, f_t t x = AffineMap.lineMap p e b) ∧ b ∈ Set.Icc (0 : ℝ) 1 := by
  intro S b
  have hseg0 : AffineMap.lineMap p e (0 : ℝ) = p := AffineMap.lineMap_apply_zero _ _
  have hseg1 : AffineMap.lineMap p e (1 : ℝ) = e := AffineMap.lineMap_apply_one _ _
  have hS_bddAbove : BddAbove S := ⟨1, fun s hs => hs.1.2⟩
  have hb_mem_Icc : b ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨le_csSup_of_le ⟨1, fun s hs => hs.1.2⟩ ⟨by simp [Set.mem_Icc], hseg0 ▸ hp⟩ (by norm_num),
    csSup_le ⟨0, by simp [Set.mem_Icc], by rw [hseg0] ; exact hp⟩ (fun c hc => hc.1.2)⟩
  have hb_not_Gt : AffineMap.lineMap p e b ∉ G := by
    intro hb_in
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hG_open _ hb_in
    have hb_lt_one : b < 1 := by
      rcases eq_or_lt_of_le hb_mem_Icc.2 with hb1 | hb1
      · exfalso; rw [hb1, hseg1] at hb_in; exact he_not hb_in
      · exact hb1
    let ε' := min ε (1 - b) / 3
    have hε'_pos : 0 < ε' := div_pos (lt_min hε (by linarith)) (by linarith)
    have hs'_le : b + ε' ≤ 1 := by unfold ε'; linarith [min_le_right ε (1 - b)]
    have hs'_close : dist (AffineMap.lineMap p e (b + ε')) (AffineMap.lineMap p e b) < ε := by
      rw [AffineMap.lineMap_apply, AffineMap.lineMap_apply, dist_eq_norm]
      simp only [vadd_eq_add, vsub_eq_sub]
      have hsimp : (b + ε') • (e - p) + p - (b • (e - p) + p) = ε' • (e - p) := by simp [add_smul]
      rw [hsimp, norm_smul, Real.norm_of_nonneg hε'_pos.le]
      have hpe : ‖e - p‖ ≤ 2 := by linarith [norm_sub_le e p, mem_closedBall_zero_iff.mp he_ball,
          mem_closedBall_zero_iff.mp (hG_sub_ball hp)]
      calc ε' * ‖e - p‖
          ≤ ε' * 2 := by exact (mul_le_mul_iff_of_pos_left hε'_pos).mpr hpe
        _ ≤ (min ε (1 - b) / 3) * 2 := by unfold ε'; linarith
        _ < ε := by linarith [min_le_left ε (1 - b)]
    linarith [le_csSup ⟨1, fun s hs => hs.1.2⟩
      (show b + ε' ∈ S from ⟨⟨by linarith [hb_mem_Icc.1], hs'_le⟩, hball hs'_close⟩)]
  have hb_closure : AffineMap.lineMap p e b ∈ closure G :=
    ContinuousWithinAt.mem_closure (s := S) AffineMap.lineMap_continuous.continuousWithinAt
    (csSup_mem_closure ⟨0, by simp [Set.mem_Icc], by rw [hseg0] ; exact hp⟩ ⟨1, fun s hs => hs.1.2⟩)
    fun s hs => hs.2
  have hb_in_image : ∃ x ∈ closedBall (0 : E) 1,f_t t x = AffineMap.lineMap p e b :=
    hft_closed.closure_subset (closure_mono hG_sub hb_closure)
  exact ⟨hb_not_Gt, hb_closure, hb_in_image, hb_mem_Icc⟩

/-- A point of the closed ball that is not interior must lie on the sphere and be fixed by `f_t`
  if `f_t` fixes the sphere. -/
lemma preimage_boundary_of_not_interior {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f_t : ℝ → E → E} {t : ℝ} (hf_fixed : ∀ x ∈ sphere (0 : E) 1, f_t t x = x)
    {x : E} (hx : x ∈ closedBall (0 : E) 1) (hx_not_int : x ∉ interior (closedBall (0 : E) 1)) :
    ‖x‖ = 1 ∧ f_t t x = x := by
  simp only [mem_ball, dist_zero_right, not_lt, interior_closedBall (0 : E) one_pos.ne']
    at hx_not_int
  have hx_norm : ‖x‖ = 1 :=
    le_antisymm (mem_closedBall_zero_iff.mp hx) hx_not_int
  have hx_sphere : x ∈ sphere (0 : E) 1 := mem_sphere_zero_iff_norm.mpr hx_norm
  exact ⟨hx_norm, hf_fixed x hx_sphere⟩

/-- If a point `e` of the closed ball is not in an open subset `G` that contains the image of the
  interior, then `e` must lie on the sphere. -/
lemma norm_eq_one_of_not_mem_image {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f_t : ℝ → E → E} {t : ℝ} (hf_fixed : ∀ x ∈ sphere (0 : E) 1, f_t t x = x)
    {G : Set E} (hG_open : IsOpen G) (hG_sub : G ⊆ f_t t '' closedBall (0 : E) 1)
    (hG_sub_ball : G ⊆ closedBall (0 : E) 1) (hft_closed : IsClosed (f_t t '' closedBall (0 : E) 1))
    (hG_nonempty : G.Nonempty) {e : E} (he_ball : e ∈ closedBall (0 : E) 1) (he_not : e ∉ G)
    (hG_image : f_t t '' interior (closedBall (0 : E) 1) ⊆ G) :
    ‖e‖ = 1 := by
  obtain ⟨p, hp⟩ := hG_nonempty
  obtain ⟨hb_not, _, ⟨x, hx_ball, hfx⟩, hb_mem_Icc⟩ :=
  sSup_segment_mem_closure_image hG_open hG_sub hG_sub_ball hp he_not he_ball hft_closed
  have hx_not_int : x ∉ interior (closedBall (0 : E) 1) := by
    intro hx_int
    have : f_t t x ∈ G := hG_image ⟨x, hx_int, rfl⟩
    rw [hfx] at this
    exact hb_not this
  obtain ⟨hx_norm, hx_fix⟩ := preimage_boundary_of_not_interior hf_fixed hx_ball hx_not_int
  by_contra he_not_sphere
  have he_lt : ‖e‖ < 1 :=
    lt_of_le_of_ne (mem_closedBall_zero_iff.mp he_ball) he_not_sphere
  have he_interior : e ∈ interior (closedBall (0 : E) 1) := by
    rw [interior_closedBall (0 : E) one_pos.ne']
    exact mem_ball_zero_iff.mpr he_lt
  have hp_interior : p ∈ interior (closedBall (0 : E) 1) := by
    apply interior_mono hG_sub_ball
    rw [hG_open.interior_eq]
    exact hp
  have hb_interior : AffineMap.lineMap p e (sSup _) ∈ interior (closedBall (0 : E) 1) :=
    (convex_closedBall 0 1).interior.lineMap_mem hp_interior he_interior hb_mem_Icc
  have hb_norm : ‖AffineMap.lineMap p e (sSup {s ∈ Set.Icc (0 : ℝ) 1 |
    AffineMap.lineMap p e s ∈ G})‖ < 1 := by
    rw [interior_closedBall (0 : E) one_pos.ne'] at hb_interior
    exact mem_ball_zero_iff.mp hb_interior
  rw [← hfx, hx_fix] at hb_norm
  linarith

/-- Under the assumptions of the stability lemma, the image of the interior equals the interior of
  the ball. -/
lemma Gt_eq_interior {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {G : Set E} (hG_open : IsOpen G) (hG_sub : G ⊆ closedBall (0 : E) 1)
    (hboundary : ∀ e ∈ closedBall (0 : E) 1, e ∉ G → ‖e‖ = 1) :
    G = interior (closedBall (0 : E) 1) := by
  apply Set.eq_of_subset_of_subset
  · intro y hy ; apply interior_mono hG_sub ; rw [hG_open.interior_eq] ; exact hy
  · intro y hy
    by_contra hy_not_Gt
    have hy_ball : y ∈ closedBall (0 : E) 1 := interior_subset hy
    have hy_norm_lt : ‖y‖ < 1 := by
      rw [interior_closedBall (0 : E) one_pos.ne'] at hy
      exact mem_ball_zero_iff.mp hy
    have hy_norm_eq : ‖y‖ = 1 := hboundary y hy_ball hy_not_Gt
    linarith

/-- When `Gt_eq_interior` holds and `t` is small enough, the map `f_t` is a bijection from the
  closed ball onto itself. -/
lemma bijOn_of_Gt_eq_interior {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : E → E} {f_t : ℝ → E → E} {g : E → E} {C : NNReal} {t : ℝ}
    (hft_def : ∀ t x, f_t t x = x + t • g x) (hg_def : ∀ x, g x = f x - x)
    (hfx : ∀ x ∈ closedBall (0 : E) 1, f x ∈ closedBall 0 1)
    (hf_fixed : ∀ x ∈ sphere (0 : E) 1, f_t t x = x)
    (hC : LipschitzOnWith C g (closedBall (0 : E) 1))
    (hGt_eq : f_t t '' interior (closedBall (0 : E) 1) = interior (closedBall (0 : E) 1))
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (ht1c : t < 1 / C) :
    Set.BijOn (f_t t) (closedBall (0 : E) 1) (closedBall (0 : E) 1) := by
  have hmaps : Set.MapsTo (f_t t) (closedBall (0 : E) 1) (closedBall (0 : E) 1) := by
    intro x hx
    rw [hft_def, show g x = f x - x from hg_def x]
    exact mapsTo_interpolation hfx ht0 ht1 hx
  have hinj : Set.InjOn (f_t t) (closedBall (0 : E) 1) := by
    intro x hx y hy hxy
    simp only [hft_def] at hxy
    exact injOn_of_lipschitz_lt_one hC ht0 ht1c hx hy hxy
  refine ⟨hmaps, hinj, fun y hy => ?_⟩
  rcases eq_or_lt_of_le (mem_closedBall_zero_iff.mp hy) with hy1 | hy1
  · exact ⟨y, hy, hf_fixed y (mem_sphere_zero_iff_norm.mpr hy1)⟩
  · have hy_interior : y ∈ interior (closedBall (0 : E) 1) := by
      rw [interior_closedBall (0 : E) one_pos.ne']
      exact mem_ball_zero_iff.mpr hy1
    rw [← hGt_eq] at hy_interior
    obtain ⟨x, hx_int, hfx⟩ := hy_interior
    exact ⟨x, interior_subset hx_int, hfx⟩

/-- The coefficient of the characteristic polynomial of `J t x` depends continuously on `x`. -/
lemma continuous_Px_coeff {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (k : ℕ) (b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E)
    {g : E → E} (hg : ContDiff ℝ 1 g) :
    Continuous (fun x => (Matrix.det (1 + (Polynomial.X : Polynomial ℝ) •
      (toMatrix b.toBasis b.toBasis (fderiv ℝ g x)).map
      Polynomial.C)).coeff k) := by
  simp only [Matrix.det_apply, Polynomial.finset_sum_coeff]
  apply continuous_finset_sum
  intro σ _
  simp only [Polynomial.coeff_smul]
  have : ∀ x, (∏ i : Fin (Module.finrank ℝ E), (1 + (Polynomial.X : Polynomial ℝ) •
    ((toMatrix b.toBasis b.toBasis) ↑(fderiv ℝ g x)).map Polynomial.C) (σ i) i) =
    ∏ i : Fin (Module.finrank ℝ E), ((if σ i = i then (1 : Polynomial ℝ) else 0) +
    Polynomial.X * Polynomial.C ((toMatrix b.toBasis b.toBasis)
    ↑(fderiv ℝ g x) (σ i) i)) := by intro x ; congr
  have hentry_cont : ∀ i j : Fin (Module.finrank ℝ E),
    Continuous (fun x => (toMatrix b.toBasis b.toBasis (fderiv ℝ g x)) i j) := by
    intro i j
    have : (fun x => (toMatrix b.toBasis b.toBasis (fderiv ℝ g x)) i j) =
        (fun x => b.repr ((fderiv ℝ g x) (b j)) i) := by
      simp [toMatrix_apply, OrthonormalBasis.coe_toBasis]
    rw [this]
    fun_prop
  apply Continuous.const_smul
  have key : ∀ (s : Finset (Fin (Module.finrank ℝ E))), ∀ m : ℕ,
      Continuous (fun x =>
        (∏ i ∈ s, ((if σ i = i then (1 : Polynomial ℝ) else 0) +
          Polynomial.X * Polynomial.C
            ((toMatrix b.toBasis b.toBasis (fderiv ℝ g x)) (σ i) i))).coeff m) := by
    intro s
    induction s using Finset.induction with
    | empty =>
      intro m
      simp only [Polynomial.X_mul_C, Finset.prod_empty, Polynomial.coeff_one]
      exact continuous_const
    | insert ha s' h_notin ih =>
      intro m
      simp_rw [Finset.prod_insert h_notin, Polynomial.coeff_mul]
      apply continuous_finset_sum
      intro ⟨j1, j2⟩ _
      refine Continuous.mul ?_ (ih j2)
      simp only [Polynomial.X_mul_C, Polynomial.coeff_add, Polynomial.coeff_C_mul]
      fun_prop
  simp_rw [this, key]

/-- If `f` is `C¹` and maps the closed unit ball into the unit sphere, then for every interior
  point `x`, the image of `fderiv ℝ f x` lies in the orthogonal complement of `span {f x}`. -/
lemma fderiv_range_subset_orthogonal {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : E → E} (hf_diff : ContDiff ℝ 1 f)
    (hf_maps : ∀ x ∈ closedBall (0 : E) 1, f x ∈ sphere (0 : E) 1)
    {x : E} (hx : x ∈ interior (closedBall (0 : E) 1)) :
    ∀ v : E, fderiv ℝ f x v ∈ (Submodule.span ℝ {f x})ᗮ := by
  have hfx_norm : ‖f x‖ = 1 :=
    mem_sphere_zero_iff_norm.mp (hf_maps x (interior_subset hx))
  have hconst_on : ∀ y ∈ interior (closedBall (0 : E) 1),
      (fun y => inner (𝕜 := ℝ) (f y) (f y)) y = 1 := by
    intro y hy
    have hfy := hf_maps y (interior_subset hy)
    rw [mem_sphere_zero_iff_norm] at hfy
    simp [hfy]
  have hfderiv_inner_zero : fderiv ℝ (fun y => inner (𝕜 := ℝ) (f y) (f y)) x = 0 :=
    HasFDerivAt.fderiv (hasFDerivAt_zero_of_eventually_const (1 : ℝ)
      (Filter.eventually_of_mem (isOpen_interior.mem_nhds hx) hconst_on))
  simp only [inner_self_eq_norm_sq_to_K, RCLike.ofReal_real_eq_id, id_eq] at hfderiv_inner_zero
  have hgdiff : (DifferentiableAt ℝ (fun x => ‖x‖ ^ 2) (f x)) :=
      DifferentiableAt.norm_sq ℝ differentiableAt_id
  rw [fderiv_comp' x (hgdiff) ((hf_diff.differentiable_one).differentiableAt)]
    at hfderiv_inner_zero
  simp only [fderiv_norm_sq_apply, ContinuousLinearMap.smul_comp] at hfderiv_inner_zero
  have hfderiv_inner_zero' : ((innerSL ℝ) (f x)).comp (fderiv ℝ f x) = 0 := by
    simp only [two_nsmul] at hfderiv_inner_zero
    ext v
    have hv := congr_fun (congr_arg DFunLike.coe hfderiv_inner_zero) v
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.zero_apply] at hv
    rw [add_self_eq_zero] at hv
    exact mem_eqLocus.mp hv
  intro v
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
  exact congr_fun (congr_arg DFunLike.coe hfderiv_inner_zero') v

/-- If `f` is `C¹`, maps the closed unit ball into the unit sphere, and `E` is nontrivial,
  then `det(Df(x)) = 0` for every interior point `x`. -/
lemma det_fderiv_eq_zero_of_range_subset_orthogonal {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E] {f : E → E}
    (hf_diff : ContDiff ℝ 1 f)
    (hf_maps : ∀ x ∈ closedBall (0 : E) 1, f x ∈ sphere (0 : E) 1)
    {x : E} (hx : x ∈ interior (closedBall (0 : E) 1)) :
    LinearMap.det (fderiv ℝ f x : E →ₗ[ℝ] E) = 0 := by
  have hfx_norm : ‖f x‖ = 1 :=
    mem_sphere_zero_iff_norm.mp (hf_maps x (interior_subset hx))
  have hfx_ne : f x ≠ 0 := by
    intro h; rw [h, norm_zero] at hfx_norm; linarith
  have hrange_le : LinearMap.range (fderiv ℝ f x : E →ₗ[ℝ] E) ≤ (Submodule.span ℝ {f x})ᗮ := by
    intro w ⟨v, hv⟩
    rw [← hv]
    exact (fderiv_range_subset_orthogonal hf_diff hf_maps hx) v
  have hdim : Module.finrank ℝ (Submodule.span ℝ {f x})ᗮ = Module.finrank ℝ E - 1 := by
    grind [finrank_span_singleton (K := ℝ) hfx_ne,
      Submodule.finrank_add_finrank_orthogonal (K := Submodule.span ℝ {f x})]
  have hrank_lt : Module.finrank ℝ (LinearMap.range (fderiv ℝ f x : E →ₗ[ℝ] E)) <
      Module.finrank ℝ E :=
    calc Module.finrank ℝ (LinearMap.range (fderiv ℝ f x : E →ₗ[ℝ] E))
        ≤ Module.finrank ℝ (Submodule.span ℝ {f x})ᗮ :=
            Submodule.finrank_mono hrange_le
      _ = Module.finrank ℝ E - 1 := hdim
      _ < Module.finrank ℝ E := Nat.sub_lt Module.finrank_pos one_pos
  have hnotinj : ¬ Function.Injective (fderiv ℝ f x : E →ₗ[ℝ] E) := by
    intro hinj
    linarith [finrank_range_of_inj hinj]
  rw [det_eq_zero_iff_ker_ne_bot, Ne, ker_eq_bot]
  exact hnotinj

/-- If the determinant of `id + s • fderiv g x` is nonzero for all `0 ≤ s < t₀`, then it is
  strictly positive for any `t ∈ [0, t₀)`. -/
lemma det_pos_of_lt_t0 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {g : E → E}
    {t0 : ℝ}
    (hdet_ne : ∀ s : ℝ, 0 ≤ s → s < t0 → ∀ x ∈ closedBall (0 : E) 1,
      (ContinuousLinearMap.id ℝ E + s • fderiv ℝ g x).det ≠ 0)
    {t : ℝ} (ht0 : 0 ≤ t) (htC : t < t0) {x : E} (hx : x ∈ closedBall (0 : E) 1) :
    0 < (ContinuousLinearMap.id ℝ E + t • fderiv ℝ g x).det := by
  have hdet_cont : ContinuousOn (fun s => (ContinuousLinearMap.id ℝ E + s • fderiv ℝ g x).det)
      (Set.Icc 0 t) := by
    apply Continuous.continuousOn
    apply ContinuousLinearMap.continuous_det.comp
    fun_prop
  have hdet_ne_zero : ∀ s ∈ Set.Icc (0 : ℝ) t,
      (ContinuousLinearMap.id ℝ E + s • fderiv ℝ g x).det ≠ 0 :=
    fun s ⟨hs0, hst⟩ => hdet_ne s hs0 (hst.trans_lt htC) x hx
  have hpos_at_zero : 0 < (ContinuousLinearMap.id ℝ E + (0 : ℝ) • fderiv ℝ g x).det := by
    simp only [zero_smul, add_zero]
    have : (ContinuousLinearMap.id ℝ E : E →L[ℝ] E).det =
        LinearMap.det (LinearMap.id : E →ₗ[ℝ] E) := by simp [ContinuousLinearMap.det]
    grind [LinearMap.det_id]
  rcases lt_or_gt_of_ne (hdet_ne_zero t ⟨ht0, le_refl t⟩) with hlt | hgt
  · obtain ⟨s, hs_mem, hs_zero⟩ := intermediate_value_Icc' ht0 hdet_cont
      (Set.mem_Icc.mpr ⟨le_of_lt hlt, le_of_lt hpos_at_zero⟩)
    exact False.elim (hdet_ne_zero s hs_mem hs_zero)
  · exact hgt

/-- If `f_t` is bijective on the closed unit ball with strictly positive Jacobian, then the
  integral of the Jacobian determinant over the ball equals the volume of the ball -/
lemma I_eq_volume_of_bij {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {g : E → E} {f_t : ℝ → E → E} {t : ℝ}
    (hft_strict_fderiv : ∀ x ∈ closedBall (0 : E) 1, HasStrictFDerivAt (f_t t)
      (ContinuousLinearMap.id ℝ E + t • fderiv ℝ g x) x)
    (hft_bij : Set.BijOn (f_t t) (closedBall (0 : E) 1) (closedBall (0 : E) 1))
    (hdet_pos : ∀ x ∈ closedBall 0 1, 0 < (ContinuousLinearMap.id ℝ E + t • fderiv ℝ g x).det) :
    ∫ x in closedBall (0 : E) 1,
      LinearMap.det (fderiv ℝ (f_t t) x : E →ₗ[ℝ] E) =
    (volume (closedBall (0 : E) 1)).toReal := by
  have hcov := MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul volume
    measurableSet_closedBall
    (fun x hx => (hft_strict_fderiv x hx).hasFDerivAt.hasFDerivWithinAt)
    hft_bij.injOn (fun _ => (1 : ℝ))
  simp only [hft_bij.image_eq, smul_eq_mul, mul_one, integral_const, MeasurableSet.univ,
    measureReal_restrict_apply, univ_inter] at hcov
  have hint_eq : ∫ x in closedBall (0 : E) 1, LinearMap.det (fderiv ℝ (f_t t) x : E →ₗ[ℝ] E) =
      ∫ x in closedBall (0 : E) 1,
      |(ContinuousLinearMap.id ℝ E + t • fderiv ℝ g x).det| := by
    apply MeasureTheory.integral_congr_ae
    apply MeasureTheory.ae_restrict_of_forall_mem measurableSet_closedBall
    intro x hx
    dsimp only
    rw [(hft_strict_fderiv x hx).hasFDerivAt.fderiv, abs_of_pos (hdet_pos x hx)]
  rw [hint_eq, ← hcov]
  rfl

/-- If the derivative of `f_t` satisfies `fderiv ℝ (f_t t) x = id + t • fderiv ℝ g x`
  everywhere, then `det(Df_t(x))` is the evaluation of an explicit polynomial `P_x` at `t`. -/
lemma det_fderiv_eq_poly_eval {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {g : E → E} {f_t : ℝ → E → E}
    (b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E)
    (hft_def : ∀ t x, fderiv ℝ (f_t t) x =
      ContinuousLinearMap.id ℝ E + t • fderiv ℝ g x) :
    let n := Module.finrank ℝ E
    let A : E → Matrix (Fin n) (Fin n) ℝ :=
      fun x => LinearMap.toMatrix b.toBasis b.toBasis (fderiv ℝ g x)
    let P_x : E → Polynomial ℝ := fun x =>
      Matrix.det (1 + (Polynomial.X : Polynomial ℝ) • (A x).map Polynomial.C)
    ∀ x : E, ∀ t : ℝ,
      LinearMap.det (fderiv ℝ (f_t t) x : E →ₗ[ℝ] E) = (P_x x).eval t := by
  intro n A P_x x t
  rw [hft_def t x]
  rw [show LinearMap.det (↑(ContinuousLinearMap.id ℝ E + t • fderiv ℝ g x) : E →ₗ[ℝ] E) =
      Matrix.det (1 + t • A x) from by
    rw [← LinearMap.det_toMatrix b.toBasis]; congr; ext i j
    simp [A, LinearMap.toMatrix_apply, Matrix.one_apply, OrthonormalBasis.coe_toBasis]]
  simp only [P_x, eval_det]
  apply congr_arg Matrix.det; ext i j
  rw [matPolyEquiv_eval]
  simp [Matrix.one_apply]
  split_ifs with hij <;> simp [mul_comm]

/-- The integral `I(t) = ∫_{B^n} det(Df_t(x)) dx` equals the evaluation of an explicit
  polynomial `P` at `t`, whose coefficients are integrals of the pointwise polynomial
  coefficients of `P_x` over the ball. -/
lemma I_eq_poly_eval {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {g : E → E} {f_t : ℝ → E → E}
    (hgcont_diff : ContDiff ℝ 1 g)
    (b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E)
    (I : ℝ → ℝ) (hI_def : ∀ t, I t = ∫ x in closedBall (0 : E) 1,
      LinearMap.det (fderiv ℝ (f_t t) x : E →ₗ[ℝ] E))
    (hdet_eval : ∀ x ∈ closedBall (0 : E) 1, ∀ t : ℝ,
      LinearMap.det (fderiv ℝ (f_t t) x : E →ₗ[ℝ] E) =
      (Matrix.det (1 + (Polynomial.X : Polynomial ℝ) •
        (LinearMap.toMatrix b.toBasis b.toBasis (fderiv ℝ g x)).map Polynomial.C)).eval t) :
    let n := Module.finrank ℝ E
    let A : E → Matrix (Fin n) (Fin n) ℝ :=
      fun x => LinearMap.toMatrix b.toBasis b.toBasis (fderiv ℝ g x)
    let P_x : E → Polynomial ℝ := fun x =>
      Matrix.det (1 + (Polynomial.X : Polynomial ℝ) • (A x).map Polynomial.C)
    let P : Polynomial ℝ := ∑ k ∈ Finset.range n.succ,
      Polynomial.monomial k (∫ x in closedBall (0 : E) 1, (P_x x).coeff k)
    ∀ t : ℝ, I t = P.eval t := by
  intro n A P_x P t
  have hP_x_deg : ∀ x, (P_x x).natDegree ≤ n := by
    intro x
    have := Polynomial.natDegree_det_X_add_C_le (A x) 1
    simp only [Fintype.card_fin] at this
    convert this using 2
    simp only [map_zero, Polynomial.C_1, Matrix.map_one, P_x, add_comm]
  rw [hI_def]
  simp only [P, Polynomial.eval_finset_sum, Polynomial.eval_monomial]
  conv_rhs => arg 2; ext k; rw [← MeasureTheory.integral_mul_const]
  rw [← MeasureTheory.integral_finset_sum]
  · apply MeasureTheory.integral_congr_ae
    apply MeasureTheory.ae_restrict_of_forall_mem measurableSet_closedBall
    intro x hx
    simp only
    rw [hdet_eval x hx t, Polynomial.eval_eq_sum_range' (n := n.succ)]
    exact Nat.lt_succ_of_le (hP_x_deg x)
  · intro k _
    apply MeasureTheory.Integrable.mul_const
    exact (ContinuousOn.integrableOn_compact' (isCompact_closedBall 0 1)
      measurableSet_closedBall
      (continuous_Px_coeff k b hgcont_diff).continuousOn).integrable

/-- A polynomial function that is constantly `c` on `[0, t₀)` equals `c` always. -/
lemma poly_const_of_const_on_Ico {t0 : ℝ} (ht0_pos : 0 < t0)
    (I : ℝ → ℝ) (c : ℝ) (hI_poly : ∃ P : Polynomial ℝ, ∀ t, I t = P.eval t)
    (hI_const_interval : ∀ t ∈ Set.Ico (0 : ℝ) t0, I t = c) :
    ∀ t : ℝ, I t = c := by
  obtain ⟨P, hP⟩ := hI_poly
  obtain hP_const | hP_nonconst := eq_or_ne P.natDegree 0
  · rw [natDegree_eq_zero] at hP_const
    obtain ⟨x, hx⟩ := nonempty_Ico.mpr ht0_pos
    grind [eval_C]
  · have h_finite :=
        (TendstoCofinite_of_nonconst_polynomial P hP_nonconst).finite_preimage_singleton _ c
    cases ((Set.Ico_infinite ht0_pos).not_finite (h_finite.subset (by grind)))

/-- No smooth retraction from the unit closed ball to the unit sphere exists. -/
theorem cont_diff_ball_to_sphere_no_fixed [Nontrivial E]
    (f : E → E) (hf_diff : ContDiff ℝ 1 f)
    (hf_maps : ∀ x ∈ closedBall (0 : E) 1, f x ∈ sphere (0 : E) 1)
    (hf_fixed : ∀ x ∈ sphere (0 : E) 1, f x = x) : False := by
  -- change cont_diff to ContDiffOn closedBall (0 : E) 1
  let g : E → E := fun x => f x - x
  let f_t : ℝ → E → E := fun t x => x + t • g x
  have hgcont_diff : ContDiff ℝ 1 g := by fun_prop
  have hg_lipschitz : ∃ K : NNReal, LipschitzOnWith K g (closedBall (0 : E) 1) :=
    ContDiffOn.exists_lipschitzOnWith hgcont_diff.contDiffOn (by norm_num) (convex_closedBall 0 1)
    (isCompact_closedBall 0 1)
  obtain ⟨C', hC'⟩ := hg_lipschitz
  let C : NNReal := max C' 1
  have hC_pos : (0 : ℝ) < ↑C := by simp [C, NNReal.coe_max]
  have hC_lip : LipschitzOnWith C g (closedBall (0 : E) 1) := hC'.weaken (le_max_left _ _)
  have hfx : ∀ x ∈ closedBall (0 : E) 1, f x ∈ closedBall 0 1 := by
    intro x
    rw [mem_closedBall_zero_iff]
    exact fun hx => le_of_eq (hf_maps x (mem_closedBall_zero_iff.mpr hx))
  let b := stdOrthonormalBasis ℝ E
  let n := (Module.finrank ℝ E)
  let J : ℝ → E → Matrix (Fin n) (Fin n) ℝ := fun t x =>
  (toMatrix b.toBasis b.toBasis) (ContinuousLinearMap.id ℝ E + t • fderiv ℝ g x)
  obtain ⟨M, hM0, hM⟩ := A_bound_of_contDiff hgcont_diff b
  let t0 : ℝ := min (min (1 / ((↑n + 1) * (M + 1))) (1 / C)) 1
  have ht0_pos : 0 < t0 := by
    simp only [t0, lt_min_iff]
    exact ⟨⟨by positivity, by positivity⟩, one_pos⟩
  have ht0_lt_diag : t0 ≤ 1 / ((↑n + 1) * (M + 1)) := (min_le_left _ _).trans (min_le_left _ _)
  have ht0_lt_C : t0 ≤ 1 / (↑C) := (min_le_left _ _).trans (min_le_right _ _)
  have ht0_lt_one : t0 ≤ 1 := min_le_right _ _
  have hdiag_dom : ∀ t : ℝ, 0 ≤ t → t < t0 → ∀ x ∈ closedBall (0 : E) 1, ∀ k : Fin n,
    ∑ j ∈ Finset.univ.erase k, ‖J t x k j‖ < ‖J t x k k‖ :=
    fun t ht0 htC x hx k =>
    diag_dom_of_lt b J (fun t x => rfl) hM0 hM (rfl) ht0 (htC.trans_le ht0_lt_diag) hx k
  have hft_nonsingular : ∀ t : ℝ, 0 ≤ t → t < t0 → ∀ x ∈ closedBall (0 : E) 1,
      IsUnit (ContinuousLinearMap.id ℝ E + t • fderiv ℝ g x) :=
    fun t ht0 htC x hx => isUnit_of_diag_dom b J (fun t x => rfl) (hdiag_dom t ht0 htC x hx)
  have hft_surj : ∀ t : ℝ, 0 ≤ t → t < t0 → ∀ x ∈ interior (closedBall (0 : E) 1),
      (ContinuousLinearMap.id ℝ E + t • fderiv ℝ g x).range = ⊤ :=
    fun t ht0 htC x hx => range_eq_top_of_isUnit (hft_nonsingular t ht0 htC x (interior_subset hx))
  have hft_strict_fderiv : ∀ t : ℝ, 0 ≤ t → t < t0 → ∀ x ∈ closedBall (0 : E) 1,
      HasStrictFDerivAt (f_t t) (ContinuousLinearMap.id ℝ E + t • fderiv ℝ g x) x :=
    fun t ht0 htC x hx => hasStrictFDerivAt_interpolation hgcont_diff t x
  let G_t := fun t => f_t t '' interior (closedBall (0 : E) 1)
  have hGt_subset : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      f_t t '' interior (closedBall (0 : E) 1) ⊆ closedBall (0 : E) 1 := by
    intro t ht0 ht1 y ⟨x, hx, hxy⟩
    rw [← hxy]
    exact mapsTo_interpolation hfx ht0 ht1 (interior_subset hx)
  have hGt_open : ∀ t : ℝ, 0 ≤ t → t < t0 → IsOpen (G_t t) :=
    fun t ht0 htC => isOpen_image_interior (fun x hx => hft_strict_fderiv t ht0 htC x hx)
    (fun x hx => hft_surj t ht0 htC x hx)
  have hft_cont : ∀ t : ℝ, Continuous (f_t t) := by fun_prop
  have hboundary_general : ∀ t : ℝ, 0 ≤ t → t < t0 → t < 1 → ∀ e ∈ closedBall (0 : E) 1,
      e ∉ G_t t → ‖e‖ = 1 :=
    fun t ht0 htC ht1 e he_ball he_not => norm_eq_one_of_not_mem_image
    (fun x hx => by simp [f_t, g, hf_fixed x hx]) (hGt_open t ht0 htC)
    (fun y ⟨x, hx, hxy⟩ => ⟨x, interior_subset hx, hxy⟩) (hGt_subset t ht0 ht1.le)
    ((isCompact_closedBall 0 1).image (hft_cont t)).isClosed
    ⟨f_t t 0, 0, mem_interior_iff_mem_nhds.mpr (closedBall_mem_nhds 0 one_pos), rfl⟩ he_ball he_not
    (Set.Subset.refl _)
  have hGt_eq_interior : ∀ t : ℝ, 0 ≤ t → t < t0 → t < 1 →
      G_t t = interior (closedBall (0 : E) 1) := by
    intro t ht0 htC ht1
    apply Set.eq_of_subset_of_subset
    · intro y hy
      apply interior_mono (hGt_subset t ht0 ht1.le)
      rw [(hGt_open t ht0 htC).interior_eq]
      exact hy
    · intro y hy
      by_contra hy_not_Gt
      have hy_norm_lt : ‖y‖ < 1 := by
        rw [interior_closedBall (0 : E) one_pos.ne'] at hy
        exact mem_ball_zero_iff.mp hy
      have hy_norm_eq : ‖y‖ = 1 := hboundary_general t ht0 htC ht1 y (interior_subset hy) hy_not_Gt
      linarith
  have hft_bij : ∀ t : ℝ, 0 ≤ t → t < t0 → t < 1 → t < 1 / C → Set.BijOn (f_t t)
      (closedBall (0 : E) 1) (closedBall (0 : E) 1) :=
    fun t ht0 htC ht1 ht1c => bijOn_of_Gt_eq_interior (fun t x => rfl) (fun x => rfl) hfx
    (fun x hx => by simp [f_t, g, hf_fixed x hx]) hC_lip (hGt_eq_interior t ht0 htC ht1)
    ht0 ht1.le ht1c
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  let I : ℝ → ℝ := fun t => ∫ x in closedBall (0 : E) 1,
    LinearMap.det (fderiv ℝ (f_t t) x : E →ₗ[ℝ] E) ∂volume
  have hI_const_interval: ∀ t : ℝ, 0 ≤ t → t < t0 → t < 1 → t < 1 / C →
      I t = (volume (closedBall (0 : E) 1)).toReal := by
    intro t ht0 htC ht1 ht1C
    have hdet_ne_all : ∀ s : ℝ, 0 ≤ s → s < t0 →
        ∀ x ∈ closedBall (0 : E) 1,
        (ContinuousLinearMap.id ℝ E + s • fderiv ℝ g x).det ≠ 0 := by
      intro s hs0 hsC x hx h
      have hdet : ∀ t : ℝ, 0 ≤ t → t < t0 → ∀ x ∈ closedBall (0 : E) 1, (J t x).det ≠ 0 :=
        fun t ht0 htC x hx => det_ne_zero_of_sum_row_lt_diag (hdiag_dom t ht0 htC x hx)
      apply hdet s hs0 hsC x hx
      rw [LinearMap.det_toMatrix]
      have : (ContinuousLinearMap.id ℝ E + s • fderiv ℝ g x).det =
          LinearMap.det (↑(ContinuousLinearMap.id ℝ E + s • fderiv ℝ g x) : E →ₗ[ℝ] E) := rfl
      rw [this, ← LinearMap.det_toMatrix b.toBasis] at h
      exact det_eq_zero_iff_ker_ne_bot.mpr fun a ↦ (hdet s hs0 hsC x hx) h
    have hdet_pos : ∀ x ∈ closedBall (0 : E) 1,
        0 < (ContinuousLinearMap.id ℝ E + t • fderiv ℝ g x).det :=
      fun x hx => det_pos_of_lt_t0 hdet_ne_all ht0 htC hx
    exact I_eq_volume_of_bij (fun x hx => hft_strict_fderiv t ht0 htC x hx)
      (hft_bij t ht0 htC ht1 ht1C) hdet_pos
  have hI_const_all : ∀ t : ℝ, I t = (volume (closedBall (0 : E) 1)).toReal := by
    let A : E → Matrix (Fin n) (Fin n) ℝ := fun x => toMatrix b.toBasis b.toBasis (fderiv ℝ g x)
    let P_x : E → Polynomial ℝ := fun x =>
      Matrix.det (1 + (Polynomial.X : Polynomial ℝ) • (A x).map Polynomial.C)
    let P : Polynomial ℝ := ∑ k ∈ Finset.range n.succ,
      Polynomial.monomial k (∫ x in closedBall (0 : E) 1, (P_x x).coeff k)
    have hft_def : ∀ t x, fderiv ℝ (f_t t) x = ContinuousLinearMap.id ℝ E + t • fderiv ℝ g x :=
      fun t x => by
        have : fderiv ℝ (f_t t) x = fderiv ℝ (fun y => y + t • (f y - y)) x := by congr
        rw [this]; exact (hasFDerivAt_interpolation hgcont_diff t x).fderiv
    have hdet_eval : ∀ x ∈ closedBall (0 : E) 1, ∀ t : ℝ,
        LinearMap.det (fderiv ℝ (f_t t) x : E →ₗ[ℝ] E) = (P_x x).eval t :=
      fun x _ t => det_fderiv_eq_poly_eval b hft_def x t
    have hI_poly : ∀ t : ℝ, I t = P.eval t :=
      I_eq_poly_eval hgcont_diff b I (fun _ => rfl) hdet_eval
    exact poly_const_of_const_on_Ico ht0_pos I _ ⟨P, hI_poly⟩ (fun t ⟨ht0, htC⟩ =>
        hI_const_interval t ht0 htC (htC.trans_le (min_le_right _ _)) (htC.trans_le ht0_lt_C))
  have hdet_zero : ∀ x ∈ interior (closedBall (0 : E) 1),
      LinearMap.det (fderiv ℝ (f_t 1) x : E →ₗ[ℝ] E) = 0 := by
    intro x hx
    rw [show f_t 1 = f from by simp [f_t, g]]
    exact det_fderiv_eq_zero_of_range_subset_orthogonal hf_diff hf_maps hx
  have hI1_zero : I 1 = 0 := by
    simp only [I]
    apply MeasureTheory.integral_eq_zero_of_ae
    apply Filter.eventually_of_mem (U := interior (closedBall (0 : E) 1))
    · rw [mem_ae_iff, interior_closedBall, Measure.restrict_apply (isOpen_ball.measurableSet.compl)]
      · have : (ball (0 : E) 1)ᶜ ∩ closedBall (0 : E) 1 = sphere (0 : E) 1 := by
          ext x
          simp only [mem_inter_iff, mem_compl_iff, mem_ball, dist_zero_right, not_lt,
            mem_closedBall, mem_sphere_iff_norm, sub_zero]
          exact ⟨fun hx => by linarith, fun hx => ⟨by linarith, by linarith⟩⟩
        rw [this]
        exact Measure.addHaar_sphere_of_ne_zero volume 0 one_ne_zero
      · exact one_ne_zero
    · exact fun x hx => hdet_zero x hx
  have hball_pos : 0 < (volume (closedBall (0 : E) 1)).toReal :=
    ENNReal.toReal_pos (measure_closedBall_pos volume (0 : E) one_pos).ne'
    measure_closedBall_lt_top.ne
  linarith [hI1_zero, hI_const_all 1]





theorem cont_diff_retract_of_cont_retract (f : E → E) (hf_cont : ContinuousOn f (closedBall 0 1))
    (hf_retract : Set.MapsTo f (closedBall 0 1) (sphere 0 1))
    (hf_fixes : ∀ x ∈ sphere 0 1, f x = x) :
    ∃ (g : E → E), ContDiffOn ℝ 1 g (closedBall 0 1) ∧ ∀ x ∈ sphere 0 1, g x = x := by
  let e := fun x => f x - x
  -- `e` is continuous, vanishes on the sphere and is bounded by `2`
  have he_cont : ContinuousOn e (closedBall 0 1) := by fun_prop
  have he_vanishes : ∀ x ∈ sphere 0 1, e x = 0 := by grind
  have he_bound : ∀ x ∈ (closedBall 0 1), ‖e x‖ ≤ 2 := by
    intro x hx
    simp only [e]
    transitivity ‖f x‖ + ‖x‖
    · exact norm_sub_le (f x) x
    · linarith [mem_sphere_zero_iff_norm.mp (hf_retract (hx)), mem_closedBall_zero_iff.mp hx]
  -- `e` is uniformly continuous on the closed ball
  have he_uc : UniformContinuousOn e (closedBall (0 : E) 1) :=
    (isCompact_closedBall 0 1).uniformContinuousOn_of_continuous he_cont
  rw [Metric.uniformContinuousOn_iff] at he_uc
  obtain ⟨δ, hδ_pos, hδ⟩ := he_uc (1/4) (by norm_num)
  have hθ_exists : ∃ θ : ℝ, 3/4 < θ ∧ θ < 1 ∧
      ∀ x ∈ closedBall (0 : E) 1, θ ≤ ‖x‖ → ‖e x‖ < 1/4 := by
    refine ⟨1 - min (δ/2) (1/8),
      by linarith [min_le_right (δ/2) (1/8 : ℝ)],
      by linarith [lt_min (half_pos hδ_pos) (by norm_num : (0:ℝ) < 1/8)],
      ?_⟩
    intro x hx hθx
    have hxle1 : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx
    have hxpos : 0 < ‖x‖ := by linarith [min_le_right (δ/2) (1/8 : ℝ), hθx]
    -- Radially project x onto the sphere
    set y := ‖x‖⁻¹ • x with hy_def
    have hy_sphere : y ∈ sphere (0 : E) 1 := by
      simp [hy_def, norm_smul, inv_mul_cancel₀ hxpos.ne']
    have hy_ball : y ∈ closedBall (0 : E) 1 := sphere_subset_closedBall hy_sphere
    -- dist(x, y) = 1 - ‖x‖ ≤ δ/2 < δ
    have hdist : dist x y < δ := by sorry
    sorry
  sorry



/-- On a compact set, any continuous map can be uniformly approximated by a differentiable map. -/
theorem differentiable_approx_of_continuous {δ : ℝ} (hδ : 0 < δ) {U : Set E}
    (hUcompact : IsCompact U) (G : E → E) (hG_cont : Continuous G) [Nontrivial E] :
    ∃ (P : C(E, E)), Differentiable ℝ P ∧ ∀ y ∈ U, ‖P y - G y‖ < δ := by
  let basis := stdOrthonormalBasis ℝ E
  let n := Module.finrank ℝ E
  -- We construct the subalgebra of polynomials from `ℝ^n` to `ℝ` and show they are differentiable
  -- Projecting onto one of the axes is continuous and differentiable
  let coord (i : Fin n) : C(E, ℝ) :=
    { toFun := fun x => basis.toBasis.equivFunL x i
      continuous_toFun := by fun_prop}
  have hcoord_diff (i : Fin n) : Differentiable ℝ (coord i) :=
    ((ContinuousLinearMap.proj i).comp
    (basis.toBasis.equivFunL : E →L[ℝ] (Fin n → ℝ))).differentiable
  -- This gives us the subalgebra of polynomials.
  let generator : Set C(E, ℝ) := Set.range coord
  have hgen_diff : ∀ f ∈ generator, Differentiable ℝ f := by
    rintro _ ⟨i, rfl⟩
    exact hcoord_diff i
  let A : Subalgebra ℝ C(E, ℝ) := Algebra.adjoin ℝ generator
  have hA_diff : ∀ f ∈ A, Differentiable ℝ f := by
    let D : Subalgebra ℝ C(E, ℝ) :=
      { carrier := {f | Differentiable ℝ f}
        zero_mem' := differentiable_const 0
        one_mem' := differentiable_const 1
        add_mem' := fun hf hg => hf.add hg
        mul_mem' := fun hf hg => hf.mul hg
        algebraMap_mem' := fun r => differentiable_const r }
    have hA_sub : A ≤ D := Algebra.adjoin_le hgen_diff
    exact fun f hf => hA_sub hf
  -- This subalgebra of polynomials separates points.
  have hAsep : A.SeparatesPoints := by
    intro x y hxy
    have hequiv: basis.toBasis.equivFunL x ≠ basis.toBasis.equivFunL y := by simpa
    obtain ⟨i, hi⟩ : ∃ i : (Fin n), basis.toBasis.equivFunL x i ≠ basis.toBasis.equivFunL y i := by
      contrapose! hequiv
      ext i
      exact (hequiv i)
    have hf_mem : coord i ∈ A := Algebra.subset_adjoin (Set.mem_range_self i)
    exact ⟨coord i, Set.mem_image_of_mem (fun f ↦ f.1) hf_mem, hi⟩
  let G_i (i : Fin n) : C(E, ℝ) :=
    {toFun := fun y => basis.toBasis.equivFunL (G y) i, continuous_toFun := by fun_prop}
  let coordEquiv := basis.toBasis.equivFunL
  have hpos_symm : 0 < ‖(coordEquiv.symm : ((Fin n) → ℝ) →L[ℝ] E)‖ := by
    refine lt_of_le_of_ne (norm_nonneg _) fun h_eq => ?_
    let w : Fin n → ℝ := fun _ => 1
    have hw : w ≠ 0 := by
      haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp Module.finrank_pos
      obtain ⟨i⟩ := (inferInstance : Nonempty (Fin n))
      intro h
      have : w i = 0 := congr_fun h i
      linarith
    have hw0 : (coordEquiv.symm : (Fin n → ℝ) →L[ℝ] E) w = 0 := by
      rw [norm_eq_zero.1 h_eq.symm]
      rfl
    have hfalse : coordEquiv (coordEquiv.symm w) = coordEquiv 0 := congrArg coordEquiv hw0
    rw [coordEquiv.apply_symm_apply w, map_zero] at hfalse
    exact hw hfalse
  -- Define `C` as the operator norm for l.symm
  let C := ‖(coordEquiv.symm : (Fin n → ℝ) →L[ℝ] E)‖
  let ε' := δ / (2 * C)
  have hε' : 0 < ε' := div_pos (hδ) (mul_pos zero_lt_two hpos_symm)
  -- Using the Stone-Weierstrass theorem, pick each `P_i` to be `ε'-close` to each `G_i`.
  have approx (i : Fin n) :=
    ContinuousMap.exists_mem_subalgebra_near_continuous_of_isCompact_of_separatesPoints
    hAsep (G_i i) hUcompact hε'
  choose p_i hp_i using approx
  -- Construct `P` as a function from `ℝ^n` to `ℝ^n` using the component functions `P_i`.
  let P : C(E, E) :=
    { toFun := fun y => basis.toBasis.equivFunL.symm (fun i => (p_i i : C(E, ℝ)) y),
      continuous_toFun := by fun_prop}
  -- The difference between `P` and `G` on `Σ` is bounded by `δ`
  have hP_bound : ∀ y ∈ U , ‖P y - G y‖ < δ := by
    intro y hy
    let v : Fin n → ℝ := fun i => (p_i i : C(E, ℝ)) y - (basis.toBasis.equivFunL (G y)) i
    have hv i : |v i| < ε' := by
      grind only [ContinuousMap.coe_mk, Real.norm_eq_abs, (hp_i i).2 y hy]
    have hnorm_v : ‖v‖ < ε' := by rw [pi_norm_lt_iff hε']; exact fun i => hv i
    have hP_eq : P y - G y = coordEquiv.symm v := by
      dsimp [P, v]
      have h_repr_eq : basis.toBasis.repr (G y) = coordEquiv (G y) := rfl
      have hG : G y = coordEquiv.symm (coordEquiv (G y)) := (coordEquiv.symm_apply_apply (G y)).symm
      have h_simp : coordEquiv (coordEquiv.symm (coordEquiv (G y))) = coordEquiv (G y) :=
        by rw [coordEquiv.symm_apply_apply (G y)]
      rw [h_repr_eq, hG, ← coordEquiv.symm.map_sub, h_simp]
      rfl
    rw [hP_eq]
    calc
      ‖coordEquiv.symm v‖
      ≤ C * ‖v‖ := le_opNorm (coordEquiv.symm : (Fin n → ℝ) →L[ℝ] E) v
    _ < C * ε' := mul_lt_mul_of_pos_left hnorm_v hpos_symm
    _ = δ / 2 := by
        unfold ε'
        field_simp [ne_of_gt hpos_symm]
        exact div_self (ne_of_gt hpos_symm)
    _ < δ := half_lt_self hδ
  have hp_i_diff (i : Fin n) : Differentiable ℝ (p_i i) := hA_diff (p_i i) (hp_i i).1
  have hP_diff : Differentiable ℝ P :=
    (basis.toBasis.equivFunL.symm : (Fin n → ℝ) →L[ℝ] E).differentiable.comp
    (differentiable_pi.mpr hp_i_diff)
  use P

variable [BrouwerFixedPoint E]
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Stability of zero (Lemma 6). If `G` is a left inverse of `f` on the closed ball,
    and `Gtilde` is a continuous function on `f(Bⁿ)` with `‖G - Gtilde‖ ≤ 1` pointwise,
    then `Gtilde` has a zero in `f(Bⁿ)`. -/
lemma stability_of_zero (f : E → E) (hf_cont : ContinuousOn f (closedBall 0 1))
    (G : C(E, E)) (hG_left_inv : ∀ x ∈ closedBall 0 1, G (f x) = x)
    (Gtilde : E → E) (hGtilde_cont : ContinuousOn Gtilde (f '' closedBall 0 1))
    (hbound : ∀ y ∈ f '' closedBall 0 1, ‖G y - Gtilde y‖ ≤ 1) :
    ∃ y ∈ f '' closedBall 0 1, Gtilde y = 0 := by
  -- Define the function whose fixed point gives the zero of `Gtilde`
  let diff_fun : E → E := fun x => x - Gtilde (f x)
  -- `B^n` contains the image of itself under diff_fun.
  have hMapsTo : Set.MapsTo diff_fun (closedBall 0 1) (closedBall 0 1) :=
    fun x hx => by grind [mem_closedBall_zero_iff]
  -- `diff_fun` is continuous on `B^n`
  have diff_fun_cont_on : ContinuousOn diff_fun (closedBall 0 1) :=
    (continuousOn_id' _).sub (hGtilde_cont.comp hf_cont (mapsTo_image f _))
  obtain ⟨x, hx⟩ := BrouwerFixedPoint.brouwer_fixed_point
    (Set.MapsTo.restrict diff_fun (closedBall 0 1) (closedBall 0 1) hMapsTo)
    (ContinuousOn.mapsToRestrict diff_fun_cont_on hMapsTo)
  have hx_eq : diff_fun (x : E) = (x : E) := congr_arg Subtype.val hx
  grind

/-- Let `B^n` be the closed unit ball (closedBall 0 1).
Let `f : B^n → ℝ^n` be an continuous injective map.
Then `f(0)` lies in the interior of `f(B^n)`. -/
theorem invariance_of_domain_interior (f : E → E)
    (hf_cont : ContinuousOn f (closedBall 0 1)) (hf_inj : Set.InjOn f (closedBall 0 1))
    : f 0 ∈ interior (f ''(closedBall 0 1)) := by
  -- In the case where `n = 0`, `ℝ^0` has only a single point.
  cases subsingleton_or_nontrivial E
  · have : Set.Nonempty (interior (f '' closedBall 0 1)) := by simp
    rw [Set.Nonempty.eq_univ this]
    simp
  -- The equivalence between `B^n` and `f(B^n)`.
  let FEquiv := Equiv.Set.imageOfInjOn f (closedBall 0 1) hf_inj
  -- The inverse map of `f` is continuous.
  let FInvCmap : C(f '' closedBall 0 1, (closedBall (0 : E) 1)) :=
  ⟨FEquiv.symm,  Continuous.continuous_symm_of_equiv_compact_to_t2 (continuous_induced_rng.mpr <|
    ContinuousOn.restrict hf_cont)⟩
  -- `f(B^n)` is closed.
  have hballimageclosed : IsClosed (f '' closedBall 0 1) :=
    ((isCompact_closedBall 0 1).image_of_continuousOn hf_cont).isClosed
  -- The Tietze extension theorem, finding a continuous function `G` that extends `f⁻¹`.
  obtain ⟨G, hG⟩ := ContinuousMap.exists_restrict_eq hballimageclosed FInvCmap
  -- `G` has a zero at `f 0`.
  have hG0 : G (f 0) = (0 : E) := by
    let fzero' : (f '' closedBall 0 1) := ⟨f 0, ⟨0, by simp, rfl⟩⟩
    have := congr($hG fzero')
    conv_lhs at this => simp [fzero']
    have H : (⟨f 0, ⟨0, by simp, rfl⟩⟩ : f '' closedBall 0 1) = FEquiv ⟨0, by simp⟩ :=
      Subtype.ext rfl
    simp [this, FInvCmap, fzero', H]
  let G' : C(E, E) := ⟨fun x => (G x : E), continuous_subtype_val.comp (ContinuousMap.continuous G)⟩
  -- Prove that `G` restricted to the image equals `FInvCmap`
  have hG_eq : ∀ y (hy : y ∈ f '' closedBall 0 1), G y = FInvCmap ⟨y, hy⟩ := by
    grind [ContinuousMap.restrict_apply]
  -- Now prove the left‑inverse property for `G'`
  have hG'_left_inv : ∀ x ∈ closedBall 0 1, G' (f x) = x := fun x hx =>
    (congr_arg Subtype.val (hG_eq (f x) (mem_image_of_mem f hx))).trans
    (congr_arg Subtype.val (FEquiv.symm_apply_apply ⟨x, hx⟩))
  -- Let `Gtilde : f(B^n) → ℝ^n` be a continuous function such that
  -- `‖G(y) - Gtilde(y)‖ ≤ 1 ∀ y ∈ f(B^n)`. Then `∃ y ∈ f (B^n)` such that `Gtilde(y)=0`.
  have hStability_of_zero (Gtilde : E → E) (hGtilde : ContinuousOn Gtilde (f '' closedBall 0 1))
      (hy : ∀ y ∈ (f '' closedBall 0 1), ‖G y - Gtilde y‖ ≤ 1) :
      ∃ y ∈ f '' closedBall 0 1, Gtilde y = 0 :=
    stability_of_zero f hf_cont G' hG'_left_inv Gtilde hGtilde hy
  -- By way of contradiction, we assume that `f(0)` is not an interior point of `f(B^n)` .
  -- From this, we construct a `Gtilde` as in the above lemma to derive a contradiction.
  by_contra hnotinterior
  -- `G` is continuous at `f(0)`.
  have hG_cont_at_f0 : ContinuousAt (fun x => (G x : E)) (f 0) := Continuous.continuousAt
    (continuous_subtype_val.comp (ContinuousMap.continuous G))
  rw [continuousAt_iff] at hG_cont_at_f0
  -- `G` is continuous on the whole space, so by picking `ε > 0` small enough,
  -- we can ensure `‖G(y)‖ ≤ 0.1` whenever `y ∈ ℝ^n` and `‖y - f(0)‖ ≤ 2ε`.
  obtain ⟨twoε, h2εpos, h2ε1⟩ := hG_cont_at_f0 0.1 (by norm_num)
  let ε : ℝ := twoε /2
  have hε1 : ε > 0 := half_pos h2εpos
  have h2εeq : twoε = 2 * ε := by ring
  -- As `f(0)` is not an interior point of `f(B^n)`, there exists a point `c ∈ ℝ^n` with
  -- `‖c - f(0)‖ < ε` not in `f(B^n)`.
  obtain ⟨c, hc1, hc2⟩ : ∃ c, dist c (f 0) < ε ∧ c ∉ f '' closedBall 0 1 := by
    rw [mem_interior] at hnotinterior
    push_neg at hnotinterior
    specialize hnotinterior (ball (f 0) ε)
    simp only [isOpen_ball, mem_ball, dist_self, forall_const, imp_not_comm] at hnotinterior
    have hnotball := hnotinterior hε1
    rw [Set.not_subset] at hnotball
    obtain ⟨c, hc⟩ := hnotball
    exact ⟨c, ⟨mem_ball.mp hc.1, (Set.mem_compl_iff (f '' closedBall 0 1) c).mp hc.2⟩⟩
  -- `‖G(y)‖ ≤ 0.1` whenever `‖y - c‖ ≤ ε`.
  have hG_small (y : E) (h : ‖y - c‖ ≤ ε) : ‖(G y : E)‖ ≤ 0.1 := by
    rw [dist_eq_norm] at hc1
    have hdist : ‖y - f 0‖ < 2 * ε := by
      have hineq := norm_add_le (y - c) (c - f 0)
      simp only [sub_add_sub_cancel] at hineq
      linarith
    grind [dist_zero_right, dist_eq_norm]
  -- Let `Σ₁ := {y ∈ f(B^n): ‖y - c‖ ≥ ε}`.
  let sigma1 : Set (E) := {y ∈ f '' closedBall 0 1 | ‖y - c‖ ≥ ε}
  -- Let `Σ₂ := {y ∈ ℝ^n : ‖y - c‖ = ε}`.
  let sigma2 : Set (E) := sphere c ε
  -- Let `Σ := Σ₁ ∪ Σ₂`.
  let sigma := sigma1 ∪ sigma2
  -- By construction, `Σ` is compact.
  -- `Σ₁` is compact.
  have hsigma1compact : IsCompact sigma1 := by
    rw [isCompact_iff_isClosed_bounded]
    -- `Σ₁` is the complement of the open ball, so it is closed.
    have hopen : IsOpen {y | ‖y - c‖ ≥ ε }ᶜ := by simpa
    [← mem_ball_iff_norm, Set.compl_setOf, -isOpen_ball] using isOpen_ball (x := c) (ε := ε)
    -- `f(B^n)` is compact as it is the image of a compact set under a continuous function
    -- As compact sets are bounded and `Σ₁` is contained in this, `Σ₁` is bounded.
    have himgcompact := IsCompact.image_of_continuousOn (isCompact_closedBall 0 1) hf_cont
    exact ⟨(IsClosed.and hballimageclosed ({isOpen_compl := (hopen) })), Bornology.IsBounded.subset
    (IsCompact.isBounded himgcompact) (Set.sep_subset (f '' closedBall 0 1) fun x ↦ ‖x - c‖ ≥ ε)⟩
  -- It remains to be shown that `Σ₂` is compact, which follows from it being a sphere.
  have hsigmacompact : IsCompact sigma := IsCompact.union hsigma1compact (isCompact_sphere c ε)
  -- Let `Φ` be the function `Φ(y) := max(ε / ‖y - c‖, 1)) * (y - c)`.
  let Phi : (E) → (E) := fun y => c + (max (ε / ‖y - c‖) (1 : ℝ)) • (y - c)
  -- The image of `f(B^n)` under `Φ` is `Σ`.
  have hPhiimg (y : E) (hy : y ∈ f '' closedBall 0 1) : Phi y ∈ sigma := by
    by_cases h : ε < ‖y - c‖
    -- If `ε < ‖y - c‖`, then `Φ(y) ∈ Σ₁`.
    · have hyc : 0 < ‖y - c‖ := by linarith
      grind [max_eq_right_of_lt, one_smul, add_sub_cancel, div_lt_one hyc]
    -- If `‖y - c‖ ≤ ε`, then `Φ(y) ∈ Σ₂`.
    · right
      simp only [not_lt] at h
      have hy_neq_c : c ≠ y := by
        by_contra h
        rw [← h] at hy
        exact hc2 hy
      have hleft : 1 ≤ ε / ‖y - c‖ :=
      (one_le_div (norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hy_neq_c)))).mpr h
      have hPhi : Phi y = c + (ε / ‖y - c‖) • (y - c) := by
        dsimp [Phi]
        rwa [max_eq_left]
      rw [hPhi]
      simp [sigma2, norm_smul, (sub_ne_zero_of_ne (Ne.symm hy_neq_c)), hε1.le]
  -- `Φ` is continuous.
  have hPhicont : ContinuousOn Phi (f '' closedBall 0 1) := by
    refine ContinuousOn.add continuousOn_const (ContinuousOn.smul ?_
    (ContinuousOn.sub (continuousOn_id' (f '' closedBall 0 1)) continuousOn_const))
    rw [continuousOn_iff_continuous_restrict]
    exact Continuous.max ((Continuous.div continuous_const (Continuous.norm
    (Continuous.sub continuous_subtype_val continuous_const)))
    (by grind [norm_eq_zero, sub_ne_zero])) continuous_const
  -- By construction, `G` is non-zero on `Σ₁`
  have hGavoids : ∀ y ∈ sigma1, G y ≠ (0 : (E)) := by
    intro y hy
    by_contra hGeq
    have hG_inj_on_image : Set.InjOn G (f '' closedBall 0 1) := by
      intro x hx y hy h
      have hx_eq : G x = FInvCmap ⟨x, hx⟩ := by grind
      have hy_eq : G y = FInvCmap ⟨y, hy⟩ := by grind
      rw [hx_eq, hy_eq] at h
      exact congr_arg Subtype.val (FEquiv.symm.injective h)
    have hyeq : y = f 0 := by
      have hf0_image : f 0 ∈ f '' closedBall 0 1 := ⟨0, by simp, rfl⟩
      have heq : G y = G (f 0) := SetCoe.ext (Eq.trans hGeq hG0.symm)
      exact hG_inj_on_image hy.1 hf0_image heq
    rw [Set.mem_sep_iff, hyeq] at hy
    rw [dist_eq_norm, ← norm_neg, neg_sub] at hc1
    linarith
  -- The norm of `G` is continuous on `Σ₁`
  let normG : E → ℝ := fun y => ‖(G y : E)‖
  have hGconton : ContinuousOn G (f '' closedBall 0 1) := (ContinuousMap.continuous G).continuousOn
  have hgnormconton1 : ContinuousOn normG sigma1 :=
    ContinuousOn.norm (continuous_subtype_val.comp_continuousOn
    (ContinuousOn.mono hGconton (Set.sep_subset (f '' closedBall 0 1) fun x ↦ ‖x - c‖ ≥ ε)))
  -- As `Σ₁` is compact, `G` is bounded below on `Σ₁` by some `δ > 0`.
  -- We can shrink `δ` to assume `δ < 0.1`.
  obtain ⟨δ, hδ1, hδ2, hδ3⟩ : ∃ (δ : ℝ), 0 < δ ∧ δ < 0.1 ∧ ∀ y ∈ sigma1, δ ≤ ‖(G y : E)‖ := by
    by_cases hP : sigma1.Nonempty
    · obtain ⟨z, hz, hmin⟩ := IsCompact.exists_isMinOn hsigma1compact hP hgnormconton1
      let δ := min (normG z) (0.05)
      have hδ_pos : 0 < δ := lt_min_iff.mpr ⟨norm_pos_iff.mpr (hGavoids z hz), by norm_num⟩
      have hδ_lt_0_1 : δ < 0.1 := (min_le_right _ 0.05).trans_lt (by norm_num)
      have hδ_lower : ∀ y ∈ sigma1, normG y ≥ δ := fun y hy => (min_le_left _ _).trans (hmin hy)
      exact ⟨δ, hδ_pos, hδ_lt_0_1, hδ_lower⟩
    · exact ⟨0.05, by norm_num, by norm_num, fun y hy ↦ False.elim (hP ⟨y, hy⟩)⟩
  obtain ⟨P, hP_diff, hP_bound⟩ :=
    differentiable_approx_of_continuous hδ1 hsigmacompact (fun (y : E) => (G y : E)) (by fun_prop)
  have h0_notin_image : (0 : E) ∉ P '' sigma1 := by
    rintro ⟨y, hy, h⟩
    have hG : ‖(G y : E)‖ ≥ δ := hδ3 y hy
    have hP : ‖P y - G y‖ < δ := hP_bound y (Set.subset_union_left hy)
    simp only [h, _root_.zero_sub, norm_neg] at hP
    linarith
  -- It is possible that `P` vanishes on `Σ₂`, so we construct a perturbation `P'` that does not.
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  -- `Σ₂` has measure `0`; `P` is differentiable. The image of `Σ₂` under P also has measure `0`.
  have hP_image_null : volume (P '' (sphere c ε)) = 0 :=
    MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
    hP_diff.differentiableOn
    (MeasureTheory.Measure.addHaar_sphere_of_ne_zero volume c (ne_of_gt hε1))
  -- As the image of `Σ₂` under P also has measure `0`, we can find a point v in the ball of radius
  -- δ that is neither in `Σ₁` nor `Σ₂`
  obtain ⟨v, hvnorm, hv1, hv2⟩ : ∃ (v : E), ‖v‖ < δ ∧ ¬ v ∈ P '' sigma1 ∧ ¬ v ∈ P '' sigma2 := by
    obtain hsigma1empty | hsigma1nonempty := sigma1.eq_empty_or_nonempty
    · have hball_pos := measure_ball_pos volume (0 : E) hδ1
      have hnot_subset2 : ¬ (ball 0 δ ⊆ P '' sigma2) := by
        intro hsub
        have : volume (ball (0 : E) δ) ≤ volume (P '' sigma2) := measure_mono hsub
        grind
      rcases Set.not_subset.1 hnot_subset2 with ⟨v, hv_in_ball, hv_notin_sigma2⟩
      exact ⟨v, ⟨mem_ball_zero_iff.mp hv_in_ball, ⟨by grind, by grind⟩⟩⟩
    have hP_cont : ContinuousOn (fun v => ‖P v‖) sigma1 := by fun_prop
    -- Let `d` be a point of `Σ₁` such that `‖P(d)‖` takes its minimum value.
    let ⟨d, _, hd⟩ := IsCompact.exists_isMinOn hsigma1compact hsigma1nonempty hP_cont
    -- Let `k` be the minimum of these two, to ensure both properties.
    let k := min ‖P d‖ δ
    obtain ⟨v, hvnorm, hv1⟩ : ∃ a ∈ ball 0 k, a ∉ P '' sphere c ε := by
      rw [← Set.not_subset]
      intro hsub
      have : volume (ball (0 : E) k) ≤ 0 := by rw [← hP_image_null]; exact measure_mono hsub
      exact LT.lt.false (lt_of_lt_of_le (measure_ball_pos volume (0 : E)
        (lt_min_iff.mpr ⟨by simp only [norm_pos_iff, ne_eq]; grind, hδ1⟩)) this)
    refine ⟨v, ⟨by linarith [mem_ball_zero_iff.mp hvnorm, min_le_right ‖P d‖ δ],
      ⟨fun hin1 => ?_, fun hin2 ↦ hv1 hin2⟩⟩⟩
    rcases hin1 with ⟨x, hx, rfl⟩
    linarith [(isMinOn_iff.mp hd) x hx, mem_ball_zero_iff.mp hvnorm, min_le_left ‖P d‖ δ]
  -- Let `P'` be the perturbation of `P` such that `P'(y) = P(y) - v`.
  let P' : C(E, E) := {toFun := fun y => P y - v, continuous_toFun:= by fun_prop}
  -- `v` is not in `Σ`.
  have hv_notin_sigma : v ∉ P '' sigma := by grind
  -- Define `Gtilde : f(B^n) → ℝ^n` as `Gtilde(y) = P'(Φ(y))`.
  let Gtilde : E → E := fun y => P' (Phi y)
  -- `Gtilde` is continuous.
  have hGtilde_cont : ContinuousOn Gtilde (f '' closedBall 0 1) :=
    (ContinuousMap.continuous P').comp_continuousOn hPhicont
  -- `P'` is never `0` on `Σ`. `Gtilde` is never `0`.
  have hGtilde_nonzero : ∀ y ∈ f '' closedBall 0 1, (P' ∘ Phi) y ≠ 0 :=
    fun y hy h_eq => (hv_notin_sigma) ⟨Phi y, hPhiimg y hy, sub_eq_zero.mp h_eq⟩
  -- We bound the difference between `G` and `Gtilde` by `1`.
  have hpeturb_bound : ∀ y ∈ f '' (closedBall (0 : E) 1), ‖G y - Gtilde y‖ ≤ 1 := by
    intro y hy
    -- There are two possible cases for the norm of `y - c`.
    by_cases hP : ε < ‖y - c‖
    · -- If `ε < ‖y - c‖`, then `Φ(y) = y`
      -- Thus `Gtilde(y) = G(Φ(y))`
      have hPhi : Phi y = y := by
        have hright : ε / ‖y - c‖ < 1 := by
          have hyc : 0 < ‖y - c‖ := by linarith
          rwa [div_lt_one hyc]
        simp [Phi, max_eq_right_of_lt hright]
      simp only [hPhi, Gtilde]
      -- We are using `P' = P - v`, `∀ y ∈ Σ, ‖P y - ↑(G y)‖ < δ` and `‖v‖ < δ`
      calc
        ‖G y - P' y‖ = ‖G y - (P y - v)‖ := rfl
        _ ≤ _ := by grw [sub_sub_eq_add_sub, add_sub_right_comm, norm_add_le, norm_sub_rev,
          hP_bound y (Or.inl ⟨hy, le_of_lt hP⟩), add_comm, hvnorm]
        _ ≤ _ := by linarith
    · -- If `‖y - c‖ ≤ ε`, then `Φ y ∈ Σ₂`.
      simp only [not_lt] at hP
      have hy_neq_c : c ≠ y := by grind
      have hleft : 1 ≤ ε / ‖y - c‖ :=
        (one_le_div (norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hy_neq_c)))).mpr hP
      have hPhi : Phi y = c + (ε / ‖y - c‖) • (y - c) := by grind [max_eq_left]
      have hyimg : Phi y ∈ sphere c ε := by
        simp [hPhi, mem_sphere_iff_norm, add_sub_cancel_left, norm_smul,
          (sub_ne_zero_of_ne (Ne.symm hy_neq_c)), hε1.le]
      have hP_approx_le : ‖P (Phi y)‖ ≤ ‖(G (Phi y) : E)‖ + δ := by
        linarith [norm_sub_rev (P (Phi y)) (G (Phi y) : E), hP_bound (Phi y) (Or.inr hyimg),
        norm_le_norm_add_norm_sub' (P (Phi y)) (G (Phi y))]
      have hG_phi_small : ‖(G (Phi y) : E)‖ ≤ 0.1 := by
        rw [dist_eq_norm] at hc1
        have hdist : ‖Phi y - f 0‖ < 2 * ε := calc
          ‖Phi y - f 0‖  ≤ ‖Phi y - c‖ + ‖c - f 0‖ := by grw [← sub_add_sub_cancel,norm_add_le]
          _ = ε + ‖c - f 0‖ := by rw [mem_sphere_iff_norm.mp hyimg]
          _ < ε + ε := add_lt_add_right hc1 ε
          _ = 2 * ε := by ring
        rw [← h2εeq, ← dist_eq_norm] at hdist
        grind [h2ε1 hdist, dist_zero_right]
      specialize hG_small y hP
      calc
        ‖G y - P' (Phi y)‖
          = ‖G y - (P (Phi y) - v)‖ := rfl
        _ ≤ ‖(G y : E)‖ + ‖P (Phi y)‖ + ‖v‖ := by grw [sub_sub_eq_add_sub, add_sub_right_comm,
          norm_add_le, norm_sub_le]
        _ ≤ _ := by linarith
  -- We derive a contradiction using the lemma for the stability of zero.
  obtain ⟨y, hy1, hy2⟩ := (((hStability_of_zero)) Gtilde hGtilde_cont) hpeturb_bound
  exact hGtilde_nonzero y hy1 hy2

/-- The invariance of domain theorem: if `U ⊆ E` is open,
  `f : E → E` is continuous on `U` and injective on `U`, then the image `f '' U` is open in `E`. -/
theorem invariance_of_domain_open_map (f : E → E) (U : Set E) (hU : IsOpen U)
    (hf_cont : ContinuousOn f U) (hf_inj : Set.InjOn f U) : IsOpen (f '' U) := by
  rw [isOpen_iff_forall_mem_open]
  rintro y ⟨x, hxU, hfx⟩
  rw [isOpen_iff] at hU
  have hclosedball: ∀ x' ∈ U, ∃ ε' > 0, closedBall x' ε' ⊆ U := by
    intro x' hx'
    obtain ⟨ε, hε, hball⟩ := hU x' hx'
    exact ⟨ε / 2, half_pos hε, (closedBall_subset_ball (div_two_lt_of_pos hε)).trans hball⟩
  obtain ⟨ε, hε , hclosedball⟩ := hclosedball x hxU
  -- Define `g` as a scaling and translating function.
  let g := fun (v : E) => ε • v + x
  have hg_inj : Function.Injective g := by simp [Function.Injective, g, hε.ne']
  have h_g_eq : g '' closedBall 0 1 = closedBall x ε := by
    rw [← Set.image_image (fun v ↦ v + x) (fun v ↦ ε • v) (closedBall 0 1), Set.image_smul,
      smul_unitClosedBall]
    simp only [Real.norm_eq_abs, Set.image_add_right, preimage_add_right_closedBall,
      sub_neg_eq_add, zero_add]
    rw [abs_of_pos hε]
  let e := f ∘ g
  have he_cont : ContinuousOn e (closedBall 0 1):=
    ContinuousOn.image_comp_continuous (h_g_eq ▸ hf_cont.mono hclosedball) (by fun_prop)
  have he_inj : Set.InjOn e (closedBall 0 1) := by
    rw [Set.InjOn.comp_iff hg_inj.injOn, h_g_eq]
    exact Set.InjOn.mono hclosedball hf_inj
  -- `e(0)` is in the interior using the prior version.
  have h_interior : e 0 ∈ interior (e '' closedBall 0 1) :=
    invariance_of_domain_interior e he_cont he_inj
  refine ⟨interior (f '' U), ⟨interior_subset, isOpen_interior, ?_⟩⟩
  unfold e g at h_interior
  rw [Set.image_comp, h_g_eq] at h_interior
  simp only [Function.comp_apply, smul_zero, zero_add] at h_interior
  grw [hfx, hclosedball] at h_interior
  exact h_interior

/-- If `f` is a partial equivalence continuous on its source, then it maps
    neighbourhoods of `x` (contained in the source) to neighbourhoods of `f(x)`. -/
theorem invariance_of_domain_partial_equiv {x : E} {s : Set E} {f : PartialEquiv E E}
    (hCont : ContinuousOn f f.source) : s ∈ nhds x → s ⊆ f.source →
    f '' s ∈ nhds (f x) := by
  intro hsin hsubset
  obtain ⟨a, ha1, ha2, ha3⟩ := _root_.mem_nhds_iff.mp hsin
  exact _root_.mem_nhds_iff.mpr ⟨f '' a, Set.image_mono ha1, invariance_of_domain_open_map (↑f) a
  ha2 (ContinuousOn.mono hCont (ha1.trans hsubset)) (Set.InjOn.mono (ha1.trans hsubset)
  (PartialEquiv.injOn f)), Set.mem_image_of_mem (↑f) ha3⟩

/-- If there is an injective map `f` from `ℝ^n` to `ℝ^m`, then `n ≤ m`. -/
theorem dim_le_of_injective_continuous
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [BrouwerFixedPoint E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (f : E → F) (hf_cont : Continuous f) (hf_inj : Function.Injective f) :
    Module.finrank ℝ E ≤ Module.finrank ℝ F := by
  -- Suppose by contradiction that `m < n`.
  by_contra h
  rw [not_le] at h
  let n := (Module.finrank ℝ E)
  let m := (Module.finrank ℝ F)
  have hdimlt : m < n :=  Nat.lt_of_succ_le h
  -- Get bases and isomorphisms with Euclidean space.
  let basisE := stdOrthonormalBasis ℝ E
  let basisF := stdOrthonormalBasis ℝ F
  let coordE := basisE.repr
  let coordF := basisF.repr
  -- Takes a vector in `ℝ^m` to `ℝ^n` by filling the last entries with `0`,
  -- `(x₀, ..., x_m) → (x₀, ..., x_m, 0, ..., 0)`
  let pad : (Fin m → ℝ) → (Fin n → ℝ) := fun v i => if hi : i.val < m then v ⟨i.val, hi⟩ else 0
  let coordF_padded : F → (Fin n → ℝ) := fun x => pad (coordF x)
  let toEuclideanE : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n) :=
    (EuclideanSpace.equiv (Fin n) ℝ).symm
  -- The inclusion map from `ℝ^m` to `ℝ^n`. It is continuous and injective.
  let incl : F → E := fun x =>
    coordE.symm (((EuclideanSpace.equiv (Fin n) ℝ).symm) (coordF_padded x))
  have hincl_cont : Continuous incl := by
    apply Continuous.comp' (LinearIsometryEquiv.continuous _)
    apply Continuous.comp' (ContinuousLinearEquiv.continuous _)
    exact continuous_pi fun i => by
      simp only [coordF_padded, pad, coordF]
      by_cases hi : i.val < m
      · simp only [dif_pos hi]; fun_prop
      · simp only [dif_neg hi]; exact continuous_const
  have hincl_inj : Function.Injective incl := by
    intro x y hxy
    apply coordF.injective
    ext i
    have hi : i.val < m := i.isLt
    have h : coordF_padded x = coordF_padded y := by
      have := congr_arg coordE hxy
      simp only [incl, LinearIsometryEquiv.apply_symm_apply,
        PiLp.continuousLinearEquiv_symm_apply, WithLp.toLp.injEq] at this
      exact this
    have := congr_fun h ⟨i.val, by grind⟩
    simp only [coordF_padded, pad, hi, dif_pos] at this
    exact this
  -- The inclusion map composed with `f` gives `g`, a continuous and injective map
  -- from `ℝ^n` to `ℝ^n`.
  let g : E → E := incl ∘ f
  have hg_cont : Continuous g := hincl_cont.comp hf_cont
  have hg_inj : Function.Injective g := hincl_inj.comp hf_inj
  -- `ℝ^n` is open
  -- By invariance of domain, `g` is an open mapping and so `g(ℝ^n)` is open.
  have hg_img_open : IsOpen (g '' Set.univ) := invariance_of_domain_open_map g Set.univ isOpen_univ
    hg_cont.continuousOn hg_inj.injOn
  -- Use definition of openness with balls.
  rw [Metric.isOpen_iff] at hg_img_open
  -- the `mth` coordinate of every point in the image is `0`.
  have hlastzero : ∀ x ∈ g '' Set.univ, (EuclideanSpace.equiv (Fin n) ℝ) (coordE x) ⟨m, h⟩ = 0 := by
    intro x ⟨y, _, hy⟩
    rw [← hy]
    simp [PiLp.continuousLinearEquiv_symm_apply, Function.comp_apply,
      LinearIsometryEquiv.apply_symm_apply, PiLp.continuousLinearEquiv_apply, lt_self_iff_false,
      ↓reduceDIte, coordE, g, incl, coordF_padded, pad]
  -- Consider some point `x` in the image of `g`.
  -- As the `mth` coordinate of every point of the image is `0`,
  have : (g '' Set.univ).Nonempty := Set.Nonempty.of_subtype
  let x : E := this.some
  have hx := Set.Nonempty.some_mem this
  -- There is a ball around it contained in `g(ℝ^n)`.
  rcases hg_img_open x hx with ⟨ε, hε, hball⟩
  -- `c` picks out the `mth` coordinate.
  let c : E → ℝ := fun y => (EuclideanSpace.equiv (Fin n) ℝ) (coordE y) ⟨m, h⟩
  -- The `mth` coordinate is `0` for every point in the ball around `x`.
  have hc_zero : ∀ y ∈ ball x ε, c y = 0 := fun y hy => (fun y hy => hlastzero y (hball hy)) y hy
  -- Take `x` and add `ε/2` in the `mth` coordinate to get a point `x'`.
  let x' : E := x + coordE.symm ((EuclideanSpace.equiv (Fin n) ℝ).symm
    (fun i => if i = ⟨m, h⟩ then ε / 2 else 0))
  -- `x'` is in the `ε-ball` around `x`.
  have hx'_in_ball : x' ∈ ball x ε := by
    simp only [x', mem_ball, dist_eq_norm, add_sub_cancel_left]
    have hconv : (EuclideanSpace.equiv (Fin n) ℝ).symm
        (fun i => if i = ⟨m, h⟩ then ε / 2 else 0) =
        EuclideanSpace.single ⟨m, h⟩ (ε / 2) := by
      ext i
      simp only [EuclideanSpace.single, EuclideanSpace.equiv,
        PiLp.continuousLinearEquiv_symm_apply]
      split_ifs with hi
      · rw [hi] ; simp
      · simp [hi]
    rw [LinearIsometryEquiv.norm_map, hconv, EuclideanSpace.norm_single,
      Real.norm_of_nonneg (by linarith)]
    linarith [half_lt_self hε]
  -- The `mth` coordinate of `x'` is non-zero, (as it is `ε/2`).
  have hx'_nonzero : c x' ≠ 0 := by
    have hsum : ((EuclideanSpace.equiv (Fin n) ℝ) (coordE x) + (EuclideanSpace.equiv (Fin n) ℝ)
      (coordE (coordE.symm ((EuclideanSpace.equiv (Fin n) ℝ).symm
      fun i => if i = ⟨m, h⟩ then ε / 2 else 0)))) ⟨m, h⟩ =
      (EuclideanSpace.equiv (Fin n) ℝ) (coordE x) ⟨m, h⟩ + ε / 2 := by simp [Pi.add_apply]
    have hcx : c x = 0 := hlastzero x hx
    unfold c at hcx
    have hsum2 : (EuclideanSpace.equiv (Fin n) ℝ) (coordE x) ⟨m, h⟩ + ε / 2 = ε / 2 := by
      rw [hcx]
      ring
    simp only [x', c, map_add, hsum, hsum2]
    linarith [half_pos hε]
  -- This contradicts all points in the ball having `mth` coordinate `0`.
  exact hx'_nonzero (hc_zero x' hx'_in_ball)

-- If there is a homeomorphism between `ℝ^m` and `ℝ^n`, then `m = n`
theorem invariance_of_dimension
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BrouwerFixedPoint E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [BrouwerFixedPoint F]
    (φ : E ≃ₜ F) :
    Module.finrank ℝ E = Module.finrank ℝ F := by
  -- From the homeomorphism, get continuous and injective functions both ways and apply the above.
  let f : E → F := φ
  let g : F → E := φ.symm
  exact Nat.le_antisymm (dim_le_of_injective_continuous f (φ.continuous) (φ.injective))
    (dim_le_of_injective_continuous g (φ.symm.continuous) (φ.symm.injective))
