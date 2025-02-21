/-
Copyright (c) 2025 Benoît Guillemet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benoît Guillemet
-/
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Algebra.BigOperators.Group.Finset

/-!
# Derivatives of multivariate polynomials

In this file we prove that derivatives of multivariate polynomials in the analysis sense agree with
their derivatives in the algebraic sense.
-/

open scoped MvPolynomial

open ContinuousLinearMap (smulRight proj)

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {𝕜 : Type} [NontriviallyNormedField 𝕜]
variable {x : ι → 𝕜} {s : Set (ι → 𝕜)}

namespace MvPolynomial

/-! ### Derivative of a multivariate polynomial -/

variable {R : Type} [CommSemiring R] [Algebra R 𝕜]
variable (p : MvPolynomial ι 𝕜) (q : MvPolynomial ι R)

theorem hasStrictFDerivAt_monomial {u : ι →₀ ℕ} (x : ι → 𝕜) :
    HasStrictFDerivAt (𝕜 := 𝕜) (fun x => ∏ i : ι, x i ^ u i)
    (∑ i ∈ u.support, (∏ j ∈ u.support.erase i, x j ^ u j) • u i • x i ^ (u i - 1) • proj i) x := by
  simp_rw [← u.prod_fintype _ (fun _ => pow_zero _)]
  refine HasStrictFDerivAt.finset_prod (fun i _ => ?_)
  have : (u i • x i ^ (u i - 1) • proj (R := 𝕜) (φ := fun _ => 𝕜) i) =
      (smulRight (1 : 𝕜 →L[𝕜] 𝕜) (u i * x i ^ (u i - 1))).comp (proj i) := by
    ext x
    simp [mul_comm, mul_assoc]
  rw [this]
  exact HasStrictFDerivAt.comp x (hasStrictDerivAt_pow (u i) (x i)).hasStrictFDerivAt
    (hasStrictFDerivAt_apply i x)

lemma prod_pow_sub_single_eq_prod_erase_mul {u : ι →₀ ℕ} {i : ι} (hi : i ∈ u.support) (x : ι → 𝕜) :
    ∏ j : ι, x j ^ (u j - Finsupp.single i 1 j)
    = (∏ j ∈ u.support.erase i, x j ^ u j) * x i ^ (u i - 1) := by
  rw [← Finset.prod_subset u.support.subset_univ (fun j _ hj => ?_),
    ← Finset.prod_erase_mul _ _ hi, Finsupp.single_apply, if_pos rfl,
    Finset.prod_congr rfl (fun j hj => ?_)]
  · rw [Finsupp.single_apply, if_neg (Finset.ne_of_mem_erase hj).symm, tsub_zero]
  · rw [Finsupp.single_apply, if_neg (fun h => hj (by rwa [← h])), tsub_zero,
      Finsupp.not_mem_support_iff.1 hj, pow_zero]

theorem hasStrictFDerivAt_monomial' {u : ι →₀ ℕ} (x : ι → 𝕜) :
    HasStrictFDerivAt (𝕜 := 𝕜) (fun x => ∏ i : ι, x i ^ u i)
    (∑ i : ι, u i • (∏ j : ι, x j ^ (u j - (Finsupp.single i 1) j)) • (proj i)) x := by
  rw [← u.sum_fintype (fun _ k => k • _) (fun _ => zero_smul _ _)]
  show HasStrictFDerivAt _ (∑ i ∈ u.support, _ • _) _
  rw [u.support.sum_congr rfl (fun i hi =>
    by rw [prod_pow_sub_single_eq_prod_erase_mul hi, smul_comm, mul_smul, ← smul_comm (u i)])]
  exact hasStrictFDerivAt_monomial x

/-- The derivative (in the analysis sense) of a multivariate polynomial `p` is given by `pderiv`. -/
protected theorem hasStrictFDerivAt (x : ι → 𝕜) :
    HasStrictFDerivAt (𝕜 := 𝕜) (fun x => eval x p)
    (∑ i : ι, (eval x (pderiv i p)) • (proj i)) x := by
  induction p using MvPolynomial.induction_on' with
  | h1 u a => simp only [eval_monomial, Finsupp.prod_pow, pderiv_monomial, Finsupp.coe_tsub,
                Pi.sub_apply, mul_smul, ← Finset.smul_sum]
              apply HasStrictFDerivAt.const_mul
              rw [Finset.sum_congr (β := (ι → 𝕜) →L[𝕜] 𝕜) rfl
                (fun _ _ => Nat.cast_smul_eq_nsmul _ _ _)]
              exact hasStrictFDerivAt_monomial' x
  | h2 p q hp hq => simp only [map_add]
                    rw [Finset.sum_congr (β := (ι → 𝕜) →L[𝕜] 𝕜) rfl (fun _ _ => add_smul _ _ _),
                      Finset.sum_add_distrib]
                    exact hp.add hq

protected theorem hasStrictFDerivAt_aeval (x : ι → 𝕜) :
    HasStrictFDerivAt (𝕜 := 𝕜) (fun x => aeval x q)
    (∑ i : ι, (aeval x (pderiv i q)) • (proj i)) x := by
  simpa only [aeval_def, eval₂_eq_eval_map, pderiv_map] using
    (q.map (algebraMap R 𝕜)).hasStrictFDerivAt x

/-- The derivative (in the analysis sense) of a polynomial `p` is given by `pderiv`. -/
protected theorem hasFDerivAt (x : ι → 𝕜) :
    HasFDerivAt (𝕜 := 𝕜) (fun x => eval x p)
    (∑ i : ι, (eval x (pderiv i p)) • (proj i)) x :=
  (p.hasStrictFDerivAt x).hasFDerivAt

protected theorem hasFDerivAt_aeval (x : ι → 𝕜) :
    HasFDerivAt (𝕜 := 𝕜) (fun x => aeval x q)
    (∑ i : ι, (aeval x (pderiv i q)) • (proj i)) x :=
  (q.hasStrictFDerivAt_aeval x).hasFDerivAt

protected theorem hasFDerivWithinAt (x : ι → 𝕜) (s : Set (ι → 𝕜)) :
    HasFDerivWithinAt (𝕜 := 𝕜) (fun x => eval x p)
    (∑ i : ι, (eval x (pderiv i p)) • (proj i)) s x :=
  (p.hasFDerivAt x).hasFDerivWithinAt

protected theorem hasFDerivWithinAt_aeval (x : ι → 𝕜) (s : Set (ι → 𝕜)) :
    HasFDerivWithinAt (𝕜 := 𝕜) (fun x => aeval x q)
    (∑ i : ι, (aeval x (pderiv i q)) • (proj i)) s x :=
  (q.hasFDerivAt_aeval x).hasFDerivWithinAt

protected theorem differentiableAt :
    DifferentiableAt 𝕜 (fun x => eval x p) x :=
  (p.hasStrictFDerivAt x).differentiableAt

protected theorem differentiableAt_aeval :
    DifferentiableAt 𝕜 (fun x => aeval x q) x :=
  (q.hasStrictFDerivAt_aeval x).differentiableAt

protected theorem differentiableWithinAt (s : Set (ι → 𝕜)) :
    DifferentiableWithinAt 𝕜 (fun x => eval x p) s x :=
  p.differentiableAt.differentiableWithinAt

protected theorem differentiableWithinAt_aeval (s : Set (ι → 𝕜)) :
    DifferentiableWithinAt 𝕜 (fun x => aeval x q) s x :=
  q.differentiableAt_aeval.differentiableWithinAt

protected theorem differentiable :
    Differentiable 𝕜 (fun x => eval x p) :=
  fun _ => p.differentiableAt

protected theorem differentiable_aeval :
    Differentiable 𝕜 (fun x : ι → 𝕜 => aeval x q) :=
  fun _ => q.differentiableAt_aeval

protected theorem differentiableOn (s : Set (ι → 𝕜)) :
    DifferentiableOn 𝕜 (fun x => eval x p) s :=
  p.differentiable.differentiableOn

protected theorem differentiableOn_aeval (s : Set (ι → 𝕜)) :
    DifferentiableOn 𝕜 (fun x : ι → 𝕜 => aeval x q) s :=
  q.differentiable_aeval.differentiableOn

@[simp]
protected theorem fderiv :
    fderiv 𝕜 (fun x => eval x p) x = ∑ i : ι, (eval x (pderiv i p)) • (proj i) :=
  (p.hasFDerivAt x).fderiv

@[simp]
protected theorem fderiv_aeval :
    fderiv 𝕜 (fun x => aeval x q) x = ∑ i : ι, (aeval x (pderiv i q)) • (proj i) :=
  (q.hasFDerivAt_aeval x).fderiv

protected theorem fderivWithin (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (fun x => eval x p) s x = ∑ i : ι, (eval x (pderiv i p)) • (proj i) := by
  rw [DifferentiableAt.fderivWithin p.differentiableAt hxs]
  exact p.fderiv

protected theorem derivWithin_aeval (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (fun x => aeval x q) s x = ∑ i : ι, (aeval x (pderiv i q)) • (proj i) := by
  simpa only [aeval_def, eval₂_eq_eval_map, pderiv_map] using
    (q.map (algebraMap R 𝕜)).fderivWithin hxs

end MvPolynomial
