/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.Analysis.NormedSpace.Exponential
import Mathlib.Topology.Instances.TrivSqZeroExt

#align_import analysis.normed_space.triv_sq_zero_ext from "leanprover-community/mathlib"@"88a563b158f59f2983cfad685664da95502e8cdd"

/-!
# Results on `TrivSqZeroExt R M` related to the norm

For now, this file contains results about `exp` for this type.

## Main results

* `TrivSqZeroExt.fst_exp`
* `TrivSqZeroExt.snd_exp`
* `TrivSqZeroExt.exp_inl`
* `TrivSqZeroExt.exp_inr`

## TODO

* Actually define a sensible norm on `TrivSqZeroExt R M`, so that we have access to lemmas
  like `exp_add`.
* Generalize more of these results to non-commutative `R`. In principle, under sufficient conditions
  we should expect
 `(exp 𝕜 x).snd = ∫ t in 0..1, exp 𝕜 (t • x.fst) • op (exp 𝕜 ((1 - t) • x.fst)) • x.snd`
  ([Physics.SE](https://physics.stackexchange.com/a/41671/185147), and
  https://link.springer.com/chapter/10.1007/978-3-540-44953-9_2).

-/


variable (𝕜 : Type*) {R M : Type*}

local notation "tsze" => TrivSqZeroExt

open NormedSpace -- For `exp`.

namespace TrivSqZeroExt

section Topology

section not_charZero
variable [Field 𝕜] [Ring R] [AddCommGroup M]
  [Algebra 𝕜 R] [Module 𝕜 M] [Module R M] [Module Rᵐᵒᵖ M]
  [SMulCommClass R Rᵐᵒᵖ M] [IsScalarTower 𝕜 R M] [IsScalarTower 𝕜 Rᵐᵒᵖ M]
  [TopologicalSpace R] [TopologicalSpace M]
  [TopologicalRing R] [TopologicalAddGroup M] [ContinuousSMul R M] [ContinuousSMul Rᵐᵒᵖ M]

@[simp] theorem fst_expSeries (x : tsze R M) (n : ℕ) :
    fst (expSeries 𝕜 (tsze R M) n fun _ => x) = expSeries 𝕜 R n fun _ => x.fst := by
  simp [expSeries_apply_eq]

end not_charZero

section Ring
variable [Field 𝕜] [CharZero 𝕜] [Ring R] [AddCommGroup M]
  [Algebra 𝕜 R] [Module 𝕜 M] [Module R M] [Module Rᵐᵒᵖ M]
  [SMulCommClass R Rᵐᵒᵖ M] [IsScalarTower 𝕜 R M] [IsScalarTower 𝕜 Rᵐᵒᵖ M]
  [TopologicalSpace R] [TopologicalSpace M]
  [TopologicalRing R] [TopologicalAddGroup M] [ContinuousSMul R M] [ContinuousSMul Rᵐᵒᵖ M]

theorem snd_expSeries_of_smul_comm
    (x : tsze R M) (hx : MulOpposite.op x.fst • x.snd = x.fst • x.snd) (n : ℕ) :
    snd (expSeries 𝕜 (tsze R M) (n + 1) fun _ => x) = (expSeries 𝕜 R n fun _ => x.fst) • x.snd := by
  simp_rw [expSeries_apply_eq, snd_smul, snd_pow_of_smul_comm _ _ hx, nsmul_eq_smul_cast 𝕜 (n + 1),
    smul_smul, smul_assoc, Nat.factorial_succ, Nat.pred_succ, Nat.cast_mul, mul_inv_rev,
    inv_mul_cancel_right₀ ((Nat.cast_ne_zero (R := 𝕜)).mpr <| Nat.succ_ne_zero n)]

/-- If `exp R x.fst` converges to `e` then `(exp R x).snd` converges to `e • x.snd`. -/
theorem hasSum_snd_expSeries_of_smul_comm (x : tsze R M)
    (hx : MulOpposite.op x.fst • x.snd = x.fst • x.snd) {e : R}
    (h : HasSum (fun n => expSeries 𝕜 R n fun _ => x.fst) e) :
    HasSum (fun n => snd (expSeries 𝕜 (tsze R M) n fun _ => x)) (e • x.snd) := by
  rw [← hasSum_nat_add_iff' 1]
  simp_rw [snd_expSeries_of_smul_comm _ _ hx]
  simp_rw [expSeries_apply_eq] at *
  rw [Finset.range_one, Finset.sum_singleton, Nat.factorial_zero, Nat.cast_one, pow_zero,
    inv_one, one_smul, snd_one, sub_zero]
  exact h.smul_const _
#align triv_sq_zero_ext.has_sum_snd_exp_series_of_smul_comm TrivSqZeroExt.hasSum_snd_expSeries_of_smul_comm

/-- If `exp R x.fst` converges to `e` then `exp R x` converges to `inl e + inr (e • x.snd)`. -/
theorem hasSum_expSeries_of_smul_comm
    (x : tsze R M) (hx : MulOpposite.op x.fst • x.snd = x.fst • x.snd)
    {e : R} (h : HasSum (fun n => expSeries 𝕜 R n fun _ => x.fst) e) :
    HasSum (fun n => expSeries 𝕜 (tsze R M) n fun _ => x) (inl e + inr (e • x.snd)) := by
  have : HasSum (fun n => fst (expSeries 𝕜 (tsze R M) n fun _ => x)) e := by
    simpa [fst_expSeries] using h
  simpa only [inl_fst_add_inr_snd_eq] using
    (hasSum_inl _ <| this).add (hasSum_inr _ <| hasSum_snd_expSeries_of_smul_comm 𝕜 x hx h)
#align triv_sq_zero_ext.has_sum_exp_series_of_smul_comm TrivSqZeroExt.hasSum_expSeries_of_smul_comm

variable [T2Space R] [T2Space M]

theorem exp_def_of_smul_comm (x : tsze R M) (hx : MulOpposite.op x.fst • x.snd = x.fst • x.snd) :
    exp 𝕜 x = inl (exp 𝕜 x.fst) + inr (exp 𝕜 x.fst • x.snd) := by
  simp_rw [exp, FormalMultilinearSeries.sum]
  by_cases h : Summable (fun (n : ℕ) => (expSeries 𝕜 R n) fun x_1 ↦ fst x)
  · refine (hasSum_expSeries_of_smul_comm 𝕜 x hx ?_).tsum_eq
    exact h.hasSum
  · rw [tsum_eq_zero_of_not_summable h, zero_smul, inr_zero, inl_zero, zero_add,
      tsum_eq_zero_of_not_summable]
    simp_rw [← fst_expSeries] at h
    refine mt ?_ h
    exact (Summable.map · (TrivSqZeroExt.fstHom 𝕜 R M).toLinearMap continuous_fst)

@[simp]
theorem exp_inl (x : R) : exp 𝕜 (inl x : tsze R M) = inl (exp 𝕜 x) := by
  rw [exp_def_of_smul_comm, snd_inl, fst_inl, smul_zero, inr_zero, add_zero]
  · rw [snd_inl, fst_inl, smul_zero, smul_zero]
#align triv_sq_zero_ext.exp_inl TrivSqZeroExt.exp_inl

@[simp]
theorem exp_inr (m : M) : exp 𝕜 (inr m : tsze R M) = 1 + inr m := by
  rw [exp_def_of_smul_comm, snd_inr, fst_inr, exp_zero, one_smul, inl_one]
  · rw [snd_inr, fst_inr, MulOpposite.op_zero, zero_smul, zero_smul]
#align triv_sq_zero_ext.exp_inr TrivSqZeroExt.exp_inr

end Ring

section CommRing
variable [Field 𝕜] [CharZero 𝕜] [CommRing R] [AddCommGroup M]
  [Algebra 𝕜 R] [Module 𝕜 M] [Module R M] [Module Rᵐᵒᵖ M]
  [IsCentralScalar R M] [IsScalarTower 𝕜 R M]
  [TopologicalSpace R] [TopologicalSpace M]
  [TopologicalRing R] [TopologicalAddGroup M] [ContinuousSMul R M] [ContinuousSMul Rᵐᵒᵖ M]

variable [T2Space R] [T2Space M]

theorem exp_def (x : tsze R M) : exp 𝕜 x = inl (exp 𝕜 x.fst) + inr (exp 𝕜 x.fst • x.snd) :=
  exp_def_of_smul_comm 𝕜 x (op_smul_eq_smul _ _)
#align triv_sq_zero_ext.exp_def TrivSqZeroExt.exp_def

@[simp]
theorem fst_exp (x : tsze R M) : fst (exp 𝕜 x) = exp 𝕜 x.fst := by
  rw [exp_def, fst_add, fst_inl, fst_inr, add_zero]
#align triv_sq_zero_ext.fst_exp TrivSqZeroExt.fst_exp

@[simp]
theorem snd_exp (x : tsze R M) : snd (exp 𝕜 x) = exp 𝕜 x.fst • x.snd := by
  rw [exp_def, snd_add, snd_inl, snd_inr, zero_add]
#align triv_sq_zero_ext.snd_exp TrivSqZeroExt.snd_exp

/-- Polar form of trivial-square-zero extension. -/
theorem eq_smul_exp_of_invertible (x : tsze R M) [Invertible x.fst] :
    x = x.fst • exp 𝕜 (⅟ x.fst • inr x.snd) := by
  rw [← inr_smul, exp_inr, smul_add, ← inl_one, ← inl_smul, ← inr_smul, smul_eq_mul, mul_one,
    smul_smul, mul_invOf_self, one_smul, inl_fst_add_inr_snd_eq]
#align triv_sq_zero_ext.eq_smul_exp_of_invertible TrivSqZeroExt.eq_smul_exp_of_invertible

end CommRing

section Field
variable [Field 𝕜] [CharZero 𝕜] [Field R] [AddCommGroup M]
  [Algebra 𝕜 R] [Module 𝕜 M] [Module R M] [Module Rᵐᵒᵖ M]
  [IsCentralScalar R M] [IsScalarTower 𝕜 R M]
  [TopologicalSpace R] [TopologicalSpace M]
  [TopologicalRing R] [TopologicalAddGroup M] [ContinuousSMul R M] [ContinuousSMul Rᵐᵒᵖ M]

variable [T2Space R] [T2Space M]

/-- More convenient version of `TrivSqZeroExt.eq_smul_exp_of_invertible` for when `R` is a
field. -/
theorem eq_smul_exp_of_ne_zero (x : tsze R M) (hx : x.fst ≠ 0) :
    x = x.fst • exp 𝕜 (x.fst⁻¹ • inr x.snd) :=
  letI : Invertible x.fst := invertibleOfNonzero hx
  eq_smul_exp_of_invertible _ _
#align triv_sq_zero_ext.eq_smul_exp_of_ne_zero TrivSqZeroExt.eq_smul_exp_of_ne_zero

end Field

end Topology

end TrivSqZeroExt
