/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Lp.ProdLp
import Mathlib.Topology.Instances.TrivSqZeroExt

/-!
# Results on `TrivSqZeroExt R M` related to the norm

This file contains results about `NormedSpace.exp` for `TrivSqZeroExt`.

It also contains a definition of the $ℓ^1$ norm,
which defines $\|r + m\| \coloneqq \|r\| + \|m\|$.
This is not a particularly canonical choice of definition,
but it is sufficient to provide a `NormedAlgebra` instance,
and thus enables `NormedSpace.exp_add_of_commute` to be used on `TrivSqZeroExt`.
If the non-canonicity becomes problematic in future,
we could keep the collection of instances behind an `open scoped`.

## Main results

* `TrivSqZeroExt.fst_exp`
* `TrivSqZeroExt.snd_exp`
* `TrivSqZeroExt.exp_inl`
* `TrivSqZeroExt.exp_inr`
* The $ℓ^1$ norm on `TrivSqZeroExt`:
  * `TrivSqZeroExt.instL1SeminormedAddCommGroup`
  * `TrivSqZeroExt.instL1SeminormedRing`
  * `TrivSqZeroExt.instL1SeminormedCommRing`
  * `TrivSqZeroExt.instL1IsBoundedSMul`
  * `TrivSqZeroExt.instL1NormedAddCommGroup`
  * `TrivSqZeroExt.instL1NormedRing`
  * `TrivSqZeroExt.instL1NormedCommRing`
  * `TrivSqZeroExt.instL1NormedSpace`
  * `TrivSqZeroExt.instL1NormedAlgebra`

## TODO

* Generalize more of these results to non-commutative `R`. In principle, under sufficient conditions
  we should expect
  `(exp 𝕜 x).snd = ∫ t in 0..1, exp 𝕜 (t • x.fst) • op (exp 𝕜 ((1 - t) • x.fst)) • x.snd`
  ([Physics.SE](https://physics.stackexchange.com/a/41671/185147), and
  https://link.springer.com/chapter/10.1007/978-3-540-44953-9_2).

-/


variable (𝕜 : Type*) {S R M : Type*}

local notation "tsze" => TrivSqZeroExt

open NormedSpace -- For `NormedSpace.exp`.

namespace TrivSqZeroExt

section Topology

section not_charZero
variable [Field 𝕜] [Ring R] [AddCommGroup M]
  [Algebra 𝕜 R] [Module 𝕜 M] [Module R M] [Module Rᵐᵒᵖ M]
  [SMulCommClass R Rᵐᵒᵖ M] [IsScalarTower 𝕜 R M] [IsScalarTower 𝕜 Rᵐᵒᵖ M]
  [TopologicalSpace R] [TopologicalSpace M]
  [IsTopologicalRing R] [IsTopologicalAddGroup M] [ContinuousSMul R M] [ContinuousSMul Rᵐᵒᵖ M]

@[simp] theorem fst_expSeries (x : tsze R M) (n : ℕ) :
    fst (expSeries 𝕜 (tsze R M) n fun _ => x) = expSeries 𝕜 R n fun _ => x.fst := by
  simp [expSeries_apply_eq]

end not_charZero

section Ring
variable [Field 𝕜] [CharZero 𝕜] [Ring R] [AddCommGroup M]
  [Algebra 𝕜 R] [Module 𝕜 M] [Module R M] [Module Rᵐᵒᵖ M]
  [SMulCommClass R Rᵐᵒᵖ M] [IsScalarTower 𝕜 R M] [IsScalarTower 𝕜 Rᵐᵒᵖ M]
  [TopologicalSpace R] [TopologicalSpace M]
  [IsTopologicalRing R] [IsTopologicalAddGroup M] [ContinuousSMul R M] [ContinuousSMul Rᵐᵒᵖ M]

theorem snd_expSeries_of_smul_comm
    (x : tsze R M) (hx : MulOpposite.op x.fst • x.snd = x.fst • x.snd) (n : ℕ) :
    snd (expSeries 𝕜 (tsze R M) (n + 1) fun _ => x) = (expSeries 𝕜 R n fun _ => x.fst) • x.snd := by
  simp_rw [expSeries_apply_eq, snd_smul, snd_pow_of_smul_comm _ _ hx,
    ← Nat.cast_smul_eq_nsmul 𝕜 (n + 1), smul_smul, smul_assoc, Nat.factorial_succ, Nat.pred_succ,
    Nat.cast_mul, mul_inv_rev,
    inv_mul_cancel_right₀ ((Nat.cast_ne_zero (R := 𝕜)).mpr <| Nat.succ_ne_zero n)]

/-- If `NormedSpace.exp R x.fst` converges to `e`
then `(NormedSpace.exp R x).snd` converges to `e • x.snd`. -/
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

/-- If `NormedSpace.exp R x.fst` converges to `e`
then `NormedSpace.exp R x` converges to `inl e + inr (e • x.snd)`. -/
theorem hasSum_expSeries_of_smul_comm
    (x : tsze R M) (hx : MulOpposite.op x.fst • x.snd = x.fst • x.snd)
    {e : R} (h : HasSum (fun n => expSeries 𝕜 R n fun _ => x.fst) e) :
    HasSum (fun n => expSeries 𝕜 (tsze R M) n fun _ => x) (inl e + inr (e • x.snd)) := by
  have : HasSum (fun n => fst (expSeries 𝕜 (tsze R M) n fun _ => x)) e := by
    simpa [fst_expSeries] using h
  simpa only [inl_fst_add_inr_snd_eq] using
    (hasSum_inl _ <| this).add (hasSum_inr _ <| hasSum_snd_expSeries_of_smul_comm 𝕜 x hx h)

variable [T2Space R] [T2Space M]

theorem exp_def_of_smul_comm (x : tsze R M) (hx : MulOpposite.op x.fst • x.snd = x.fst • x.snd) :
    exp 𝕜 x = inl (exp 𝕜 x.fst) + inr (exp 𝕜 x.fst • x.snd) := by
  simp_rw [exp, FormalMultilinearSeries.sum]
  by_cases h : Summable (fun (n : ℕ) => (expSeries 𝕜 R n) fun _ ↦ fst x)
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
  rw [snd_inl, fst_inl, smul_zero, smul_zero]

@[simp]
theorem exp_inr (m : M) : exp 𝕜 (inr m : tsze R M) = 1 + inr m := by
  rw [exp_def_of_smul_comm, snd_inr, fst_inr, exp_zero, one_smul, inl_one]
  rw [snd_inr, fst_inr, MulOpposite.op_zero, zero_smul, zero_smul]

end Ring

section CommRing
variable [Field 𝕜] [CharZero 𝕜] [CommRing R] [AddCommGroup M]
  [Algebra 𝕜 R] [Module 𝕜 M] [Module R M] [Module Rᵐᵒᵖ M]
  [IsCentralScalar R M] [IsScalarTower 𝕜 R M]
  [TopologicalSpace R] [TopologicalSpace M]
  [IsTopologicalRing R] [IsTopologicalAddGroup M] [ContinuousSMul R M] [ContinuousSMul Rᵐᵒᵖ M]

variable [T2Space R] [T2Space M]

theorem exp_def (x : tsze R M) : exp 𝕜 x = inl (exp 𝕜 x.fst) + inr (exp 𝕜 x.fst • x.snd) :=
  exp_def_of_smul_comm 𝕜 x (op_smul_eq_smul _ _)

@[simp]
theorem fst_exp (x : tsze R M) : fst (exp 𝕜 x) = exp 𝕜 x.fst := by
  rw [exp_def, fst_add, fst_inl, fst_inr, add_zero]

@[simp]
theorem snd_exp (x : tsze R M) : snd (exp 𝕜 x) = exp 𝕜 x.fst • x.snd := by
  rw [exp_def, snd_add, snd_inl, snd_inr, zero_add]

/-- Polar form of trivial-square-zero extension. -/
theorem eq_smul_exp_of_invertible (x : tsze R M) [Invertible x.fst] :
    x = x.fst • exp 𝕜 (⅟x.fst • inr x.snd) := by
  rw [← inr_smul, exp_inr, smul_add, ← inl_one, ← inl_smul, ← inr_smul, smul_eq_mul, mul_one,
    smul_smul, mul_invOf_self, one_smul, inl_fst_add_inr_snd_eq]

end CommRing

section Field
variable [Field 𝕜] [CharZero 𝕜] [Field R] [AddCommGroup M]
  [Algebra 𝕜 R] [Module 𝕜 M] [Module R M] [Module Rᵐᵒᵖ M]
  [IsCentralScalar R M] [IsScalarTower 𝕜 R M]
  [TopologicalSpace R] [TopologicalSpace M]
  [IsTopologicalRing R] [IsTopologicalAddGroup M] [ContinuousSMul R M] [ContinuousSMul Rᵐᵒᵖ M]

variable [T2Space R] [T2Space M]

/-- More convenient version of `TrivSqZeroExt.eq_smul_exp_of_invertible` for when `R` is a
field. -/
theorem eq_smul_exp_of_ne_zero (x : tsze R M) (hx : x.fst ≠ 0) :
    x = x.fst • exp 𝕜 (x.fst⁻¹ • inr x.snd) :=
  letI : Invertible x.fst := invertibleOfNonzero hx
  eq_smul_exp_of_invertible _ _

end Field

end Topology

/-!
### The $ℓ^1$ norm on the trivial square zero extension
-/

noncomputable section Seminormed

section Ring
variable [SeminormedCommRing S] [SeminormedRing R] [SeminormedAddCommGroup M]
variable [Algebra S R] [Module S M]
variable [IsBoundedSMul S R] [IsBoundedSMul S M]

instance instL1SeminormedAddCommGroup : SeminormedAddCommGroup (tsze R M) :=
  inferInstanceAs <| SeminormedAddCommGroup (WithLp 1 <| R × M)

example :
    (TrivSqZeroExt.instUniformSpace : UniformSpace (tsze R M)) =
    PseudoMetricSpace.toUniformSpace := rfl

theorem norm_def (x : tsze R M) : ‖x‖ = ‖fst x‖ + ‖snd x‖ := by
  rw [WithLp.prod_norm_eq_add (by simp)]
  simp only [ENNReal.toReal_one, Real.rpow_one, div_one, fst, snd]

theorem nnnorm_def (x : tsze R M) : ‖x‖₊ = ‖fst x‖₊ + ‖snd x‖₊ := by
  ext; simp [norm_def]

@[simp] theorem norm_inl (r : R) : ‖(inl r : tsze R M)‖ = ‖r‖ := by simp [norm_def]
@[simp] theorem norm_inr (m : M) : ‖(inr m : tsze R M)‖ = ‖m‖ := by simp [norm_def]

@[simp] theorem nnnorm_inl (r : R) : ‖(inl r : tsze R M)‖₊ = ‖r‖₊ := by simp [nnnorm_def]
@[simp] theorem nnnorm_inr (m : M) : ‖(inr m : tsze R M)‖₊ = ‖m‖₊ := by simp [nnnorm_def]

variable [Module R M] [IsBoundedSMul R M] [Module Rᵐᵒᵖ M] [IsBoundedSMul Rᵐᵒᵖ M]
  [SMulCommClass R Rᵐᵒᵖ M]

instance instL1SeminormedRing : SeminormedRing (tsze R M) where
  __ : Ring (tsze R M) := inferInstance
  __ : SeminormedAddCommGroup (tsze R M) := inferInstance
  norm_mul_le
  | ⟨r₁, m₁⟩, ⟨r₂, m₂⟩ => by
    simp_rw [norm_def]
    calc ‖r₁ * r₂‖ + ‖r₁ • m₂ + MulOpposite.op r₂ • m₁‖
    _ ≤ ‖r₁‖ * ‖r₂‖ + (‖r₁‖ * ‖m₂‖ + ‖r₂‖ * ‖m₁‖) := by
      gcongr
      · apply norm_mul_le
      · refine norm_add_le_of_le ?_ ?_ <;>
        apply norm_smul_le
    _ ≤ ‖r₁‖ * ‖r₂‖ + (‖r₁‖ * ‖m₂‖ + ‖r₂‖ * ‖m₁‖) + (‖m₁‖ * ‖m₂‖) := by
      apply le_add_of_nonneg_right
      positivity
    _ = (‖r₁‖ + ‖m₁‖) * (‖r₂‖ + ‖m₂‖) := by ring

instance instL1IsBoundedSMul : IsBoundedSMul S (tsze R M) :=
  inferInstanceAs <| IsBoundedSMul S (WithLp 1 <| R × M)

instance [NormOneClass R] : NormOneClass (tsze R M) where
  norm_one := by rw [norm_def, fst_one, snd_one, norm_zero, norm_one, add_zero]


end Ring

section CommRing

variable [SeminormedCommRing R] [SeminormedAddCommGroup M]
variable [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M]
variable [IsBoundedSMul R M]

instance instL1SeminormedCommRing : SeminormedCommRing (tsze R M) where
  __ : CommRing (tsze R M) := inferInstance
  __ : SeminormedRing (tsze R M) := inferInstance

end CommRing

end Seminormed

noncomputable section Normed

section Ring

variable [NormedRing R] [NormedAddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M]
variable [IsBoundedSMul R M] [IsBoundedSMul Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M]

instance instL1NormedAddCommGroup : NormedAddCommGroup (tsze R M) :=
  inferInstanceAs <| NormedAddCommGroup (WithLp 1 <| R × M)

instance instL1NormedRing : NormedRing (tsze R M) where
  __ : SeminormedRing (tsze R M) := inferInstance
  __ : NormedAddCommGroup (tsze R M) := inferInstance

end Ring

section CommRing

variable [NormedCommRing R] [NormedAddCommGroup M]
variable [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M]
variable [IsBoundedSMul R M]

instance instL1NormedCommRing : NormedCommRing (tsze R M) where
  __ : CommRing (tsze R M) := inferInstance
  __ : NormedRing (tsze R M) := inferInstance

end CommRing

section Algebra

variable [NormedField 𝕜] [NormedRing R] [NormedAddCommGroup M]
variable [NormedAlgebra 𝕜 R] [NormedSpace 𝕜 M] [Module R M] [Module Rᵐᵒᵖ M]
variable [IsBoundedSMul R M] [IsBoundedSMul Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M]
variable [IsScalarTower 𝕜 R M] [IsScalarTower 𝕜 Rᵐᵒᵖ M]

instance instL1NormedSpace : NormedSpace 𝕜 (tsze R M) :=
  inferInstanceAs <| NormedSpace 𝕜 (WithLp 1 <| R × M)

instance instL1NormedAlgebra : NormedAlgebra 𝕜 (tsze R M) where
  norm_smul_le := _root_.norm_smul_le

end Algebra


end Normed

section

variable [RCLike 𝕜] [NormedRing R] [NormedAddCommGroup M]
variable [NormedAlgebra 𝕜 R] [NormedSpace 𝕜 M] [Module R M] [Module Rᵐᵒᵖ M]
variable [IsBoundedSMul R M] [IsBoundedSMul Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M]
variable [IsScalarTower 𝕜 R M] [IsScalarTower 𝕜 Rᵐᵒᵖ M]
variable [CompleteSpace R] [CompleteSpace M]

-- Evidence that we have sufficient instances on `tsze R N`
-- to make `NormedSpace.exp_add_of_commute` usable
example (a b : tsze R M) (h : Commute a b) : exp 𝕜 (a + b) = exp 𝕜 a * exp 𝕜 b :=
  exp_add_of_commute h

end

end TrivSqZeroExt
