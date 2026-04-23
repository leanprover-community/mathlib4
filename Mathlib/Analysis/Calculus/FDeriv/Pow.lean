/-
Copyright (c) 2025 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Calculus.TangentCone.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Algebra.Order.Sub.Unbundled.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Real.Sqrt
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Metrizable.Uniformity

/-!
# Fréchet Derivative of `f x ^ n`, `n : ℕ`

In this file we prove that the Fréchet derivative of `fun x => f x ^ n`,
where `n` is a natural number, is `n • f x ^ (n - 1)) • f'`.
Additionally, we prove the case for non-commutative rings (with primed names like `fderiv_pow'`),
where the result is instead `∑ i ∈ Finset.range n, f x ^ (n.pred - i) •> f' <• f x ^ i`.

For detailed documentation of the Fréchet derivative,
see the module docstring of `Mathlib/Analysis/Calculus/FDeriv/Basic.lean`.

## Keywords

derivative, power
-/

public section

variable {𝕜 𝔸 E : Type*}

section NormedRing
variable [NontriviallyNormedField 𝕜] [NormedRing 𝔸] [NormedAddCommGroup E]
variable [NormedAlgebra 𝕜 𝔸] [NormedSpace 𝕜 E] {f : E → 𝔸} {f' : E →L[𝕜] 𝔸} {x : E} {s : Set E}

open scoped RightActions

private theorem aux (f : E → 𝔸) (f' : E →L[𝕜] 𝔸) (x : E) (n : ℕ) :
    f x •> ∑ i ∈ Finset.range (n + 1), f x ^ ((n + 1).pred - i) •> f' <• f x ^ i
      + f' <• (f x ^ (n + 1)) =
    ∑ i ∈ Finset.range (n + 1 + 1), f x ^ ((n + 1 + 1).pred - i) •> f' <• f x ^ i := by
  rw [Finset.sum_range_succ _ (n + 1), Finset.smul_sum]
  simp only [Nat.pred_eq_sub_one, add_tsub_cancel_right, tsub_self, pow_zero, one_smul]
  simp_rw [smul_comm (_ : 𝔸) (_ : 𝔸ᵐᵒᵖ), smul_smul, ← pow_succ']
  congr! 5 with x hx
  simp only [Finset.mem_range, Nat.lt_succ_iff] at hx
  rw [tsub_add_eq_add_tsub hx]

theorem HasStrictFDerivAt.fun_pow' (h : HasStrictFDerivAt f f' x) (n : ℕ) :
    HasStrictFDerivAt (fun x ↦ f x ^ n)
      (∑ i ∈ Finset.range n, f x ^ (n.pred - i) •> f' <• f x ^ i) x :=
  match n with
  | 0 => by simpa using hasStrictFDerivAt_const 1 x
  | 1 => by simpa using h
  | n + 1 + 1 => by
    have := h.mul' (h.fun_pow' (n + 1))
    simp_rw [pow_succ' _ (n + 1)]
    refine this.congr_fderiv <| aux _ _ _ _

theorem HasStrictFDerivAt.pow' (h : HasStrictFDerivAt f f' x) (n : ℕ) :
    HasStrictFDerivAt (f ^ n)
      (∑ i ∈ Finset.range n, f x ^ (n.pred - i) •> f' <• f x ^ i) x := h.fun_pow' n

theorem hasStrictFDerivAt_pow' (n : ℕ) {x : 𝔸} :
    HasStrictFDerivAt (𝕜 := 𝕜) (fun x ↦ x ^ n)
      (∑ i ∈ Finset.range n, x ^ (n.pred - i) •> ContinuousLinearMap.id 𝕜 _ <• x ^ i) x :=
  hasStrictFDerivAt_id _ |>.pow' n

theorem HasFDerivWithinAt.fun_pow' (h : HasFDerivWithinAt f f' s x) (n : ℕ) :
    HasFDerivWithinAt (fun x ↦ f x ^ n)
      (∑ i ∈ Finset.range n, f x ^ (n.pred - i) •> f' <• f x ^ i) s x :=
  match n with
  | 0 => by simpa using hasFDerivWithinAt_const 1 x s
  | 1 => by simpa using h
  | n + 1 + 1 => by
    have := h.mul' (h.fun_pow' (n + 1))
    simp_rw [pow_succ' _ (n + 1)]
    exact this.congr_fderiv <| aux _ _ _ _

theorem HasFDerivWithinAt.pow' (h : HasFDerivWithinAt f f' s x) (n : ℕ) :
    HasFDerivWithinAt (f ^ n)
      (∑ i ∈ Finset.range n, f x ^ (n.pred - i) •> f' <• f x ^ i) s x := h.fun_pow' n

theorem hasFDerivWithinAt_pow' (n : ℕ) {x : 𝔸} {s : Set 𝔸} :
    HasFDerivWithinAt (𝕜 := 𝕜) (fun x ↦ x ^ n)
      (∑ i ∈ Finset.range n, x ^ (n.pred - i) •> ContinuousLinearMap.id 𝕜 _ <• x ^ i) s x :=
  hasFDerivWithinAt_id _ _ |>.pow' n

theorem HasFDerivAt.fun_pow' (h : HasFDerivAt f f' x) (n : ℕ) :
    HasFDerivAt (fun x ↦ f x ^ n) (∑ i ∈ Finset.range n, f x ^ (n.pred - i) •> f' <• f x ^ i) x :=
  match n with
  | 0 => by simpa using hasFDerivAt_const 1 x
  | 1 => by simpa using h
  | n + 1 + 1 => by
    have := h.mul' (h.fun_pow' (n + 1))
    simp_rw [pow_succ' _ (n + 1)]
    exact this.congr_fderiv <| aux _ _ _ _

theorem HasFDerivAt.pow' (h : HasFDerivAt f f' x) (n : ℕ) :
    HasFDerivAt (f ^ n) (∑ i ∈ Finset.range n, f x ^ (n.pred - i) •> f' <• f x ^ i) x :=
  h.fun_pow' n

theorem hasFDerivAt_pow' (n : ℕ) {x : 𝔸} :
    HasFDerivAt (𝕜 := 𝕜) (fun x ↦ x ^ n)
      (∑ i ∈ Finset.range n, x ^ (n.pred - i) •> ContinuousLinearMap.id 𝕜 _ <• x ^ i) x :=
  hasFDerivAt_id _ |>.pow' n

@[fun_prop]
theorem DifferentiableWithinAt.fun_pow (hf : DifferentiableWithinAt 𝕜 f s x) (n : ℕ) :
    DifferentiableWithinAt 𝕜 (fun x => f x ^ n) s x :=
  let ⟨_, hf'⟩ := hf; ⟨_, hf'.pow' n⟩

@[fun_prop]
theorem DifferentiableWithinAt.pow (hf : DifferentiableWithinAt 𝕜 f s x) :
    ∀ n : ℕ, DifferentiableWithinAt 𝕜 (f ^ n) s x :=
  hf.fun_pow

theorem differentiableWithinAt_pow (n : ℕ) {x : 𝔸} {s : Set 𝔸} :
    DifferentiableWithinAt 𝕜 (fun x : 𝔸 => x ^ n) s x :=
  differentiableWithinAt_id.pow _

@[simp, fun_prop]
theorem DifferentiableAt.fun_pow (hf : DifferentiableAt 𝕜 f x) (n : ℕ) :
    DifferentiableAt 𝕜 (fun x => f x ^ n) x :=
  differentiableWithinAt_univ.mp <| hf.differentiableWithinAt.pow n

@[simp, fun_prop]
theorem DifferentiableAt.pow (hf : DifferentiableAt 𝕜 f x) (n : ℕ) :
    DifferentiableAt 𝕜 (f ^ n) x := hf.fun_pow n

theorem differentiableAt_pow (n : ℕ) {x : 𝔸} : DifferentiableAt 𝕜 (fun x : 𝔸 => x ^ n) x :=
  differentiableAt_id.pow _

@[fun_prop]
theorem DifferentiableOn.fun_pow (hf : DifferentiableOn 𝕜 f s) (n : ℕ) :
    DifferentiableOn 𝕜 (fun x => f x ^ n) s := fun x h => (hf x h).pow n

@[fun_prop]
theorem DifferentiableOn.pow (hf : DifferentiableOn 𝕜 f s) (n : ℕ) :
    DifferentiableOn 𝕜 (f ^ n) s := hf.fun_pow n

theorem differentiableOn_pow (n : ℕ) {s : Set 𝔸} : DifferentiableOn 𝕜 (fun x : 𝔸 => x ^ n) s :=
  differentiableOn_id.pow n

@[simp, fun_prop]
theorem Differentiable.fun_pow (hf : Differentiable 𝕜 f) (n : ℕ) :
    Differentiable 𝕜 fun x => f x ^ n :=
  fun x => (hf x).pow n

@[simp, fun_prop]
theorem Differentiable.pow (hf : Differentiable 𝕜 f) (n : ℕ) : Differentiable 𝕜 (f ^ n) :=
  hf.fun_pow n

theorem differentiable_pow (n : ℕ) : Differentiable 𝕜 fun x : 𝔸 => x ^ n :=
  differentiable_id.pow _

theorem fderiv_fun_pow' (n : ℕ) (hf : DifferentiableAt 𝕜 f x) :
    fderiv 𝕜 (fun x ↦ f x ^ n) x
      = (∑ i ∈ Finset.range n, f x ^ (n.pred - i) •> fderiv 𝕜 f x <• f x ^ i) :=
  hf.hasFDerivAt.pow' n |>.fderiv

theorem fderiv_pow' (n : ℕ) (hf : DifferentiableAt 𝕜 f x) :
    fderiv 𝕜 (f ^ n) x
      = (∑ i ∈ Finset.range n, f x ^ (n.pred - i) •> fderiv 𝕜 f x <• f x ^ i) :=
  fderiv_fun_pow' n hf

theorem fderiv_pow_ring' {x : 𝔸} (n : ℕ) :
    fderiv 𝕜 (fun x : 𝔸 ↦ x ^ n) x
      = (∑ i ∈ Finset.range n, x ^ (n.pred - i) •> .id _ _ <• x ^ i) := by
  rw [fderiv_fun_pow' n differentiableAt_fun_id, fderiv_id']

theorem fderivWithin_fun_pow' (hxs : UniqueDiffWithinAt 𝕜 s x)
    (n : ℕ) (hf : DifferentiableWithinAt 𝕜 f s x) :
    fderivWithin 𝕜 (fun x ↦ f x ^ n) s x
      = (∑ i ∈ Finset.range n, f x ^ (n.pred - i) •> fderivWithin 𝕜 f s x <• f x ^ i) :=
  hf.hasFDerivWithinAt.pow' n |>.fderivWithin hxs

theorem fderivWithin_pow' (hxs : UniqueDiffWithinAt 𝕜 s x)
    (n : ℕ) (hf : DifferentiableWithinAt 𝕜 f s x) :
    fderivWithin 𝕜 (f ^ n) s x
      = (∑ i ∈ Finset.range n, f x ^ (n.pred - i) •> fderivWithin 𝕜 f s x <• f x ^ i) :=
  fderivWithin_fun_pow' hxs n hf

theorem fderivWithin_pow_ring' {s : Set 𝔸} {x : 𝔸} (n : ℕ) (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (fun x : 𝔸 ↦ x ^ n) s x
      = (∑ i ∈ Finset.range n, x ^ (n.pred - i) •> .id _ _ <• x ^ i) := by
  rw [fderivWithin_fun_pow' hxs n differentiableAt_fun_id.differentiableWithinAt,
    fderivWithin_id' hxs]

end NormedRing

section NormedCommRing
variable [NontriviallyNormedField 𝕜] [NormedCommRing 𝔸] [NormedAddCommGroup E]
variable [NormedAlgebra 𝕜 𝔸] [NormedSpace 𝕜 E] {f : E → 𝔸} {f' : E →L[𝕜] 𝔸} {x : E} {s : Set E}

private theorem aux_sum_eq_pow (n : ℕ) :
    ∑ i ∈ Finset.range n, MulOpposite.op (f x ^ i) • f x ^ (n.pred - i) • f' =
      (n • f x ^ (n - 1)) • f' := by
  simp_rw [op_smul_eq_smul, smul_smul, ← pow_add, ← Finset.sum_smul]
  rw [Finset.sum_eq_card_nsmul, Finset.card_range, smul_assoc]
  intro a ha
  congr
  exact add_tsub_cancel_of_le (Nat.le_pred_of_lt <| Finset.mem_range.1 ha)

theorem HasStrictFDerivAt.pow (h : HasStrictFDerivAt f f' x) (n : ℕ) :
    HasStrictFDerivAt (fun x ↦ f x ^ n) ((n • f x ^ (n - 1)) • f') x :=
  h.pow' n |>.congr_fderiv <| aux_sum_eq_pow _

theorem hasStrictFDerivAt_pow (n : ℕ) {x : 𝔸} :
    HasStrictFDerivAt (𝕜 := 𝕜)
      (fun x : 𝔸 ↦ x ^ n) ((n • x ^ (n - 1)) • ContinuousLinearMap.id 𝕜 𝔸) x :=
  hasStrictFDerivAt_id _ |>.pow n

theorem HasFDerivWithinAt.pow (h : HasFDerivWithinAt f f' s x) (n : ℕ) :
    HasFDerivWithinAt (fun x ↦ f x ^ n) ((n • f x ^ (n - 1)) • f') s x :=
  h.pow' n |>.congr_fderiv <| aux_sum_eq_pow _

theorem hasFDerivWithinAt_pow (n : ℕ) {x : 𝔸} {s : Set 𝔸} :
    HasFDerivWithinAt (𝕜 := 𝕜)
      (fun x : 𝔸 ↦ x ^ n) ((n • x ^ (n - 1)) • ContinuousLinearMap.id 𝕜 𝔸) s x :=
  hasFDerivWithinAt_id _ _ |>.pow n

theorem HasFDerivAt.pow (h : HasFDerivAt f f' x) (n : ℕ) :
    HasFDerivAt (fun x ↦ f x ^ n) ((n • f x ^ (n - 1)) • f') x :=
  h.pow' n |>.congr_fderiv <| aux_sum_eq_pow _

theorem hasFDerivAt_pow (n : ℕ) {x : 𝔸} :
    HasFDerivAt (𝕜 := 𝕜)
      (fun x : 𝔸 ↦ x ^ n) ((n • x ^ (n - 1)) • ContinuousLinearMap.id 𝕜 𝔸) x :=
  hasFDerivAt_id _ |>.pow n

theorem fderiv_fun_pow (n : ℕ) (hf : DifferentiableAt 𝕜 f x) :
    fderiv 𝕜 (fun x ↦ f x ^ n) x = (n • f x ^ (n - 1)) • fderiv 𝕜 f x :=
  hf.hasFDerivAt.pow n |>.fderiv

theorem fderiv_pow (n : ℕ) (hf : DifferentiableAt 𝕜 f x) :
    fderiv 𝕜 (fun x ↦ f x ^ n) x = (n • f x ^ (n - 1)) • fderiv 𝕜 f x :=
  fderiv_fun_pow n hf

theorem fderiv_pow_ring {x : 𝔸} (n : ℕ) :
    fderiv 𝕜 (fun x : 𝔸 ↦ x ^ n) x = (n • x ^ (n - 1)) • .id _ _ := by
  rw [fderiv_fun_pow n differentiableAt_fun_id, fderiv_id']

theorem fderivWithin_fun_pow (hxs : UniqueDiffWithinAt 𝕜 s x)
    (n : ℕ) (hf : DifferentiableWithinAt 𝕜 f s x) :
    fderivWithin 𝕜 (fun x ↦ f x ^ n) s x = (n • f x ^ (n - 1)) • fderivWithin 𝕜 f s x :=
  hf.hasFDerivWithinAt.pow n |>.fderivWithin hxs

theorem fderivWithin_pow (hxs : UniqueDiffWithinAt 𝕜 s x)
    (n : ℕ) (hf : DifferentiableWithinAt 𝕜 f s x) :
    fderivWithin 𝕜 (f ^ n) s x = (n • f x ^ (n - 1)) • fderivWithin 𝕜 f s x :=
  fderivWithin_fun_pow hxs n hf

theorem fderivWithin_pow_ring {s : Set 𝔸} {x : 𝔸} (n : ℕ) (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (fun x : 𝔸 ↦ x ^ n) s x = (n • x ^ (n - 1)) • .id _ _ := by
  rw [fderivWithin_fun_pow hxs n differentiableAt_fun_id.differentiableWithinAt,
    fderivWithin_id' hxs]

end NormedCommRing
