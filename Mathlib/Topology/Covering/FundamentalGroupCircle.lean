/-
Copyright (c) 2026 Ruize Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruize Chen
-/
module

public import Mathlib.Topology.Covering.AddCircle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Instances.ZMultiples
public import Mathlib.Analysis.Convex.Contractible

/-!
# The fundamental group of the circle

For `0 < p`, the fundamental group of `AddCircle p` at any basepoint is isomorphic to `ℤ`
(`AddCircle.windingNumberIso`). The winding number `AddCircle.windingNumber` of a loop is
`(f 1 - f 0) / p` for any continuous lift `f : I → ℝ` of the loop
(`AddCircle.windingNumber_eq_div`); in particular the loop `t ↦ n • (t * p) + x` has winding
number `n` (`AddCircle.windingNumber_zsmulLoop`).
-/

@[expose] public section

open unitInterval

namespace AddCircle

variable (p : ℝ)

/-- The loop in `AddCircle p` based at `x` that winds `n` times, defined as
`t ↦ n • (t * p) + x`. -/
def zsmulLoop (x : ℝ) (n : ℤ) : Path (x : AddCircle p) x where
  toFun t := n • (t * p : ℝ) + x
  source' := by simp
  target' := by simp [coe_period]
  continuous_toFun := by fun_prop

@[simp]
theorem zsmulLoop_apply (x : ℝ) (n : ℤ) (t : I) :
    zsmulLoop p x n t = n • (t * p : ℝ) + x :=
  rfl

variable {p} [hp : Fact (0 < p)]

/-- **The fundamental group of the circle is `ℤ`**: the isomorphism sends the class of a loop to
its winding number (`windingNumber_eq_div`). It does not depend on the choice of a lift of the
basepoint (`IsAddQuotientCoveringMap.fundamentalGroupEquiv_eq`). -/
noncomputable def windingNumberIso (x : AddCircle p) :
    FundamentalGroup (AddCircle p) x ≃* Multiplicative ℤ :=
  ((isAddQuotientCoveringMap_coe p).fundamentalGroupEquiv (x := x)
      ⟨(equivIco p 0 x : ℝ), coe_equivIco⟩).trans <|
    MulOpposite.opMulEquiv.symm.trans (AddSubgroup.zmultiplesEquivInt hp.out.ne').toMultiplicative

/-- The winding number of a loop in `AddCircle p`, defined as its image under `windingNumberIso`. -/
noncomputable def windingNumber {x : AddCircle p} (γ : FundamentalGroup (AddCircle p) x) : ℤ :=
  (windingNumberIso x γ).toAdd

/-- The winding number of a loop in `AddCircle p` is `(f 1 - f 0) / p`, for any continuous lift
`f` of the loop to `ℝ`. -/
theorem windingNumber_eq_div {x : AddCircle p} (γ : Path x x) (f : C(I, ℝ)) (hf : (↑) ∘ f = γ) :
    (windingNumber (.mk γ) : ℝ) = (f 1 - f 0) / p := by
  have h0 : (f 0 : AddCircle p) = x := congr($hf 0).trans γ.source
  obtain ⟨n, hn⟩ : ∃ n : ℤ, n • p = f 1 - f 0 :=
    AddSubgroup.mem_zmultiples_iff.mp <| QuotientAddGroup.eq_iff_sub_mem.mp <|
      congr($hf 1).trans <| γ.target.trans h0.symm
  have h : (isAddQuotientCoveringMap_coe p).fundamentalGroupEquiv (x := x) ⟨f 0, h0⟩ (.mk γ) =
      .op (.ofAdd ⟨n • p, n, rfl⟩) :=
    (isAddQuotientCoveringMap_coe p).fundamentalGroupToMulOpposite_apply_mk_eq hf rfl (by simp [hn])
  simp [windingNumber, windingNumberIso, AddSubgroup.zmultiplesEquivInt_apply_zsmul hp.out.ne' n,
    (isAddQuotientCoveringMap_coe p).fundamentalGroupEquiv_eq _ ⟨f 0, h0⟩, h,
    eq_div_iff hp.out.ne', ← zsmul_eq_mul, ← hn]

/-- The loop `t ↦ n • (t * p) + x` has winding number `n`. -/
theorem windingNumber_zsmulLoop (x : ℝ) (n : ℤ) :
    windingNumber (x := x) (.mk (zsmulLoop p x n)) = n := by
  simpa [hp.out.ne'] using windingNumber_eq_div (zsmulLoop p x n)
    ⟨fun t ↦ n • (t * p) + x, by fun_prop⟩ rfl

end AddCircle
