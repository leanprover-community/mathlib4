/-
Copyright (c) 2025 Ruize Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruize Chen
-/
module

public import Mathlib.Topology.Covering.AddCircle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Instances.ZMultiples
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

/-!
# The fundamental group of the circle

For `0 < p`, the fundamental group of `AddCircle p` at any basepoint is isomorphic to `ℤ`
(`AddCircle.windingNumberIso`). The winding number of a loop is `(f 1 - f 0) / p` for any
continuous lift `f : I → ℝ` of the loop (`AddCircle.windingNumber_eq_div`); in particular the
loop `t ↦ n • (t * p) + x` has winding number `n` (`AddCircle.windingNumber_zsmulLoop`).
-/

public section

open unitInterval

namespace AddCircle

variable (p : ℝ)

/-- The loop in `AddCircle p` based at `x` that winds `n` times, defined as
`t ↦ n • (t * p) + x`. -/
def zsmulLoop (x : ℝ) (n : ℤ) : Path (x : AddCircle p) x where
  toFun t := ((n • ((t : ℝ) * p) + x : ℝ) : AddCircle p)
  source' := by simp
  target' := by simp [coe_period]
  continuous_toFun := by fun_prop

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
  Multiplicative.toAdd (windingNumberIso x γ)

/-- The winding number of a loop in `AddCircle p` is `(f 1 - f 0) / p`, for any continuous lift
`f` of the loop to `ℝ`. -/
theorem windingNumber_eq_div {x : AddCircle p} (γ : Path x x) (f : C(I, ℝ))
    (hf : ∀ t, (f t : AddCircle p) = γ t) :
    (windingNumber (FundamentalGroup.fromPath (.mk γ)) : ℝ) = (f 1 - f 0) / p := by
  have h0 : ((f 0 : ℝ) : AddCircle p) = x := (hf 0).trans γ.source
  obtain ⟨n, hn⟩ : ∃ n : ℤ, n • p = f 1 - f 0 :=
    AddSubgroup.mem_zmultiples_iff.mp <| QuotientAddGroup.eq_iff_sub_mem.mp <|
      (hf 1).trans <| γ.target.trans h0.symm
  have hlift : (isCoveringMap_coe p).liftPath γ (f 0) (γ.source.trans h0.symm) = f :=
    (((isCoveringMap_coe p).eq_liftPath_iff' _).mpr ⟨funext hf, rfl⟩).symm
  have hmono : ((isCoveringMap_coe p).monodromy (.mk γ) ⟨f 0, h0⟩ : ℝ) = f 1 := by
    rw [IsCoveringMap.coe_monodromy_mk, hlift]
  have h : (isAddQuotientCoveringMap_coe p).fundamentalGroupEquiv (x := x) ⟨f 0, h0⟩
      (FundamentalGroup.fromPath (.mk γ)) =
      MulOpposite.op (Multiplicative.ofAdd
        (⟨n • p, AddSubgroup.zsmul_mem_zmultiples p n⟩ : AddSubgroup.zmultiples p)) :=
    (IsAddQuotientCoveringMap.fundamentalGroupToMulOpposite_apply_eq_Iff
      (isAddQuotientCoveringMap_coe p)).mpr <| by
      simp [hmono, AddSubgroup.vadd_def, vadd_eq_add, hn]
  have hw : windingNumber (FundamentalGroup.fromPath (.mk γ)) = n := by
    simp only [windingNumber, windingNumberIso]
    rw [(isAddQuotientCoveringMap_coe p).fundamentalGroupEquiv_eq _ ⟨f 0, h0⟩]
    simp only [MulEquiv.trans_apply, h, MulOpposite.coe_symm_opMulEquiv, MulOpposite.unop_op]
    exact AddSubgroup.zmultiplesEquivInt_apply_zsmul hp.out.ne' n
  rw [hw, eq_div_iff hp.out.ne', ← zsmul_eq_mul, hn]

/-- The loop `t ↦ n • (t * p) + x` has winding number `n`. -/
theorem windingNumber_zsmulLoop (x : ℝ) (n : ℤ) :
    windingNumber (FundamentalGroup.fromPath (.mk (zsmulLoop p x n))) = n := by
  refine Int.cast_injective (α := ℝ) ?_
  rw [windingNumber_eq_div (zsmulLoop p x n) ⟨fun t ↦ n • ((t : ℝ) * p) + x, by fun_prop⟩
    fun _ ↦ rfl]
  simp [hp.out.ne']

end AddCircle
