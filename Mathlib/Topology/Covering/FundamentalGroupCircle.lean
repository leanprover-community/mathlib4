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
-/

public section

open unitInterval

theorem IsCoveringMap.coe_monodromy_mk {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {p : E → X} (cov : IsCoveringMap p) {x y : X} (γ : Path x y) (e : p ⁻¹' {x}) :
    (cov.monodromy (.mk γ) e : E) =
      cov.liftPath γ.toContinuousMap e (γ.source.trans e.2.symm) 1 :=
  rfl

namespace AddCircle

/-- The loop in `AddCircle 1` that winds `n` times, defined as `t ↦ n • t`. -/
def zsmulLoop (n : ℤ) : Path (0 : AddCircle (1 : ℝ)) 0 where
  toFun t := n • t
  source' := by simp
  target' := by simp [coe_period]
  continuous_toFun := (continuous_zsmul n).comp
    (continuous_quotient_mk'.comp continuous_subtype_val)

lemma liftPath_zsmulLoop (n : ℤ) (t : I) :
    (isCoveringMap_coe 1).liftPath (zsmulLoop n).toContinuousMap 0 (by simp) t = (n : ℝ) * t := by
  have h : (⟨fun t : I ↦ (n : ℝ) * t, by fun_prop⟩ : C(I, ℝ)) =
      (isCoveringMap_coe 1).liftPath (zsmulLoop n).toContinuousMap 0 (by simp) := by
    rw [IsCoveringMap.eq_liftPath_iff']
    refine ⟨funext fun t ↦ ?_, by simp⟩
    simp only [Function.comp_apply, ContinuousMap.coe_mk, zsmulLoop, ← zsmul_eq_mul, coe_zsmul]
  exact (DFunLike.congr_fun h t).symm

lemma monodromy_zsmulLoop (n : ℤ) :
    (((isCoveringMap_coe (1 : ℝ)).monodromy (.mk (zsmulLoop n)) ⟨0, by simp⟩ : _) : ℝ) = n := by
  simp [IsCoveringMap.coe_monodromy_mk, liftPath_zsmulLoop]

/-- The isomorphism between the subgroup of integer multiples of `1 : ℝ` and `ℤ`,
sending `m • (1 : ℝ)` to `m`. -/
noncomputable def zmultiplesOneEquivInt : AddSubgroup.zmultiples (1 : ℝ) ≃+ ℤ :=
  (AddEquiv.addSubgroupCongr (AddSubgroup.range_zmultiplesHom (1 : ℝ)).symm).trans
    (AddMonoidHom.ofInjective (f := zmultiplesHom ℝ (1 : ℝ))
      (smul_left_injective ℤ one_ne_zero)).symm

@[simp]
lemma coe_zmultiplesOneEquivInt_symm (m : ℤ) :
    ((zmultiplesOneEquivInt.symm m : AddSubgroup.zmultiples (1 : ℝ)) : ℝ) = m := by
  simp only [zmultiplesOneEquivInt, AddEquiv.symm_trans_apply, AddEquiv.symm_symm,
    AddEquiv.addSubgroupCongr_symm_apply]
  exact (AddMonoidHom.ofInjective_apply _).trans (by simp)

lemma zmultiplesOneEquivInt_apply_intCast (m : ℤ)
    (h : (m : ℝ) ∈ AddSubgroup.zmultiples (1 : ℝ)) :
    zmultiplesOneEquivInt ⟨(m : ℝ), h⟩ = m :=
  zmultiplesOneEquivInt.apply_eq_iff_eq_symm_apply.mpr <|
    Subtype.ext (coe_zmultiplesOneEquivInt_symm m).symm

/-- **The fundamental group of the circle is `ℤ`**: the isomorphism sends the class of the loop
winding `n` times around the circle to `n` -/
noncomputable def windingNumberIso :
    FundamentalGroup (AddCircle (1 : ℝ)) 0 ≃* Multiplicative ℤ :=
  ((isAddQuotientCoveringMap_coe (1 : ℝ)).fundamentalGroupEquiv (x := 0) ⟨0, by simp⟩).trans <|
    MulOpposite.opMulEquiv.symm.trans zmultiplesOneEquivInt.toMultiplicative

theorem windingNumberIso_zsmulLoop (n : ℤ) :
    windingNumberIso (FundamentalGroup.fromPath (.mk (zsmulLoop n))) =
      Multiplicative.ofAdd n := by
  have h : (isAddQuotientCoveringMap_coe (1 : ℝ)).fundamentalGroupEquiv (x := 0) ⟨0, by simp⟩
      (FundamentalGroup.fromPath (.mk (zsmulLoop n))) =
      MulOpposite.op (Multiplicative.ofAdd
        (⟨(n : ℝ), ⟨n, by simp⟩⟩ : AddSubgroup.zmultiples (1 : ℝ))) :=
    (IsAddQuotientCoveringMap.fundamentalGroupToMulOpposite_apply_eq_Iff
      (isAddQuotientCoveringMap_coe (1 : ℝ))).mpr <| by
      simp [monodromy_zsmulLoop, AddSubgroup.vadd_def, vadd_eq_add]
  simp only [windingNumberIso, MulEquiv.trans_apply, h, MulOpposite.coe_symm_opMulEquiv,
    MulOpposite.unop_op]
  exact congrArg Multiplicative.ofAdd (zmultiplesOneEquivInt_apply_intCast n ⟨n, by simp⟩)

/-- The winding number of a loop in the circle, defined as its image under `windingNumberIso`. -/
noncomputable def windingNumber (γ : FundamentalGroup (AddCircle (1 : ℝ)) 0) : ℤ :=
  Multiplicative.toAdd (windingNumberIso γ)

lemma windingNumber_zsmulLoop (n : ℤ) :
    windingNumber (FundamentalGroup.fromPath (.mk (zsmulLoop n))) = n :=
  congrArg Multiplicative.toAdd (windingNumberIso_zsmulLoop n)

end AddCircle
