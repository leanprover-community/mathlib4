/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Topology.Covering.Quotient
public import Mathlib.Topology.Instances.AddCircle.Defs

/-!
# Covering maps involving `AddCircle`

-/

public section

namespace AddCircle

section AddCommGroup

open AddSubgroup

variable {𝕜 : Type*} [AddCommGroup 𝕜] (p : 𝕜) [TopologicalSpace 𝕜] [IsTopologicalAddGroup 𝕜]
  [DiscreteTopology (zmultiples p)]

theorem isAddQuotientCoveringMap_coe :
    IsAddQuotientCoveringMap ((↑) : 𝕜 → AddCircle p) (zmultiples p) :=
  isAddQuotientCoveringMap_of_comm _ DiscreteTopology.isDiscrete

theorem isCoveringMap_coe : IsCoveringMap ((↑) : 𝕜 → AddCircle p) :=
  (isAddQuotientCoveringMap_coe p).isCoveringMap

theorem isLocalHomeomorph_coe : IsLocalHomeomorph ((↑) : 𝕜 → AddCircle p) :=
  (isCoveringMap_coe p).isLocalHomeomorph

end AddCommGroup

section Field

open Topology

variable {𝕜 : Type*} [TopologicalSpace 𝕜] [Ring 𝕜] [IsTopologicalRing 𝕜]
variable (p : 𝕜) [T0Space (AddCircle p)]
/- This instance can be supplied from:
- `[NormedSpace ℚ 𝕜]` (with import `Mathlib.Analysis.Normed.Module.Basic`), or
- `[LinearOrder 𝕜] [IsOrderedMonoid 𝕜] [OrderTopology 𝕜]`
  (with import `Mathlib.Topology.Algebra.Order.ArchimedeanDiscrete`)
and `𝕜 := ℝ` satisfies both. -/

theorem isAddQuotientCoveringMap_zsmul {n : ℤ} (hn : IsUnit (n : 𝕜)) :
    IsAddQuotientCoveringMap (n • · : AddCircle p → _)
      (zsmulAddGroupHom (α := AddCircle p) n).ker := by
  refine hn.isQuotientMap_zsmul (QuotientAddGroup.mk' _) isQuotientMap_quotient_mk'
    |>.isAddQuotientCoveringMap_of_isDiscrete_ker_addMonoidHom
    (f := zsmulAddGroupHom (α := AddCircle p) n)
    (Set.Finite.isDiscrete <| finite_torsion_of_isSMulRegular_int _ _ fun _ ↦ ?_)
  simp_rw [zsmul_eq_mul]
  apply hn.isSMulRegular 𝕜

theorem isAddQuotientCoveringMap_nsmul {n : ℕ} (hn : IsUnit (n : 𝕜)) :
    IsAddQuotientCoveringMap (n • · : AddCircle p → _)
      (nsmulAddMonoidHom (α := AddCircle p) n).ker := by
  convert isAddQuotientCoveringMap_zsmul p (n := n) (mod_cast hn)
  all_goals ext; simp

theorem isAddQuotientCoveringMap_zsmul_of_ne_zero [Algebra ℚ 𝕜] (n : ℤ) [NeZero n] :
    IsAddQuotientCoveringMap (n • · : AddCircle p → _)
      (zsmulAddGroupHom (α := AddCircle p) n).ker :=
  isAddQuotientCoveringMap_zsmul p (n := n) <| by
    convert (Int.cast_ne_zero.mpr <| NeZero.ne n).isUnit.map (algebraMap ℚ 𝕜); simp

theorem isAddQuotientCoveringMap_nsmul_of_ne_zero [Algebra ℚ 𝕜] (n : ℕ) [NeZero n] :
    IsAddQuotientCoveringMap (n • · : AddCircle p → _)
      (nsmulAddMonoidHom (α := AddCircle p) n).ker :=
  isAddQuotientCoveringMap_nsmul p (n := n) <| by
    convert (Nat.cast_ne_zero.mpr <| NeZero.ne n).isUnit.map (algebraMap ℚ 𝕜); simp

end Field

end AddCircle
