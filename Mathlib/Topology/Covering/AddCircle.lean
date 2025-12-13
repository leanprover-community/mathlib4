/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Covering.Quotient
public import Mathlib.Topology.Instances.AddCircle.Defs

/-!
# Covering maps involving `AddCircle`

-/

@[expose] public section

open AddSubgroup (zmultiples)

namespace AddCircle

section AddCommGroup

variable {𝕜 : Type*} [AddCommGroup 𝕜] (p : 𝕜) [TopologicalSpace 𝕜] [IsTopologicalAddGroup 𝕜]
  [DiscreteTopology (AddSubgroup.zmultiples p)]

theorem isQuotientCoveringMap_coe :
    IsAddQuotientCoveringMap ((↑) : 𝕜 → AddCircle p) (zmultiples p) :=
  AddSubgroup.isQuotientCoveringMap_of_comm _ DiscreteTopology.isDiscrete

theorem isCoveringMap_coe : IsCoveringMap ((↑) : 𝕜 → AddCircle p) :=
  (isQuotientCoveringMap_coe p).isCoveringMap

theorem isLocalHomeomorph_coe : IsLocalHomeomorph ((↑) : 𝕜 → AddCircle p) :=
  (isCoveringMap_coe p).isLocalHomeomorph

example (p : ℝ) : IsCoveringMap ((↑) : ℝ → AddCircle p) := isCoveringMap_coe p

end AddCommGroup

section Field

open Topology

variable {𝕜 : Type*} [NormedField 𝕜] [NormedSpace ℚ 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  (p : 𝕜)

open DistribMulAction

theorem isAddQuotientCoveringMap_zsmul {n : ℤ} (hn : n ≠ 0) :
    IsAddQuotientCoveringMap (n • · : AddCircle p → _) (toAddMonoidHom (AddCircle p) n).ker := by
  refine IsQuotientMap.isQuotientCoveringMap_of_isDiscrete_ker_addMonoidHom
    (f := toAddMonoidHom ..) ?_ (Set.Finite.isDiscrete ?_) rfl
  · /- To show that (n • ·) on AddCircle p is a quotient map, it suffices to show
      its composition with ℝ → AddCircle p is a quotient map. -/
    apply IsQuotientMap.of_comp (f := ((↑) : 𝕜 → _)) continuous_quotient_mk' (continuous_zsmul n)
    /- This composition is equal to the composition with (n • ·) on ℝ (a homeomorphism)
      and the quotient map ℝ → AddCircle p. -/
    convert isQuotientMap_quotient_mk'.comp (affineHomeomorph (n : 𝕜) 0 (mod_cast hn)).isQuotientMap
    ext x
    simp_rw [Function.comp_apply, affineHomeomorph_apply, add_zero, ← zsmul_eq_mul]
    rfl
  rw [AddMonoidHom.coe_ker, Set.preimage, ← n.sign_mul_natAbs]
  simp_rw [toAddMonoidHom_apply, Set.mem_singleton_iff]
  obtain neg | pos := hn.lt_or_gt
  on_goal 1 => simp_rw [n.sign_eq_neg_one_of_neg neg, neg_mul, one_mul, neg_smul, neg_eq_zero]
  on_goal 2 => rw [n.sign_eq_one_of_pos pos, one_mul]
  all_goals simpa using finite_torsion p (n.natAbs_pos.mpr hn)

theorem isAddQuotientCoveringMap_nsmul {n : ℕ} (hn : n ≠ 0) :
    IsAddQuotientCoveringMap (n • · : AddCircle p → _) (toAddMonoidHom (AddCircle p) n).ker := by
  convert isAddQuotientCoveringMap_zsmul p (n := n) (mod_cast hn)
  all_goals ext; simp

end Field

end AddCircle
