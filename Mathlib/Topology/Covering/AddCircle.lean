/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Covering.Galois
import Mathlib.Topology.Instances.AddCircle

/-!
# Covering maps involving `AddCircle`

-/

namespace AddCircle

section AddCommGroup

variable {𝕜 : Type*} [AddCommGroup 𝕜] (p : 𝕜) [TopologicalSpace 𝕜] [IsTopologicalAddGroup 𝕜]
  [DiscreteTopology (AddSubgroup.zmultiples p)]

theorem isCoveringMap_coe : IsCoveringMap ((↑) : 𝕜 → AddCircle p) := AddSubgroup.isCoveringMap _

theorem isLocalHomeomorph_coe : IsLocalHomeomorph ((↑) : 𝕜 → AddCircle p) :=
  (isCoveringMap_coe p).isLocalHomeomorph

example (p : ℝ) : IsCoveringMap ((↑) : ℝ → AddCircle p) := isCoveringMap_coe p

end AddCommGroup

section Field

open Topology

variable {𝕜 : Type*} [NormedField 𝕜] [NormedSpace ℚ 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  (p : 𝕜)

theorem isCoveringMap_zsmul {n : ℤ} (hn : n ≠ 0) :
    IsCoveringMap fun x : AddCircle p ↦ n • x := by
  apply IsQuotientMap.isCoveringMap_of_discrete_ker_addMonoidHom
    (f := DistribMulAction.toAddMonoidHom _ n)
  · /- To show that (n • ·) on AddCircle p is a quotient map, it suffices to show
      its composition with ℝ → AddCircle p is a quotient map. -/
    apply IsQuotientMap.of_comp (f := ((↑) : 𝕜 → _)) _ (continuous_zsmul n)
    · /- This composition is equal to the composition with (n • ·) on ℝ (a homeomorphism)
        and the quotient map ℝ → AddCircle p. -/
      convert isQuotientMap_quotient_mk'.comp
        (affineHomeomorph (n : 𝕜) 0 <| by exact_mod_cast hn).isQuotientMap
      ext x; dsimp only [Function.comp_apply]
      rw [affineHomeomorph_apply, add_zero, ← zsmul_eq_mul]; rfl
    · exact continuous_quotient_mk'
  refine @Finite.instDiscreteTopology _ _ _ ?_
  simp_rw [AddMonoidHom.mem_ker, DistribMulAction.toAddMonoidHom_apply]
  rw [← n.sign_mul_natAbs]
  obtain neg | pos := hn.lt_or_lt
  on_goal 1 => simp_rw [n.sign_eq_neg_one_of_neg neg, neg_mul, one_mul, neg_smul, neg_eq_zero]
  on_goal 2 => rw [n.sign_eq_one_of_pos pos, one_mul]
  all_goals simpa only [Nat.cast_smul_eq_nsmul] using
    Set.finite_coe_iff.mpr (finite_torsion p (n.natAbs_pos.mpr hn))

theorem isCoveringMap_nsmul {n : ℕ} (hn : n ≠ 0) :
    IsCoveringMap fun x : AddCircle p ↦ n • x := by
  simpa using isCoveringMap_zsmul p (n := n) (by exact_mod_cast hn)

end Field

end AddCircle
