/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.Topology.Instances.AddCircle
import Mathlib.Topology.Covering.Galois

/-!
# Covering maps involving `AddCircle`

-/

example (p : ℝ) : IsCoveringMap ((↑) : ℝ → AddCircle p) := AddSubgroup.isCoveringMap _

open Topology in
theorem isCoveringMap_nsmul (p : ℝ) [Fact (0 < p)] {n : ℕ} (hn : 0 < n) :
    IsCoveringMap fun x : AddCircle p ↦ n • x := by
  apply IsQuotientMap.isCoveringMap_of_discrete_ker_addMonoidHom
    (f := DistribMulAction.toAddMonoidHom _ n)
  · /- To show that (n • ·) on AddCircle p is a quotient map, it suffices to show
      its composition with ℝ → AddCircle p is a quotient map. -/
    apply IsQuotientMap.of_comp (f := ((↑) : ℝ → _)) _ (continuous_zsmul n)
    · /- This composition is equal to the composition with (n • ·) on ℝ (a homeomorphism)
        and the quotient map ℝ → AddCircle p. -/
      convert isQuotientMap_quotient_mk'.comp (affineHomeomorph (n : ℝ) 0 _).isQuotientMap
      on_goal 2 => exact_mod_cast hn.ne'
      ext x; dsimp only [Function.comp_apply]
      rw [affineHomeomorph_apply, add_zero, ← nsmul_eq_mul]; rfl
    · exact continuous_quotient_mk'
  · refine @Finite.instDiscreteTopology _ _ _ ?_
    simp_rw [AddMonoidHom.mem_ker, DistribMulAction.toAddMonoidHom_apply]
    exact Set.finite_coe_iff.mpr (AddCircle.finite_torsion p hn)
