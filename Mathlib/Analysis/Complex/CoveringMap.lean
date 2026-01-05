/-
Copyright (c) 2026 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Topology.Covering.AddCircle

/-!
# Covering maps involving the complex plane

In this file, we show that `Complex.exp` is a covering map on `{0}ᶜ`.
-/

@[expose] public section

open Topology

namespace Complex

theorem isAddQuotientCoveringMap_exp :
    IsAddQuotientCoveringMap (fun z : ℂ ↦ (⟨_, z.exp_ne_zero⟩ : {z : ℂ // z ≠ 0}))
      (AddSubgroup.zmultiples (2 * Real.pi * I)) := by
  refine Topology.IsQuotientMap.isAddQuotientCoveringMap_of_addSubgroup ?_
    _ ⟨NormedSpace.discreteTopology_zmultiples _⟩ fun {z _} ↦ ?_
  · refine IsOpenMap.isQuotientMap ?_ (by fun_prop) fun z ↦ ⟨_, Subtype.ext (exp_log z.2)⟩
    exact (IsOpen.isOpenEmbedding_subtypeVal isClosed_singleton.1).isOpenMap_iff.mpr isOpenMap_exp
  · simp_rw [Subtype.ext_iff, eq_comm (a := exp z), exp_eq_exp_iff_exists_int,
      AddSubgroup.mem_zmultiples_iff, eq_add_neg_iff_add_eq, eq_comm, add_comm, zsmul_eq_mul]

/-- `exp : ℂ → ℂ \ {0}` is a covering map. -/
theorem isCoveringMap_exp : IsCoveringMap fun z : ℂ ↦ (⟨_, z.exp_ne_zero⟩ : {z : ℂ // z ≠ 0}) :=
  isAddQuotientCoveringMap_exp.isCoveringMap

theorem isCoveringMapOn_exp : IsCoveringMapOn Complex.exp {0}ᶜ :=
  .of_isCoveringMap_subtype (by simp) _ isCoveringMap_exp

end Complex
