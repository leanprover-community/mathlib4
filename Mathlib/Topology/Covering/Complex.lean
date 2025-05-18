/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Topology.Covering.AddCircle

/-!
# Covering maps involving the complex plane

-/

open Topology

theorem isCoveringMap_circleExp : IsCoveringMap Circle.exp :=
  (isCoveringMap_coe_addCircle (2 * Real.pi)).homeomorph_comp AddCircle.homeomorphCircle'

namespace Complex

/-- `exp : ℂ → ℂ \ {0}` is a covering map. -/
theorem isCoverinMap_exp : IsCoveringMap fun z : ℂ ↦ (⟨_, z.exp_ne_zero⟩ : {z : ℂ // z ≠ 0}) := by
  apply Topology.IsQuotientMap.isCoveringMap_of_addSubgroup _ (.zmultiples (2 * Real.pi * I))
  · intro z₁ z₂; simp_rw [Subtype.ext_iff, eq_comm (a := exp z₁), exp_eq_exp_iff_exists_int,
      AddSubgroup.mem_zmultiples_iff, eq_neg_add_iff_add_eq, eq_comm, zsmul_eq_mul]
  refine IsOpenMap.isQuotientMap ?_ (by fun_prop) fun z ↦ ⟨_, Subtype.ext (exp_log z.2)⟩
  exact (IsOpen.isOpenEmbedding_subtypeVal isClosed_singleton.1).isOpenMap_iff.mpr isOpenMap_exp

/- theorem isCoveringMapOn_exp : IsCoveringMapOn Complex.exp {0}ᶜ :=
  Complex.isOpenMap_exp.isQuotientMap. -/

/-- `(· ^ n) : ℂ \ {0} → ℂ \ {0}` is a covering map. -/
theorem isCoveringMap_zpow (n : ℤ) [NeZero n] :
    IsCoveringMap fun z : {z : ℂ // z ≠ 0} ↦ (⟨z ^ n, zpow_ne_zero n z.2⟩ : {z : ℂ // z ≠ 0}) := by
  /-have := Int.natAbs_ne_zero.mpr (NeZero.ne n)
  obtain ⟨ζ, hζ⟩ : ∃ ζ, IsPrimitiveRoot ζ n.natAbs := ⟨_, isPrimitiveRoot_exp _ this⟩
  let _ : AddAction (ZMod n.natAbs) {z : ℂ // z ≠ 0} :=
  { vadd i z := ⟨ζ ^ i.val * z.1, mul_ne_zero (pow_ne_zero _ <| hζ.ne_zero this) z.2⟩
    zero_vadd z := Subtype.ext <| show ζ ^ 0 * z = z by simp
    add_vadd := _ } -/
  sorry

theorem isCoveringMapOn_zpow (n : ℤ) [NeZero n] : IsCoveringMapOn (· ^ n) ({0}ᶜ : Set ℂ) := by
  sorry

theorem isCoveringMap_zpow_units (n : ℤ) [NeZero n] : IsCoveringMap fun z : ℂˣ ↦ z ^ n := by
  apply IsQuotientMap.isCoveringMap_of_discrete_ker_monoidHom (f := zpowGroupHom (α := ℂˣ) n)
  sorry
  infer_instance


theorem isCoveringMap_npow (n : ℕ) [NeZero n] :
    IsCoveringMap fun z : {z : ℂ // z ≠ 0} ↦ (⟨z ^ n, zpow_ne_zero n z.2⟩ : {z : ℂ // z ≠ 0}) :=
  isCoveringMap_zpow n

theorem isCoveringMapOn_npow (n : ℕ) [NeZero n] : IsCoveringMapOn (· ^ n) ({0}ᶜ : Set ℂ) :=
  isCoveringMapOn_zpow n

theorem isCoveringMap_npow_units (n : ℕ) [NeZero n] : IsCoveringMap fun z : ℂˣ ↦ z ^ n :=
  isCoveringMap_zpow_units n

end Complex
