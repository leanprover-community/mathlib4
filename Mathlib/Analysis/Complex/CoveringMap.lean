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
--public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
#trans_imports "Mathlib."

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
  refine Topology.IsQuotientMap.isAddQuotientCoveringMap_of_addSubgroup ?_ _
    ⟨NormedSpace.discreteTopology_zmultiples _⟩ fun {z _} ↦ ?_
  · refine IsOpenMap.isQuotientMap ?_ (by fun_prop) fun z ↦ ⟨_, Subtype.ext (exp_log z.2)⟩
    exact (IsOpen.isOpenEmbedding_subtypeVal isClosed_singleton.1).isOpenMap_iff.mpr isOpenMap_exp
  · simp_rw [Subtype.ext_iff, eq_comm (a := exp z), exp_eq_exp_iff_exists_int,
      AddSubgroup.mem_zmultiples_iff, eq_add_neg_iff_add_eq, eq_comm, add_comm, zsmul_eq_mul]

/-- `exp : ℂ → ℂ \ {0}` is a covering map. -/
theorem isCoveringMap_exp : IsCoveringMap fun z : ℂ ↦ (⟨_, z.exp_ne_zero⟩ : {z : ℂ // z ≠ 0}) :=
  isAddQuotientCoveringMap_exp.isCoveringMap

theorem isCoveringMapOn_exp : IsCoveringMapOn exp {0}ᶜ :=
  .of_isCoveringMap_subtype (by simp) _ isCoveringMap_exp

attribute [-instance] Units.mulAction' in
theorem isQuotientCoveringMap_zpow (n : ℤ) [NeZero n] :
    IsQuotientCoveringMap (fun z : ℂˣ ↦ z ^ n) (rootsOfUnity n.natAbs ℂ) := by
  refine Topology.IsQuotientMap.isQuotientCoveringMap_of_subgroup ?_ _
    (Set.Finite.isDiscrete <| inferInstanceAs (Finite (rootsOfUnity ..))) fun {_ _} ↦ ?_
  · refine IsOpenMap.isQuotientMap ?_ (by fun_prop) fun z ↦ ⟨_, Subtype.ext (exp_log z.2)⟩
  · simp [mul_zpow, mul_inv_eq_one, eq_comm]

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
