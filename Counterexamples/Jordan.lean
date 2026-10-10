/-
Copyright (c) 2026 Vincent Quenneville-Belair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Quenneville-Belair
-/
module

public import Mathlib.GroupTheory.GroupAction.Jordan

import Mathlib.Tactic.FinCases

/-!
# A singleton complement is insufficient for Jordan's strong transitivity criterion

The hypothesis `n + 2 < Nat.card α` in
`MulAction.IsPreprimitive.is_two_pretransitive'` cannot be weakened to `n + 1 < Nat.card α`.
Take the natural action of `Equiv.Perm (Fin 3)` on `Fin 3`, with `s = {0, 1}` and `n = 1`.
This action is primitive, and the fixing subgroup acts transitively on the singleton complement.
However, the fixing subgroup and its normal closure are trivial, so the normal closure does not
act 2-pretransitively.
-/

public section

open MulAction SubMulAction Subgroup

namespace Counterexample.Jordan

private theorem fixingSubgroup_pair_eq_bot :
    fixingSubgroup (Equiv.Perm (Fin 3)) ({0, 1} : Set (Fin 3)) = ⊥ := by
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro g hg
  have h0 : g 0 = 0 := (mem_fixingSubgroup_iff _).mp hg 0 (by simp)
  have h1 : g 1 = 1 := (mem_fixingSubgroup_iff _).mp hg 1 (by simp)
  apply Equiv.ext
  intro i
  change g i = i
  fin_cases i
  · exact h0
  · exact h1
  · have h20 := g.injective.ne (by decide : (2 : Fin 3) ≠ 0)
    have h21 := g.injective.ne (by decide : (2 : Fin 3) ≠ 1)
    simp only [h0, h1, Fin.ne_iff_vne] at h20 h21
    apply Fin.ext
    change (g 2).val = 2
    omega

/-- Every hypothesis of the strong criterion with the weaker bound holds, but its conclusion fails.
The cardinality hypothesis uses `Nat.card s`, as in the original wanted statement. -/
theorem singleton_complement_counterexample :
    IsPreprimitive (Equiv.Perm (Fin 3)) (Fin 3) ∧
    Nat.card ({0, 1} : Set (Fin 3)) = 1 + 1 ∧
    1 + 1 < Nat.card (Fin 3) ∧
    IsPretransitive (fixingSubgroup (Equiv.Perm (Fin 3)) ({0, 1} : Set (Fin 3)))
      (ofFixingSubgroup (Equiv.Perm (Fin 3)) ({0, 1} : Set (Fin 3))) ∧
    ¬ IsMultiplyPretransitive
      (normalClosure (fixingSubgroup (Equiv.Perm (Fin 3)) ({0, 1} : Set (Fin 3)) :
        Set (Equiv.Perm (Fin 3)))) (Fin 3) 2 := by
  have : Subsingleton (ofFixingSubgroup (Equiv.Perm (Fin 3)) ({0, 1} : Set (Fin 3))) := by
    refine ⟨fun ⟨x, hx⟩ ⟨y, hy⟩ ↦ Subtype.ext ?_⟩
    change x = y
    change x ∉ ({0, 1} : Set (Fin 3)) at hx
    change y ∉ ({0, 1} : Set (Fin 3)) at hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or, Fin.ne_iff_vne] at hx hy
    apply Fin.ext
    omega
  refine ⟨inferInstance, ?_, by simp, inferInstance, ?_⟩
  · rw [Nat.card_coe_set_eq, Set.ncard_pair (by decide)]
  · rw [fixingSubgroup_pair_eq_bot, normalClosure_eq_self]
    intro h
    obtain ⟨g, hg, _⟩ := is_two_pretransitive_iff.mp h
      (by decide : (0 : Fin 3) ≠ 1) (by decide : (1 : Fin 3) ≠ 0)
    have hg1 : (g : Equiv.Perm (Fin 3)) = 1 := Subgroup.mem_bot.mp g.prop
    change (g : Equiv.Perm (Fin 3)) 0 = 1 at hg
    rw [hg1] at hg
    exact Fin.zero_ne_one hg

end Counterexample.Jordan
