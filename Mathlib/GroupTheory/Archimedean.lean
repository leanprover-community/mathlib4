/-
Copyright (c) 2020 Heather Macbeth, Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Patrick Massot
-/
import Mathlib.Algebra.Order.Archimedean
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.Data.Set.Lattice

#align_import group_theory.archimedean from "leanprover-community/mathlib"@"f93c11933efbc3c2f0299e47b8ff83e9b539cbf6"

/-!
# Archimedean groups

This file proves a few facts about ordered groups which satisfy the `Archimedean` property, that is:
`class Archimedean (α) [OrderedAddCommMonoid α] : Prop :=`
`(arch : ∀ (x : α) {y}, 0 < y → ∃ n : ℕ, x ≤ n • y)`

They are placed here in a separate file (rather than incorporated as a continuation of
`Algebra.Order.Archimedean`) because they rely on some imports from `GroupTheory` -- bundled
subgroups in particular.

The main result is `AddSubgroup.cyclic_of_min`:  a subgroup of a decidable archimedean abelian
group is cyclic, if its set of positive elements has a minimal element.

This result is used in this file to deduce `Int.subgroup_cyclic`, proving that every subgroup of `ℤ`
is cyclic.  (There are several other methods one could use to prove this fact, including more purely
algebraic methods, but none seem to exist in mathlib as of writing.  The closest is
`Subgroup.is_cyclic`, but that has not been transferred to `AddSubgroup`.)

The result is also used in `Topology.Instances.Real` as an ingredient in the classification of
subgroups of `ℝ`.
-/

open Set
variable {G : Type*} [LinearOrderedAddCommGroup G] [Archimedean G]

/-- Given a subgroup `H` of a decidable linearly ordered archimedean abelian group `G`, if there
exists a minimal element `a` of `H ∩ G_{>0}` then `H` is generated by `a`. -/
theorem AddSubgroup.cyclic_of_min {H : AddSubgroup G} {a : G}
    (ha : IsLeast { g : G | g ∈ H ∧ 0 < g } a) : H = AddSubgroup.closure {a} := by
  obtain ⟨⟨a_in, a_pos⟩, a_min⟩ := ha
  refine' le_antisymm _ (H.closure_le.mpr <| by simp [a_in])
  intro g g_in
  obtain ⟨k, ⟨nonneg, lt⟩, _⟩ := existsUnique_zsmul_near_of_pos' a_pos g
  have h_zero : g - k • a = 0 := by
    by_contra h
    have h : a ≤ g - k • a := by
      refine' a_min ⟨_, _⟩
      · exact AddSubgroup.sub_mem H g_in (AddSubgroup.zsmul_mem H a_in k)
      · exact lt_of_le_of_ne nonneg (Ne.symm h)
    have h' : ¬a ≤ g - k • a := not_le.mpr lt
    contradiction
  simp [sub_eq_zero.mp h_zero, AddSubgroup.mem_closure_singleton]
#align add_subgroup.cyclic_of_min AddSubgroup.cyclic_of_min

/-- If a nontrivial additive subgroup of a linear ordered additive commutative group is disjoint
with the interval `Set.Ioo 0 a` for some positive `a`, then the set of positive elements of this
group admits the least element. -/
theorem AddSubgroup.exists_isLeast_pos {H : AddSubgroup G} (hbot : H ≠ ⊥) {a : G} (h₀ : 0 < a)
    (hd : Disjoint (H : Set G) (Ioo 0 a)) : ∃ b, IsLeast { g : G | g ∈ H ∧ 0 < g } b := by
  -- todo: move to a lemma?
  have hex : ∀ g > 0, ∃ n : ℕ, g ∈ Ioc (n • a) ((n + 1) • a) := fun g hg => by
    rcases existsUnique_add_zsmul_mem_Ico h₀ 0 (g - a) with ⟨m, ⟨hm, hm'⟩, -⟩
    simp only [zero_add, sub_le_iff_le_add, sub_add_cancel, ← add_one_zsmul] at hm hm'
    lift m to ℕ
    · rw [← Int.lt_add_one_iff, ← zsmul_lt_zsmul_iff h₀, zero_zsmul]
      exact hg.trans_le hm
    · simp only [← Nat.cast_succ, coe_nat_zsmul] at hm hm'
      exact ⟨m, hm', hm⟩
  have : ∃ n : ℕ, Set.Nonempty (H ∩ Ioc (n • a) ((n + 1) • a)) := by
    rcases (bot_or_exists_ne_zero H).resolve_left hbot with ⟨g, hgH, hg₀⟩
    rcases hex |g| (abs_pos.2 hg₀) with ⟨n, hn⟩
    exact ⟨n, _, (@abs_mem_iff (AddSubgroup G) G _ _).2 hgH, hn⟩
  classical rcases Nat.findX this with ⟨n, ⟨x, hxH, hnx, hxn⟩, hmin⟩
  by_contra hxmin
  simp only [IsLeast, not_and, mem_setOf_eq, mem_lowerBounds, not_exists, not_forall,
    not_le] at hxmin
  rcases hxmin x ⟨hxH, (nsmul_nonneg h₀.le _).trans_lt hnx⟩ with ⟨y, ⟨hyH, hy₀⟩, hxy⟩
  rcases hex y hy₀ with ⟨m, hm⟩
  cases' lt_or_le m n with hmn hnm
  · exact hmin m hmn ⟨y, hyH, hm⟩
  · refine disjoint_left.1 hd (sub_mem hxH hyH) ⟨sub_pos.2 hxy, sub_lt_iff_lt_add'.2 ?_⟩
    calc x ≤ (n + 1) • a := hxn
    _ ≤ (m + 1) • a := nsmul_le_nsmul_left h₀.le (add_le_add_right hnm _)
    _ = m • a + a := succ_nsmul' _ _
    _ < y + a := add_lt_add_right hm.1 _

/-- If an additive subgroup of a linear ordered additive commutative group is disjoint with the
interval `Set.Ioo 0 a` for some positive `a`, then this is a cyclic subgroup. -/
theorem AddSubgroup.cyclic_of_isolated_zero {H : AddSubgroup G} {a : G} (h₀ : 0 < a)
    (hd : Disjoint (H : Set G) (Ioo 0 a)) : ∃ b, H = closure {b} := by
  rcases eq_or_ne H ⊥ with rfl | hbot
  · exact ⟨0, closure_singleton_zero.symm⟩
  · exact (exists_isLeast_pos hbot h₀ hd).imp fun _ => cyclic_of_min

/-- Every subgroup of `ℤ` is cyclic. -/
theorem Int.subgroup_cyclic (H : AddSubgroup ℤ) : ∃ a, H = AddSubgroup.closure {a} :=
  have : Ioo (0 : ℤ) 1 = ∅ := eq_empty_of_forall_not_mem fun m hm =>
    hm.1.not_le (lt_add_one_iff.1 hm.2)
  AddSubgroup.cyclic_of_isolated_zero one_pos <| by simp [this]
#align int.subgroup_cyclic Int.subgroup_cyclic
