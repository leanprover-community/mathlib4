/-
Copyright (c) 2020 Heather Macbeth, Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Patrick Massot
-/
import Mathlib.Algebra.Group.Subgroup.Order
import Mathlib.Algebra.Order.Archimedean.Basic

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

The file also supports multiplicative groups via `MulArchimedean`.

The result is also used in `Topology.Instances.Real` as an ingredient in the classification of
subgroups of `ℝ`.
-/

open Set
variable {G : Type*} [LinearOrderedCommGroup G] [MulArchimedean G]

/-- Given a subgroup `H` of a decidable linearly ordered mul-archimedean abelian group `G`, if there
exists a minimal element `a` of `H ∩ G_{>1}` then `H` is generated by `a`. -/
@[to_additive AddSubgroup.cyclic_of_min "Given a subgroup `H` of a decidable linearly ordered
archimedean abelian group `G`, if there exists a minimal element `a` of `H ∩ G_{>0}` then `H` is
generated by `a`. "]
theorem Subgroup.cyclic_of_min {H : Subgroup G} {a : G}
    (ha : IsLeast { g : G | g ∈ H ∧ 1 < g } a) : H = closure {a} := by
  obtain ⟨⟨a_in, a_pos⟩, a_min⟩ := ha
  refine le_antisymm ?_ (H.closure_le.mpr <| by simp [a_in])
  intro g g_in
  obtain ⟨k, ⟨nonneg, lt⟩, _⟩ := existsUnique_zpow_near_of_one_lt a_pos g
  have h_zero : g / (a ^ k) = 1 := by
    by_contra h
    have h : a ≤ g / (a ^ k) := by
      refine a_min ⟨?_, ?_⟩
      · exact Subgroup.div_mem H g_in (Subgroup.zpow_mem H a_in k)
      · exact lt_of_le_of_ne (by simpa using nonneg) (Ne.symm h)
    have h' : ¬a ≤ g / (a ^ k) := not_le.mpr (by simpa [zpow_add_one, div_lt_iff_lt_mul'] using lt)
    contradiction
  simp [div_eq_one.mp h_zero, mem_closure_singleton]

/-- If a nontrivial subgroup of a linear ordered commutative group is disjoint
with the interval `Set.Ioo 1 a` for some `1 < a`, then the set of elements greater than 1 of this
group admits the least element. -/
@[to_additive "If a nontrivial additive subgroup of a linear ordered additive commutative group is
disjoint with the interval `Set.Ioo 0 a` for some positive `a`, then the set of positive elements of
this group admits the least element."]
theorem Subgroup.exists_isLeast_one_lt {H : Subgroup G} (hbot : H ≠ ⊥) {a : G} (h₀ : 1 < a)
    (hd : Disjoint (H : Set G) (Ioo 1 a)) : ∃ b, IsLeast { g : G | g ∈ H ∧ 1 < g } b := by
  -- todo: move to a lemma?
  have hex : ∀ g > 1, ∃ n : ℕ, g ∈ Ioc (a ^ n) (a ^ (n + 1)) := fun g hg => by
    rcases existsUnique_mul_zpow_mem_Ico h₀ 1 (g / a) with ⟨m, ⟨hm, hm'⟩, -⟩
    simp only [one_mul, div_le_iff_le_mul, div_mul_cancel, ← zpow_add_one] at hm hm'
    lift m to ℕ
    · rw [← Int.lt_add_one_iff, ← zpow_lt_zpow_iff h₀, zpow_zero]
      exact hg.trans_le hm
    · simp only [← Nat.cast_succ, zpow_natCast] at hm hm'
      exact ⟨m, hm', hm⟩
  have : ∃ n : ℕ, Set.Nonempty (H ∩ Ioc (a ^ n) (a ^ (n + 1))) := by
    rcases (bot_or_exists_ne_one H).resolve_left hbot with ⟨g, hgH, hg₀⟩
    rcases hex |g|ₘ (one_lt_mabs.2 hg₀) with ⟨n, hn⟩
    exact ⟨n, _, (@mabs_mem_iff (Subgroup G) G _ _).2 hgH, hn⟩
  classical rcases Nat.findX this with ⟨n, ⟨x, hxH, hnx, hxn⟩, hmin⟩
  by_contra hxmin
  simp only [IsLeast, not_and, mem_setOf_eq, mem_lowerBounds, not_exists, not_forall,
    not_le] at hxmin
  rcases hxmin x ⟨hxH, (one_le_pow_of_one_le'  h₀.le _).trans_lt hnx⟩ with ⟨y, ⟨hyH, hy₀⟩, hxy⟩
  rcases hex y hy₀ with ⟨m, hm⟩
  cases' lt_or_le m n with hmn hnm
  · exact hmin m hmn ⟨y, hyH, hm⟩
  · refine disjoint_left.1 hd (div_mem hxH hyH) ⟨one_lt_div'.2 hxy, div_lt_iff_lt_mul'.2 ?_⟩
    calc x ≤ a^ (n + 1) := hxn
    _ ≤ a ^ (m + 1) := pow_le_pow_right' h₀.le (add_le_add_right hnm _)
    _ = a ^ m * a := pow_succ _ _
    _ < y * a := mul_lt_mul_right' hm.1 _

/-- If a subgroup of a linear ordered commutative group is disjoint with the
interval `Set.Ioo 1 a` for some `1 < a`, then this is a cyclic subgroup. -/
@[to_additive AddSubgroup.cyclic_of_isolated_zero "If an additive subgroup of a linear ordered
additive commutative group is disjoint with the interval `Set.Ioo 0 a` for some positive `a`, then
this is a cyclic subgroup."]
theorem Subgroup.cyclic_of_isolated_one {H : Subgroup G} {a : G} (h₀ : 1 < a)
    (hd : Disjoint (H : Set G) (Ioo 1 a)) : ∃ b, H = closure {b} := by
  rcases eq_or_ne H ⊥ with rfl | hbot
  · exact ⟨1, closure_singleton_one.symm⟩
  · exact (exists_isLeast_one_lt hbot h₀ hd).imp fun _ => cyclic_of_min

/-- Every subgroup of `ℤ` is cyclic. -/
theorem Int.subgroup_cyclic (H : AddSubgroup ℤ) : ∃ a, H = AddSubgroup.closure {a} :=
  have : Ioo (0 : ℤ) 1 = ∅ := eq_empty_of_forall_not_mem fun _ hm =>
    hm.1.not_le (lt_add_one_iff.1 hm.2)
  AddSubgroup.cyclic_of_isolated_zero one_pos <| by simp [this]
