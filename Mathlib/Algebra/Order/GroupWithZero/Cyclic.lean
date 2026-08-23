/-
Copyright (c) 2026 Edison Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Edison Xie
-/
module

public import Mathlib.Algebra.GroupWithZero.Cyclic
public import Mathlib.Algebra.Order.Group.Cyclic
public import Mathlib.Algebra.Order.GroupWithZero.Subgroup

/-!
# The generator below one of a cyclic subgroup with zero

For a cyclic, non-degenerate subgroup with zero `s` of a `LinearOrderedCommGroupWithZero`, this
file provides its distinguished generator `s.genLTOne₀`, the one that is `< 1`.

## Implementation notes

The non-degeneracy hypothesis is `[Nontrivial sˣ]`, not `[Nontrivial s]`: the latter holds for
every subgroup with zero, since `⊥ = {0, 1}`.

The extra conjunct `0 < g` in `exists_generator_lt_one₀` is not redundant. In a
`LinearOrderedCommGroupWithZero` one has `0 < 1`, so `g < 1` no longer implies `g ≠ 0`, and
`zpowers₀ 0 = ⊥`.

## Tags
subgroup with zero, cyclic, generator
-/

@[expose] public section

noncomputable section

namespace SubgroupWithZero

variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
variable (s : SubgroupWithZero Γ) [Nontrivial sˣ] [IsCyclicWithZero s]

/-- With-zero analogue of `LinearOrderedCommGroup.Subgroup.exists_generator_lt_one`.

Note the extra `0 < g`: it is not implied by `g < 1`, since `0 < 1`. -/
lemma exists_generator_lt_one₀ : ∃ g : Γ, 0 < g ∧ g < 1 ∧ zpowers₀ g = s := by
  obtain ⟨a, ha1, ha⟩ := LinearOrderedCommGroup.Subgroup.exists_generator_lt_one s.units
  refine ⟨(a : Γ), zero_lt_iff.2 a.ne_zero, ?_, ?_⟩
  · rw [← Units.val_one, Units.val_lt_val]
    exact ha1
  · rw [← unitsOrderIso.injective.eq_iff, unitsOrderIso_apply, unitsOrderIso_apply,
      units_zpowers₀ a.ne_zero, Units.mk0_val, ha]

/-- The distinguished generator of a cyclic, non-degenerate subgroup with zero: the one that is
`< 1` (and, necessarily, `> 0`). -/
protected def genLTOne₀ : Γ := s.exists_generator_lt_one₀.choose

@[simp] lemma genLTOne₀_pos : 0 < s.genLTOne₀ := s.exists_generator_lt_one₀.choose_spec.1

@[simp] lemma genLTOne₀_ne_zero : s.genLTOne₀ ≠ 0 := s.genLTOne₀_pos.ne'

lemma genLTOne₀_lt_one : s.genLTOne₀ < 1 := s.exists_generator_lt_one₀.choose_spec.2.1

lemma genLTOne₀_ne_one : s.genLTOne₀ ≠ 1 := s.genLTOne₀_lt_one.ne

@[simp]
lemma genLTOne₀_zpowers₀_eq : zpowers₀ s.genLTOne₀ = s := s.exists_generator_lt_one₀.choose_spec.2.2

lemma genLTOne₀_mem : s.genLTOne₀ ∈ s := s.genLTOne₀_zpowers₀_eq.le (mem_zpowers₀ _)

/-- The generator is the greatest element of `s` that is `< 1`. -/
lemma genLTOne₀_isGreatest : IsGreatest {x : Γ | x ∈ s ∧ x < 1} s.genLTOne₀ := by
  refine ⟨⟨s.genLTOne₀_mem, s.genLTOne₀_lt_one⟩, ?_⟩
  rintro x ⟨hxs, hx1⟩
  rcases eq_or_ne x 0 with rfl | hx0
  · exact s.genLTOne₀_pos.le
  have hxs' : x ∈ zpowers₀ s.genLTOne₀ := s.genLTOne₀_zpowers₀_eq.ge hxs
  rw [mem_zpowers₀_iff_of_ne_zero hx0] at hxs'
  obtain ⟨n, rfl⟩ := hxs'
  have hg := s.genLTOne₀_pos
  have hg1 := s.genLTOne₀_lt_one
  have hn : 1 ≤ n := by
    by_contra hn
    exact absurd hx1 (not_lt.2 (one_le_zpow_of_nonpos₀ hg hg1.le (by omega)))
  calc s.genLTOne₀ ^ n ≤ s.genLTOne₀ ^ (1 : ℤ) :=
        zpow_le_zpow_right_of_le_one₀ hg hg1.le hn
    _ = s.genLTOne₀ := zpow_one _

end SubgroupWithZero
