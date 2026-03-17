/-
Copyright (c) 2026 Edward van de Meent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edward van de Meent
-/
module

public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# Definition of Cayley graphs

This file defines and proves several fact about Cayley graphs.
A Cayley graph over type `M` with generators `s : Set M` is a graph in which two vertices `u ≠ v`
are adjacent if and only if there is some `g ∈ s` such that `u * g = v` or `v * g = u`.
The elements of `s` are called generators.

## Main declarations

* `SimpleGraph.mulCayley s`: the Cayley graph over `M` induced by `[Mul M]` with generators `s`.
* `SimpleGraph.addCayley s`: the Cayley graph over `M` induced by `[Add M]` with generators `s`.
-/

@[expose] public section

namespace SimpleGraph

/-- the Cayley graph induced by an operation `[Mul M]` with generators `s` -/
@[to_additive /-- the Cayley graph induced by an operation `[Add M]` with generators `s` -/]
def mulCayley {M : Type*} (s : Set M) [Mul M] : SimpleGraph M :=
  fromRel (∃ g ∈ s, · * g = ·)

variable {M : Type*} (s : Set M)

section mul
variable [Mul M]

@[to_additive]
lemma mulCayley_adj' (u v : M) :
    (mulCayley s).Adj u v ↔ u ≠ v ∧ ∃ g ∈ s, u * g = v ∨ u = v * g := by
  simp [mulCayley,← exists_or,← and_or_left, eq_comm]

@[to_additive]
instance [Fintype M] [DecidableEq M] [DecidablePred (· ∈ s)] :
    DecidableRel (mulCayley s).Adj := fun u v =>
  decidable_of_iff (u ≠ v ∧ ∃ g ∈ s, u * g = v ∨ u = v * g) (mulCayley_adj' s u v).symm

@[to_additive (attr := gcongr)]
theorem mulCayley_mono ⦃U V : Set M⦄ (hUV : U ⊆ V) : mulCayley U ≤ mulCayley V := by
  intro _ _
  simp_rw [mulCayley_adj']
  gcongr

variable (M) in
/-- `mulCayley` is a left (order-)adjoint. -/
@[to_additive]
lemma mulCayley_gc :
    GaloisConnection (mulCayley ·) ({g : M | ∀ a , a * g ≠ a → ·.Adj (a * g) a}) := by
  apply GaloisConnection.monotone_intro _ mulCayley_mono
  · intro s x hx
    simp_rw [Set.mem_setOf, mulCayley_adj']
    intro a hab
    use hab, x, hx
    simp
  · intro s x y
    simp only [ne_eq, mulCayley_adj', Set.mem_setOf_eq, and_imp, forall_exists_index]
    rintro hne z hz (rfl|rfl)
    · exact (hz x (hne ·.symm)).symm
    · exact hz y hne
  · intro G H hle
    simp only [ne_eq, Set.le_eq_subset, Set.setOf_subset_setOf]
    intro z hz m hm
    exact hle (hz m hm)

set_option backward.isDefEq.respectTransparency false in
@[to_additive (attr := simp)]
theorem mulCayley_empty : mulCayley (∅ : Set M) = ⊥ := by
  exact (mulCayley_gc M).l_bot

set_option backward.isDefEq.respectTransparency false in
@[to_additive (attr := simp)]
theorem mulCayley_union (s₁ s₂ : Set M) : mulCayley (s₁ ∪ s₂) = mulCayley s₁ ⊔ mulCayley s₂ := by
  exact (mulCayley_gc M).l_sup

end mul
section semigroup
variable [Semigroup M]

@[to_additive]
theorem mulCayley_adj_mul_left_iff [IsLeftCancelMul M] {s : Set M} {u v d : M} :
    (mulCayley s).Adj u v ↔ (mulCayley s).Adj (d * u) (d * v) := by
  simp [mulCayley_adj', mul_assoc]

end semigroup
section muloneclass
variable [MulOneClass M]

@[to_additive (attr := simp)]
theorem mulCayley_eq_erase_one : mulCayley (s \ {1}) = mulCayley s := by
  nth_rw 2 [← Set.diff_union_inter s {1}]
  rw [mulCayley_union]
  ext u v
  simp +contextual [mulCayley_adj']

@[to_additive]
theorem mulCayley_eq_union_one : mulCayley (s ∪ {1}) = mulCayley s := by
  simp [-Set.union_singleton, ← mulCayley_eq_erase_one]

@[to_additive (attr := simp)]
theorem mulCayley_singleton_one : mulCayley ({1} : Set M) = ⊥ := by
  rw [← mulCayley_eq_erase_one, Set.diff_self, mulCayley_empty]

end muloneclass
section group
variable [Group M]

@[to_additive]
lemma mulCayley_adj (u v : M) :
    (mulCayley s).Adj u v ↔ u ≠ v ∧ (u⁻¹ * v ∈ s ∨ v⁻¹ * u ∈ s) := by
  simp [mulCayley_adj',← eq_inv_mul_iff_mul_eq (b := u),← inv_mul_eq_iff_eq_mul (a := v),
    and_or_left, exists_or]

@[to_additive (attr := simp)]
theorem mulCayley_inv_eq : mulCayley s⁻¹ = mulCayley s := by
  ext u v
  simp [mulCayley_adj, or_comm]

@[to_additive]
theorem mulCayley_eq_symm : mulCayley s = mulCayley (s ∪ (s⁻¹)) := by
  simpa using mulCayley_mono (Set.Subset.refl s)

@[to_additive]
instance [DecidableEq M] [DecidablePred (· ∈ s)] : DecidableRel (mulCayley s).Adj :=
  fun u v => decidable_of_iff (u ≠ v ∧ (u⁻¹ * v ∈ s ∨ v⁻¹ * u ∈ s)) (mulCayley_adj s u v).symm

@[to_additive (attr := simp)]
theorem mulCayley_univ : mulCayley (Set.univ : Set M) = ⊤ := by
  ext _ _
  simp [mulCayley_adj]

@[to_additive (attr := simp)]
theorem mulCayley_compl_singleton_one : mulCayley ({1}ᶜ : Set M) = ⊤ := by
  simp [Set.compl_eq_univ_diff]

end group

end SimpleGraph
