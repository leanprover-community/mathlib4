/-
Copyright (c) 2025 Dexin Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dexin Zhang
-/
module

public import Mathlib.Algebra.Group.Ideal
public import Mathlib.Algebra.Order.Monoid.Canonical.Defs
public import Mathlib.Order.WellFoundedSet

/-!
# Semigroup ideals in a canonically ordered and well-quasi-ordered monoid

This file proves that in a canonically ordered and well-quasi-ordered monoid, any semigroup ideal is
finitely generated, and the semigroup ideals satisfy the ascending chain condition.

## References

* [Samuel Eilenberg and M. P. Schützenberger, *Rational Sets in Commutative Monoids*][eilenberg1969]
-/

@[expose] public section

namespace SemigroupIdeal

variable {M : Type*} [CommMonoid M] [PartialOrder M] [WellQuasiOrderedLE M]
  [CanonicallyOrderedMul M]

/-- In a canonically ordered and well-quasi-ordered monoid, any semigroup ideal is finitely
generated. -/
@[to_additive /-- In a canonically ordered and well-quasi-ordered additive monoid, any semigroup
ideal is finitely generated. -/]
theorem fg_of_wellQuasiOrderedLE (I : SemigroupIdeal M) : I.FG := by
  have hpwo := Set.isPWO_of_wellQuasiOrderedLE { x | x ∈ I }
  refine ⟨_, (setOf_minimal_antichain _).finite_of_partiallyWellOrderedOn
    (hpwo.mono (setOf_minimal_subset _)), ?_⟩
  ext x
  simp only [mem_closure'', SetLike.setOf_mem_eq, SetLike.mem_coe, Set.mem_setOf_eq]
  constructor
  · intro hx
    rcases hpwo.exists_le_minimal hx with ⟨z, hz, hz'⟩
    rw [le_iff_exists_mul'] at hz
    rcases hz with ⟨y, rfl⟩
    exact ⟨y, z, hz', rfl⟩
  · rintro ⟨y, z, hz, rfl⟩
    apply SubMulAction.smul_mem
    exact hz.1

/-- In a canonically ordered and well-quasi-ordered monoid, the semigroup ideals satisfy the
ascending chain condition. -/
@[to_additive /-- A canonically ordered and well-quasi-ordered additive monoid, the semigroup ideals
satisfy the ascending chain condition. -/]
instance : WellFoundedGT (SemigroupIdeal M) := by
  rw [wellFoundedGT_iff_monotone_chain_condition]
  intro f
  rcases fg_iff.1 (fg_of_wellQuasiOrderedLE (⨆ i, f i)) with ⟨s, hI⟩
  have hs : ∀ x ∈ s, ∃ i, x ∈ f i := by
    intro x hx
    apply subset_closure (s := (s : Set M)) at hx
    simpa [← hI] using hx
  choose! g hg using hs
  exists s.sup g
  intro n hn
  apply (f.mono hn).antisymm
  apply (le_iSup f n).trans
  intro x hx
  rw [hI, mem_closure''] at hx
  rcases hx with ⟨y, z, hz, rfl⟩
  exact SemigroupIdeal.mul_mem _ _ (f.mono (Finset.le_sup hz) (hg _ hz))

end SemigroupIdeal
