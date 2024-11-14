/-
Copyright (c) 2024 Hannah Fechtner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hannah Fechtner
-/
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.Data.Nat.Dist

/-!
#  Braid Groups

Artin's braid group on infintely many strands

## Main definitions

* `BraidGroupInf ` is the braid group on infinitely many strands, defined as a PresentedGroup
  on the braid relations

## Main results
* will add in as they get PR'd

## Tags
braid group

## TODO
* `braid_group n` is the braid group on n+1 strands (thus n generators)

-/


/-- the set of relations on FreeGroup ℕ corresponding to valid braid moves. generators are indexed
by natural numbers. commutativity holds if the generators are at least 2 apart. if two generators
a and b are adjacent, then aba is congruent to bab -/
def braid_rels_inf : Set (FreeGroup ℕ) :=
  { r | ∃ i j : ℕ , 1 = Nat.dist i j ∧ r = .of i * .of j * .of i *
    (.of j)⁻¹ * (.of i)⁻¹ * (.of j)⁻¹} ∪
  { r | ∃ i j : ℕ, 2 ≤ Nat.dist i j ∧ r = .of i * .of j * (.of i)⁻¹ * (.of j)⁻¹}

/-- Artin's braid group on infinitely many strands -/
def BraidGroupInf := PresentedGroup braid_rels_inf

instance : Group BraidGroupInf := by
  unfold BraidGroupInf; infer_instance

namespace BraidGroupInf

/-- the ith generator of the infinite braid group, whose geometric interpretation is crossing
the ith strand over the (i+1)th strand -/
def σ (k : ℕ) : BraidGroupInf := PresentedGroup.of k

theorem BraidGroupInf.braid {i j : ℕ} (h : 1 = Nat.dist i j): σ i * σ j * σ i =
    σ j * σ i * σ j := by
  symm; rw [← mul_inv_eq_one]
  exact QuotientGroup.eq.mpr <| Subgroup.subset_normalClosure <| Or.inl <| Exists.intro i <|
    Exists.intro j <| ⟨h, rfl⟩

theorem BraidGroupInf.comm {i j : ℕ} (h : 2 ≤ Nat.dist i j) : σ i * σ j = σ j * σ i := by
  symm; rw [← mul_inv_eq_one]
  apply QuotientGroup.eq.mpr
  apply Subgroup.subset_normalClosure
  right
  simp only [mul_inv_rev, inv_inv, mul_one, Set.mem_setOf_eq]
  use i; use j
  exact ⟨h, by simp only [mul_assoc]⟩

section toGroup
variable {G : Type*} [Group G] {f : ℕ → G}

/-- The extension of a map `f : α → G` that satisfies the braid relations to a group homomorphism
from `BraidGroupInf → G`. -/
def toGroup (h : ∀ r ∈ braid_rels_inf, FreeGroup.lift f r = 1) : BraidGroupInf →* G :=
  PresentedGroup.toGroup h

@[simp]
theorem toGroup.of (h : ∀ r ∈ braid_rels_inf, FreeGroup.lift f r = 1) {x : ℕ} :
    toGroup h (σ x) = f x := PresentedGroup.toGroup.of h

theorem toGroup.unique (h : ∀ r ∈ braid_rels_inf, FreeGroup.lift f r = 1) (g : BraidGroupInf →* G)
    (hg : ∀ x : ℕ, g (σ x) = f x) : ∀ {x}, g x = toGroup h x :=
  PresentedGroup.toGroup.unique h g hg

end toGroup
end BraidGroup
