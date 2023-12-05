/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Data.Set.Pointwise.SMul
import Mathlib.Topology.Bornology.Constructions

#align_import analysis.locally_convex.basic from "leanprover-community/mathlib"@"f2ce6086713c78a7f880485f7917ea547a215982"

/-!
# Definitions of `Absorbs` and `Absorbent`

Let `M` act on `α`, let `A` and `B` be sets in `α`.
We say that `A` *absorbs* `B` if for sufficiently large `a : M`, we have `B ⊆ a • A`.
Formally, "for sufficiently large `a : M`" means "for all but a bounded set of `a`".

Traditionally, this definition is formulated
for the action of a (semi)normed ring on a module over that ring.

We formulate it in a more general settings for two reasons:

- this way we don't have to depend on metric spaces, normed rings etc;
- some proofs look nicer with this definition than with something like
  `∃ r : ℝ, ∀ a : R, r ≤ ‖a‖ → B ⊆ a • A`.

-/

open Set Bornology Filter
open scoped Pointwise

assert_not_exists Real

/-- A set `A` absorbs another set `B` if `B` is contained in all scalings of `A`
by all but a bounded set of elements. -/
def Absorbs (M : Type*) {α : Type*} [Bornology M] [SMul M α] (A B : Set α) : Prop :=
  ∀ᶠ a in cobounded M, B ⊆ a • A
#align absorbs Absorbs

namespace Absorbs

section SMul

variable {M α : Type*} [Bornology M] [SMul M α] {s t : Set α}

protected lemma empty : Absorbs M s ∅ := by simp [Absorbs]
#align absorbs_empty Absorbs.empty

protected lemma eventually (h : Absorbs M s t) : ∀ᶠ a in cobounded M, t ⊆ a • s := h

@[simp] lemma of_boundedSpace [BoundedSpace M] : Absorbs M s t := by simp [Absorbs]

lemma mono_left {s'} (h : Absorbs M s t) (hs : s ⊆ s') : Absorbs M s' t :=
  h.mono fun _a ha ↦ ha.trans <| smul_set_mono hs
#align absorbs.mono_left Absorbs.mono_left

lemma mono_right {t'} (h : Absorbs M s t) (ht : t' ⊆ t) : Absorbs M s t' :=
  h.mono fun _ ↦ ht.trans
#align absorbs.mono_right Absorbs.mono_right

lemma mono {s' t'} (h : Absorbs M s t) (hs : s ⊆ s') (ht : t' ⊆ t) : Absorbs M s' t' :=
  (h.mono_left hs).mono_right ht
#align absorbs.mono Absorbs.mono

@[simp]
lemma _root_.absorbs_union {t₁ t₂} : Absorbs M s (t₁ ∪ t₂) ↔ Absorbs M s t₁ ∧ Absorbs M s t₂ := by
  simp [Absorbs]
#align absorbs_union absorbs_union

protected lemma union {t₁ t₂} (h₁ : Absorbs M s t₁) (h₂ : Absorbs M s t₂) : Absorbs M s (t₁ ∪ t₂) :=
  absorbs_union.2 ⟨h₁, h₂⟩
#align absorbs.union Absorbs.union

lemma _root_.Set.Finite.absorbs_sUnion {T : Set (Set α)} (hT : T.Finite) :
    Absorbs M s (⋃₀ T) ↔ ∀ t ∈ T, Absorbs M s t := by
  simp [Absorbs, hT]

protected lemma sUnion {T : Set (Set α)} (hT : T.Finite) (hs : ∀ t ∈ T, Absorbs M s t) :
    Absorbs M s (⋃₀ T) :=
  hT.absorbs_sUnion.2 hs

@[simp]
lemma _root_.absorbs_iUnion {ι : Sort*} [Finite ι] {t : ι → Set α} :
    Absorbs M s (⋃ i, t i) ↔ ∀ i, Absorbs M s (t i) :=
  (finite_range t).absorbs_sUnion.trans forall_range_iff

protected lemma iUnion {ι : Sort*} [Finite ι] {t : ι → Set α} (h : ∀ i, Absorbs M s (t i)) :
    Absorbs M s (⋃ i, t i) :=
  absorbs_iUnion.2 h

lemma _root_.Set.Finite.absorbs_biUnion {ι : Type*} {t : ι → Set α} {I : Set ι} (hI : I.Finite) :
    Absorbs M s (⋃ i ∈ I, t i) ↔ ∀ i ∈ I, Absorbs M s (t i) := by
  simp [Absorbs, hI]
#align set.finite.absorbs_Union Set.Finite.absorbs_biUnion

protected lemma biUnion {ι : Type*} {t : ι → Set α} {I : Set ι} (hI : I.Finite)
    (h : ∀ i ∈ I, Absorbs M s (t i)) : Absorbs M s (⋃ i ∈ I, t i) :=
  hI.absorbs_biUnion.2 h

@[simp]
lemma _root_.absorbs_biUnion_finset {ι : Type*} {t : ι → Set α} {I : Finset ι} :
    Absorbs M s (⋃ i ∈ I, t i) ↔ ∀ i ∈ I, Absorbs M s (t i) :=
  I.finite_toSet.absorbs_biUnion
#align absorbs_Union_finset absorbs_biUnion_finset

protected lemma biUnion_finset {ι : Type*} {t : ι → Set α} {I : Finset ι}
    (h : ∀ i ∈ I, Absorbs M s (t i)) : Absorbs M s (⋃ i ∈ I, t i) :=
  absorbs_biUnion_finset.2 h

end SMul

protected lemma add {M E : Type*} [Bornology M] [AddZeroClass E] [DistribSMul M E]
    {s₁ s₂ t₁ t₂ : Set E} (h₁ : Absorbs M s₁ t₁) (h₂ : Absorbs M s₂ t₂) :
    Absorbs M (s₁ + s₂) (t₁ + t₂) :=
  h₂.mp <| h₁.eventually.mono fun x hx₁ hx₂ ↦ by rw [smul_add]; exact add_subset_add hx₁ hx₂

@[simp]
protected lemma univ {G₀ α : Type*} [GroupWithZero G₀] [Bornology G₀] [MulAction G₀ α]
    {s : Set α} : Absorbs G₀ univ s :=
  (eventually_ne_cobounded 0).mono fun a ha ↦ by rw [smul_set_univ₀ ha]; apply subset_univ

end Absorbs

@[simp]
lemma absorbs_neg_neg {M E : Type*} [Monoid M] [AddGroup E] [DistribMulAction M E] [Bornology M]
    {s t : Set E} : Absorbs M (-s) (-t) ↔ Absorbs M s t := by
  simp [Absorbs]

alias ⟨Absorbs.of_neg_neg, Absorbs.neg_neg⟩ := absorbs_neg_neg
