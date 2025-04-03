/-
Copyright (c) 2020 Jean Lo, Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean Lo, Yury Kudryashov
-/
import Mathlib.Data.Set.Pointwise.SMul
import Mathlib.Topology.Bornology.Basic

#align_import analysis.locally_convex.basic from "leanprover-community/mathlib"@"f2ce6086713c78a7f880485f7917ea547a215982"

/-!
# Absorption of sets

Let `M` act on `α`, let `A` and `B` be sets in `α`.
We say that `A` *absorbs* `B` if for sufficiently large `a : M`, we have `B ⊆ a • A`.
Formally, "for sufficiently large `a : M`" means "for all but a bounded set of `a`".

Traditionally, this definition is formulated
for the action of a (semi)normed ring on a module over that ring.

We formulate it in a more general settings for two reasons:

- this way we don't have to depend on metric spaces, normed rings etc;
- some proofs look nicer with this definition than with something like
  `∃ r : ℝ, ∀ a : R, r ≤ ‖a‖ → B ⊆ a • A`.

## Implementation notes

For now, all theorems assume that we deal with (a generalization of) a module over a division ring.
Some lemmas have multiplicative versions for `MulDistribMulAction`s.
They can be added later when someone needs them.

## Keywords

absorbs, absorbent
-/

open Set Bornology Filter
open scoped Pointwise

assert_not_exists Real

section Defs

variable (M : Type*) {α : Type*} [Bornology M] [SMul M α]

/-- A set `s` absorbs another set `t` if `t` is contained in all scalings of `s`
by all but a bounded set of elements. -/
def Absorbs (s t : Set α) : Prop :=
  ∀ᶠ a in cobounded M, t ⊆ a • s
#align absorbs Absorbs

/-- A set is *absorbent* if it absorbs every singleton. -/
def Absorbent (s : Set α) : Prop :=
  ∀ x, Absorbs M s {x}
#align absorbent Absorbent

end Defs

namespace Absorbs

section SMul

variable {M α : Type*} [Bornology M] [SMul M α] {s s₁ s₂ t t₁ t₂ : Set α} {S T : Set (Set α)}

protected lemma empty : Absorbs M s ∅ := by simp [Absorbs]
#align absorbs_empty Absorbs.empty

@[deprecated (since := "2024-01-16")]
alias _root_.absorbs_empty := Absorbs.empty

protected lemma eventually (h : Absorbs M s t) : ∀ᶠ a in cobounded M, t ⊆ a • s := h

@[simp] lemma of_boundedSpace [BoundedSpace M] : Absorbs M s t := by simp [Absorbs]

lemma mono_left (h : Absorbs M s₁ t) (hs : s₁ ⊆ s₂) : Absorbs M s₂ t :=
  h.mono fun _a ha ↦ ha.trans <| smul_set_mono hs
#align absorbs.mono_left Absorbs.mono_left

lemma mono_right (h : Absorbs M s t₁) (ht : t₂ ⊆ t₁) : Absorbs M s t₂ :=
  h.mono fun _ ↦ ht.trans
#align absorbs.mono_right Absorbs.mono_right

lemma mono (h : Absorbs M s₁ t₁) (hs : s₁ ⊆ s₂) (ht : t₂ ⊆ t₁) : Absorbs M s₂ t₂ :=
  (h.mono_left hs).mono_right ht
#align absorbs.mono Absorbs.mono

@[simp]
lemma _root_.absorbs_union : Absorbs M s (t₁ ∪ t₂) ↔ Absorbs M s t₁ ∧ Absorbs M s t₂ := by
  simp [Absorbs]
#align absorbs_union absorbs_union

protected lemma union (h₁ : Absorbs M s t₁) (h₂ : Absorbs M s t₂) : Absorbs M s (t₁ ∪ t₂) :=
  absorbs_union.2 ⟨h₁, h₂⟩
#align absorbs.union Absorbs.union

lemma _root_.Set.Finite.absorbs_sUnion {T : Set (Set α)} (hT : T.Finite) :
    Absorbs M s (⋃₀ T) ↔ ∀ t ∈ T, Absorbs M s t := by
  simp [Absorbs, hT]

protected lemma sUnion (hT : T.Finite) (hs : ∀ t ∈ T, Absorbs M s t) :
    Absorbs M s (⋃₀ T) :=
  hT.absorbs_sUnion.2 hs

@[simp]
lemma _root_.absorbs_iUnion {ι : Sort*} [Finite ι] {t : ι → Set α} :
    Absorbs M s (⋃ i, t i) ↔ ∀ i, Absorbs M s (t i) :=
  (finite_range t).absorbs_sUnion.trans forall_mem_range

protected alias ⟨_, iUnion⟩ := absorbs_iUnion

lemma _root_.Set.Finite.absorbs_biUnion {ι : Type*} {t : ι → Set α} {I : Set ι} (hI : I.Finite) :
    Absorbs M s (⋃ i ∈ I, t i) ↔ ∀ i ∈ I, Absorbs M s (t i) := by
  simp [Absorbs, hI]
#align set.finite.absorbs_Union Set.Finite.absorbs_biUnion

protected alias ⟨_, biUnion⟩ := Set.Finite.absorbs_biUnion

@[deprecated (since := "2024-01-16")]
alias _root_.Set.Finite.absorbs_iUnion := Set.Finite.absorbs_biUnion

@[simp]
lemma _root_.absorbs_biUnion_finset {ι : Type*} {t : ι → Set α} {I : Finset ι} :
    Absorbs M s (⋃ i ∈ I, t i) ↔ ∀ i ∈ I, Absorbs M s (t i) :=
  I.finite_toSet.absorbs_biUnion
#align absorbs_Union_finset absorbs_biUnion_finset

protected alias ⟨_, biUnion_finset⟩ := absorbs_biUnion_finset

@[deprecated (since := "2024-01-16")]
alias _root_.absorbs_iUnion_finset := absorbs_biUnion_finset

end SMul

section AddZero

variable {M E : Type*} [Bornology M] {s₁ s₂ t₁ t₂ : Set E}

protected lemma add [AddZeroClass E] [DistribSMul M E]
    (h₁ : Absorbs M s₁ t₁) (h₂ : Absorbs M s₂ t₂) : Absorbs M (s₁ + s₂) (t₁ + t₂) :=
  h₂.mp <| h₁.eventually.mono fun x hx₁ hx₂ ↦ by rw [smul_add]; exact add_subset_add hx₁ hx₂
#align absorbs.add Absorbs.add

protected lemma zero [Zero E] [SMulZeroClass M E] {s : Set E} (hs : 0 ∈ s) : Absorbs M s 0 :=
  eventually_of_forall fun _ ↦ zero_subset.2 <| zero_mem_smul_set hs

end AddZero

section GroupWithZero

variable {G₀ α : Type*} [GroupWithZero G₀] [Bornology G₀] [MulAction G₀ α]
  {s t u : Set α} {S : Set (Set α)}

@[simp]
protected lemma univ : Absorbs G₀ univ s :=
  (eventually_ne_cobounded 0).mono fun a ha ↦ by rw [smul_set_univ₀ ha]; apply subset_univ

lemma _root_.absorbs_iff_eventually_cobounded_mapsTo :
    Absorbs G₀ s t ↔ ∀ᶠ c in cobounded G₀, MapsTo (c⁻¹ • ·) t s :=
  eventually_congr <| (eventually_ne_cobounded 0).mono fun c hc ↦ by
    rw [← preimage_smul_inv₀ hc]; rfl

alias ⟨eventually_cobounded_mapsTo, _⟩ := absorbs_iff_eventually_cobounded_mapsTo

lemma _root_.Set.Finite.absorbs_sInter (hS : S.Finite) :
    Absorbs G₀ (⋂₀ S) t ↔ ∀ s ∈ S, Absorbs G₀ s t := by
  simp only [absorbs_iff_eventually_cobounded_mapsTo, mapsTo_sInter, hS.eventually_all]

protected alias ⟨_, sInter⟩ := Set.Finite.absorbs_sInter

@[simp]
lemma _root_.absorbs_inter : Absorbs G₀ (s ∩ t) u ↔ Absorbs G₀ s u ∧ Absorbs G₀ t u := by
  simpa using ((finite_singleton t).insert s).absorbs_sInter
#align absorbs_inter absorbs_inter

protected lemma inter (hs : Absorbs G₀ s u) (ht : Absorbs G₀ t u) : Absorbs G₀ (s ∩ t) u :=
  absorbs_inter.2 ⟨hs, ht⟩
#align absorbs.inter Absorbs.inter

@[simp]
lemma _root_.absorbs_iInter {ι : Sort*} [Finite ι] {s : ι → Set α} :
    Absorbs G₀ (⋂ i, s i) t ↔ ∀ i, Absorbs G₀ (s i) t :=
  (finite_range s).absorbs_sInter.trans forall_mem_range

protected alias ⟨_, iInter⟩ := absorbs_iInter

lemma _root_.Set.Finite.absorbs_biInter {ι : Type*} {I : Set ι} (hI : I.Finite) {s : ι → Set α} :
    Absorbs G₀ (⋂ i ∈ I, s i) t ↔ ∀ i ∈ I, Absorbs G₀ (s i) t := by
  simpa only [sInter_image, forall_mem_image] using (hI.image s).absorbs_sInter

protected alias ⟨_, biInter⟩ := Set.Finite.absorbs_biInter

@[simp]
lemma _root_.absorbs_zero_iff [NeBot (cobounded G₀)] {E : Type*} [AddMonoid E]
    [DistribMulAction G₀ E] {s : Set E} : Absorbs G₀ s 0 ↔ 0 ∈ s := by
  simp only [absorbs_iff_eventually_cobounded_mapsTo, ← singleton_zero,
    mapsTo_singleton, smul_zero, eventually_const]
#align absorbs_zero_iff absorbs_zero_iff

end GroupWithZero

end Absorbs

section AddGroup

variable {M E : Type*} [Monoid M] [AddGroup E] [DistribMulAction M E] [Bornology M]

@[simp]
lemma absorbs_neg_neg {s t : Set E} : Absorbs M (-s) (-t) ↔ Absorbs M s t := by simp [Absorbs]

alias ⟨Absorbs.of_neg_neg, Absorbs.neg_neg⟩ := absorbs_neg_neg
#align absorbs.neg Absorbs.neg_neg

lemma Absorbs.sub {s₁ s₂ t₁ t₂ : Set E} (h₁ : Absorbs M s₁ t₁) (h₂ : Absorbs M s₂ t₂) :
    Absorbs M (s₁ - s₂) (t₁ - t₂) := by
  simpa only [sub_eq_add_neg] using h₁.add h₂.neg_neg
#align absorbs.sub Absorbs.sub

end AddGroup

namespace Absorbent

section SMul

variable {M α : Type*} [Bornology M] [SMul M α] {s t : Set α}

protected theorem mono (ht : Absorbent M s) (hsub : s ⊆ t) : Absorbent M t := fun x ↦
  (ht x).mono_left hsub
#align absorbent.subset Absorbent.mono

@[deprecated (since := "2024-01-16")]
protected alias subset := Absorbent.mono

theorem _root_.absorbent_iff_forall_absorbs_singleton : Absorbent M s ↔ ∀ x, Absorbs M s {x} := .rfl
#align absorbent_iff_forall_absorbs_singleton absorbent_iff_forall_absorbs_singleton

protected theorem absorbs (hs : Absorbent M s) {x : α} : Absorbs M s {x} := hs x
#align absorbent.absorbs Absorbent.absorbs

#noalign absorbent_iff_nonneg_lt

theorem absorbs_finite (hs : Absorbent M s) (ht : t.Finite) : Absorbs M s t := by
  rw [← Set.biUnion_of_singleton t]
  exact .biUnion ht fun _ _ => hs.absorbs
#align absorbent.absorbs_finite Absorbent.absorbs_finite

end SMul

theorem vadd_absorbs {M E : Type*} [Bornology M] [AddZeroClass E] [DistribSMul M E]
    {s₁ s₂ t : Set E} {x : E} (h₁ : Absorbent M s₁) (h₂ : Absorbs M s₂ t) :
    Absorbs M (s₁ + s₂) (x +ᵥ t) := by
  rw [← singleton_vadd]; exact (h₁ x).add h₂

end Absorbent

section GroupWithZero

variable {G₀ α E : Type*} [GroupWithZero G₀] [Bornology G₀] [MulAction G₀ α]

lemma absorbent_univ : Absorbent G₀ (univ : Set α) := fun _ ↦ .univ
#align absorbent_univ absorbent_univ

lemma absorbent_iff_inv_smul {s : Set α} :
    Absorbent G₀ s ↔ ∀ x, ∀ᶠ c in cobounded G₀, c⁻¹ • x ∈ s :=
  forall_congr' fun x ↦ by simp only [absorbs_iff_eventually_cobounded_mapsTo, mapsTo_singleton]

lemma Absorbent.zero_mem [NeBot (cobounded G₀)] [AddMonoid E] [DistribMulAction G₀ E]
    {s : Set E} (hs : Absorbent G₀ s) : (0 : E) ∈ s :=
  absorbs_zero_iff.1 (hs 0)
#align absorbent.zero_mem Absorbent.zero_mem
