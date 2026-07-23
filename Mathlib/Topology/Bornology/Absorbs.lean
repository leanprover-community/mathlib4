/-
Copyright (c) 2020 Jean Lo, Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean Lo, Yury Kudryashov
-/
module

public import Mathlib.Algebra.GroupWithZero.Action.Pointwise.Set
public import Mathlib.Algebra.Ring.Action.Pointwise.Set
public import Mathlib.Topology.Algebra.Module.Basic

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

If `M` is a `GroupWithZero` (e.g., a division ring),
the sets absorbing a given set form a filter, see `Filter.absorbing`.

## Implementation notes

For now, all theorems assume that we deal with (a generalization of) a module over a division ring.
Some lemmas have multiplicative versions for `MulDistribMulAction`s.
They can be added later when someone needs them.

## Keywords

absorbs, absorbent
-/

@[expose] public section

assert_not_exists Real

open Set Bornology Filter
open scoped Pointwise Topology

section Defs

variable (M : Type*) {α : Type*} [Zero M] [SMul M α] [TopologicalSpace M]

/-- A set `s` absorbs another set `t` if `t` is contained in all scalings of `s`
by all but a bounded set of elements. -/
def Absorbs (s t : Set α) : Prop :=
  ∀ᶠ a in 𝓝[≠] (0 : M), MapsTo (a • ·) t s

/-- A set is *absorbent* if it absorbs every singleton. -/
def Absorbent (s : Set α) : Prop :=
  ∀ x, Absorbs M s {x}

end Defs

namespace Absorbs

section SMul

variable {M α : Type*} [TopologicalSpace M] [Zero M] [SMul M α] {s s₁ s₂ t t₁ t₂ : Set α}
  {S T : Set (Set α)}

protected lemma empty : Absorbs M s ∅ := by simp [Absorbs, mapsTo_empty]

theorem _root_.absorbs_iff_eventually_nhdsNE_zero :
    Absorbs M s t ↔ ∀ᶠ c : M in 𝓝[≠] 0, MapsTo (c • ·) t s := .rfl

protected alias ⟨eventually_nhdsNE_zero, _⟩ := absorbs_iff_eventually_nhdsNE_zero

protected alias eventually := Absorbs.eventually_nhdsNE_zero

-- TODO: deprecation
--@[simp] lemma of_boundedSpace [BoundedSpace M] : Absorbs M s t := by simp [Absorbs]

@[simp] lemma of_discreteTopology [DiscreteTopology M] : Absorbs M s t := by
  -- Should exist somewhere
  have : 𝓝[≠] (0 : M) = ⊥ := by simp_rw [nhdsWithin, nhds_discrete, ← principal_singleton,
    inf_principal, inter_compl_self, principal_empty]
  simp [Absorbs, this]

lemma mono_left (h : Absorbs M s₁ t) (hs : s₁ ⊆ s₂) : Absorbs M s₂ t :=
  h.mono fun _a ha ↦ ha.mono_right hs

lemma mono_right (h : Absorbs M s t₁) (ht : t₂ ⊆ t₁) : Absorbs M s t₂ :=
  h.mono fun _a ha ↦ ha.mono_left ht

lemma mono (h : Absorbs M s₁ t₁) (hs : s₁ ⊆ s₂) (ht : t₂ ⊆ t₁) : Absorbs M s₂ t₂ :=
  (h.mono_left hs).mono_right ht

@[simp]
lemma _root_.absorbs_union : Absorbs M s (t₁ ∪ t₂) ↔ Absorbs M s t₁ ∧ Absorbs M s t₂ := by
  simp [Absorbs]

protected lemma union (h₁ : Absorbs M s t₁) (h₂ : Absorbs M s t₂) : Absorbs M s (t₁ ∪ t₂) :=
  absorbs_union.2 ⟨h₁, h₂⟩

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

protected alias ⟨_, biUnion⟩ := Set.Finite.absorbs_biUnion

@[simp]
lemma _root_.absorbs_biUnion_finset {ι : Type*} {t : ι → Set α} {I : Finset ι} :
    Absorbs M s (⋃ i ∈ I, t i) ↔ ∀ i ∈ I, Absorbs M s (t i) :=
  I.finite_toSet.absorbs_biUnion

protected alias ⟨_, biUnion_finset⟩ := absorbs_biUnion_finset

@[simp]
protected lemma univ : Absorbs M univ s := by
  simp [Absorbs]

@[simp]
lemma _root_.absorbs_inter : Absorbs M (s₁ ∩ s₂) t ↔ Absorbs M s₁ t ∧ Absorbs M s₂ t := by
  simp [Absorbs]

protected lemma inter (hs : Absorbs M s₁ t) (ht : Absorbs M s₂ t) : Absorbs M (s₁ ∩ s₂) t :=
  absorbs_inter.2 ⟨hs, ht⟩

variable (M t) in
/-- The filter of sets that absorb `u`. -/
def _root_.Filter.absorbing : Filter α where
  sets := {s | Absorbs M s t}
  univ_sets := .univ
  sets_of_superset h := h.mono_left
  inter_sets := .inter

@[simp]
lemma _root_.Filter.mem_absorbing : s ∈ absorbing M t ↔ Absorbs M s t := .rfl

lemma _root_.Set.Finite.absorbs_sInter (hS : S.Finite) :
    Absorbs M (⋂₀ S) t ↔ ∀ s ∈ S, Absorbs M s t :=
  sInter_mem (f := absorbing M t) hS

protected alias ⟨_, sInter⟩ := Set.Finite.absorbs_sInter

@[simp]
lemma _root_.absorbs_iInter {ι : Sort*} [Finite ι] {s : ι → Set α} :
    Absorbs M (⋂ i, s i) t ↔ ∀ i, Absorbs M (s i) t :=
  iInter_mem (f := absorbing M t)

protected alias ⟨_, iInter⟩ := absorbs_iInter

lemma _root_.Set.Finite.absorbs_biInter {ι : Type*} {I : Set ι} (hI : I.Finite) {s : ι → Set α} :
    Absorbs M (⋂ i ∈ I, s i) t ↔ ∀ i ∈ I, Absorbs M (s i) t :=
  biInter_mem (f := absorbing M t) hI

protected alias ⟨_, biInter⟩ := Set.Finite.absorbs_biInter

end SMul

section AddZeroNeg

variable {M E : Type*} [TopologicalSpace M] [Zero M] {s t s₁ s₂ t₁ t₂ : Set E}

theorem _root_.absorbs_iff_eventually_nhds_zero [Zero E] [SMulWithZero M E] (h₀ : 0 ∈ s) :
    Absorbs M s t ↔ ∀ᶠ c : M in 𝓝 0, MapsTo (c • ·) t s := by
  rw [← nhdsNE_sup_pure, eventually_sup, eventually_pure,
    ← absorbs_iff_eventually_nhdsNE_zero, and_iff_left]
  intro x _
  simpa only [zero_smul]

theorem eventually_nhds_zero [Zero E] [SMulWithZero M E] (h : Absorbs M s t) (h₀ : 0 ∈ s) :
    ∀ᶠ c : M in 𝓝 0, MapsTo (c • ·) t s :=
  (absorbs_iff_eventually_nhds_zero h₀).1 h

protected lemma add [AddZeroClass E] [DistribSMul M E]
    (h₁ : Absorbs M s₁ t₁) (h₂ : Absorbs M s₂ t₂) : Absorbs M (s₁ + s₂) (t₁ + t₂) :=
  h₂.mp <| h₁.eventually.mono fun x hx₁ hx₂ ↦ by
    simp_rw [mapsTo_iff_image_subset, image_smul, smul_add] at hx₁ hx₂ ⊢
    exact add_subset_add hx₁ hx₂

protected lemma zero [Zero E] [SMulZeroClass M E] {s : Set E} (hs : 0 ∈ s) : Absorbs M s 0 :=
  Eventually.of_forall fun _ ↦ by simp [mapsTo_iff_image_subset, hs]

@[simp]
lemma _root_.absorbs_zero_iff [NeBot (𝓝[≠] (0 : M))] [Zero E] [SMulZeroClass M E] {s : Set E} :
    Absorbs M s 0 ↔ 0 ∈ s := by
  simp [Absorbs, mapsTo_iff_image_subset]

@[simp]
lemma _root_.absorbs_neg_neg [AddGroup E] [DistribSMul M E] :
    Absorbs M (-s) (-t) ↔ Absorbs M s t := by
  simp [Absorbs, mapsTo_iff_image_subset]

alias ⟨of_neg_neg, neg_neg⟩ := absorbs_neg_neg

protected lemma sub [AddGroup E] [DistribSMul M E]
    (h₁ : Absorbs M s₁ t₁) (h₂ : Absorbs M s₂ t₂) : Absorbs M (s₁ - s₂) (t₁ - t₂) := by
  simpa only [sub_eq_add_neg] using h₁.add h₂.neg_neg

end AddZeroNeg

protected theorem restrict_scalars
    {M N α : Type*} [Zero M] [Zero N] [Monoid N] [SMul M N] [SMul M α] [MulAction N α]
    [IsScalarTower M N α] [TopologicalSpace M] [TopologicalSpace N]
    {s t : Set α} (h : Absorbs N s t) (h_tendsto : Tendsto (· • 1 : M → N) (𝓝[≠] 0) (𝓝[≠] 0)) :
    Absorbs M s t :=
  (h_tendsto.eventually h).mono <| fun x hx ↦ by simpa using hx

end Absorbs

section GroupWithZero

variable {G₀ α : Type*} [GroupWithZero G₀] [TopologicalSpace G₀] [MulAction G₀ α]
  {s t u : Set α} {S : Set (Set α)}

-- lemma absorbs_iff_eventually_cobounded_mapsTo :
--     Absorbs G₀ s t ↔ ∀ᶠ c in cobounded G₀, MapsTo (c⁻¹ • ·) t s :=
--   eventually_congr <| (eventually_ne_cobounded 0).mono fun c hc ↦ by
--     rw [← preimage_smul_inv₀ hc]; rfl

-- alias ⟨eventually_cobounded_mapsTo, _⟩ := absorbs_iff_eventually_cobounded_mapsTo

end GroupWithZero

namespace Absorbent

section SMul

variable {M α : Type*} [Zero M] [SMul M α] [TopologicalSpace M] {s t : Set α}

theorem _root_.absorbent_iff_eventually_nhdsNE_zero :
    Absorbent M s ↔ ∀ x : α, ∀ᶠ c : M in 𝓝[≠] 0, c • x ∈ s :=
  forall_congr' fun x ↦ by simp only [absorbs_iff_eventually_nhdsNE_zero, mapsTo_singleton]

alias ⟨eventually_nhdsNE_zero, _⟩ := absorbent_iff_eventually_nhdsNE_zero

protected theorem mono (ht : Absorbent M s) (hsub : s ⊆ t) : Absorbent M t := fun x ↦
  (ht x).mono_left hsub

theorem _root_.absorbent_iff_forall_absorbs_singleton : Absorbent M s ↔ ∀ x, Absorbs M s {x} := .rfl

protected theorem absorbs (hs : Absorbent M s) {x : α} : Absorbs M s {x} := hs x

theorem absorbs_finite (hs : Absorbent M s) (ht : t.Finite) : Absorbs M s t := by
  rw [← Set.biUnion_of_singleton t]
  exact .biUnion ht fun _ _ => hs.absorbs

lemma _root_.absorbent_univ : Absorbent M (univ : Set α) := fun _ ↦ .univ

end SMul

section AddZeroNeg

variable {M E : Type*} [TopologicalSpace M] [Zero M] {s t s₁ s₂ t₁ t₂ : Set E}

lemma zero_mem [NeBot (𝓝[≠] (0 : M))] [Zero E] [SMulZeroClass M E]
    {s : Set E} (hs : Absorbent M s) : (0 : E) ∈ s :=
  absorbs_zero_iff.1 (hs 0)

theorem vadd_absorbs [AddZeroClass E] [DistribSMul M E]
    {s₁ s₂ t : Set E} {x : E} (h₁ : Absorbent M s₁) (h₂ : Absorbs M s₂ t) :
    Absorbs M (s₁ + s₂) (x +ᵥ t) := by
  rw [← singleton_vadd]; exact (h₁ x).add h₂

/-- Every neighbourhood of the origin is absorbent. -/
theorem _root_.absorbent_nhds_zero [Zero E] [SMulWithZero M E] [TopologicalSpace E]
    [ContinuousSMul M E] (hs : s ∈ 𝓝 (0 : E)) :
    Absorbent M s := by
  rw [absorbent_iff_eventually_nhdsNE_zero]
  intro x
  have : Tendsto (· • x) (𝓝 (0 : M)) (𝓝 0) :=
    continuous_id.smul continuous_const |>.tendsto' _ _ (zero_smul _ _)
  exact this.mono_left nhdsWithin_le_nhds hs

end AddZeroNeg

end Absorbent

section GroupWithZero

variable {G₀ α E : Type*} [GroupWithZero G₀] [Bornology G₀] [MulAction G₀ α]

-- lemma absorbent_iff_inv_smul {s : Set α} :
--     Absorbent G₀ s ↔ ∀ x, ∀ᶠ c in cobounded G₀, c⁻¹ • x ∈ s :=
--   forall_congr' fun x ↦ by simp only [absorbs_iff_eventually_cobounded_mapsTo, mapsTo_singleton]
--

end GroupWithZero
