/-
Copyright (c) 2021 Alena Gusakov, Bhavik Mehta, Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alena Gusakov, Bhavik Mehta, Kyle Miller

! This file was ported from Lean 3 source module combinatorics.hall.basic
! leanprover-community/mathlib commit 8195826f5c428fc283510bc67303dd4472d78498
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Combinatorics.Hall.Finite
import Mathbin.CategoryTheory.CofilteredSystem
import Mathbin.Data.Rel

/-!
# Hall's Marriage Theorem

Given a list of finite subsets $X_1, X_2, \dots, X_n$ of some given set
$S$, P. Hall in [Hall1935] gave a necessary and sufficient condition for
there to be a list of distinct elements $x_1, x_2, \dots, x_n$ with
$x_i\in X_i$ for each $i$: it is when for each $k$, the union of every
$k$ of these subsets has at least $k$ elements.

Rather than a list of finite subsets, one may consider indexed families
`t : ι → finset α` of finite subsets with `ι` a `fintype`, and then the list
of distinct representatives is given by an injective function `f : ι → α`
such that `∀ i, f i ∈ t i`, called a *matching*.
This version is formalized as `finset.all_card_le_bUnion_card_iff_exists_injective'`
in a separate module.

The theorem can be generalized to remove the constraint that `ι` be a `fintype`.
As observed in [Halpern1966], one may use the constrained version of the theorem
in a compactness argument to remove this constraint.
The formulation of compactness we use is that inverse limits of nonempty finite sets
are nonempty (`nonempty_sections_of_finite_inverse_system`), which uses the
Tychonoff theorem.
The core of this module is constructing the inverse system: for every finite subset `ι'` of
`ι`, we can consider the matchings on the restriction of the indexed family `t` to `ι'`.

## Main statements

* `finset.all_card_le_bUnion_card_iff_exists_injective` is in terms of `t : ι → finset α`.
* `fintype.all_card_le_rel_image_card_iff_exists_injective` is in terms of a relation
  `r : α → β → Prop` such that `rel.image r {a}` is a finite set for all `a : α`.
* `fintype.all_card_le_filter_rel_iff_exists_injective` is in terms of a relation
  `r : α → β → Prop` on finite types, with the Hall condition given in terms of
  `finset.univ.filter`.

## Todo

* The statement of the theorem in terms of bipartite graphs is in preparation.

## Tags

Hall's Marriage Theorem, indexed families
-/


open Finset

universe u v

/-- The set of matchings for `t` when restricted to a `finset` of `ι`. -/
def hallMatchingsOn {ι : Type u} {α : Type v} (t : ι → Finset α) (ι' : Finset ι) :=
  { f : ι' → α | Function.Injective f ∧ ∀ x, f x ∈ t x }
#align hall_matchings_on hallMatchingsOn

/-- Given a matching on a finset, construct the restriction of that matching to a subset. -/
def hallMatchingsOn.restrict {ι : Type u} {α : Type v} (t : ι → Finset α) {ι' ι'' : Finset ι}
    (h : ι' ⊆ ι'') (f : hallMatchingsOn t ι'') : hallMatchingsOn t ι' :=
  by
  refine' ⟨fun i => f.val ⟨i, h i.property⟩, _⟩
  cases' f.property with hinj hc
  refine' ⟨_, fun i => hc ⟨i, h i.property⟩⟩
  rintro ⟨i, hi⟩ ⟨j, hj⟩ hh
  simpa only [Subtype.mk_eq_mk] using hinj hh
#align hall_matchings_on.restrict hallMatchingsOn.restrict

/-- When the Hall condition is satisfied, the set of matchings on a finite set is nonempty.
This is where `finset.all_card_le_bUnion_card_iff_exists_injective'` comes into the argument. -/
theorem hallMatchingsOn.nonempty {ι : Type u} {α : Type v} [DecidableEq α] (t : ι → Finset α)
    (h : ∀ s : Finset ι, s.card ≤ (s.biUnion t).card) (ι' : Finset ι) :
    Nonempty (hallMatchingsOn t ι') := by
  classical
    refine' ⟨Classical.indefiniteDescription _ _⟩
    apply (all_card_le_bUnion_card_iff_exists_injective' fun i : ι' => t i).mp
    intro s'
    convert h (s'.image coe) using 1
    simp only [card_image_of_injective s' Subtype.coe_injective]
    rw [image_bUnion]
#align hall_matchings_on.nonempty hallMatchingsOn.nonempty

-- TODO: This takes a long time to elaborate for an unknown reason.
/-- This is the `hall_matchings_on` sets assembled into a directed system.
-/
def hallMatchingsFunctor {ι : Type u} {α : Type v} (t : ι → Finset α) : (Finset ι)ᵒᵖ ⥤ Type max u v
    where
  obj ι' := hallMatchingsOn t ι'.unop
  map ι' ι'' g f := hallMatchingsOn.restrict t (CategoryTheory.leOfHom g.unop) f
#align hall_matchings_functor hallMatchingsFunctor

instance hallMatchingsOn.finite {ι : Type u} {α : Type v} (t : ι → Finset α) (ι' : Finset ι) :
    Finite (hallMatchingsOn t ι') := by
  classical
    rw [hallMatchingsOn]
    let g : hallMatchingsOn t ι' → ι' → ι'.bUnion t :=
      by
      rintro f i
      refine' ⟨f.val i, _⟩
      rw [mem_bUnion]
      exact ⟨i, i.property, f.property.2 i⟩
    apply Finite.of_injective g
    intro f f' h
    simp only [g, Function.funext_iff, Subtype.val_eq_coe] at h
    ext a
    exact h a
#align hall_matchings_on.finite hallMatchingsOn.finite

/-- This is the version of **Hall's Marriage Theorem** in terms of indexed
families of finite sets `t : ι → finset α`.  It states that there is a
set of distinct representatives if and only if every union of `k` of the
sets has at least `k` elements.

Recall that `s.bUnion t` is the union of all the sets `t i` for `i ∈ s`.

This theorem is bootstrapped from `finset.all_card_le_bUnion_card_iff_exists_injective'`,
which has the additional constraint that `ι` is a `fintype`.
-/
theorem Finset.all_card_le_biUnion_card_iff_exists_injective {ι : Type u} {α : Type v}
    [DecidableEq α] (t : ι → Finset α) :
    (∀ s : Finset ι, s.card ≤ (s.biUnion t).card) ↔
      ∃ f : ι → α, Function.Injective f ∧ ∀ x, f x ∈ t x :=
  by
  constructor
  · intro h
    -- Set up the functor
    haveI : ∀ ι' : (Finset ι)ᵒᵖ, Nonempty ((hallMatchingsFunctor t).obj ι') := fun ι' =>
      hallMatchingsOn.nonempty t h ι'.unop
    classical
      haveI : ∀ ι' : (Finset ι)ᵒᵖ, Finite ((hallMatchingsFunctor t).obj ι') :=
        by
        intro ι'
        rw [hallMatchingsFunctor]
        infer_instance
      -- Apply the compactness argument
      obtain ⟨u, hu⟩ := nonempty_sections_of_finite_inverse_system (hallMatchingsFunctor t)
      -- Interpret the resulting section of the inverse limit
      refine' ⟨_, _, _⟩
      ·-- Build the matching function from the section
        exact fun i =>
          (u (Opposite.op ({i} : Finset ι))).val ⟨i, by simp only [Opposite.unop_op, mem_singleton]⟩
      · -- Show that it is injective
        intro i i'
        have subi : ({i} : Finset ι) ⊆ {i, i'} := by simp
        have subi' : ({i'} : Finset ι) ⊆ {i, i'} := by simp
        have le : ∀ {s t : Finset ι}, s ⊆ t → s ≤ t := fun _ _ h => h
        rw [← hu (CategoryTheory.homOfLE (le subi)).op, ← hu (CategoryTheory.homOfLE (le subi')).op]
        let uii' := u (Opposite.op ({i, i'} : Finset ι))
        exact fun h => subtype.mk_eq_mk.mp (uii'.property.1 h)
      · -- Show that it maps each index to the corresponding finite set
        intro i
        apply (u (Opposite.op ({i} : Finset ι))).property.2
  · -- The reverse direction is a straightforward cardinality argument
    rintro ⟨f, hf₁, hf₂⟩ s
    rw [← Finset.card_image_of_injective s hf₁]
    apply Finset.card_le_of_subset
    intro
    rw [Finset.mem_image, Finset.mem_biUnion]
    rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, hf₂ x⟩
#align finset.all_card_le_bUnion_card_iff_exists_injective Finset.all_card_le_biUnion_card_iff_exists_injective

/-- Given a relation such that the image of every singleton set is finite, then the image of every
finite set is finite. -/
instance {α : Type u} {β : Type v} [DecidableEq β] (r : α → β → Prop)
    [∀ a : α, Fintype (Rel.image r {a})] (A : Finset α) : Fintype (Rel.image r A) :=
  by
  have h : Rel.image r A = (A.bUnion fun a => (Rel.image r {a}).toFinset : Set β) :=
    by
    ext
    simp [Rel.image]
  rw [h]
  apply FinsetCoe.fintype

/-- This is a version of **Hall's Marriage Theorem** in terms of a relation
between types `α` and `β` such that `α` is finite and the image of
each `x : α` is finite (it suffices for `β` to be finite; see
`fintype.all_card_le_filter_rel_iff_exists_injective`).  There is
a transversal of the relation (an injective function `α → β` whose graph is
a subrelation of the relation) iff every subset of
`k` terms of `α` is related to at least `k` terms of `β`.

Note: if `[fintype β]`, then there exist instances for `[∀ (a : α), fintype (rel.image r {a})]`.
-/
theorem Fintype.all_card_le_rel_image_card_iff_exists_injective {α : Type u} {β : Type v}
    [DecidableEq β] (r : α → β → Prop) [∀ a : α, Fintype (Rel.image r {a})] :
    (∀ A : Finset α, A.card ≤ Fintype.card (Rel.image r A)) ↔
      ∃ f : α → β, Function.Injective f ∧ ∀ x, r x (f x) :=
  by
  let r' a := (Rel.image r {a}).toFinset
  have h : ∀ A : Finset α, Fintype.card (Rel.image r A) = (A.biUnion r').card :=
    by
    intro A
    rw [← Set.toFinset_card]
    apply congr_arg
    ext b
    simp [Rel.image]
  have h' : ∀ (f : α → β) (x), r x (f x) ↔ f x ∈ r' x := by simp [Rel.image]
  simp only [h, h']
  apply Finset.all_card_le_biUnion_card_iff_exists_injective
#align fintype.all_card_le_rel_image_card_iff_exists_injective Fintype.all_card_le_rel_image_card_iff_exists_injective

-- TODO: decidable_pred makes Yael sad. When an appropriate decidable_rel-like exists, fix it.
/-- This is a version of **Hall's Marriage Theorem** in terms of a relation to a finite type.
There is a transversal of the relation (an injective function `α → β` whose graph is a subrelation
of the relation) iff every subset of `k` terms of `α` is related to at least `k` terms of `β`.

It is like `fintype.all_card_le_rel_image_card_iff_exists_injective` but uses `finset.filter`
rather than `rel.image`.
-/
theorem Fintype.all_card_le_filter_rel_iff_exists_injective {α : Type u} {β : Type v} [Fintype β]
    (r : α → β → Prop) [∀ a, DecidablePred (r a)] :
    (∀ A : Finset α, A.card ≤ (univ.filterₓ fun b : β => ∃ a ∈ A, r a b).card) ↔
      ∃ f : α → β, Function.Injective f ∧ ∀ x, r x (f x) :=
  by
  haveI := Classical.decEq β
  let r' a := univ.filter fun b => r a b
  have h : ∀ A : Finset α, (univ.filter fun b : β => ∃ a ∈ A, r a b) = A.biUnion r' :=
    by
    intro A
    ext b
    simp
  have h' : ∀ (f : α → β) (x), r x (f x) ↔ f x ∈ r' x := by simp
  simp_rw [h, h']
  apply Finset.all_card_le_biUnion_card_iff_exists_injective
#align fintype.all_card_le_filter_rel_iff_exists_injective Fintype.all_card_le_filter_rel_iff_exists_injective

