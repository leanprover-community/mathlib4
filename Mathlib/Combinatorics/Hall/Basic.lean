/-
Copyright (c) 2021 Alena Gusakov, Bhavik Mehta, Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alena Gusakov, Bhavik Mehta, Kyle Miller
-/
module

public import Mathlib.Combinatorics.Hall.Finite
public import Mathlib.CategoryTheory.CofilteredSystem
public import Mathlib.Data.Rel

/-!
# Hall's Marriage Theorem

Given a list of finite subsets $X_1, X_2, \dots, X_n$ of some given set
$S$, P. Hall in [Hall1935] gave a necessary and sufficient condition for
there to be a list of distinct elements $x_1, x_2, \dots, x_n$ with
$x_i\in X_i$ for each $i$: it is when for each $k$, the union of every
$k$ of these subsets has at least $k$ elements.

Rather than a list of finite subsets, one may consider indexed families
`t : ι → Finset α` of finite subsets with `ι` a `Fintype`, and then the list
of distinct representatives is given by an injective function `f : ι → α`
such that `∀ i, f i ∈ t i`, called a *matching*.
This version is formalized as `Finset.all_card_le_biUnion_card_iff_exists_injective'`
in a separate module.

The theorem can be generalized to remove the constraint that `ι` be a `Fintype`.
As observed in [Halpern1966], one may use the constrained version of the theorem
in a compactness argument to remove this constraint.
The formulation of compactness we use is that inverse limits of nonempty finite sets
are nonempty (`nonempty_sections_of_finite_inverse_system`), which uses the
Tychonoff theorem.
The core of this module is constructing the inverse system: for every finite subset `ι'` of
`ι`, we can consider the matchings on the restriction of the indexed family `t` to `ι'`.

## Main statements

* `Finset.all_card_le_biUnion_card_iff_exists_injective` is in terms of `t : ι → Finset α`.
* `Fintype.all_card_le_rel_image_card_iff_exists_injective` is in terms of a relation
  `r : α → β → Prop` such that `R.image {a}` is a finite set for all `a : α`.
* `Fintype.all_card_le_filter_rel_iff_exists_injective` is in terms of a relation
  `r : α → β → Prop` on finite types, with the Hall condition given in terms of
  `finset.univ.filter`.

## Tags

Hall's Marriage Theorem, indexed families
-/

@[expose] public section

open Finset Function CategoryTheory
open scoped SetRel

universe u v

/-- The set of matchings for `t` when restricted to a `Finset` of `ι`. -/
def hallMatchingsOn {ι : Type u} {α : Type v} (t : ι → Finset α) (ι' : Finset ι) :=
  { f : ι' → α | Function.Injective f ∧ ∀ (x : {x // x ∈ ι'}), f x ∈ t x }

/-- Given a matching on a finset, construct the restriction of that matching to a subset. -/
def hallMatchingsOn.restrict {ι : Type u} {α : Type v} (t : ι → Finset α) {ι' ι'' : Finset ι}
    (h : ι' ⊆ ι'') (f : hallMatchingsOn t ι'') : hallMatchingsOn t ι' := by
  refine ⟨fun i => f.val ⟨i, h i.property⟩, ?_⟩
  obtain ⟨hinj, hc⟩ := f.property
  refine ⟨?_, fun i => hc ⟨i, h i.property⟩⟩
  rintro ⟨i, hi⟩ ⟨j, hj⟩ hh
  simpa only [Subtype.mk_eq_mk] using hinj hh

/-- When the Hall condition is satisfied, the set of matchings on a finite set is nonempty.
This is where `Finset.all_card_le_biUnion_card_iff_existsInjective'` comes into the argument. -/
theorem hallMatchingsOn.nonempty {ι : Type u} {α : Type v} [DecidableEq α] (t : ι → Finset α)
    (h : ∀ s : Finset ι, #s ≤ #(s.biUnion t)) (ι' : Finset ι) :
    Nonempty (hallMatchingsOn t ι') := by
  classical
    refine ⟨Classical.indefiniteDescription _ ?_⟩
    apply (all_card_le_biUnion_card_iff_existsInjective' fun i : ι' => t i).mp
    intro s'
    convert h (s'.image (↑)) using 1
    · simp only [card_image_of_injective s' Subtype.coe_injective]
    · rw [image_biUnion]

/-- This is the `hallMatchingsOn` sets assembled into a directed system.
-/
def hallMatchingsFunctor {ι : Type u} {α : Type v} (t : ι → Finset α) :
    (Finset ι)ᵒᵖ ⥤ Type (max u v) where
  obj ι' := <| hallMatchingsOn t ι'.unop
  map {_ _} g := TypeCat.ofHom ⟨hallMatchingsOn.restrict t (CategoryTheory.leOfHom g.unop)⟩

instance hallMatchingsOn.finite {ι : Type u} {α : Type v} (t : ι → Finset α) (ι' : Finset ι) :
    Finite (hallMatchingsOn t ι') := by
  classical
    rw [hallMatchingsOn]
    let g : hallMatchingsOn t ι' → ι' → ι'.biUnion t := by
      rintro f i
      refine ⟨f.val i, ?_⟩
      rw [mem_biUnion]
      exact ⟨i, i.property, f.property.2 i⟩
    apply Finite.of_injective g
    intro f f' h
    ext a
    rw [funext_iff] at h
    simpa [g] using h a

/-- This is the version of **Hall's Marriage Theorem** in terms of indexed
families of finite sets `t : ι → Finset α`.  It states that there is a
set of distinct representatives if and only if every union of `k` of the
sets has at least `k` elements.

Recall that `s.biUnion t` is the union of all the sets `t i` for `i ∈ s`.

This theorem is bootstrapped from `Finset.all_card_le_biUnion_card_iff_exists_injective'`,
which has the additional constraint that `ι` is a `Fintype`.
-/
theorem Finset.all_card_le_biUnion_card_iff_exists_injective {ι : Type u} {α : Type v}
    [DecidableEq α] (t : ι → Finset α) :
    (∀ s : Finset ι, #s ≤ #(s.biUnion t)) ↔
      ∃ f : ι → α, Function.Injective f ∧ ∀ x, f x ∈ t x := by
  constructor
  · intro h
    -- Set up the functor
    haveI : ∀ ι' : (Finset ι)ᵒᵖ, Nonempty ((hallMatchingsFunctor t).obj ι') := fun ι' =>
      hallMatchingsOn.nonempty t h ι'.unop
    classical
      haveI : ∀ ι' : (Finset ι)ᵒᵖ, Finite ((hallMatchingsFunctor t).obj ι') := by
        intro ι'
        rw [hallMatchingsFunctor]
        infer_instance
      -- Apply the compactness argument
      obtain ⟨u, hu⟩ := nonempty_sections_of_finite_inverse_system (hallMatchingsFunctor t)
      -- Interpret the resulting section of the inverse limit
      refine ⟨?_, ?_, ?_⟩
      · -- Build the matching function from the section
        exact fun i =>
          (u (Opposite.op ({i} : Finset ι))).val ⟨i, by simp only [mem_singleton]⟩
      · -- Show that it is injective
        intro i i'
        have subi : ({i} : Finset ι) ⊆ {i, i'} := by simp
        have subi' : ({i'} : Finset ι) ⊆ {i, i'} := by simp
        rw [← Finset.le_iff_subset] at subi subi'
        simp only
        rw [← hu (CategoryTheory.homOfLE subi).op, ← hu (CategoryTheory.homOfLE subi').op]
        let uii' := u (Opposite.op ({i, i'} : Finset ι))
        exact fun h => Subtype.mk_eq_mk.mp (uii'.property.1 h)
      · -- Show that it maps each index to the corresponding finite set
        intro i
        apply (u (Opposite.op ({i} : Finset ι))).property.2
  · -- The reverse direction is a straightforward cardinality argument
    rintro ⟨f, hf₁, hf₂⟩ s
    rw [← Finset.card_image_of_injective s hf₁]
    apply Finset.card_le_card
    grind

/-- Given a relation such that the image of every singleton set is finite, then the image of every
finite set is finite. -/
instance {α : Type u} {β : Type v} [DecidableEq β] (R : SetRel α β)
    [∀ a : α, Fintype (R.image {a})] (A : Finset α) : Fintype (R.image A) := by
  have h : R.image A = (A.biUnion fun a => (R.image {a}).toFinset : Set β) := by
    ext
    simp [SetRel.image]
  rw [h]
  apply FinsetCoe.fintype

/-- This is a version of **Hall's Marriage Theorem** in terms of a relation
between types `α` and `β` such that `α` is finite and the image of
each `x : α` is finite (it suffices for `β` to be finite; see
`Fintype.all_card_le_filter_rel_iff_exists_injective`).  There is
a transversal of the relation (an injective function `α → β` whose graph is
a subrelation of the relation) iff every subset of
`k` terms of `α` is related to at least `k` terms of `β`.

Note: if `[Fintype β]`, then there exist instances for `[∀ (a : α), Fintype (R.image {a})]`.
-/
theorem Fintype.all_card_le_rel_image_card_iff_exists_injective {α : Type u} {β : Type v}
    [DecidableEq β] (R : SetRel α β) [∀ a : α, Fintype (R.image {a})] :
    (∀ A : Finset α, #A ≤ Fintype.card (R.image A)) ↔
      ∃ f : α → β, Function.Injective f ∧ ∀ x, x ~[R] f x := by
  let r' a := (R.image {a}).toFinset
  have h : ∀ A : Finset α, Fintype.card (R.image A) = #(A.biUnion r') := by
    intro A
    rw [← Set.toFinset_card]
    apply congr_arg
    ext b
    simp [r', SetRel.image]
  have h' : ∀ (f : α → β) (x), x ~[R] f x ↔ f x ∈ r' x := by simp [r', SetRel.image]
  simp only [h, h']
  apply Finset.all_card_le_biUnion_card_iff_exists_injective

/-- This is a version of **Hall's Marriage Theorem** in terms of a relation to a finite type.
There is a transversal of the relation (an injective function `α → β` whose graph is a subrelation
of the relation) iff every subset of `k` terms of `α` is related to at least `k` terms of `β`.

It is like `Fintype.all_card_le_rel_image_card_iff_exists_injective` but uses `Finset.filter`
rather than `Rel.image`.
-/
theorem Fintype.all_card_le_filter_rel_iff_exists_injective {α : Type u} {β : Type v} [Fintype β]
    (r : α → β → Prop) [DecidableRel r] :
    (∀ A : Finset α, #A ≤ #{b | ∃ a ∈ A, r a b}) ↔ ∃ f : α → β, Injective f ∧ ∀ x, r x (f x) := by
  haveI := Classical.decEq β
  let r' a : Finset β := {b | r a b}
  have h : ∀ A : Finset α, ({b | ∃ a ∈ A, r a b} : Finset _) = A.biUnion r' := by
    intro A
    ext b
    simp [r']
  have h' : ∀ (f : α → β) (x), r x (f x) ↔ f x ∈ r' x := by simp [r']
  simp_rw [h, h']
  apply Finset.all_card_le_biUnion_card_iff_exists_injective
