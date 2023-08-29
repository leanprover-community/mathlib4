/-
Copyright (c) 2021 Alena Gusakov, Bhavik Mehta, Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alena Gusakov, Bhavik Mehta, Kyle Miller
-/
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.CategoryTheory.CofilteredSystem
import Mathlib.Data.Rel

#align_import combinatorics.hall.basic from "leanprover-community/mathlib"@"8195826f5c428fc283510bc67303dd4472d78498"

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
  `r : α → β → Prop` such that `Rel.image r {a}` is a finite set for all `a : α`.
* `Fintype.all_card_le_filter_rel_iff_exists_injective` is in terms of a relation
  `r : α → β → Prop` on finite types, with the Hall condition given in terms of
  `finset.univ.filter`.

## Todo

* The statement of the theorem in terms of bipartite graphs is in preparation.

## Tags

Hall's Marriage Theorem, indexed families
-/


open Finset CategoryTheory

universe u v

/-- The set of matchings for `t` when restricted to a `Finset` of `ι`. -/
def hallMatchingsOn {ι : Type u} {α : Type v} (t : ι → Finset α) (ι' : Finset ι) :=
  { f : ι' → α | Function.Injective f ∧ ∀ x, f x ∈ t x }
#align hall_matchings_on hallMatchingsOn

/-- Given a matching on a finset, construct the restriction of that matching to a subset. -/
def hallMatchingsOn.restrict {ι : Type u} {α : Type v} (t : ι → Finset α) {ι' ι'' : Finset ι}
    (h : ι' ⊆ ι'') (f : hallMatchingsOn t ι'') : hallMatchingsOn t ι' := by
  refine' ⟨fun i => f.val ⟨i, h i.property⟩, _⟩
  -- ⊢ (fun i => ↑f { val := ↑i, property := (_ : ↑i ∈ ι'') }) ∈ hallMatchingsOn t ι'
  cases' f.property with hinj hc
  -- ⊢ (fun i => ↑f { val := ↑i, property := (_ : ↑i ∈ ι'') }) ∈ hallMatchingsOn t ι'
  refine' ⟨_, fun i => hc ⟨i, h i.property⟩⟩
  -- ⊢ Function.Injective fun i => ↑f { val := ↑i, property := (_ : ↑i ∈ ι'') }
  rintro ⟨i, hi⟩ ⟨j, hj⟩ hh
  -- ⊢ { val := i, property := hi } = { val := j, property := hj }
  simpa only [Subtype.mk_eq_mk] using hinj hh
  -- 🎉 no goals
#align hall_matchings_on.restrict hallMatchingsOn.restrict

/-- When the Hall condition is satisfied, the set of matchings on a finite set is nonempty.
This is where `Finset.all_card_le_biUnion_card_iff_existsInjective'` comes into the argument. -/
theorem hallMatchingsOn.nonempty {ι : Type u} {α : Type v} [DecidableEq α] (t : ι → Finset α)
    (h : ∀ s : Finset ι, s.card ≤ (s.biUnion t).card) (ι' : Finset ι) :
    Nonempty (hallMatchingsOn t ι') := by
  classical
    refine' ⟨Classical.indefiniteDescription _ _⟩
    apply (all_card_le_biUnion_card_iff_existsInjective' fun i : ι' => t i).mp
    intro s'
    convert h (s'.image (↑)) using 1
    simp only [card_image_of_injective s' Subtype.coe_injective]
    rw [image_biUnion]
#align hall_matchings_on.nonempty hallMatchingsOn.nonempty

/-- This is the `hallMatchingsOn` sets assembled into a directed system.
-/
def hallMatchingsFunctor {ι : Type u} {α : Type v} (t : ι → Finset α) : (Finset ι)ᵒᵖ ⥤ Type max u v
    where
  obj ι' := hallMatchingsOn t ι'.unop
  map {ι' ι''} g f := hallMatchingsOn.restrict t (CategoryTheory.leOfHom g.unop) f
#align hall_matchings_functor hallMatchingsFunctor

instance hallMatchingsOn.finite {ι : Type u} {α : Type v} (t : ι → Finset α) (ι' : Finset ι) :
    Finite (hallMatchingsOn t ι') := by
  classical
    rw [hallMatchingsOn]
    let g : hallMatchingsOn t ι' → ι' → ι'.biUnion t := by
      rintro f i
      refine' ⟨f.val i, _⟩
      rw [mem_biUnion]
      exact ⟨i, i.property, f.property.2 i⟩
    apply Finite.of_injective g
    intro f f' h
    ext a
    rw [Function.funext_iff] at h
    simpa using h a
#align hall_matchings_on.finite hallMatchingsOn.finite

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
    (∀ s : Finset ι, s.card ≤ (s.biUnion t).card) ↔
      ∃ f : ι → α, Function.Injective f ∧ ∀ x, f x ∈ t x := by
  constructor
  -- ⊢ (∀ (s : Finset ι), card s ≤ card (Finset.biUnion s t)) → ∃ f, Function.Injec …
  · intro h
    -- ⊢ ∃ f, Function.Injective f ∧ ∀ (x : ι), f x ∈ t x
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
      refine' ⟨_, _, _⟩
      ·-- Build the matching function from the section
        exact fun i =>
          (u (Opposite.op ({i} : Finset ι))).val ⟨i, by simp only [Opposite.unop_op, mem_singleton]⟩
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
    -- ⊢ card s ≤ card (Finset.biUnion s t)
    rw [← Finset.card_image_of_injective s hf₁]
    -- ⊢ card (image f s) ≤ card (Finset.biUnion s t)
    apply Finset.card_le_of_subset
    -- ⊢ image f s ⊆ Finset.biUnion s t
    intro
    -- ⊢ a✝ ∈ image f s → a✝ ∈ Finset.biUnion s t
    rw [Finset.mem_image, Finset.mem_biUnion]
    -- ⊢ (∃ a, a ∈ s ∧ f a = a✝) → ∃ a, a ∈ s ∧ a✝ ∈ t a
    rintro ⟨x, hx, rfl⟩
    -- ⊢ ∃ a, a ∈ s ∧ f x ∈ t a
    exact ⟨x, hx, hf₂ x⟩
    -- 🎉 no goals
#align finset.all_card_le_bUnion_card_iff_exists_injective Finset.all_card_le_biUnion_card_iff_exists_injective

/-- Given a relation such that the image of every singleton set is finite, then the image of every
finite set is finite. -/
instance {α : Type u} {β : Type v} [DecidableEq β] (r : α → β → Prop)
    [∀ a : α, Fintype (Rel.image r {a})] (A : Finset α) : Fintype (Rel.image r A) := by
  have h : Rel.image r A = (A.biUnion fun a => (Rel.image r {a}).toFinset : Set β) := by
    ext
    -- Porting note: added `Set.mem_toFinset`
    simp [Rel.image, (Set.mem_toFinset)]
  rw [h]
  -- ⊢ Fintype ↑↑(Finset.biUnion A fun a => Set.toFinset (Rel.image r {a}))
  apply FinsetCoe.fintype
  -- 🎉 no goals

/-- This is a version of **Hall's Marriage Theorem** in terms of a relation
between types `α` and `β` such that `α` is finite and the image of
each `x : α` is finite (it suffices for `β` to be finite; see
`Fintype.all_card_le_filter_rel_iff_exists_injective`).  There is
a transversal of the relation (an injective function `α → β` whose graph is
a subrelation of the relation) iff every subset of
`k` terms of `α` is related to at least `k` terms of `β`.

Note: if `[Fintype β]`, then there exist instances for `[∀ (a : α), Fintype (Rel.image r {a})]`.
-/
theorem Fintype.all_card_le_rel_image_card_iff_exists_injective {α : Type u} {β : Type v}
    [DecidableEq β] (r : α → β → Prop) [∀ a : α, Fintype (Rel.image r {a})] :
    (∀ A : Finset α, A.card ≤ Fintype.card (Rel.image r A)) ↔
      ∃ f : α → β, Function.Injective f ∧ ∀ x, r x (f x) := by
  let r' a := (Rel.image r {a}).toFinset
  -- ⊢ (∀ (A : Finset α), Finset.card A ≤ card ↑(Rel.image r ↑A)) ↔ ∃ f, Function.I …
  have h : ∀ A : Finset α, Fintype.card (Rel.image r A) = (A.biUnion r').card := by
    intro A
    rw [← Set.toFinset_card]
    apply congr_arg
    ext b
    -- Porting note: added `Set.mem_toFinset`
    simp [Rel.image, (Set.mem_toFinset)]
  -- Porting note: added `Set.mem_toFinset`
  have h' : ∀ (f : α → β) (x), r x (f x) ↔ f x ∈ r' x := by simp [Rel.image, (Set.mem_toFinset)]
  -- ⊢ (∀ (A : Finset α), Finset.card A ≤ card ↑(Rel.image r ↑A)) ↔ ∃ f, Function.I …
  simp only [h, h']
  -- ⊢ (∀ (A : Finset α), Finset.card A ≤ Finset.card (Finset.biUnion A fun a => Se …
  apply Finset.all_card_le_biUnion_card_iff_exists_injective
  -- 🎉 no goals
#align fintype.all_card_le_rel_image_card_iff_exists_injective Fintype.all_card_le_rel_image_card_iff_exists_injective

-- TODO: decidable_pred makes Yael sad. When an appropriate decidable_rel-like exists, fix it.
/-- This is a version of **Hall's Marriage Theorem** in terms of a relation to a finite type.
There is a transversal of the relation (an injective function `α → β` whose graph is a subrelation
of the relation) iff every subset of `k` terms of `α` is related to at least `k` terms of `β`.

It is like `Fintype.all_card_le_rel_image_card_iff_exists_injective` but uses `Finset.filter`
rather than `Rel.image`.
-/
theorem Fintype.all_card_le_filter_rel_iff_exists_injective {α : Type u} {β : Type v} [Fintype β]
    (r : α → β → Prop) [∀ a, DecidablePred (r a)] :
    (∀ A : Finset α, A.card ≤ (univ.filter fun b : β => ∃ a ∈ A, r a b).card) ↔
      ∃ f : α → β, Function.Injective f ∧ ∀ x, r x (f x) := by
  haveI := Classical.decEq β
  -- ⊢ (∀ (A : Finset α), Finset.card A ≤ Finset.card (filter (fun b => ∃ a, a ∈ A  …
  let r' a := univ.filter fun b => r a b
  -- ⊢ (∀ (A : Finset α), Finset.card A ≤ Finset.card (filter (fun b => ∃ a, a ∈ A  …
  have h : ∀ A : Finset α, (univ.filter fun b : β => ∃ a ∈ A, r a b) = A.biUnion r' := by
    intro A
    ext b
    simp
  have h' : ∀ (f : α → β) (x), r x (f x) ↔ f x ∈ r' x := by simp
  -- ⊢ (∀ (A : Finset α), Finset.card A ≤ Finset.card (filter (fun b => ∃ a, a ∈ A  …
  simp_rw [h, h']
  -- ⊢ (∀ (A : Finset α), Finset.card A ≤ Finset.card (Finset.biUnion A fun a => fi …
  apply Finset.all_card_le_biUnion_card_iff_exists_injective
  -- 🎉 no goals
#align fintype.all_card_le_filter_rel_iff_exists_injective Fintype.all_card_le_filter_rel_iff_exists_injective
