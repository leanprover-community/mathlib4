/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.Data.List.Chain
import Mathlib.CategoryTheory.IsConnected
import Mathlib.CategoryTheory.Sigma.Basic
import Mathlib.CategoryTheory.FullSubcategory

#align_import category_theory.connected_components from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!
# Connected components of a category

Defines a type `ConnectedComponents J` indexing the connected components of a category, and the
full subcategories giving each connected component: `Component j : Type u₁`.
We show that each `Component j` is in fact connected.

We show every category can be expressed as a disjoint union of its connected components, in
particular `Decomposed J` is the category (definitionally) given by the sigma-type of the connected
components of `J`, and it is shown that this is equivalent to `J`.
-/

set_option autoImplicit true


universe v₁ v₂ v₃ u₁ u₂

noncomputable section

open CategoryTheory.Category

namespace CategoryTheory

attribute [instance 100] IsConnected.is_nonempty

variable {J : Type u₁} [Category.{v₁} J]

variable {C : Type u₂} [Category.{u₁} C]

/-- This type indexes the connected components of the category `J`. -/
def ConnectedComponents (J : Type u₁) [Category.{v₁} J] : Type u₁ :=
  Quotient (Zigzag.setoid J)
#align category_theory.connected_components CategoryTheory.ConnectedComponents

instance [Inhabited J] : Inhabited (ConnectedComponents J) :=
  ⟨Quotient.mk'' default⟩

/-- Given an index for a connected component, produce the actual component as a full subcategory. -/
def Component (j : ConnectedComponents J) : Type u₁ :=
  FullSubcategory fun k => Quotient.mk'' k = j
#align category_theory.component CategoryTheory.Component

instance : Category (Component (j : ConnectedComponents J)) :=
  FullSubcategory.category _

--porting note : it was originally @[simps (config := { rhsMd := semireducible })]
/-- The inclusion functor from a connected component to the whole category. -/
@[simps!]
def Component.ι (j : ConnectedComponents J) : Component j ⥤ J :=
  fullSubcategoryInclusion _
#align category_theory.component.ι CategoryTheory.Component.ι

instance : Full (Component.ι (j : ConnectedComponents J)) :=
  FullSubcategory.full _

instance : Faithful (Component.ι (j : ConnectedComponents J)) :=
  FullSubcategory.faithful _

/-- Each connected component of the category is nonempty. -/
instance (j : ConnectedComponents J) : Nonempty (Component j) := by
  induction j using Quotient.inductionOn'
  -- ⊢ Nonempty (Component (Quotient.mk'' a✝))
  exact ⟨⟨_, rfl⟩⟩
  -- 🎉 no goals

instance (j : ConnectedComponents J) : Inhabited (Component j) :=
  Classical.inhabited_of_nonempty'

/-- Each connected component of the category is connected. -/
instance (j : ConnectedComponents J) : IsConnected (Component j) := by
  -- Show it's connected by constructing a zigzag (in `Component j`) between any two objects
  apply isConnected_of_zigzag
  -- ⊢ ∀ (j₁ j₂ : Component j), ∃ l, List.Chain Zag j₁ l ∧ List.getLast (j₁ :: l) ( …
  rintro ⟨j₁, hj₁⟩ ⟨j₂, rfl⟩
  -- ⊢ ∃ l, List.Chain Zag { obj := j₁, property := hj₁ } l ∧ List.getLast ({ obj : …
  -- We know that the underlying objects j₁ j₂ have some zigzag between them in `J`
  have h₁₂ : Zigzag j₁ j₂ := Quotient.exact' hj₁
  -- ⊢ ∃ l, List.Chain Zag { obj := j₁, property := hj₁ } l ∧ List.getLast ({ obj : …
  -- Get an explicit zigzag as a list
  rcases List.exists_chain_of_relationReflTransGen h₁₂ with ⟨l, hl₁, hl₂⟩
  -- ⊢ ∃ l, List.Chain Zag { obj := j₁, property := hj₁ } l ∧ List.getLast ({ obj : …
  -- Everything which has a zigzag to j₂ can be lifted to the same component as `j₂`.
  let f : ∀ x, Zigzag x j₂ → Component (Quotient.mk'' j₂) := fun x h => ⟨x, Quotient.sound' h⟩
  -- ⊢ ∃ l, List.Chain Zag { obj := j₁, property := hj₁ } l ∧ List.getLast ({ obj : …
  -- Everything in our chosen zigzag from `j₁` to `j₂` has a zigzag to `j₂`.
  have hf : ∀ a : J, a ∈ l → Zigzag a j₂ := by
    intro i hi
    apply List.Chain.induction (fun t => Zigzag t j₂) _ hl₁ hl₂ _ _ _ (List.mem_of_mem_tail hi)
    · intro j k
      apply Relation.ReflTransGen.head
    · apply Relation.ReflTransGen.refl
  -- Now lift the zigzag from `j₁` to `j₂` in `J` to the same thing in `component j`.
  refine' ⟨l.pmap f hf, _, _⟩
  -- ⊢ List.Chain Zag { obj := j₁, property := hj₁ } (List.pmap f l hf)
  · refine' @List.chain_pmap_of_chain _ _ _ _ _ f (fun x y _ _ h => _) _ _ hl₁ h₁₂ _
    -- ⊢ Zag (f x x✝¹) (f y x✝)
    exact zag_of_zag_obj (Component.ι _) h
    -- 🎉 no goals
  · erw [List.getLast_pmap _ f (j₁ :: l) (by simpa [h₁₂] using hf) (List.cons_ne_nil _ _)]
    -- ⊢ f (List.getLast (j₁ :: l) (_ : j₁ :: l ≠ [])) (_ : Zigzag (List.getLast (j₁  …
    exact FullSubcategory.ext _ _ hl₂
    -- 🎉 no goals

/-- The disjoint union of `J`s connected components, written explicitly as a sigma-type with the
category structure.
This category is equivalent to `J`.
-/
abbrev Decomposed (J : Type u₁) [Category.{v₁} J] :=
  Σj : ConnectedComponents J, Component j
#align category_theory.decomposed CategoryTheory.Decomposed

-- This name may cause clashes further down the road, and so might need to be changed.
/--
The inclusion of each component into the decomposed category. This is just `sigma.incl` but having
this abbreviation helps guide typeclass search to get the right category instance on `decomposed J`.
-/
abbrev inclusion (j : ConnectedComponents J) : Component j ⥤ Decomposed J :=
  Sigma.incl _
#align category_theory.inclusion CategoryTheory.inclusion

--porting note : it was originally @[simps (config := { rhsMd := semireducible })]
/-- The forward direction of the equivalence between the decomposed category and the original. -/
@[simps!]
def decomposedTo (J : Type u₁) [Category.{v₁} J] : Decomposed J ⥤ J :=
  Sigma.desc Component.ι
#align category_theory.decomposed_to CategoryTheory.decomposedTo

@[simp]
theorem inclusion_comp_decomposedTo (j : ConnectedComponents J) :
    inclusion j ⋙ decomposedTo J = Component.ι j :=
  rfl
#align category_theory.inclusion_comp_decomposed_to CategoryTheory.inclusion_comp_decomposedTo

instance : Full (decomposedTo J)
    where
  preimage := by
    rintro ⟨j', X, hX⟩ ⟨k', Y, hY⟩ f
    -- ⊢ { fst := j', snd := { obj := X, property := hX } } ⟶ { fst := k', snd := { o …
    dsimp at f
    -- ⊢ { fst := j', snd := { obj := X, property := hX } } ⟶ { fst := k', snd := { o …
    have : j' = k'
    -- ⊢ j' = k'
    rw [← hX, ← hY, Quotient.eq'']
    -- ⊢ Setoid.r X Y
    exact Relation.ReflTransGen.single (Or.inl ⟨f⟩)
    -- ⊢ { fst := j', snd := { obj := X, property := hX } } ⟶ { fst := k', snd := { o …
    subst this
    -- ⊢ { fst := j', snd := { obj := X, property := hX } } ⟶ { fst := j', snd := { o …
    exact Sigma.SigmaHom.mk f
    -- 🎉 no goals
  witness := by
    rintro ⟨j', X, hX⟩ ⟨_, Y, rfl⟩ f
    -- ⊢ (decomposedTo J).map (Sigma.casesOn (motive := fun x => {Y : Decomposed J} → …
    have : Quotient.mk'' Y = j' := by
      rw [← hX, Quotient.eq'']
      exact Relation.ReflTransGen.single (Or.inr ⟨f⟩)
    subst this
    -- ⊢ (decomposedTo J).map (Sigma.casesOn (motive := fun x => {Y : Decomposed J} → …
    rfl
    -- 🎉 no goals

instance : Faithful (decomposedTo J) where
  map_injective := by
    rintro ⟨_, j, rfl⟩ ⟨_, k, hY⟩ ⟨f⟩ ⟨_⟩ rfl
    -- ⊢ Sigma.SigmaHom.mk f = Sigma.SigmaHom.mk ((decomposedTo J).map (Sigma.SigmaHo …
    rfl
    -- 🎉 no goals

instance : EssSurj (decomposedTo J) where mem_essImage j := ⟨⟨_, j, rfl⟩, ⟨Iso.refl _⟩⟩

instance : IsEquivalence (decomposedTo J) :=
  Equivalence.ofFullyFaithfullyEssSurj _

-- porting note: it was originally @[simps (config := { rhsMd := semireducible }) Functor]
/-- This gives that any category is equivalent to a disjoint union of connected categories. -/
@[simps! functor]
def decomposedEquiv : Decomposed J ≌ J :=
  (decomposedTo J).asEquivalence
#align category_theory.decomposed_equiv CategoryTheory.decomposedEquiv

end CategoryTheory
