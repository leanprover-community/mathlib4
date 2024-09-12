/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.Data.List.Chain
import Mathlib.CategoryTheory.IsConnected
import Mathlib.CategoryTheory.Sigma.Basic
import Mathlib.CategoryTheory.FullSubcategory
import Mathlib.Data.List.Infix

/-!
# Connected components of a category

Defines a type `ConnectedComponents J` indexing the connected components of a category, and the
full subcategories giving each connected component: `Component j : Type u₁`.
We show that each `Component j` is in fact connected.

We show every category can be expressed as a disjoint union of its connected components, in
particular `Decomposed J` is the category (definitionally) given by the sigma-type of the connected
components of `J`, and it is shown that this is equivalent to `J`.
-/

universe v₁ v₂ v₃ u₁ u₂

noncomputable section

open CategoryTheory.Category

namespace CategoryTheory

attribute [instance 100] IsConnected.is_nonempty

variable {J : Type u₁} [Category.{v₁} J]

/-- This type indexes the connected components of the category `J`. -/
def ConnectedComponents (J : Type u₁) [Category.{v₁} J] : Type u₁ :=
  Quotient (Zigzag.setoid J)

/-- The map `ConnectedComponents J → ConnectedComponents K` induced by a functor `J ⥤ K`. -/
def Functor.mapConnectedComponents {K : Type u₂} [Category.{v₂} K] (F : J ⥤ K)
    (x : ConnectedComponents J) : ConnectedComponents K :=
  x |> Quotient.lift (Quotient.mk (Zigzag.setoid _) ∘ F.obj)
    (fun _ _ ↦ Quot.sound ∘ zigzag_obj_of_zigzag F)

@[simp]
lemma Functor.mapConnectedComponents_mk {K : Type u₂} [Category.{v₂} K] (F : J ⥤ K) (j : J) :
    F.mapConnectedComponents (Quotient.mk _ j) = Quotient.mk _ (F.obj j) := rfl

instance [Inhabited J] : Inhabited (ConnectedComponents J) :=
  ⟨Quotient.mk'' default⟩

/-- Every function from connected components of a category gives a functor to discrete category -/
def ConnectedComponents.functorToDiscrete   (X : Type*)
    (f : ConnectedComponents J → X) : J ⥤ Discrete X where
  obj Y :=  Discrete.mk (f (Quotient.mk (Zigzag.setoid _) Y))
  map g := Discrete.eqToHom (congrArg f (Quotient.sound (Zigzag.of_hom g)))

/-- Every functor to a discrete category gives a function from connected components -/
def ConnectedComponents.liftFunctor (J) [Category J] {X : Type*} (F :J ⥤ Discrete X) :
    (ConnectedComponents J → X) :=
  Quotient.lift (fun c => (F.obj c).as)
    (fun _ _ h => eq_of_zigzag X (zigzag_obj_of_zigzag F h))

/-- Functions from connected components and functors to discrete category are in bijection -/
def ConnectedComponents.typeToCatHomEquiv (J) [Category J] (X : Type*) :
    (ConnectedComponents J → X) ≃ (J ⥤ Discrete X)   where
  toFun := ConnectedComponents.functorToDiscrete _
  invFun := ConnectedComponents.liftFunctor _
  left_inv := fun f ↦ funext fun x ↦ by
    obtain ⟨x, h⟩ := Quotient.exists_rep x
    rw [← h]
    rfl
  right_inv  := fun fctr ↦
    Functor.hext (fun _ ↦ rfl) (fun c d f ↦
      have : Subsingleton (fctr.obj c ⟶ fctr.obj d) := Discrete.instSubsingletonDiscreteHom _ _
      (Subsingleton.elim (fctr.map f) _).symm.heq)

/-- Given an index for a connected component, produce the actual component as a full subcategory. -/
def Component (j : ConnectedComponents J) : Type u₁ :=
  FullSubcategory fun k => Quotient.mk'' k = j

instance {j : ConnectedComponents J} : Category (Component j) :=
  FullSubcategory.category _

-- Porting note: it was originally @[simps (config := { rhsMd := semireducible })]
/-- The inclusion functor from a connected component to the whole category. -/
@[simps!]
def Component.ι (j : ConnectedComponents J) : Component j ⥤ J :=
  fullSubcategoryInclusion _

instance {j : ConnectedComponents J} : Functor.Full (Component.ι j) :=
  FullSubcategory.full _

instance {j : ConnectedComponents J} : Functor.Faithful (Component.ι j) :=
  FullSubcategory.faithful _

/-- Each connected component of the category is nonempty. -/
instance (j : ConnectedComponents J) : Nonempty (Component j) := by
  induction j using Quotient.inductionOn'
  exact ⟨⟨_, rfl⟩⟩

instance (j : ConnectedComponents J) : Inhabited (Component j) :=
  Classical.inhabited_of_nonempty'

/-- Each connected component of the category is connected. -/
instance (j : ConnectedComponents J) : IsConnected (Component j) := by
  -- Show it's connected by constructing a zigzag (in `Component j`) between any two objects
  apply isConnected_of_zigzag
  rintro ⟨j₁, hj₁⟩ ⟨j₂, rfl⟩
  -- We know that the underlying objects j₁ j₂ have some zigzag between them in `J`
  have h₁₂ : Zigzag j₁ j₂ := Quotient.exact' hj₁
  -- Get an explicit zigzag as a list
  rcases List.exists_chain_of_relationReflTransGen h₁₂ with ⟨l, hl₁, hl₂⟩
  -- Everything which has a zigzag to j₂ can be lifted to the same component as `j₂`.
  let f : ∀ x, Zigzag x j₂ → Component (Quotient.mk'' j₂) := fun x h => ⟨x, Quotient.sound' h⟩
  -- Everything in our chosen zigzag from `j₁` to `j₂` has a zigzag to `j₂`.
  have hf : ∀ a : J, a ∈ l → Zigzag a j₂ := by
    intro i hi
    apply hl₁.backwards_induction (fun t => Zigzag t j₂) _ hl₂ _ _ _ (List.mem_of_mem_tail hi)
    · intro j k
      apply Relation.ReflTransGen.head
    · apply Relation.ReflTransGen.refl
  -- Now lift the zigzag from `j₁` to `j₂` in `J` to the same thing in `component j`.
  refine ⟨l.pmap f hf, ?_, ?_⟩
  · refine @List.chain_pmap_of_chain _ _ _ _ _ f (fun x y _ _ h => ?_) _ _ hl₁ h₁₂ _
    exact zag_of_zag_obj (Component.ι _) h
  · erw [List.getLast_pmap f (j₁ :: l) (by simpa [h₁₂] using hf) (List.cons_ne_nil _ _)]
    exact FullSubcategory.ext hl₂

/-- The disjoint union of `J`s connected components, written explicitly as a sigma-type with the
category structure.
This category is equivalent to `J`.
-/
abbrev Decomposed (J : Type u₁) [Category.{v₁} J] :=
  Σj : ConnectedComponents J, Component j

-- This name may cause clashes further down the road, and so might need to be changed.
/--
The inclusion of each component into the decomposed category. This is just `sigma.incl` but having
this abbreviation helps guide typeclass search to get the right category instance on `decomposed J`.
-/
abbrev inclusion (j : ConnectedComponents J) : Component j ⥤ Decomposed J :=
  Sigma.incl _

-- Porting note: it was originally @[simps (config := { rhsMd := semireducible })]
/-- The forward direction of the equivalence between the decomposed category and the original. -/
@[simps!]
def decomposedTo (J : Type u₁) [Category.{v₁} J] : Decomposed J ⥤ J :=
  Sigma.desc Component.ι

@[simp]
theorem inclusion_comp_decomposedTo (j : ConnectedComponents J) :
    inclusion j ⋙ decomposedTo J = Component.ι j :=
  rfl

instance : (decomposedTo J).Full where
  map_surjective := by
    rintro ⟨j', X, hX⟩ ⟨k', Y, hY⟩ f
    dsimp at f
    have : j' = k' := by
      rw [← hX, ← hY, Quotient.eq'']
      exact Relation.ReflTransGen.single (Or.inl ⟨f⟩)
    subst this
    exact ⟨Sigma.SigmaHom.mk f, rfl⟩

instance : (decomposedTo J).Faithful where
  map_injective := by
    rintro ⟨_, j, rfl⟩ ⟨_, k, hY⟩ ⟨f⟩ ⟨_⟩ rfl
    rfl

instance : (decomposedTo J).EssSurj where mem_essImage j := ⟨⟨_, j, rfl⟩, ⟨Iso.refl _⟩⟩

instance : (decomposedTo J).IsEquivalence where

-- Porting note: it was originally @[simps (config := { rhsMd := semireducible }) Functor]
/-- This gives that any category is equivalent to a disjoint union of connected categories. -/
@[simps! functor]
def decomposedEquiv : Decomposed J ≌ J :=
  (decomposedTo J).asEquivalence

end CategoryTheory
