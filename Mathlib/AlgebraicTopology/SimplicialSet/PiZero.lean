/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Nonempty

/-!
# Connected components of simplicial sets

In this file, we define the type `π₀ X` of connected components
of a simplicial sets. We also introduce typeclasses
`IsPreconnected X` and `IsConnected X`.

## TODO

* Define the subcomplex of `X` corresponding to an element in `π₀ X` (@joelriou)
* Show `π₀ X` is a coequalizer of the two face maps `X _⦋1⦌ → X _⦋0⦌` (@joelriou)
* Show `π₀ X` identifies to the colimit of `X` as a functor to types

## References:

- [Kerodon 00G5: Connected Components of Simplicial Sets](https://kerodon.net/tag/00G5)

-/

@[expose] public section

universe u

open CategoryTheory Simplicial Limits Opposite

namespace SSet

variable {X Y Z : SSet.{u}}

/-- The homotopy relation on `0`-simplices of a simplicial set. It holds
for `x₀` and `x₁` when there exists an edge from `x₀` to `x₁`. -/
def π₀Rel (x₀ x₁ : X _⦋0⦌) : Prop :=
  Nonempty (Edge x₀ x₁)

variable (X) in
/-- The type of connected components of a simplicial set. -/
def π₀ : Type u := Quot (π₀Rel (X := X))

attribute [irreducible] π₀

namespace π₀

unseal π₀ in
/-- The connected component of a `0`-simplex of a simplicial set. -/
def mk : X _⦋0⦌ → π₀ X := Quot.mk _

unseal π₀ in
lemma mk_surjective : Function.Surjective (π₀.mk (X := X)) := Quot.mk_surjective

unseal π₀ in
lemma sound {x₀ x₁ : X _⦋0⦌} (e : Edge x₀ x₁) :
    π₀.mk x₀ = π₀.mk x₁ :=
  Quot.sound ⟨e⟩

unseal π₀ in
lemma mk_eq_mk_iff (x₀ x₁ : X _⦋0⦌) :
    π₀.mk x₀ = π₀.mk x₁ ↔ Relation.EqvGen π₀Rel x₀ x₁ :=
  Quot.eq

@[elab_as_elim, cases_eliminator, induction_eliminator]
lemma rec {motive : π₀ X → Prop} (mk : ∀ (x : X _⦋0⦌), motive (.mk x)) (x : π₀ X) :
    motive x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  exact mk x

unseal π₀ in
/-- Constructor for maps from the type of connected components of a simplicial set. -/
def lift {T : Type*} (f : X _⦋0⦌ → T) (hf : ∀ ⦃x₀ x₁ : X _⦋0⦌⦄ (_ : X.Edge x₀ x₁), f x₀ = f x₁) :
    π₀ X → T :=
  Quot.lift f (by rintro x y ⟨e⟩; exact hf e)

@[simp]
lemma lift_mk {T : Type*} (f : X _⦋0⦌ → T)
    (hf : ∀ ⦃x₀ x₁ : X _⦋0⦌⦄ (_ : X.Edge x₀ x₁), f x₀ = f x₁) (x : X _⦋0⦌) :
    lift f hf (.mk x) = f x :=
  rfl

end π₀

/-- The map `π₀ X → π₀ Y` induced by a morphism `X ⟶ Y` of simplicial sets. -/
def mapπ₀ (f : X ⟶ Y) : π₀ X → π₀ Y :=
  π₀.lift (π₀.mk ∘ f.app _) (fun _ _ e ↦ π₀.sound (e.map f))

@[simp]
lemma mapπ₀_mk (f : X ⟶ Y) (x₀ : X _⦋0⦌) :
    mapπ₀ f (π₀.mk x₀) = π₀.mk (f.app _ x₀) :=
  rfl

@[simp]
lemma mapπ₀_id_apply (x : π₀ X) : mapπ₀ (𝟙 X) x = x := by
  induction x
  simp

@[simp]
lemma mapπ₀_comp_apply (f : X ⟶ Y) (g : Y ⟶ Z) (x : π₀ X) :
    mapπ₀ (f ≫ g) x = mapπ₀ g (mapπ₀ f x) := by
  induction x
  simp

/-- The functor which sends a simplicial set to the type of its connected components. -/
@[simps]
def π₀Functor : SSet.{u} ⥤ Type u where
  obj X := π₀ X
  map f := TypeCat.ofHom <| mapπ₀ f

variable (X)

/-- A simplicial set is preconnected when it has at most one connected component. -/
protected abbrev IsPreconnected : Prop := Subsingleton (π₀ X)

/-- A simplicial set is econnected when it has exactly one connected component. -/
protected class IsConnected : Prop extends SSet.IsPreconnected X where
  nonempty : X.Nonempty := by infer_instance

attribute [instance] IsConnected.nonempty

end SSet
