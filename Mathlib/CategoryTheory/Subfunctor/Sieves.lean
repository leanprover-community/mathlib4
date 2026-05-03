/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.CategoryTheory.Subfunctor.Basic
public import Mathlib.CategoryTheory.Sites.IsSheafFor
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Terminal
public import Mathlib.CategoryTheory.Limits.Types.Products

/-!
# Sieves attached to subpresheaves

Given a subpresheaf `G` of a presheaf of types `F : Cᵒᵖ ⥤ Type w` and
a section `s : F.obj U`, we define a sieve `G.sieveOfSection s : Sieve (unop U)`
and the associated compatible family of elements with values in `G.toFunctor`.

-/

@[expose] public section

universe w v u

namespace CategoryTheory.Subfunctor

open Opposite

variable {C : Type u} [Category.{v} C] {F : Cᵒᵖ ⥤ Type w} (G : Subfunctor F)

/-- Given a subpresheaf `G` of `F`, an `F`-section `s` on `U`, we may define a sieve of `U`
consisting of all `f : V ⟶ U` such that the restriction of `s` along `f` is in `G`. -/
@[simps]
def sieveOfSection {U : Cᵒᵖ} (s : F.obj U) : Sieve (unop U) where
  arrows V f := F.map f.op s ∈ G.obj (op V)
  downward_closed := @fun V W i hi j => by
    simpa using G.map _ hi

/-- Given an `F`-section `s` on `U` and a subpresheaf `G`, we may define a family of elements in
`G` consisting of the restrictions of `s` -/
def familyOfElementsOfSection {U : Cᵒᵖ} (s : F.obj U) :
    (G.sieveOfSection s).1.FamilyOfElements G.toFunctor := fun _ i hi => ⟨F.map i.op s, hi⟩

theorem family_of_elements_compatible {U : Cᵒᵖ} (s : F.obj U) :
    (G.familyOfElementsOfSection s).Compatible := by
  intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ e
  refine Subtype.ext ?_ -- Porting note: `ext1` does not work here
  change F.map g₁.op (F.map f₁.op s) = F.map g₂.op (F.map f₂.op s)
  rw [← comp_apply, ← Functor.map_comp, ← comp_apply, ← Functor.map_comp, ← op_comp, ← op_comp, e]

@[deprecated (since := "2025-12-11")] alias Subpresheaf.sieveOfSection := sieveOfSection
@[deprecated (since := "2025-12-11")] alias Subpresheaf.familyOfElementsOfSection :=
  familyOfElementsOfSection
@[deprecated (since := "2025-12-11")] alias Subpresheaf.family_of_elements_compatible :=
  family_of_elements_compatible

/-- Given a family of objects `X : ι → C` in a category `C`, this is the subfunctor
of the constant functor `Cᵒᵖ ⥤ Type w` with value `PUnit` which sends an object
`U : C` to `Set.univ` when there exists a morphism `U ⟶ X i` for some `i`,
and `∅` otherwise. -/
def ofObjects {ι : Type*} (X : ι → C) :
    Subfunctor ((Functor.const Cᵒᵖ).obj PUnit.{w + 1}) where
  obj U := setOf (fun _ ↦ ∃ (i : ι), Nonempty (U.unop ⟶ X i))
  map := by
    rintro _ _ f _ ⟨i, ⟨g⟩⟩
    exact ⟨i, ⟨f.unop ≫ g⟩⟩

lemma ofObjects_obj_eq_univ {ι : Type*} {X : ι → C} {U : Cᵒᵖ} {i : ι} (f : U.unop ⟶ X i) :
    (ofObjects X).obj U = ⊤ := by
  ext
  simp only [ofObjects, Set.top_eq_univ, Set.mem_univ, iff_true]
  exact ⟨i, ⟨f⟩⟩

set_option backward.isDefEq.respectTransparency false in
lemma ofObjects_obj_eq_empty {ι : Type*} {X : ι → C} {U : Cᵒᵖ}
    (h : ∀ (i : ι), IsEmpty (U.unop ⟶ X i)) :
    (ofObjects X).obj U = ∅ := by
  ext
  simpa [ofObjects]

set_option backward.isDefEq.respectTransparency false in
/-- The value of `ofObjects X` on an object `U : Cᵒᵖ` contains a unique element
when there is a morphism `f : U.unop ⟶ X i`. -/
def uniqueOfObjectsObj {ι : Type*} {X : ι → C} {U : Cᵒᵖ} {i : ι} (f : U.unop ⟶ X i) :
    Unique ((ofObjects.{w} X).obj U) where
  default := ⟨.unit, by simp [ofObjects_obj_eq_univ f]⟩
  uniq := by rintro ⟨⟨⟩, _⟩; rfl

open Limits in
/-- `(ofObjects X).toFunctor` is a terminal object when there is a morphism
`f : T ⟶ X i` with `T` a terminal object. -/
noncomputable def isTerminalOfObjectsToFunctor {ι : Type*} (X : ι → C) {T : C} {i : ι} (f : T ⟶ X i)
    (hT : IsTerminal T) :
    IsTerminal (ofObjects X).toFunctor :=
  Functor.isTerminal
    (fun _ ↦ (Types.isTerminalEquivUnique _).2 (uniqueOfObjectsObj (hT.from _ ≫ f)))

end CategoryTheory.Subfunctor
