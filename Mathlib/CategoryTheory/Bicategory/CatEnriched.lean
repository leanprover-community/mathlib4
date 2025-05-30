/-
Copyright (c) 2025 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Emily Riehl
-/
import Mathlib.CategoryTheory.Monoidal.Cartesian.Cat
import Mathlib.CategoryTheory.Enriched.Basic

/-!
# The strict bicategory associated to a Cat-enriched category

If `C` is a type with a `EnrichedCategory Cat C` structure, then it has hom-categories, whose
objects define 1-dimensional arrows on `C` and whose morphisms define 2-dimensional arrows between
these. The enriched category axioms equip this data with the structure of a strict bicategory.

We define a type alias `CatEnriched C` for a type `C` with a `EnrichedCategory Cat C` structure.

We provide this with an instance of a strict bicategory structure constructing
`Bicategory.Strict (CatEnriched C)`.
-/

namespace CategoryTheory
open Category

variable {C : Type*} [EnrichedCategory Cat C]

/-- A type synonym for `C`, which should come equipped with a `Cat`-enriched category structure.
This converts it to a strict bicategory where `Category (X ⟶ Y)` is `(X ⟶[Cat] Y)`. -/
def CatEnriched (C : Type*) := C

namespace CatEnriched

instance : EnrichedCategory Cat (CatEnriched C) := inferInstanceAs (EnrichedCategory Cat C)

/-- Any enriched category has an underlying category structure defined by `ForgetEnrichment`.
This is equivalent but not definitionally equal the category structure constructed here, which is
more canonically associated to the data of an `EnrichedCategory Cat` structure. -/
instance : CategoryStruct (CatEnriched C) where
  Hom X Y := X ⟶[Cat] Y
  id X := (eId Cat X).obj ⟨⟨()⟩⟩
  comp {X Y Z} f g := (eComp Cat X Y Z).obj (f, g)

theorem id_eq (X : CatEnriched C) : 𝟙 X = (eId Cat X).obj ⟨⟨()⟩⟩ := rfl

theorem comp_eq {X Y Z : CatEnriched C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    f ≫ g = (eComp Cat X Y Z).obj (f, g) := rfl

instance {X Y : CatEnriched C} : Category (X ⟶ Y) := inferInstanceAs (Category (X ⟶[Cat] Y).α)

/-- The horizonal composition on 2-morphisms is defined using the action on arrows of the
composition bifunctor from the enriched category structure. -/
def hComp {a b c : CatEnriched C} {f f' : a ⟶ b} {g g' : b ⟶ c}
  (η : f ⟶ f') (θ : g ⟶ g') : f ≫ g ⟶ f' ≫ g' := (eComp Cat a b c).map (η, θ)

@[simp]
theorem id_hComp_id {a b c : CatEnriched C} (f : a ⟶ b) (g : b ⟶ c) :
    hComp (𝟙 f) (𝟙 g) = 𝟙 (f ≫ g) := Functor.map_id ..

/-- The interchange law for horizontal and vertical composition of 2-cells in a bicategory. -/
@[simp]
theorem hComp_comp {a b c : CatEnriched C} {f₁ f₂ f₃ : a ⟶ b} {g₁ g₂ g₃ : b ⟶ c}
    (η : f₁ ⟶ f₂) (η' : f₂ ⟶ f₃) (θ : g₁ ⟶ g₂) (θ' : g₂ ⟶ g₃) :
    hComp η θ ≫ hComp η' θ' = hComp (η ≫ η') (θ ≫ θ') :=
  ((eComp Cat a b c).map_comp (Y := (_, _)) (_, _) (_, _)).symm

/-- The action on objects of the `EnrichedCategory Cat` coherences proves the category axioms. -/
instance : Category (CatEnriched C) where
  id_comp {X Y} f := congrArg (·.obj f) (e_id_comp (V := Cat) X Y)
  comp_id {X Y} f := congrArg (·.obj f) (e_comp_id (V := Cat) X Y)
  assoc {X Y Z W} f g h := congrArg (·.obj (f, g, h)) (e_assoc (V := Cat) X Y Z W)

theorem id_hComp_heq {a b : CatEnriched C} {f f' : a ⟶ b} (η : f ⟶ f') :
    HEq (hComp (𝟙 (𝟙 a)) η) η := by
  rw [id_eq, ← Functor.map_id]
  exact congr_arg_heq (·.map η) (e_id_comp (V := Cat) a b)

theorem id_hComp {a b : CatEnriched C} {f f' : a ⟶ b} (η : f ⟶ f') :
    hComp (𝟙 (𝟙 a)) η = eqToHom (id_comp f) ≫ η ≫ eqToHom (id_comp f').symm := by
  simp [← heq_eq_eq, id_hComp_heq]

theorem hComp_id_heq {a b : CatEnriched C} {f f' : a ⟶ b} (η : f ⟶ f') :
    HEq (hComp η (𝟙 (𝟙 b))) η := by
  rw [id_eq, ← Functor.map_id]
  exact congr_arg_heq (·.map η) (e_comp_id (V := Cat) a b)

theorem hComp_id {a b : CatEnriched C} {f f' : a ⟶ b} (η : f ⟶ f') :
    hComp η (𝟙 (𝟙 b)) = eqToHom (comp_id f) ≫ η ≫ eqToHom (comp_id f').symm := by
  simp [← heq_eq_eq, hComp_id_heq]

theorem hComp_assoc_heq {a b c d : CatEnriched C} {f f' : a ⟶ b} {g g' : b ⟶ c} {h h' : c ⟶ d}
    (η : f ⟶ f') (θ : g ⟶ g') (κ : h ⟶ h') :
    HEq (hComp (hComp η θ) κ) (hComp η (hComp θ κ)) :=
  congr_arg_heq (·.map (X := (_, _, _)) (Y := (_, _, _)) (η, θ, κ)) (e_assoc (V := Cat) a b c d)

theorem hComp_assoc {a b c d : CatEnriched C} {f f' : a ⟶ b} {g g' : b ⟶ c} {h h' : c ⟶ d}
    (η : f ⟶ f') (θ : g ⟶ g') (κ : h ⟶ h') :
    hComp (hComp η θ) κ =
      eqToHom (assoc f g h) ≫ hComp η (hComp θ κ) ≫ eqToHom (assoc f' g' h').symm := by
  simp [← heq_eq_eq, hComp_assoc_heq]

instance : Bicategory (CatEnriched C) where
  homCategory := inferInstance
  whiskerLeft {_ _ _} f {_ _} η := hComp (𝟙 f) η
  whiskerRight η h := hComp η (𝟙 h)
  associator f g h := eqToIso (assoc f g h)
  leftUnitor f := eqToIso (id_comp f)
  rightUnitor f := eqToIso (comp_id f)
  id_whiskerLeft := id_hComp
  comp_whiskerLeft := by simp [← id_hComp_id, hComp_assoc]
  whiskerRight_id := hComp_id
  whiskerRight_comp := by simp [hComp_assoc]
  whisker_assoc := by simp [hComp_assoc]
  pentagon f g h i := by
    generalize_proofs h1 h2 h3 h4; revert h1 h2 h3 h4
    generalize (f ≫ g) ≫ h = x, (g ≫ h) ≫ i = w
    rintro rfl _ rfl _; simp
  triangle f g := by
    generalize_proofs h1 h2 h3; revert h1 h2 h3
    generalize 𝟙 _ ≫ g = g, f ≫ 𝟙 _ = f
    rintro _ rfl rfl; simp

/-- As the associator and left and right unitors are defined as eqToIso of category axioms, the
bicategory structure on `CatEnriched C` is strict. -/
instance : Bicategory.Strict (CatEnriched C) where

end CatEnriched

end CategoryTheory
