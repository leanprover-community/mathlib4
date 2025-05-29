/-
Copyright (c) 2025 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Emily Riehl
-/
import Mathlib.CategoryTheory.Monoidal.Cartesian.Cat
import Mathlib.CategoryTheory.Enriched.Basic

namespace CategoryTheory
open Category

variable {C : Type*} [EnrichedCategory Cat C]

/-- A type synonym for `C`, which should come equipped with a `Cat`-enriched category structure.
This converts it to a strict bicategory where `X ⟶ Y` is `(𝟙_ Cat) ⟶ (X ⟶[W] Y)`. -/
def CatEnriched (C : Type*) := C

namespace CatEnriched

instance : EnrichedCategory Cat (CatEnriched C) := inferInstanceAs (EnrichedCategory Cat C)

instance : CategoryStruct (CatEnriched C) where
  Hom X Y := X ⟶[Cat] Y
  id X := (eId Cat X).obj ⟨⟨()⟩⟩
  comp {X Y Z} f g := (eComp Cat X Y Z).obj (f, g)

theorem id_eq (X : CatEnriched C) : 𝟙 X = (eId Cat X).obj ⟨⟨()⟩⟩ := rfl
theorem comp_eq {X Y Z : CatEnriched C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    f ≫ g = (eComp Cat X Y Z).obj (f, g) := rfl

instance {X Y : CatEnriched C} : Category (X ⟶ Y) := inferInstanceAs (Category (X ⟶[Cat] Y).α)

def bicomp {a b c : CatEnriched C} {f f' : a ⟶ b} {g g' : b ⟶ c}
  (η : f ⟶ f') (θ : g ⟶ g') : f ≫ g ⟶ f' ≫ g' := (eComp Cat ..).map (η, θ)

@[simp]
theorem id_bicomp_id {a b c : CatEnriched C} (f : a ⟶ b) (g : b ⟶ c) :
    bicomp (𝟙 f) (𝟙 g) = 𝟙 (f ≫ g) := Functor.map_id ..

@[simp]
theorem bicomp_comp {a b c : CatEnriched C} {f₁ f₂ f₃ : a ⟶ b} {g₁ g₂ g₃ : b ⟶ c}
    (η : f₁ ⟶ f₂) (η' : f₂ ⟶ f₃) (θ : g₁ ⟶ g₂) (θ' : g₂ ⟶ g₃) :
    bicomp η θ ≫ bicomp η' θ' = bicomp (η ≫ η') (θ ≫ θ') :=
  ((eComp Cat a b c).map_comp (Y := (_, _)) (_, _) (_, _)).symm

instance : Category (CatEnriched C) where
  id_comp {X Y} f := congrArg (·.obj f) (e_id_comp (V := Cat) X Y)
  comp_id {X Y} f := congrArg (·.obj f) (e_comp_id (V := Cat) X Y)
  assoc {X Y Z W} f g h := congrArg (·.obj (f, g, h)) (e_assoc (V := Cat) X Y Z W)

theorem id_bicomp_heq {a b : CatEnriched C} {f f' : a ⟶ b} (η : f ⟶ f') :
    HEq (bicomp (𝟙 (𝟙 a)) η) η := by
  rw [id_eq, ← Functor.map_id]
  exact congr_arg_heq (·.map η) (e_id_comp (V := Cat) a b)

theorem id_bicomp {a b : CatEnriched C} {f f' : a ⟶ b} (η : f ⟶ f') :
    bicomp (𝟙 (𝟙 a)) η = eqToHom (id_comp f) ≫ η ≫ eqToHom (id_comp f').symm := by
  simp [← heq_eq_eq, id_bicomp_heq]

theorem bicomp_id_heq {a b : CatEnriched C} {f f' : a ⟶ b} (η : f ⟶ f') :
    HEq (bicomp η (𝟙 (𝟙 b))) η := by
  rw [id_eq, ← Functor.map_id]
  exact congr_arg_heq (·.map η) (e_comp_id (V := Cat) a b)

theorem bicomp_id {a b : CatEnriched C} {f f' : a ⟶ b} (η : f ⟶ f') :
    bicomp η (𝟙 (𝟙 b)) = eqToHom (comp_id f) ≫ η ≫ eqToHom (comp_id f').symm := by
  simp [← heq_eq_eq, bicomp_id_heq]

theorem bicomp_assoc_heq {a b c d : CatEnriched C} {f f' : a ⟶ b} {g g' : b ⟶ c} {h h' : c ⟶ d}
    (η : f ⟶ f') (θ : g ⟶ g') (κ : h ⟶ h') :
    HEq (bicomp (bicomp η θ) κ) (bicomp η (bicomp θ κ)) :=
  congr_arg_heq (·.map (X := (_, _, _)) (Y := (_, _, _)) (η, θ, κ)) (e_assoc (V := Cat) a b c d)

theorem bicomp_assoc {a b c d : CatEnriched C} {f f' : a ⟶ b} {g g' : b ⟶ c} {h h' : c ⟶ d}
    (η : f ⟶ f') (θ : g ⟶ g') (κ : h ⟶ h') :
    bicomp (bicomp η θ) κ =
      eqToHom (assoc f g h) ≫ bicomp η (bicomp θ κ) ≫ eqToHom (assoc f' g' h').symm := by
  simp [← heq_eq_eq, bicomp_assoc_heq]

instance : Bicategory (CatEnriched C) where
  homCategory := inferInstance
  whiskerLeft {_ _ _} f {_ _} η := bicomp (𝟙 f) η
  whiskerRight η h := bicomp η (𝟙 h)
  associator f g h := eqToIso (assoc f g h)
  leftUnitor f := eqToIso (id_comp f)
  rightUnitor f := eqToIso (comp_id f)
  whiskerLeft_id := id_bicomp_id
  whiskerLeft_comp := by simp
  id_whiskerLeft := id_bicomp
  comp_whiskerLeft := by simp [← id_bicomp_id, bicomp_assoc]
  id_whiskerRight := id_bicomp_id
  comp_whiskerRight := by simp
  whiskerRight_id := bicomp_id
  whiskerRight_comp := by simp [bicomp_assoc]
  whisker_assoc := by simp [bicomp_assoc]
  whisker_exchange η θ := by simp
  pentagon {a b c d e} f g h i := by
    generalize_proofs h1 h2 h3 h4; revert h1 h2 h3 h4
    generalize (f ≫ g) ≫ h = x, (g ≫ h) ≫ i = w
    rintro rfl _ rfl _; simp
  triangle {a b c} f g := by
    generalize_proofs h1 h2 h3; revert h1 h2 h3
    generalize 𝟙 b ≫ g = g, f ≫ 𝟙 b = f
    rintro _ rfl rfl; simp

instance : Bicategory.Strict (CatEnriched C) where

end CatEnriched

end CategoryTheory
