/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Localization.Monoidal.Basic
public import Mathlib.CategoryTheory.Monoidal.Linear

/-!
# Additive and linear monoidal localization
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Functor.Monoidal

namespace CategoryTheory.Localization.Monoidal

variable {C D : Type*} [Category C] [Category D] (L : C ⥤ D) (W : MorphismProperty C)
  [MonoidalCategory C]

variable [W.IsMonoidal] [L.IsLocalization W] {unit : D} (ε : L.obj (𝟙_ C) ≅ unit)

local notation "L'" => toMonoidalCategory L W ε

variable [Preadditive C] [MonoidalPreadditive C] [Preadditive D]

instance : Preadditive (LocalizedMonoidal L W ε) := inferInstanceAs (Preadditive D)

instance [L.Additive] : (L').Additive := inferInstanceAs (L.Additive)

lemma monoidalPreadditive [L.Additive] (R : D ⥤ C) [R.Full] [R.Faithful] (adj : L ⊣ R) :
    MonoidalPreadditive (LocalizedMonoidal L W ε) where
  whiskerLeft_zero {X Y Z} := by
    obtain ⟨X', ⟨eX⟩⟩ : ∃ X₁, Nonempty ((L').obj X₁ ≅ X) := ⟨_, ⟨(L').objObjPreimageIso X⟩⟩
    obtain ⟨Y', ⟨eY⟩⟩ : ∃ X₁, Nonempty ((L').obj X₁ ≅ Y) := ⟨_, ⟨(L').objObjPreimageIso Y⟩⟩
    obtain ⟨Z', ⟨eZ⟩⟩ : ∃ X₁, Nonempty ((L').obj X₁ ≅ Z) := ⟨_, ⟨(L').objObjPreimageIso Z⟩⟩
    suffices (L').obj X' ◁ (0 : (L').obj Y' ⟶ (L').obj Z') = 0 by
      refine Eq.trans ?_ (((eX.inv ⊗ₘ eY.inv) ≫= this =≫ (eX.hom ⊗ₘ eZ.hom)).trans ?_)
      · rw [← id_tensorHom, ← id_tensorHom, ← tensor_comp, ← tensor_comp]
        simp
      · simp
    rw [← Functor.PreservesZeroMorphisms.map_zero, map_whiskerLeft']
    simp
  zero_whiskerRight {X Y Z} := by
    obtain ⟨X', ⟨eX⟩⟩ : ∃ X₁, Nonempty ((L').obj X₁ ≅ X) := ⟨_, ⟨(L').objObjPreimageIso X⟩⟩
    obtain ⟨Y', ⟨eY⟩⟩ : ∃ X₁, Nonempty ((L').obj X₁ ≅ Y) := ⟨_, ⟨(L').objObjPreimageIso Y⟩⟩
    obtain ⟨Z', ⟨eZ⟩⟩ : ∃ X₁, Nonempty ((L').obj X₁ ≅ Z) := ⟨_, ⟨(L').objObjPreimageIso Z⟩⟩
    suffices (0 : (L').obj Y' ⟶ (L').obj Z') ▷ (L').obj X' = 0 by
      refine Eq.trans ?_ (((eY.inv ⊗ₘ eX.inv) ≫= this =≫ (eZ.hom ⊗ₘ eX.hom)).trans ?_)
      · rw [← tensorHom_id, ← tensorHom_id, ← tensor_comp, ← tensor_comp]
        simp
      · simp
    rw [← Functor.PreservesZeroMorphisms.map_zero, map_whiskerRight']
    simp
  whiskerLeft_add {X Y Z} f g := by
    let eX : (L').obj (R.obj X) ≅ X := (asIso adj.counit).app X
    let eY : (L').obj (R.obj Y) ≅ Y := (asIso adj.counit).app Y
    let eZ : (L').obj (R.obj Z) ≅ Z := (asIso adj.counit).app Z
    suffices (L').obj (R.obj X) ◁ ((L').map (R.map f) + (L').map (R.map g)) =
        ((L').obj (R.obj X) ◁ (L').map (R.map f)) + ((L').obj (R.obj X) ◁ (L').map (R.map g)) by
      refine Eq.trans ?_ (((eX.inv ⊗ₘ eY.inv) ≫= this =≫ (eX.hom ⊗ₘ eZ.hom)).trans ?_)
      · rw [← id_tensorHom, ← id_tensorHom, ← tensor_comp_assoc, ← Functor.map_add, ← tensor_comp]
        simp [eZ, eY, toMonoidalCategory]
      · rw [← id_tensorHom, ← id_tensorHom, ← id_tensorHom,
          CategoryTheory.Preadditive.comp_add_assoc, ← tensor_comp, ← tensor_comp,
          CategoryTheory.Preadditive.add_comp, ← tensor_comp, ← tensor_comp]
        simp [eY, eZ, toMonoidalCategory]
    rw [← Functor.map_add, map_whiskerLeft', map_whiskerLeft', map_whiskerLeft' (F := L')]
    simp
  add_whiskerRight {X Y Z} f g := by
    let eX : (L').obj (R.obj X) ≅ X := (asIso adj.counit).app X
    let eY : (L').obj (R.obj Y) ≅ Y := (asIso adj.counit).app Y
    let eZ : (L').obj (R.obj Z) ≅ Z := (asIso adj.counit).app Z
    suffices  ((L').map (R.map f) + (L').map (R.map g)) ▷ (L').obj (R.obj X) =
        ((L').map (R.map f)) ▷ (L').obj (R.obj X) + ((L').map (R.map g) ▷ (L').obj (R.obj X)) by
      refine Eq.trans ?_ (((eY.inv ⊗ₘ eX.inv) ≫= this =≫ (eZ.hom ⊗ₘ eX.hom)).trans ?_)
      · rw [← tensorHom_id, ← tensorHom_id, ← tensor_comp_assoc, ← Functor.map_add, ← tensor_comp]
        simp [eZ, eY, toMonoidalCategory]
      · rw [← tensorHom_id, ← tensorHom_id, ← tensorHom_id,
          CategoryTheory.Preadditive.comp_add_assoc, ← tensor_comp, ← tensor_comp,
          CategoryTheory.Preadditive.add_comp, ← tensor_comp, ← tensor_comp]
        simp [eY, eZ, toMonoidalCategory]
    rw [← Functor.map_add, map_whiskerRight', map_whiskerRight', map_whiskerRight' (F := L')]
    simp

lemma monoidalLinear (A : Type u) [Ring A] [L.Additive] (R : D ⥤ C) [R.Full] [R.Faithful]
    (adj : L ⊣ R) [Linear A D] [Linear A C] [L.Linear A]
    [MonoidalLinear A C] :
    @MonoidalLinear A _ (LocalizedMonoidal L W ε) _ _ (inferInstanceAs (Linear A D)) _
      (monoidalPreadditive L W ε R adj) := by
  have := monoidalPreadditive L W ε R adj
  let : Linear A (LocalizedMonoidal L W ε) := inferInstanceAs (Linear A D)
  let : (L').Linear A := inferInstanceAs (L.Linear A)
  refine ⟨?_, ?_⟩
  · intro X Y Z r f
    let eX : (L').obj (R.obj X) ≅ X := (asIso adj.counit).app X
    let eY : (L').obj (R.obj Y) ≅ Y := (asIso adj.counit).app Y
    let eZ : (L').obj (R.obj Z) ≅ Z := (asIso adj.counit).app Z
    suffices ((L').obj (R.obj X)) ◁ (r • (L').map (R.map f)) =
        r • ((L').obj (R.obj X)) ◁ ((L').map (R.map f)) by
      refine Eq.trans ?_ (((eX.inv ⊗ₘ eY.inv) ≫= this =≫ (eX.hom ⊗ₘ eZ.hom)).trans ?_)
      · rw [← id_tensorHom, ← id_tensorHom, ← tensor_comp_assoc, ← Functor.map_smul, ← tensor_comp]
        simp [eZ, eY, toMonoidalCategory]
      · simp [eX, eY, eZ, toMonoidalCategory, ← MonoidalCategory.id_tensorHom]
    rw [← Functor.map_smul, map_whiskerLeft', map_whiskerLeft']
    simp
  · intro r Y Z f X
    let eX : (L').obj (R.obj X) ≅ X := (asIso adj.counit).app X
    let eY : (L').obj (R.obj Y) ≅ Y := (asIso adj.counit).app Y
    let eZ : (L').obj (R.obj Z) ≅ Z := (asIso adj.counit).app Z
    suffices (r • (L').map (R.map f)) ▷ ((L').obj (R.obj X)) =
        r • ((L').map (R.map f)) ▷ ((L').obj (R.obj X)) by
      refine Eq.trans ?_ (((eY.inv ⊗ₘ eX.inv) ≫= this =≫ (eZ.hom ⊗ₘ eX.hom)).trans ?_)
      · rw [← tensorHom_id, ← tensorHom_id, ← tensor_comp_assoc, ← Functor.map_smul, ← tensor_comp]
        simp [eZ, eY, toMonoidalCategory]
      · simp [eX, eY, eZ, toMonoidalCategory, ← MonoidalCategory.tensorHom_id]
    rw [← Functor.map_smul, map_whiskerRight', map_whiskerRight']
    simp

end CategoryTheory.Localization.Monoidal
