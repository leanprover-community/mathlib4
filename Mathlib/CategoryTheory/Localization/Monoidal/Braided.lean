/-
Copyright (c) 2025 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Localization.Monoidal.Basic
import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!

# Localization of symmetric monoidal categories

Let `C` be a monoidal category equipped with a class of morphisms `W` which
is compatible with the monoidal category structure. The file
`Mathlib.CategoryTheory.Localization.Monoidal.Basic` constructs a monoidal structure on
the localized on `D` such that the localization functor is monoidal.

In this file we promote this monoidal structure to a braided structure in the case where `C` is
braided, in such a way that the localization functor is braided. If `C` is symmetric monoidal, then
the monoidal structure on `D` is also symmetric.
-/

open CategoryTheory Category MonoidalCategory BraidedCategory

namespace CategoryTheory.Localization.Monoidal

variable {C D : Type*} [Category C] [Category D] (L : C ⥤ D) (W : MorphismProperty C)
  [MonoidalCategory C] [W.IsMonoidal] [L.IsLocalization W]
  {unit : D} (ε : L.obj (𝟙_ C) ≅ unit)

local notation "L'" => toMonoidalCategory L W ε

instance : (L').IsLocalization W := inferInstanceAs (L.IsLocalization W)

section Braided

variable [BraidedCategory C]

noncomputable instance : Lifting₂ L' L' W W ((curriedTensor C).flip ⋙ (whiskeringRight C C
    (LocalizedMonoidal L W ε)).obj L') (tensorBifunctor L W ε).flip :=
  inferInstanceAs (Lifting₂ L' L' W W (((curriedTensor C) ⋙ (whiskeringRight C C
    (LocalizedMonoidal L W ε)).obj L')).flip (tensorBifunctor L W ε).flip )

/-- The braiding on the localized category as a natural isomorphism of bifunctors. -/
noncomputable def braidingNatIso : tensorBifunctor L W ε ≅ (tensorBifunctor L W ε).flip :=
  lift₂NatIso L' L' W W
    ((curriedTensor C) ⋙ (whiskeringRight C C
      (LocalizedMonoidal L W ε)).obj L')
    (((curriedTensor C).flip ⋙ (whiskeringRight C C
      (LocalizedMonoidal L W ε)).obj L'))
    _ _  (isoWhiskerRight (curriedBraidingNatIso C) _)

lemma braidingNatIso_hom_app (X Y : C) :
    ((braidingNatIso L W ε).hom.app ((L').obj X)).app ((L').obj Y) =
      (Functor.LaxMonoidal.μ (L') X Y) ≫
        (L').map (β_ X Y).hom ≫
          (Functor.OplaxMonoidal.δ (L') Y X) := by
  simp [braidingNatIso, lift₂NatIso]
  rfl

lemma braidingNatIso_hom_μ_left (X Y Z : C) :
    ((braidingNatIso L W ε).hom.app ((L').obj X)).app ((L').obj Y ⊗ (L').obj Z)
      ≫ (Functor.LaxMonoidal.μ (L') Y Z) ▷ (L').obj X =
        (L').obj X ◁ (Functor.LaxMonoidal.μ (L') Y Z) ≫
          ((braidingNatIso L W ε).hom.app ((L').obj X)).app ((L').obj (Y ⊗ Z)) := by
  erw [← ((braidingNatIso L W ε).hom.app ((L').obj X)).naturality
    ((Functor.LaxMonoidal.μ (L') Y Z))]
  rfl

lemma braidingNatIso_hom_μ_right (X Y Z : C) :
    ((braidingNatIso L W ε).hom.app ((L').obj X ⊗ (L').obj Y)).app ((L').obj Z)
      ≫ (L').obj Z ◁ (Functor.LaxMonoidal.μ (L') X Y) =
        (Functor.LaxMonoidal.μ (L') X Y) ▷ (L').obj Z ≫
          ((braidingNatIso L W ε).hom.app ((L').obj (X ⊗ Y))).app ((L').obj Z) := by
  have := NatTrans.congr_app
    ((braidingNatIso L W ε).hom.naturality ((Functor.LaxMonoidal.μ (L') X Y))) ((L').obj Z)
  dsimp [Functor.flip] at this
  erw [← this]
  rfl

@[reassoc]
lemma braiding_naturality {X X' Y Y' : LocalizedMonoidal L W ε} (f : X ⟶ Y) (g : X' ⟶ Y') :
    (f ⊗ g) ≫ ((braidingNatIso L W ε).hom.app Y).app Y' =
      ((braidingNatIso L W ε).hom.app X).app X' ≫ (g ⊗ f) := by
  rw [← id_comp f, ← comp_id g, tensor_comp, id_tensorHom, tensorHom_id,
    tensor_comp, id_tensorHom, tensorHom_id, ← assoc]
  erw [← ((braidingNatIso L W ε).app _).hom.naturality g]
  simp only [assoc]
  congr 1
  exact NatTrans.congr_app ((braidingNatIso L W ε).hom.naturality f) Y'

lemma map_hexagon_forward (X Y Z : C) :
    (α_ ((L').obj X) ((L').obj Y) ((L').obj Z)).hom ≫
      (((braidingNatIso L W ε).app ((L').obj X)).app (((L').obj Y) ⊗ ((L').obj Z))).hom ≫
        (α_ ((L').obj Y) ((L').obj Z) ((L').obj X)).hom =
      (((braidingNatIso L W ε).app ((L').obj X)).app ((L').obj Y)).hom ▷ ((L').obj Z) ≫
        (α_ ((L').obj Y) ((L').obj X) ((L').obj Z)).hom ≫
        ((L').obj Y) ◁ (((braidingNatIso L W ε).app ((L').obj X)).app ((L').obj Z)).hom := by
  simp only [associator_hom, Iso.app_hom, braidingNatIso_hom_app]
  slice_rhs 0 4 =>
    simp only [Functor.flip_obj_obj, Functor.CoreMonoidal.toMonoidal_toLaxMonoidal,
      Functor.CoreMonoidal.toMonoidal_toOplaxMonoidal, comp_whiskerRight, assoc,
      Functor.Monoidal.whiskerRight_δ_μ_assoc, Functor.LaxMonoidal.μ_natural_left]
  simp only [assoc]
  congr 2
  slice_rhs 3 6 =>
    simp only [Functor.flip_obj_obj, Functor.CoreMonoidal.toMonoidal_toOplaxMonoidal,
      Functor.CoreMonoidal.toMonoidal_toLaxMonoidal, MonoidalCategory.whiskerLeft_comp,
      Functor.Monoidal.whiskerLeft_δ_μ_assoc, Functor.OplaxMonoidal.δ_natural_right_assoc]
  simp only [← assoc]
  slice_lhs 4 5 =>
    rw [braidingNatIso_hom_μ_left, braidingNatIso_hom_app]
  simp

lemma map_hexagon_reverse (X Y Z : C) :
    (α_ ((L').obj X) ((L').obj Y) ((L').obj Z)).inv ≫
      (((braidingNatIso L W ε).app ((L').obj X ⊗ (L').obj Y)).app ((L').obj Z)).hom ≫
        (α_ ((L').obj Z) ((L').obj X) ((L').obj Y)).inv =
      ((L').obj X) ◁ (((braidingNatIso L W ε).app ((L').obj Y)).app ((L').obj Z)).hom ≫
        (α_ ((L').obj X) ((L').obj Z) ((L').obj Y)).inv ≫
        (((braidingNatIso L W ε).app ((L').obj X)).app ((L').obj Z)).hom ▷ ((L').obj Y) := by
  simp only [associator_inv, Iso.app_hom, braidingNatIso_hom_app]
  slice_rhs 0 3 =>
    simp only [Functor.flip_obj_obj, Functor.CoreMonoidal.toMonoidal_toLaxMonoidal,
      Functor.CoreMonoidal.toMonoidal_toOplaxMonoidal, MonoidalCategory.whiskerLeft_comp, assoc,
      Functor.Monoidal.whiskerLeft_δ_μ, comp_id]
  simp only [assoc]
  congr 1
  slice_rhs 4 7 =>
    simp only [Functor.flip_obj_obj, Functor.CoreMonoidal.toMonoidal_toOplaxMonoidal,
      Functor.CoreMonoidal.toMonoidal_toLaxMonoidal, comp_whiskerRight,
      Functor.Monoidal.whiskerRight_δ_μ_assoc, Functor.OplaxMonoidal.δ_natural_left_assoc]
  simp only [← assoc]
  congr 2
  slice_rhs 0 3 =>
    simp only [Functor.CoreMonoidal.toMonoidal_toLaxMonoidal,
      Functor.LaxMonoidal.μ_natural_right_assoc]
  simp only [assoc]
  congr 1
  slice_lhs 4 5 =>
    rw [braidingNatIso_hom_μ_right, braidingNatIso_hom_app]
  simp

noncomputable instance : BraidedCategory (LocalizedMonoidal L W ε) where
  braiding X Y := ((braidingNatIso L W ε).app X).app Y
  braiding_naturality_right X Y Z f := ((braidingNatIso L W ε).app X).hom.naturality f
  braiding_naturality_left {X Y} f Z :=
    NatTrans.congr_app ((braidingNatIso L W ε).hom.naturality f) Z
  hexagon_forward X Y Z := by
    obtain ⟨x, ⟨eX⟩⟩ : ∃ x, Nonempty ((L').obj x ≅ X) := ⟨_, ⟨(L').objObjPreimageIso X⟩⟩
    obtain ⟨y, ⟨eY⟩⟩ : ∃ x, Nonempty ((L').obj x ≅ Y) := ⟨_, ⟨(L').objObjPreimageIso Y⟩⟩
    obtain ⟨z, ⟨eZ⟩⟩ : ∃ x, Nonempty ((L').obj x ≅ Z) := ⟨_, ⟨(L').objObjPreimageIso Z⟩⟩
    suffices (α_ ((L').obj x) ((L').obj y) ((L').obj z)).hom ≫
        (((braidingNatIso L W ε).app ((L').obj x)).app (((L').obj y) ⊗ ((L').obj z))).hom ≫
          (α_ ((L').obj y) ((L').obj z) ((L').obj x)).hom =
        (((braidingNatIso L W ε).app ((L').obj x)).app ((L').obj y)).hom ▷ ((L').obj z) ≫
          (α_ ((L').obj y) ((L').obj x) ((L').obj z)).hom ≫
          ((L').obj y) ◁ (((braidingNatIso L W ε).app ((L').obj x)).app ((L').obj z)).hom by
      refine Eq.trans ?_ ((((eX.inv ⊗ eY.inv) ⊗ eZ.inv) ≫= this =≫
        (eY.hom ⊗ eZ.hom ⊗ eX.hom)).trans ?_)
      · simp only [Iso.app_hom, associator_conjugation, Functor.flip_obj_obj, assoc,
          Iso.inv_hom_id_assoc, Iso.cancel_iso_hom_left]
        rw [← Iso.eq_comp_inv]
        simp [← associator_conjugation, ← braiding_naturality, ← whiskerLeft_comp_assoc]
      · simp only [Functor.flip_obj_obj, Iso.app_hom, assoc, ← tensorHom_id]
        simp only [← assoc]
        rw [← tensor_comp, braiding_naturality]
        simp only [Functor.flip_obj_obj, comp_id, assoc]
        rw [← id_comp eZ.inv, tensor_comp, tensorHom_id]
        rw [← id_tensorHom, ← tensor_comp, ← braiding_naturality]
        simp [← whiskerLeft_comp_assoc]
    exact map_hexagon_forward L W ε x y z
  hexagon_reverse X Y Z := by
    obtain ⟨x, ⟨eX⟩⟩ : ∃ x, Nonempty ((L').obj x ≅ X) := ⟨_, ⟨(L').objObjPreimageIso X⟩⟩
    obtain ⟨y, ⟨eY⟩⟩ : ∃ x, Nonempty ((L').obj x ≅ Y) := ⟨_, ⟨(L').objObjPreimageIso Y⟩⟩
    obtain ⟨z, ⟨eZ⟩⟩ : ∃ x, Nonempty ((L').obj x ≅ Z) := ⟨_, ⟨(L').objObjPreimageIso Z⟩⟩
    suffices (α_ ((L').obj x) ((L').obj y) ((L').obj z)).inv ≫
        (((braidingNatIso L W ε).app ((L').obj x ⊗ (L').obj y)).app ((L').obj z)).hom ≫
          (α_ ((L').obj z) ((L').obj x) ((L').obj y)).inv =
        ((L').obj x) ◁ (((braidingNatIso L W ε).app ((L').obj y)).app ((L').obj z)).hom ≫
          (α_ ((L').obj x) ((L').obj z) ((L').obj y)).inv ≫
          (((braidingNatIso L W ε).app ((L').obj x)).app ((L').obj z)).hom ▷ ((L').obj y)  by
      refine Eq.trans ?_ (((eX.inv ⊗ (eY.inv ⊗ eZ.inv)) ≫= this =≫
        ((eZ.hom ⊗ eX.hom) ⊗ eY.hom)).trans ?_)
      · simp [← braiding_naturality_assoc, ← whiskerLeft_comp_assoc]
      · simp only [Functor.flip_obj_obj, Iso.app_hom, assoc, ← id_tensorHom]
        rw [← tensor_comp_assoc, braiding_naturality]
        simp only [comp_id, Functor.flip_obj_obj, assoc, associator_conjugation,
          MonoidalCategory.id_tensorHom]
        rw [← id_comp eX.inv, tensor_comp, id_tensorHom]
        simp only [← associator_conjugation]
        rw [← tensorHom_id, ← tensor_comp, ← braiding_naturality]
        simp only [Functor.flip_obj_obj, id_comp]
        rw [← comp_id eY.hom, tensor_comp, tensorHom_id]
        simp only [associator_conjugation, assoc, Iso.inv_hom_id_assoc, inv_hom_id_tensor_assoc,
          MonoidalCategory.id_tensorHom]
        rw [← whiskerLeft_comp_assoc, ← whiskerLeft_comp_assoc]
        simp only [assoc, tensor_inv_hom_id, MonoidalCategory.tensorHom_id, inv_hom_whiskerRight,
          MonoidalCategory.whiskerLeft_comp]
        congr 1
        exact whiskerLeft_id_assoc X _ _
    exact map_hexagon_reverse L W ε x y z

lemma β_hom_app (X Y : C) :
    (β_ ((L').obj X) ((L').obj Y)).hom =
      (Functor.LaxMonoidal.μ (L') X Y) ≫
        (L').map (β_ X Y).hom ≫
          (Functor.OplaxMonoidal.δ (L') Y X) :=
  braidingNatIso_hom_app L W ε X Y

noncomputable instance : (toMonoidalCategory L W ε).Braided where
  braided X Y := by simp [β_hom_app]

end Braided

section Symmetric

variable [SymmetricCategory C]

noncomputable instance : SymmetricCategory (LocalizedMonoidal L W ε) where
  toBraidedCategory := inferInstance
  symmetry X Y := by
    obtain ⟨x, ⟨eX⟩⟩ : ∃ x, Nonempty ((L').obj x ≅ X) := ⟨_, ⟨(L').objObjPreimageIso X⟩⟩
    obtain ⟨y, ⟨eY⟩⟩ : ∃ x, Nonempty ((L').obj x ≅ Y) := ⟨_, ⟨(L').objObjPreimageIso Y⟩⟩
    suffices (β_ ((L').obj x) ((L').obj y)).hom ≫ (β_ ((L').obj y) ((L').obj x)).hom = 𝟙 _ by
      refine Eq.trans ?_ (((eX.inv ⊗ eY.inv) ≫= this =≫
        (eX.hom ⊗ eY.hom)).trans ?_)
      all_goals simp
    simp [-Functor.map_braiding, β_hom_app, ← Functor.map_comp_assoc]

end Symmetric

end CategoryTheory.Localization.Monoidal
