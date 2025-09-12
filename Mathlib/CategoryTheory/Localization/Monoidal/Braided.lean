/-
Copyright (c) 2025 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Localization.Monoidal.Basic
import Mathlib.CategoryTheory.Monoidal.Braided.Multifunctor

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

open CategoryTheory Category MonoidalCategory BraidedCategory Functor

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
    (f ⊗ₘ g) ≫ ((braidingNatIso L W ε).hom.app Y).app Y' =
      ((braidingNatIso L W ε).hom.app X).app X' ≫ (g ⊗ₘ f) := by
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

noncomputable instance : BraidedCategory (LocalizedMonoidal L W ε) := by
  refine .ofBifunctor (braidingNatIso L W ε) ?_ ?_
  · apply natTrans₃_ext (L') (L') (L') W W W
    intro X Y Z
    simpa using map_hexagon_forward _ _ _ _ _ _
  · apply natTrans₃_ext (L') (L') (L') W W W
    intro X Y Z
    simpa using map_hexagon_reverse _ _ _ _ _ _

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
  symmetry := by
    suffices
        (braidingNatIso L W ε).hom ≫ (flipFunctor _ _ _).map (braidingNatIso L W ε).hom = 𝟙 _ by
      intro X Y
      exact NatTrans.congr_app (NatTrans.congr_app this X) Y
    apply natTrans₂_ext (L') (L') W W
    intro X Y
    change (β_ ((L').obj X) ((L').obj Y)).hom ≫ (β_ ((L').obj Y) ((L').obj X)).hom = 𝟙 _
    simp [-Functor.map_braiding, β_hom_app, ← Functor.map_comp_assoc]

end Symmetric

end CategoryTheory.Localization.Monoidal
