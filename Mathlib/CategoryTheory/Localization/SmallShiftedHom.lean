/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Localization.LocalizerMorphism
import Mathlib.CategoryTheory.Localization.SmallHom
import Mathlib.CategoryTheory.Shift.ShiftedHom
import Mathlib.CategoryTheory.Shift.Localization

universe w w' v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory

open Category

variable {C : Type u₁} [Category.{v₁} C] (W : MorphismProperty C)
  {C' : Type u₂} [Category.{v₂} C'] (W' : MorphismProperty C')
  {D : Type u₃} [Category.{v₃} D]
  {D' : Type u₄} [Category.{v₄} D']
  {M : Type w'} [AddMonoid M] [HasShift C M] [HasShift C' M] [HasShift D M]
  [W.IsCompatibleWithShift M] [W'.IsCompatibleWithShift M]

namespace MorphismProperty

variable (X Y : C)

variable (M) in
abbrev HasSmallLocalizedShiftedHom : Prop :=
  ∀ (a b : M), HasSmallLocalizedHom.{w} W (X⟦a⟧) (Y⟦b⟧)

variable [HasSmallLocalizedShiftedHom.{w} W M X Y]

variable (M) in
lemma hasSmallLocalizedHom_of_hasSmallLocalizedShiftedHom₀ :
    HasSmallLocalizedHom.{w} W X Y :=
  (hasSmallLocalizedHom_iff_of_isos W
    ((shiftFunctorZero C M).app X) ((shiftFunctorZero C M).app Y)).1 inferInstance

instance hasSmallLocalizedHom_of_hasSmallLocalizedShiftedHom₁ (m : M) :
    HasSmallLocalizedHom.{w} W X (Y⟦m⟧) :=
  (hasSmallLocalizedHom_iff_of_isos W
    ((shiftFunctorZero C M).app X) (Iso.refl (Y⟦m⟧))).1 inferInstance

instance hasSmallLocalizedHom_of_hasSmallLocalizedShiftedHom₂ (m m' n : M) :
    HasSmallLocalizedHom.{w} W (X⟦m⟧⟦m'⟧) (Y⟦n⟧) :=
  (hasSmallLocalizedHom_iff_of_isos W
    ((shiftFunctorAdd C m m').app X) (Iso.refl (Y⟦n⟧))).1 inferInstance

instance hasSmallLocalizedHom_of_hasSmallLocalizedShiftedHom₃ (m n n' : M) :
    HasSmallLocalizedHom.{w} W (X⟦m⟧) (Y⟦n⟧⟦n'⟧) :=
  (hasSmallLocalizedHom_iff_of_isos W
    (Iso.refl (X⟦m⟧)) ((shiftFunctorAdd C n n').app Y)).1 inferInstance

instance hasSmallLocalizedHom_of_hasSmallLocalizedShiftedHom₄ (m : M) :
    HasSmallLocalizedHom.{w} W (X⟦m⟧) Y :=
  (hasSmallLocalizedHom_iff_of_isos W
    (Iso.refl (X⟦m⟧)) ((shiftFunctorZero C M).app Y)).1 inferInstance

end MorphismProperty

namespace Localization

namespace SmallHom

variable {W}
variable (L : C ⥤ D) [L.IsLocalization W] [L.CommShift M]
variable {X Y : C} [MorphismProperty.HasSmallLocalizedHom.{w} W X Y]
    (f : SmallHom.{w} W X Y) (a : M) [MorphismProperty.HasSmallLocalizedHom.{w} W (X⟦a⟧) (Y⟦a⟧)]

noncomputable def shift : SmallHom.{w} W (X⟦a⟧) (Y⟦a⟧) :=
  f.map (LocalizerMorphism.mk (shiftFunctor C a)
    (by rw [MorphismProperty.IsCompatibleWithShift.condition]))

lemma equiv_shift : equiv W L (f.shift a) =
    (L.commShiftIso a).hom.app X ≫ (equiv W L f)⟦a⟧' ≫ (L.commShiftIso a).inv.app Y :=
  equiv_map (LocalizerMorphism.mk (shiftFunctor C a) _) _ _ _ (L.commShiftIso a) f

end SmallHom

def SmallShiftedHom (X Y : C)
    [MorphismProperty.HasSmallLocalizedShiftedHom.{w} W M X Y] (m : M) : Type w :=
  SmallHom W X (Y⟦m⟧)

namespace SmallShiftedHom

section

variable {W}
variable {X Y Z : C}

noncomputable def shift {a : M} [MorphismProperty.HasSmallLocalizedShiftedHom.{w} W M X Y]
    [MorphismProperty.HasSmallLocalizedShiftedHom.{w} W M Y Y]
  (f : SmallShiftedHom.{w} W X Y a) (n a' : M) (h : a + n = a') :
    SmallHom.{w} W (X⟦n⟧) (Y⟦a'⟧) :=
  (SmallHom.shift f n).comp (SmallHom.mk W ((shiftFunctorAdd' C a n a' h).inv.app Y))

noncomputable def comp {a b c : M} [MorphismProperty.HasSmallLocalizedShiftedHom.{w} W M X Y]
    [MorphismProperty.HasSmallLocalizedShiftedHom.{w} W M Y Z]
    [MorphismProperty.HasSmallLocalizedShiftedHom.{w} W M X Z]
    [MorphismProperty.HasSmallLocalizedShiftedHom.{w} W M Z Z]
    (f : SmallShiftedHom.{w} W X Y a) (g : SmallShiftedHom.{w} W Y Z b) (h : b + a = c) :
    SmallShiftedHom.{w} W X Z c :=
  SmallHom.comp f (g.shift a c h)

noncomputable def equiv₀ [MorphismProperty.HasSmallLocalizedShiftedHom.{w} W M X Y]
    [MorphismProperty.HasSmallLocalizedShiftedHom.{w} W M Y Y] :
    SmallShiftedHom.{w} W X Y (0 : M) ≃
      letI := W.hasSmallLocalizedHom_of_hasSmallLocalizedShiftedHom₀ M X Y; SmallHom.{w} W X Y :=
  letI := W.hasSmallLocalizedHom_of_hasSmallLocalizedShiftedHom₀ M X Y
  letI := W.hasSmallLocalizedHom_of_hasSmallLocalizedShiftedHom₀ M Y Y
  { toFun := fun f ↦ SmallHom.comp f (SmallHom.mk W ((shiftFunctorZero C M).hom.app Y))
    invFun := fun g ↦ SmallHom.comp g (SmallHom.mk W ((shiftFunctorZero C M).inv.app Y))
    left_inv := fun f ↦ by simp [SmallHom.mk_comp_mk]
    right_inv := fun g ↦ by simp [SmallHom.mk_comp_mk] }

end

section

variable (L : C ⥤ D) [L.IsLocalization W] [HasShift D M] [L.CommShift M]
  {X Y Z T : C}

noncomputable def equiv [MorphismProperty.HasSmallLocalizedShiftedHom.{w} W M X Y] {m : M} :
    SmallShiftedHom.{w} W X Y m ≃ ShiftedHom (L.obj X) (L.obj Y) m :=
  (SmallHom.equiv W L).trans ((L.commShiftIso m).app Y).homToEquiv

lemma equiv_shift' {a : M} [MorphismProperty.HasSmallLocalizedShiftedHom.{w} W M X Y]
    [MorphismProperty.HasSmallLocalizedShiftedHom.{w} W M Y Y]
    (f : SmallShiftedHom.{w} W X Y a) (n a' : M) (h : a + n = a') :
    SmallHom.equiv W L (f.shift n a' h) = (L.commShiftIso n).hom.app X ≫
        (SmallHom.equiv W L f)⟦n⟧' ≫ ((L.commShiftIso a).hom.app Y)⟦n⟧' ≫
        (shiftFunctorAdd' D a n a' h).inv.app (L.obj Y) ≫ (L.commShiftIso a').inv.app Y := by
  simp only [shift, SmallHom.equiv_comp, SmallHom.equiv_shift, SmallHom.equiv_mk, assoc,
    L.commShiftIso_add' h, Functor.CommShift.isoAdd'_inv_app, Iso.inv_hom_id_app_assoc,
    ← Functor.map_comp_assoc, Iso.hom_inv_id_app, Functor.comp_obj, comp_id]

lemma equiv_shift {a : M} [MorphismProperty.HasSmallLocalizedShiftedHom.{w} W M X Y]
    [MorphismProperty.HasSmallLocalizedShiftedHom.{w} W M Y Y]
    (f : SmallShiftedHom.{w} W X Y a) (n a' : M) (h : a + n = a') :
    equiv W L (f.shift n a' h) = (L.commShiftIso n).hom.app X ≫ (equiv W L f)⟦n⟧' ≫
      (shiftFunctorAdd' D a n a' h).inv.app (L.obj Y) := by
  dsimp [equiv]
  erw [Iso.homToEquiv_apply, Iso.homToEquiv_apply, equiv_shift']
  simp only [Functor.comp_obj, Iso.app_hom, assoc, Iso.inv_hom_id_app, comp_id, Functor.map_comp]
  rfl

lemma equiv_comp [MorphismProperty.HasSmallLocalizedShiftedHom.{w} W M X Y]
    [MorphismProperty.HasSmallLocalizedShiftedHom.{w} W M Y Z]
    [MorphismProperty.HasSmallLocalizedShiftedHom.{w} W M X Z]
    [MorphismProperty.HasSmallLocalizedShiftedHom.{w} W M Z Z] {a b c : M}
    (f : SmallShiftedHom.{w} W X Y a) (g : SmallShiftedHom.{w} W Y Z b) (h : b + a = c) :
    equiv W L (f.comp g h) = (equiv W L f).comp (equiv W L g) h := by
  dsimp [comp, equiv, ShiftedHom.comp]
  erw [Iso.homToEquiv_apply, Iso.homToEquiv_apply, Iso.homToEquiv_apply, SmallHom.equiv_comp]
  simp only [equiv_shift', Functor.comp_obj, Iso.app_hom, assoc, Iso.inv_hom_id_app,
    comp_id, Functor.map_comp]
  rfl

end

lemma comp_assoc {X Y Z T : C} {a₁ a₂ a₃ a₁₂ a₂₃ a : M}
    [MorphismProperty.HasSmallLocalizedShiftedHom.{w} W M X Y]
    [MorphismProperty.HasSmallLocalizedShiftedHom.{w} W M X Z]
    [MorphismProperty.HasSmallLocalizedShiftedHom.{w} W M X T]
    [MorphismProperty.HasSmallLocalizedShiftedHom.{w} W M Y Z]
    [MorphismProperty.HasSmallLocalizedShiftedHom.{w} W M Y T]
    [MorphismProperty.HasSmallLocalizedShiftedHom.{w} W M Z T]
    [MorphismProperty.HasSmallLocalizedShiftedHom.{w} W M Z Z]
    [MorphismProperty.HasSmallLocalizedShiftedHom.{w} W M T T]
    (α : SmallShiftedHom.{w} W X Y a₁)
    (β : SmallShiftedHom.{w} W Y Z a₂) (γ : SmallShiftedHom.{w} W Z T a₃)
    (h₁₂ : a₂ + a₁ = a₁₂) (h₂₃ : a₃ + a₂ = a₂₃) (h : a₃ + a₂ + a₁ = a) :
    (α.comp β h₁₂).comp γ (show a₃ + a₁₂ = a by rw [← h₁₂, ← add_assoc, h]) =
      α.comp (β.comp γ h₂₃) (by rw [← h₂₃, h]) := by
  apply (equiv W W.Q).injective
  simp only [equiv_comp, ShiftedHom.comp_assoc _ _ _ h₁₂ h₂₃ h]

end SmallShiftedHom

end Localization

end CategoryTheory
