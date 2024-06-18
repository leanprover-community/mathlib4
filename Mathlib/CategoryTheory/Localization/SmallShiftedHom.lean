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

namespace Localization

variable {C : Type u₁} [Category.{v₁} C] (W : MorphismProperty C)
  {C' : Type u₂} [Category.{v₂} C'] (W' : MorphismProperty C')
  {D : Type u₃} [Category.{v₃} D]
  {D' : Type u₄} [Category.{v₄} D']
  {M : Type w'} [AddMonoid M] [HasShift C M] [HasShift C' M]
  [W.IsCompatibleWithShift M]
  [W'.IsCompatibleWithShift M] (X Y Z : C)

variable (M) in
abbrev HasSmallLocalizedShiftedHom : Prop :=
  ∀ (m : M), MorphismProperty.HasSmallLocalizedHom.{w} W X (Y⟦m⟧)

def SmallShiftedHom [HasSmallLocalizedShiftedHom.{w} W M X Y] (m : M) : Type w :=
  SmallHom W X (Y⟦m⟧)

namespace SmallShiftedHom

variable {X Y Z}
section

variable [HasSmallLocalizedShiftedHom.{w} W M X Y]

section

variable (L : C ⥤ D) [L.IsLocalization W] [HasShift D M] [L.CommShift M]

noncomputable def equiv {m : M} :
    SmallShiftedHom.{w} W X Y m ≃ ShiftedHom (L.obj X) (L.obj Y) m :=
  (SmallHom.equiv W L).trans ((L.commShiftIso m).app Y).homToEquiv

variable [HasSmallLocalizedShiftedHom.{w} W M Y Z]
  [HasSmallLocalizedShiftedHom.{w} W M X Z]

variable {a b c : M} (f : SmallShiftedHom.{w} W X Y a)
  (g : SmallShiftedHom.{w} W Y Z b) (h : b + a = c)

noncomputable def comp' : SmallShiftedHom.{w} W X Z c :=
  (equiv W L).symm ((equiv W L f).comp (equiv W L g) h)


end

variable [HasSmallLocalizedShiftedHom.{w} W M Y Z]
  [HasSmallLocalizedShiftedHom.{w} W M X Z]

variable {a b c : M} (f : SmallShiftedHom.{w} W X Y a)
  (g : SmallShiftedHom.{w} W Y Z b) (h : b + a = c)

noncomputable def comp : SmallShiftedHom.{w} W X Z c :=
  comp' W W.Q f g h

end

section

variable {W W'}

section

noncomputable def map' [HasSmallLocalizedShiftedHom.{w} W M X Y]
    {a : M} (f : SmallShiftedHom.{w} W X Y a)
    (Φ : LocalizerMorphism W W')
    [HasSmallLocalizedShiftedHom.{w} W' M (Φ.functor.obj X) (Φ.functor.obj Y)]
    (L : C ⥤ D) [L.IsLocalization W] [HasShift D M] [L.CommShift M]
    (L' : C' ⥤ D') [L'.IsLocalization W'] [HasShift D' M] [L'.CommShift M]
    (G : D ⥤ D') [G.CommShift M] (e : Φ.functor ⋙ L' ≅ L ⋙ G) :
    SmallShiftedHom.{w} W' (Φ.functor.obj X) (Φ.functor.obj Y) a :=
  (equiv W' L').symm
    ((ShiftedHom.mk₀ (0 : M) rfl (e.hom.app X)).comp
      (((equiv W L f).map G).comp
      (ShiftedHom.mk₀ (0 : M) rfl (e.inv.app Y)) (zero_add a)) (add_zero a))

noncomputable def map [HasSmallLocalizedShiftedHom.{w} W M X Y]
    {a : M} (f : SmallShiftedHom.{w} W X Y a)
    (Φ : LocalizerMorphism W W')
    [HasSmallLocalizedShiftedHom.{w} W' M (Φ.functor.obj X) (Φ.functor.obj Y)] :
    SmallShiftedHom.{w} W' (Φ.functor.obj X) (Φ.functor.obj Y) a := by
  have : (Φ.localizedFunctor W.Q W'.Q).CommShift M := sorry
  exact f.map' Φ W.Q W'.Q (Φ.localizedFunctor W.Q W'.Q)
    (CatCommSq.iso _ _ _ _)

-- TODO: show that `comp'` and `map'` do not depend on `L`, `L'`, etc.

end

end

end SmallShiftedHom

end Localization

end CategoryTheory
