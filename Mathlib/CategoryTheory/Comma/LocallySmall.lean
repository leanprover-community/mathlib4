/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.EssentiallySmall

/-!
# Comma categories are locally small

We introduce instances showing that the various comma categories
are locally small when the relevant categories that are
involved are locally small.

-/

universe w v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

variable {A : Type u₁} {B : Type u₂} {T : Type u₃}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} T]

instance Comma.locallySmall
    (L : A ⥤ T) (R : B ⥤ T) [LocallySmall.{w} A] [LocallySmall.{w} B] :
    LocallySmall.{w} (Comma L R) where
  hom_small X Y := small_of_injective.{w}
      (f := fun g ↦ (⟨g.left, g.right⟩ : _ × _))
        (fun _ _ _ ↦ by aesop)

instance StructuredArrow.locallySmall (S : T) (T : B ⥤ T)
    [LocallySmall.{w} B] :
    LocallySmall.{w} (StructuredArrow S T) :=
  Comma.locallySmall _ _

instance CostructuredArrow.locallySmall (S : A ⥤ T) (X : T)
    [LocallySmall.{w} A] :
    LocallySmall.{w} (CostructuredArrow S X) :=
  Comma.locallySmall _ _

instance Over.locallySmall (X : T) [LocallySmall.{w} T] :
    LocallySmall.{w} (Over X) :=
  CostructuredArrow.locallySmall _ _

instance Under.locallySmall (X : T) [LocallySmall.{w} T] :
    LocallySmall.{w} (Under X) :=
  StructuredArrow.locallySmall _ _

end CategoryTheory
