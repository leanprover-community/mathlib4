/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.Limits.Creates
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Creation of limits and pullbacks

We show some lemmas relating creation of (co)limits and pullbacks (resp. pushouts).
-/

namespace CategoryTheory.Limits

variable {C : Type*} [Category C] {D : Type*} [Category D]

lemma HasPullback.of_createsLimit (F : C ⥤ D) {X Y S : C} (f : X ⟶ S) (g : Y ⟶ S)
    [CreatesLimit (cospan f g) F] [HasPullback (F.map f) (F.map g)] :
    HasPullback f g :=
  have : HasLimit (cospan f g ⋙ F) := hasLimit_of_iso (cospanCompIso F f g).symm
  hasLimit_of_created _ F

lemma HasPushout.of_createsColimit (F : C ⥤ D) {X Y S : C} (f : S ⟶ X) (g : S ⟶ Y)
    [CreatesColimit (span f g) F] [HasPushout (F.map f) (F.map g)] :
    HasPushout f g :=
  have : HasColimit (span f g ⋙ F) := hasColimit_of_iso (spanCompIso F f g)
  hasColimit_of_created _ F

end CategoryTheory.Limits
