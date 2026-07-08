/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Limits.Creates
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Creation of limits and pullbacks

We show some lemmas relating creation of (co)limits and pullbacks (resp. pushouts).
-/

public section

namespace CategoryTheory.Limits

variable {C : Type*} [Category* C] {D : Type*} [Category* D]

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


-- Dual/order lemmas discovered by the Manifold Destiny verifier-mediated learner.
-- Paper: https://github.com/sumofagents/manifold-destiny
section
theorem CategoryTheory.Precoverage.comap_sup : ∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u_1} [inst_1 : CategoryTheory.Category.{v_1, u_1} D] {F : CategoryTheory.Functor C D} {J K : CategoryTheory.Precoverage D}, CategoryTheory.Precoverage.comap F (J ⊔ K) = CategoryTheory.Precoverage.comap F J ⊔ CategoryTheory.Precoverage.comap F K := by
  open CategoryTheory CategoryTheory.Precoverage Limits in
    intro C inst D inst_1 F J K
    exact (rfl)

end
