/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise

/-! # The Kan extension functor

Given a functor `L : C ⥤ D`, we define the left Kan extension functor
`L.lan : (C ⥤ H) ⥤ (D ⥤ H)` which sends a functor `F : C ⥤ H` to its
left Kan extension along `L`. This is defined if all `F` have such
a left Kan extension. It is shown that `L.lan` is the left adjoint to
the functor `(D ⥤ H) ⥤ (C ⥤ H)` given by the precomposition
with `L` (see `Functor.lanAdjunction`).

## TODO
- dualize the results for right Kan extensions
- refactor the file `CategoryTheory.Limits.KanExtension` so that
the definitions of `Lan` and `Ran` in that file (which rely on the
existence of (co)limits) are replaced by the new definition
`Functor.lan` which is based on Kan extensions API.

-/

namespace CategoryTheory

open Category

namespace Functor

variable {C D : Type*} [Category C] [Category D] (L : C ⥤ D)
  {H : Type*} [Category H] [∀ (F : C ⥤ H), HasLeftKanExtension L F]

/-- The left Kan extension functor `(C ⥤ H) ⥤ (D ⥤ H)` along a functor `C ⥤ D`. -/
noncomputable def lan : (C ⥤ H) ⥤ (D ⥤ H) where
  obj F := leftKanExtension L F
  map {F₁ F₂} φ := descOfIsLeftKanExtension _ (leftKanExtensionUnit L F₁) _
    (φ ≫ leftKanExtensionUnit L F₂)

/-- The natural transformation `F ⟶ L ⋙ (L.lan).obj G`. -/
noncomputable def lanUnit : (𝟭 (C ⥤ H)) ⟶ L.lan ⋙ (whiskeringLeft C D H).obj L where
  app F := leftKanExtensionUnit L F
  naturality {F₁ F₂} φ := by ext; simp [lan]

instance (F : C ⥤ H) : (L.lan.obj F).IsLeftKanExtension (L.lanUnit.app F) := by
  dsimp [lan, lanUnit]
  infer_instance

/-- If there exists a pointwise left Kan extension of `F` along `L`,
then `L.lan.obj G` is a pointwise left Kan extension of `F`. -/
noncomputable def isPointwiseLeftKanExtensionLanUnit
    (F : C ⥤ H) [HasPointwiseLeftKanExtension L F] :
    (LeftExtension.mk _ (L.lanUnit.app F)).IsPointwiseLeftKanExtension :=
  isPointwiseLeftKanExtensionOfIsLeftKanExtension (F := F) _ (L.lanUnit.app F)

variable (H) in
/-- The left Kan extension functor `L.Lan` is left adjoint to the
precomposition by `L`. -/
noncomputable def lanAdjunction : L.lan ⊣ (whiskeringLeft C D H).obj L :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun F G => homEquivOfIsLeftKanExtension _ (L.lanUnit.app F) G
      homEquiv_naturality_left_symm := fun {F₁ F₂ G} f α =>
        hom_ext_of_isLeftKanExtension _  (L.lanUnit.app F₁) _ _ (by
          ext X
          dsimp [homEquivOfIsLeftKanExtension]
          rw [descOfIsLeftKanExtension_fac_app, NatTrans.comp_app, ← assoc]
          have h := congr_app (L.lanUnit.naturality f) X
          dsimp at h ⊢
          rw [← h, assoc, descOfIsLeftKanExtension_fac_app] )
      homEquiv_naturality_right := fun {F G₁ G₂} β f => by
        dsimp [homEquivOfIsLeftKanExtension]
        rw [assoc] }

variable (H) in
@[simp]
lemma lanAdjunction_unit : (L.lanAdjunction H).unit = L.lanUnit := by
  ext F : 2
  dsimp [lanAdjunction, homEquivOfIsLeftKanExtension]
  simp

lemma lanAdjunction_counit_app (G : D ⥤ H) :
    (L.lanAdjunction H).counit.app G =
      descOfIsLeftKanExtension (L.lan.obj (L ⋙ G)) (L.lanUnit.app (L ⋙ G)) G (𝟙 (L ⋙ G)) :=
  rfl

@[reassoc (attr := simp)]
lemma lanUnit_app_whiskerLeft_lanAdjunction_counit_app (G : D ⥤ H) :
    L.lanUnit.app (L ⋙ G) ≫ whiskerLeft L ((L.lanAdjunction H).counit.app G) = 𝟙 (L ⋙ G) := by
  simp [lanAdjunction_counit_app]

@[reassoc (attr := simp)]
lemma lanUnit_app_app_lanAdjunction_counit_app_app (G : D ⥤ H) (X : C) :
    (L.lanUnit.app (L ⋙ G)).app X ≫ ((L.lanAdjunction H).counit.app G).app (L.obj X) = 𝟙 _ :=
  congr_app (L.lanUnit_app_whiskerLeft_lanAdjunction_counit_app G) X

lemma isIso_lanAdjunction_counit_app_iff (G : D ⥤ H) :
    IsIso ((L.lanAdjunction H).counit.app G) ↔ G.IsLeftKanExtension (𝟙 (L ⋙ G)) :=
  (isLeftKanExtension_iff_isIso _ (L.lanUnit.app (L ⋙ G)) _ (by simp)).symm

section

variable [Full L] [Faithful L]

instance (F : C ⥤ H) (X : C) [HasPointwiseLeftKanExtension L F] :
    IsIso ((L.lanUnit.app F).app X) :=
  (isPointwiseLeftKanExtensionLanUnit L F (L.obj X)).isIso_hom_app

instance (F : C ⥤ H) [HasPointwiseLeftKanExtension L F] :
    IsIso (L.lanUnit.app F) :=
  NatIso.isIso_of_isIso_app _

instance coreflective [∀ (F : C ⥤ H), HasPointwiseLeftKanExtension L F] :
    IsIso (L.lanUnit (H := H)) := by
  apply NatIso.isIso_of_isIso_app _

instance (F : C ⥤ H) [HasPointwiseLeftKanExtension L F] :
    IsIso ((L.lanAdjunction H).unit.app F) := by
  rw [lanAdjunction_unit]
  infer_instance

instance coreflective' [∀ (F : C ⥤ H), HasPointwiseLeftKanExtension L F] :
    IsIso (L.lanAdjunction H).unit := by
  apply NatIso.isIso_of_isIso_app _

end

end Functor

end CategoryTheory
