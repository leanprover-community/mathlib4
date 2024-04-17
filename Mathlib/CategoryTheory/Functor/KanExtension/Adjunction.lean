/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise

/-! # The Kan extension functor

Given a functor `F : C ⥤ D`, we define the left Kan extension functor
`F.lan : (C ⥤ E) ⥤ (D ⥤ E)` which sends a functor `G : C ⥤ E` to its
left Kan extension along `F`. This is defined if all `G` have such
a left Kan extension. It is shown that `F.lan` is the left adjoint to
the functor `(D ⥤ E) ⥤ (C ⥤ E)` given by the precomposition
with `F` (see `Functor.lanAdjunction`).

## TODO
- dualize the results for right Kan extensions
- refactor the file `CategoryTheory.Limits.KanExtension`

-/

namespace CategoryTheory

open Category

namespace Functor

variable {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
  {E : Type*} [Category E] [∀ (G : C ⥤ E), HasLeftKanExtension F G]

/-- The left Kan extension functor `(C ⥤ E) ⥤ (D ⥤ E)` along a functor `C ⥤ D`. -/
@[pp_dot]
noncomputable def lan : (C ⥤ E) ⥤ (D ⥤ E) where
  obj G := leftKanExtension F G
  map {G₁ G₂} φ := descOfIsLeftKanExtension _ (leftKanExtensionUnit F G₁) _
    (φ ≫ leftKanExtensionUnit F G₂)

/-- The natural transformation `G ⟶ F ⋙ (F.lan).obj G`. -/
@[pp_dot]
noncomputable def lanUnit : (𝟭 (C ⥤ E)) ⟶ F.lan ⋙ (whiskeringLeft C D E).obj F where
  app G := leftKanExtensionUnit F G
  naturality {G₁ G₂} φ := by ext; simp [lan]

instance (G : C ⥤ E) : (F.lan.obj G).IsLeftKanExtension (F.lanUnit.app G) := by
  dsimp [lan, lanUnit]
  infer_instance

instance (G : D ⥤ E) :
    (((whiskeringLeft C D E).obj F ⋙ F.lan).obj G).IsLeftKanExtension
      (F.lanUnit.app (F ⋙ G)) := by
  dsimp
  infer_instance

/-- If there exists a pointwise left Kan extension of `G` along `F`,
then `F.lan.obj G` is a pointwise left Kan extension of `G`. -/
noncomputable def isPointwiseLeftKanExtensionLanUnit
    (G : C ⥤ E) [HasPointwiseLeftKanExtension F G] :
    (LeftExtension.mk _ (F.lanUnit.app G)).IsPointwiseLeftKanExtension :=
  isPointwiseLeftKanExtensionOfIsLeftKanExtension (F := G) _ (F.lanUnit.app G)

variable (E) in
/-- The left Kan extension functor `F.Lan` is left adjoint to the
precomposition by `F`. -/
@[pp_dot]
noncomputable def lanAdjunction : F.lan ⊣ (whiskeringLeft C D E).obj F :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun G H => homEquivOfIsLeftKanExtension _ (F.lanUnit.app G) H
      homEquiv_naturality_left_symm := fun {G₁ G₂ H} f α =>
        hom_ext_of_isLeftKanExtension _  (F.lanUnit.app G₁) _ _ (by
          ext X
          dsimp [homEquivOfIsLeftKanExtension]
          rw [descOfIsLeftKanExtension_fac_app, NatTrans.comp_app, ← assoc]
          have h := congr_app (F.lanUnit.naturality f) X
          dsimp at h ⊢
          rw [← h, assoc, descOfIsLeftKanExtension_fac_app] )
      homEquiv_naturality_right := fun {G H₁ H₂} β f => by
        dsimp [homEquivOfIsLeftKanExtension]
        rw [assoc] }

variable (E) in
@[simp]
lemma lanAdjunction_unit :
    (F.lanAdjunction E).unit =
      lanUnit F := by
  ext G : 2
  dsimp [lanAdjunction, homEquivOfIsLeftKanExtension]
  simp

lemma lanAdjunction_counit_app (G : D ⥤ E) :
    (F.lanAdjunction E).counit.app G =
      descOfIsLeftKanExtension (F.lan.obj (F ⋙ G)) (F.lanUnit.app (F ⋙ G)) G (𝟙 (F ⋙ G)) :=
  rfl

@[reassoc (attr := simp)]
lemma lanUnit_app_whiskerLeft_lanAdjunction_counit_app (G : D ⥤ E) :
    F.lanUnit.app (F ⋙ G) ≫ whiskerLeft F ((F.lanAdjunction E).counit.app G) = 𝟙 (F ⋙ G) := by
  simp [lanAdjunction_counit_app]

@[reassoc (attr := simp)]
lemma lanUnit_app_app_lanAdjunction_counit_app_app (G : D ⥤ E) (X : C) :
    (F.lanUnit.app (F ⋙ G)).app X ≫ ((F.lanAdjunction E).counit.app G).app (F.obj X) = 𝟙 _ :=
  congr_app (F.lanUnit_app_whiskerLeft_lanAdjunction_counit_app G) X

lemma isIso_lanAdjunction_counit_app_iff (G : D ⥤ E) :
    IsIso ((F.lanAdjunction E).counit.app G) ↔ G.IsLeftKanExtension (𝟙 (F ⋙ G)) :=
  (isLeftKanExtension_iff_isIso _ (F.lanUnit.app (F ⋙ G)) _ (by simp)).symm

section

variable [Full F] [Faithful F]

instance (G : C ⥤ E) (X : C) [HasPointwiseLeftKanExtension F G] :
    IsIso ((F.lanUnit.app G).app X) :=
  (isPointwiseLeftKanExtensionLanUnit F G (F.obj X)).isIso_hom_app

instance (G : C ⥤ E) [HasPointwiseLeftKanExtension F G] :
    IsIso (F.lanUnit.app G) :=
  NatIso.isIso_of_isIso_app _

instance coreflective [∀ (G : C ⥤ E), HasPointwiseLeftKanExtension F G] :
    IsIso (F.lanUnit (E := E)) := by
  apply NatIso.isIso_of_isIso_app _

instance (G : C ⥤ E) [HasPointwiseLeftKanExtension F G] :
    IsIso ((F.lanAdjunction E).unit.app G) := by
  rw [lanAdjunction_unit]
  infer_instance

instance coreflective' [∀ (G : C ⥤ E), HasPointwiseLeftKanExtension F G] :
    IsIso (F.lanAdjunction E).unit := by
  apply NatIso.isIso_of_isIso_app _

end

end Functor

end CategoryTheory
