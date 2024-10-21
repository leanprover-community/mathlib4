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

Similarly, we define the right Kan extension functor
`L.ran : (C ⥤ H) ⥤ (D ⥤ H)` which sends a functor `F : C ⥤ H` to its
right Kan extension along `L`.

-/

namespace CategoryTheory

open Category Limits

namespace Functor

variable {C D : Type*} [Category C] [Category D] (L : C ⥤ D) {H : Type*} [Category H]

section lan

section

variable [∀ (F : C ⥤ H), HasLeftKanExtension L F]

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

/-- If a left Kan extension is pointwise, then evaluating it at an object is isomorphic to
taking a colimit. -/
noncomputable def lanObjObjIsoColimit (F : C ⥤ H) [HasPointwiseLeftKanExtension L F] (X : D) :
    (L.lan.obj F).obj X ≅ Limits.colimit (CostructuredArrow.proj L X ⋙ F) :=
  LeftExtension.IsPointwiseLeftKanExtensionAt.isoColimit (F := F)
   (isPointwiseLeftKanExtensionLanUnit L F X)

@[reassoc (attr := simp)]
lemma ι_lanObjObjIsoColimit_inv
    (F : C ⥤ H) [HasPointwiseLeftKanExtension L F] (X : D) (f : CostructuredArrow L X) :
    Limits.colimit.ι _ f ≫ (L.lanObjObjIsoColimit F X).inv =
    (L.lanUnit.app F).app f.left ≫ (L.lan.obj F).map f.hom := by
  simp [lanObjObjIsoColimit, lanUnit]

@[reassoc (attr := simp)]
lemma ι_lanObjObjIsoColimit_hom
    (F : C ⥤ H) [HasPointwiseLeftKanExtension L F] (X : D) (f : CostructuredArrow L X) :
    (L.lanUnit.app F).app f.left ≫ (L.lan.obj F).map f.hom ≫ (L.lanObjObjIsoColimit F X).hom =
    Limits.colimit.ι (CostructuredArrow.proj L X ⋙ F) f :=
  LeftExtension.IsPointwiseLeftKanExtensionAt.ι_isoColimit_hom (F := F)
    (isPointwiseLeftKanExtensionLanUnit L F X) f

variable (H) in
/-- The left Kan extension functor `L.Lan` is left adjoint to the
precomposition by `L`. -/
noncomputable def lanAdjunction : L.lan ⊣ (whiskeringLeft C D H).obj L :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun F G => homEquivOfIsLeftKanExtension _ (L.lanUnit.app F) G
      homEquiv_naturality_left_symm := fun {F₁ F₂ G} f α =>
        hom_ext_of_isLeftKanExtension _ (L.lanUnit.app F₁) _ _ (by
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

/-- Composing the left Kan extension of `L : C ⥤ D` with `colim` on shapes `D` is isomorphic
to `colim` on shapes `C`. -/
@[simps!]
noncomputable def lanCompColimIso (L : C ⥤ D) [∀ (G : C ⥤ H), L.HasLeftKanExtension G]
    [HasColimitsOfShape C H] [HasColimitsOfShape D H] : L.lan ⋙ colim ≅ colim (C := H) :=
  Iso.symm <| NatIso.ofComponents
    (fun G ↦ (colimitIsoOfIsLeftKanExtension _ (L.lanUnit.app G)).symm)
    (fun f ↦ colimit.hom_ext (fun i ↦ by
      dsimp
      rw [ι_colimMap_assoc, ι_colimitIsoOfIsLeftKanExtension_inv,
        ι_colimitIsoOfIsLeftKanExtension_inv_assoc, ι_colimMap, ← assoc, ← assoc]
      congr 1
      exact congr_app (L.lanUnit.naturality f) i))

end

section

variable [Full L] [Faithful L]

instance (F : C ⥤ H) (X : C) [HasPointwiseLeftKanExtension L F]
    [∀ (F : C ⥤ H), HasLeftKanExtension L F] :
    IsIso ((L.lanUnit.app F).app X) :=
  (isPointwiseLeftKanExtensionLanUnit L F (L.obj X)).isIso_hom_app

instance (F : C ⥤ H) [HasPointwiseLeftKanExtension L F]
    [∀ (F : C ⥤ H), HasLeftKanExtension L F] :
    IsIso (L.lanUnit.app F) :=
  NatIso.isIso_of_isIso_app _

instance coreflective [∀ (F : C ⥤ H), HasPointwiseLeftKanExtension L F] :
    IsIso (L.lanUnit (H := H)) := by
  apply NatIso.isIso_of_isIso_app _

instance (F : C ⥤ H) [HasPointwiseLeftKanExtension L F]
    [∀ (F : C ⥤ H), HasLeftKanExtension L F] :
    IsIso ((L.lanAdjunction H).unit.app F) := by
  rw [lanAdjunction_unit]
  infer_instance

instance coreflective' [∀ (F : C ⥤ H), HasPointwiseLeftKanExtension L F] :
    IsIso (L.lanAdjunction H).unit := by
  apply NatIso.isIso_of_isIso_app _

end

end lan

section ran

section

variable [∀ (F : C ⥤ H), HasRightKanExtension L F]

/-- The right Kan extension functor `(C ⥤ H) ⥤ (D ⥤ H)` along a functor `C ⥤ D`. -/
noncomputable def ran : (C ⥤ H) ⥤ (D ⥤ H) where
  obj F := rightKanExtension L F
  map {F₁ F₂} φ := liftOfIsRightKanExtension _ (rightKanExtensionCounit L F₂) _
    (rightKanExtensionCounit L F₁ ≫ φ)

/-- The natural transformation `L ⋙ (L.lan).obj G ⟶ L`. -/
noncomputable def ranCounit : L.ran ⋙ (whiskeringLeft C D H).obj L ⟶ (𝟭 (C ⥤ H)) where
  app F := rightKanExtensionCounit L F
  naturality {F₁ F₂} φ := by ext; simp [ran]

instance (F : C ⥤ H) : (L.ran.obj F).IsRightKanExtension (L.ranCounit.app F) := by
  dsimp [ran, ranCounit]
  infer_instance

/-- If there exists a pointwise right Kan extension of `F` along `L`,
then `L.ran.obj G` is a pointwise right Kan extension of `F`. -/
noncomputable def isPointwiseRightKanExtensionRanCounit
    (F : C ⥤ H) [HasPointwiseRightKanExtension L F] :
    (RightExtension.mk _ (L.ranCounit.app F)).IsPointwiseRightKanExtension :=
  isPointwiseRightKanExtensionOfIsRightKanExtension (F := F) _ (L.ranCounit.app F)

/-- If a right Kan extension is pointwise, then evaluating it at an object is isomorphic to
taking a limit. -/
noncomputable def ranObjObjIsoLimit (F : C ⥤ H) [HasPointwiseRightKanExtension L F] (X : D) :
    (L.ran.obj F).obj X ≅ Limits.limit (StructuredArrow.proj X L ⋙ F) :=
  RightExtension.IsPointwiseRightKanExtensionAt.isoLimit (F := F)
    (isPointwiseRightKanExtensionRanCounit L F X)

@[reassoc (attr := simp)]
lemma ranObjObjIsoLimit_hom_π
    (F : C ⥤ H) [HasPointwiseRightKanExtension L F] (X : D) (f : StructuredArrow X L) :
    (L.ranObjObjIsoLimit F X).hom ≫ Limits.limit.π _ f =
    (L.ran.obj F).map f.hom ≫ (L.ranCounit.app F).app f.right := by
  simp [ranObjObjIsoLimit, ran, ranCounit]

@[reassoc (attr := simp)]
lemma ranObjObjIsoLimit_inv_π
    (F : C ⥤ H) [HasPointwiseRightKanExtension L F] (X : D) (f : StructuredArrow X L) :
    (L.ranObjObjIsoLimit F X).inv ≫ (L.ran.obj F).map f.hom ≫ (L.ranCounit.app F).app f.right =
    Limits.limit.π _ f :=
  RightExtension.IsPointwiseRightKanExtensionAt.isoLimit_inv_π (F := F)
    (isPointwiseRightKanExtensionRanCounit L F X) f

variable (H) in
/-- The right Kan extension functor `L.ran` is right adjoint to the
precomposition by `L`. -/
noncomputable def ranAdjunction : (whiskeringLeft C D H).obj L ⊣ L.ran :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun F G =>
        (homEquivOfIsRightKanExtension (α := L.ranCounit.app G) _ F).symm
      homEquiv_naturality_right := fun {F G₁ G₂} β f ↦
        hom_ext_of_isRightKanExtension _ (L.ranCounit.app G₂) _ _ (by
        ext X
        dsimp [homEquivOfIsRightKanExtension]
        rw [liftOfIsRightKanExtension_fac_app, NatTrans.comp_app, assoc]
        have h := congr_app (L.ranCounit.naturality f) X
        dsimp at h ⊢
        rw [h, liftOfIsRightKanExtension_fac_app_assoc])
      homEquiv_naturality_left_symm := fun {F₁ F₂ G} β f ↦ by
        dsimp [homEquivOfIsRightKanExtension]
        rw [assoc] }

variable (H) in
@[simp]
lemma ranAdjunction_counit : (L.ranAdjunction H).counit = L.ranCounit := by
  ext F : 2
  dsimp [ranAdjunction, homEquivOfIsRightKanExtension]
  simp

lemma ranAdjunction_unit_app (G : D ⥤ H) :
    (L.ranAdjunction H).unit.app G =
      liftOfIsRightKanExtension (L.ran.obj (L ⋙ G)) (L.ranCounit.app (L ⋙ G)) G (𝟙 (L ⋙ G)) :=
  rfl

@[reassoc (attr := simp)]
lemma ranCounit_app_whiskerLeft_ranAdjunction_unit_app (G : D ⥤ H) :
    whiskerLeft L ((L.ranAdjunction H).unit.app G) ≫ L.ranCounit.app (L ⋙ G) = 𝟙 (L ⋙ G) := by
  simp [ranAdjunction_unit_app]

@[reassoc (attr := simp)]
lemma ranCounit_app_app_ranAdjunction_unit_app_app (G : D ⥤ H) (X : C) :
    ((L.ranAdjunction H).unit.app G).app (L.obj X) ≫ (L.ranCounit.app (L ⋙ G)).app X = 𝟙 _ :=
  congr_app (L.ranCounit_app_whiskerLeft_ranAdjunction_unit_app G) X

lemma isIso_ranAdjunction_unit_app_iff (G : D ⥤ H) :
    IsIso ((L.ranAdjunction H).unit.app G) ↔ G.IsRightKanExtension (𝟙 (L ⋙ G)) :=
  (isRightKanExtension_iff_isIso _ (L.ranCounit.app (L ⋙ G)) _ (by simp)).symm

/-- Composing the right Kan extension of `L : C ⥤ D` with `lim` on shapes `D` is isomorphic
to `lim` on shapes `C`. -/
@[simps!]
noncomputable def ranCompLimIso (L : C ⥤ D) [∀ (G : C ⥤ H), L.HasRightKanExtension G]
    [HasLimitsOfShape C H] [HasLimitsOfShape D H] : L.ran ⋙ lim ≅ lim (C := H) :=
  NatIso.ofComponents
    (fun G ↦ (limitIsoOfIsRightKanExtension _ (L.ranCounit.app G)))
    (fun f ↦ limit.hom_ext (fun i ↦ by
      dsimp
      rw [assoc, assoc, limMap_π, limitIsoOfIsRightKanExtension_hom_π_assoc,
        limitIsoOfIsRightKanExtension_hom_π, limMap_π_assoc]
      congr 1
      exact congr_app (L.ranCounit.naturality f) i))

end

section

variable [Full L] [Faithful L]

instance (F : C ⥤ H) (X : C) [HasPointwiseRightKanExtension L F]
    [∀ (F : C ⥤ H), HasRightKanExtension L F] :
    IsIso ((L.ranCounit.app F).app X) :=
  (isPointwiseRightKanExtensionRanCounit L F (L.obj X)).isIso_hom_app

instance (F : C ⥤ H) [HasPointwiseRightKanExtension L F]
    [∀ (F : C ⥤ H), HasRightKanExtension L F] :
    IsIso (L.ranCounit.app F) :=
  NatIso.isIso_of_isIso_app _

instance reflective [∀ (F : C ⥤ H), HasPointwiseRightKanExtension L F] :
    IsIso (L.ranCounit (H := H)) := by
  apply NatIso.isIso_of_isIso_app _

instance (F : C ⥤ H) [HasPointwiseRightKanExtension L F]
    [∀ (F : C ⥤ H), HasRightKanExtension L F] :
    IsIso ((L.ranAdjunction H).counit.app F) := by
  rw [ranAdjunction_counit]
  infer_instance

instance reflective' [∀ (F : C ⥤ H), HasPointwiseRightKanExtension L F] :
    IsIso (L.ranAdjunction H).counit := by
  apply NatIso.isIso_of_isIso_app _

end

end ran

end Functor

end CategoryTheory
