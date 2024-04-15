-- refactor of Limits.KanExtension
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise

namespace CategoryTheory

open Category

namespace Limits

namespace IsColimit

variable {J C : Type*} [Category J] [Category C] {F : J ⥤ C} {c : Cocone F}
  (hc : IsColimit c)

lemma isIso_ι_app_of_isTerminal (X : J) (hX : IsTerminal X) : IsIso (c.ι.app X) := by
  change IsIso (coconePointUniqueUpToIso (colimitOfDiagramTerminal hX F) hc).hom
  infer_instance

end IsColimit

end Limits

namespace Functor

variable {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
  {E : Type*} [Category E] [∀ (G : C ⥤ E), HasLeftKanExtension F G]

noncomputable def lan : (C ⥤ E) ⥤ (D ⥤ E) where
  obj G := leftKanExtension F G
  map {G₁ G₂} φ := descOfIsLeftKanExtension _ (leftKanExtensionUnit F G₁) _
    (φ ≫ leftKanExtensionUnit F G₂)

noncomputable def lanUnit : (𝟭 (C ⥤ E)) ⟶ lan F ⋙ (whiskeringLeft C D E).obj F where
  app G := leftKanExtensionUnit F G
  naturality {G₁ G₂} φ := by ext; simp [lan]

instance (G : C ⥤ E) : ((lan F).obj G).IsLeftKanExtension ((lanUnit F).app G) := by
  dsimp [lan, lanUnit]
  infer_instance

noncomputable def isPointwiseLeftKanExtensionLanUnit
    (G : C ⥤ E) [HasPointwiseLeftKanExtension F G] :
    (LeftExtension.mk _ ((lanUnit F).app G)).IsPointwiseLeftKanExtension := by
  have : HasPointwiseLeftKanExtension F ((𝟭 (C ⥤ E)).obj G) := by
    dsimp
    infer_instance
  exact isPointwiseLeftKanExtensionOfIsLeftKanExtension _ ((lanUnit F).app G)

variable {F} in
noncomputable def homEquivOfIsLeftKanExtension
    {G : C ⥤ E} (G' : D ⥤ E) (α : G ⟶ F ⋙ G') (H : D ⥤ E)
    [G'.IsLeftKanExtension α] : (G' ⟶ H) ≃ (G ⟶ F ⋙ H) where
  toFun β := α ≫ whiskerLeft _ β
  invFun β := descOfIsLeftKanExtension _ α _ β
  left_inv β := Functor.hom_ext_of_isLeftKanExtension _ α _ _ (by aesop_cat)
  right_inv := by aesop_cat

variable (E) in
noncomputable def Lan.adjunction : lan F ⊣ (whiskeringLeft _ _ E).obj F :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun G H => homEquivOfIsLeftKanExtension _ ((lanUnit F).app G) H
      homEquiv_naturality_left_symm := fun {G₁ G₂ H} f α =>
        hom_ext_of_isLeftKanExtension _  ((lanUnit F).app G₁) _ _ (by
          ext X
          dsimp [homEquivOfIsLeftKanExtension]
          rw [descOfIsLeftKanExtension_fac_app, NatTrans.comp_app, ← assoc]
          have h := congr_app ((lanUnit F).naturality f) X
          dsimp at h ⊢
          rw [← h, assoc, descOfIsLeftKanExtension_fac_app] )
      homEquiv_naturality_right := fun {G H₁ H₂} β f => by
        dsimp [homEquivOfIsLeftKanExtension]
        rw [assoc] }

variable (E) in
@[simp]
lemma Lan.adjunction_unit :
    (Lan.adjunction F E).unit =
      lanUnit F := by
  ext G : 2
  dsimp [adjunction, homEquivOfIsLeftKanExtension]
  simp

namespace LeftExtension

namespace IsPointwiseLeftKanExtensionAt

variable {F}
variable {G : C ⥤ E} {e : LeftExtension F G} {X : C}
    (he : e.IsPointwiseLeftKanExtensionAt (F.obj X))

lemma isIso_hom_app [F.Full] [F.Faithful] : IsIso (e.hom.app X) := by
  simpa using he.isIso_ι_app_of_isTerminal _ CostructuredArrow.mkIdTerminal

end IsPointwiseLeftKanExtensionAt

namespace IsPointwiseLeftKanExtension

variable {F}
variable {G : C ⥤ E} {e : LeftExtension F G}
    (he : e.IsPointwiseLeftKanExtension)

lemma isIso_hom [Full F] [Faithful F] : IsIso e.hom := by
  have : ∀ (X : C), IsIso (e.hom.app X) := fun (X : C) => (he (F.obj X)).isIso_hom_app
  apply NatIso.isIso_of_isIso_app

end IsPointwiseLeftKanExtension

end LeftExtension

section

variable [Full F] [Faithful F]

instance (G : C ⥤ E) (X : C) [HasPointwiseLeftKanExtension F G] :
    IsIso (((Lan.adjunction F E).unit.app G).app X) := by
  simpa using (isPointwiseLeftKanExtensionLanUnit F G (F.obj X)).isIso_hom_app

instance (G : C ⥤ E) [HasPointwiseLeftKanExtension F G] :
    IsIso ((Lan.adjunction F E).unit.app G) :=
  NatIso.isIso_of_isIso_app _

instance coreflective [∀ (G : C ⥤ E), HasPointwiseLeftKanExtension F G] :
    IsIso ((Lan.adjunction F E).unit) :=
  NatIso.isIso_of_isIso_app _

instance coreflective' [∀ (G : C ⥤ E), HasPointwiseLeftKanExtension F G] :
    IsIso (lanUnit F : (𝟭 (C ⥤ E)) ⟶ _) := by
  rw [← Lan.adjunction_unit]
  infer_instance

end

end Functor

end CategoryTheory
