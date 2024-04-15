/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise

/-! # The left Kan extension functor

Given a functor `F : C ⥤ D`, we define the left Kan extension functor
`F.lan : (C ⥤ E) ⥤ (D ⥤ E)` which sends a functor `G : C ⥤ E` to its
left Kan extension along `F`. This is defined if all `G` have such
a left Kan extension. It is shown that if `G` admits a pointwise
left Kan extension, then `F.lan.obj G` is also a pointwise left
Kan extension. It is shown that `F.lan` is the left adjoint to the
functor `(D ⥤ E) ⥤ (C ⥤ E)` given by the precomposition
with `F` (see `Functor.lanAdjunction`).

## TODO
- dualize the results for right Kan extensions
- refactor the file `CategoryTheory.Limits.KanExtension`

-/

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

namespace IsLimit

variable {J C : Type*} [Category J] [Category C] {F : J ⥤ C} {c : Cone F}
  (hc : IsLimit c)

lemma isIso_π_app_of_isInitial (X : J) (hX : IsInitial X) : IsIso (c.π.app X) := by
  change IsIso (conePointUniqueUpToIso (limitOfDiagramInitial hX F) hc).inv
  infer_instance

end IsLimit


end Limits

namespace Functor

variable {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
  {E : Type*} [Category E] [∀ (G : C ⥤ E), HasLeftKanExtension F G]

noncomputable def lan : (C ⥤ E) ⥤ (D ⥤ E) where
  obj G := leftKanExtension F G
  map {G₁ G₂} φ := descOfIsLeftKanExtension _ (leftKanExtensionUnit F G₁) _
    (φ ≫ leftKanExtensionUnit F G₂)

noncomputable def lanUnit : (𝟭 (C ⥤ E)) ⟶ F.lan ⋙ (whiskeringLeft C D E).obj F where
  app G := leftKanExtensionUnit F G
  naturality {G₁ G₂} φ := by ext; simp [lan]

instance (G : C ⥤ E) : (F.lan.obj G).IsLeftKanExtension (F.lanUnit.app G) := by
  dsimp [lan, lanUnit]
  infer_instance

noncomputable def isPointwiseLeftKanExtensionLanUnit
    (G : C ⥤ E) [HasPointwiseLeftKanExtension F G] :
    (LeftExtension.mk _ (F.lanUnit.app G)).IsPointwiseLeftKanExtension :=
  isPointwiseLeftKanExtensionOfIsLeftKanExtension (F := G) _ (F.lanUnit.app G)

variable {F} in
noncomputable def homEquivOfIsLeftKanExtension
    {G : C ⥤ E} (G' : D ⥤ E) (α : G ⟶ F ⋙ G') (H : D ⥤ E)
    [G'.IsLeftKanExtension α] : (G' ⟶ H) ≃ (G ⟶ F ⋙ H) where
  toFun β := α ≫ whiskerLeft _ β
  invFun β := descOfIsLeftKanExtension _ α _ β
  left_inv β := Functor.hom_ext_of_isLeftKanExtension _ α _ _ (by aesop_cat)
  right_inv := by aesop_cat

variable (E) in
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
    IsIso ((F.lanUnit.app G).app X) := by
  simpa using (isPointwiseLeftKanExtensionLanUnit F G (F.obj X)).isIso_hom_app

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
