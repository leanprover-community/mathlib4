-- refactor of Limits.KanExtension
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise

namespace CategoryTheory

open Category

namespace Functor

variable {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
  {E : Type*} [Category E] [∀ (G : C ⥤ E), HasLeftKanExtension F G]

noncomputable def lan : (C ⥤ E) ⥤ (D ⥤ E) where
  obj G := leftKanExtension F G
  map {G₁ G₂} φ := leftKanExtensionDesc _ (leftKanExtensionUnit F G₁) _
    (φ ≫ leftKanExtensionUnit F G₂)
  map_id G := leftKanExtension_ext _ (leftKanExtensionUnit F G) _ _ (by aesop_cat)
  map_comp φ₁ φ₂ := leftKanExtension_ext _ (leftKanExtensionUnit F _) _ _ (by aesop_cat)

noncomputable def lanUnit : (𝟭 (C ⥤ E)) ⟶ lan F ⋙ (whiskeringLeft C D E).obj F where
  app G := leftKanExtensionUnit F G
  naturality {G₁ G₂} φ := by ext; simp [lan]

instance (G : C ⥤ E) : ((lan F).obj G).IsLeftKanExtension ((lanUnit F).app G) := by
  dsimp [lan, lanUnit]
  infer_instance

noncomputable def isPointwiseLeftKanExtensionLanUnit
    (G : C ⥤ E) [G.HasPointwiseLeftKanExtension F] :
    (LeftExtension.mk _ ((lanUnit F).app G)).IsPointwiseLeftKanExtension := by
  have : HasPointwiseLeftKanExtension ((𝟭 (C ⥤ E)).obj G) F := by
    dsimp
    infer_instance
  exact isPointwiseLeftKanExtensionOfIsLeftKanExtension _ ((lanUnit F).app G)

noncomputable def Lan.homEquiv (G : C ⥤ E) (H : D ⥤ E) :
    ((lan F).obj G ⟶ H) ≃ (G ⟶ F ⋙ H) where
  toFun α := (lanUnit F).app G ≫ whiskerLeft _ α
  invFun β := leftKanExtensionDesc _  ((lanUnit F).app G) _ β
  left_inv α := leftKanExtension_ext _  ((lanUnit F).app G) _ _ (by aesop_cat)
  right_inv β := by aesop_cat

noncomputable def Lan.adjunction : lan F ⊣ (whiskeringLeft _ _ E).obj F :=
  Adjunction.mkOfHomEquiv
    { homEquiv := Lan.homEquiv F
      homEquiv_naturality_left_symm := fun {G₁ G₂ H} f α =>
        leftKanExtension_ext _  ((lanUnit F).app G₁) _ _ (by
          ext X
          dsimp [homEquiv]
          rw [leftKanExtension_fac_app, NatTrans.comp_app, ← assoc]
          have h := congr_app ((lanUnit F).naturality f) X
          dsimp at h ⊢
          rw [← h, assoc, leftKanExtension_fac_app] )
      homEquiv_naturality_right := fun {G H₁ H₂} β f => by simp [homEquiv] }

end Functor

end CategoryTheory
