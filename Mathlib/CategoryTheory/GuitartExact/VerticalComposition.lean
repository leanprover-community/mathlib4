import Mathlib.CategoryTheory.GuitartExact
import Mathlib.CategoryTheory.CatCommSq

namespace CategoryTheory

open Category

variable {C₁ C₂ C₃ D₁ D₂ D₃ : Type*} [Category C₁] [Category C₂] [Category C₃]
  [Category D₁] [Category D₂] [Category D₃]
  {H₁ : C₁ ⥤ D₁} {L₁ : C₁ ⥤ C₂} {R₁ : D₁ ⥤ D₂} {H₂ : C₂ ⥤ D₂}
  (w : TwoSquare H₁ L₁ R₁ H₂)
  {L₂ : C₂ ⥤ C₃} {R₂ : D₂ ⥤ D₃} {H₃ : C₃ ⥤ D₃}
  (w' : TwoSquare H₂ L₂ R₂ H₃)

namespace Functor

end Functor

namespace TwoSquare

@[simps!]
def vComp : TwoSquare H₁ (L₁ ⋙ L₂) (R₁ ⋙ R₂) H₃ :=
  (Functor.associator _ _ _).inv ≫ whiskerRight w R₂ ≫
    (Functor.associator _ _ _).hom ≫ whiskerLeft L₁ w' ≫ (Functor.associator _ _ _).inv

def structuredArrowDownwardsComp (Y₁ : D₁) :
    w.structuredArrowDownwards Y₁ ⋙ w'.structuredArrowDownwards (R₁.obj Y₁) ≅
      (w.vComp w').structuredArrowDownwards Y₁ :=
  NatIso.ofComponents (fun f => StructuredArrow.isoMk (Iso.refl _))
    (by aesop_cat)

@[simps!]
def vComp' {L₁₂ : C₁ ⥤ C₃} {R₁₂ : D₁ ⥤ D₃} (eL : L₁ ⋙ L₂ ≅ L₁₂)
    (eR : R₁ ⋙ R₂ ≅ R₁₂) : TwoSquare H₁ L₁₂ R₁₂ H₃ :=
  (w.vComp w').whiskerVertical eL.hom eR.inv

namespace GuitartExact

instance vComp [hw : w.GuitartExact] [hw' : w'.GuitartExact] :
    (w.vComp w').GuitartExact := by
  simp only [TwoSquare.guitartExact_iff_initial]
  intro Y₁
  rw [← Functor.initial_natIso_iff (structuredArrowDownwardsComp w w' Y₁)]
  infer_instance

instance vComp' [GuitartExact w] [GuitartExact w'] {L₁₂ : C₁ ⥤ C₃}
    {R₁₂ : D₁ ⥤ D₃} (eL : L₁ ⋙ L₂ ≅ L₁₂)
    (eR : R₁ ⋙ R₂ ≅ R₁₂) : (w.vComp' w' eL eR).GuitartExact := by
  dsimp only [TwoSquare.vComp']
  infer_instance

lemma vComp_iff_of_equivalences (eL : C₂ ≌ C₃) (eR : D₂ ≌ D₃)
    (w' : H₂ ⋙ eR.functor ≅ eL.functor ⋙ H₃) :
    (w.vComp w'.hom).GuitartExact ↔ w.GuitartExact := by
  constructor
  · intro hww'
    letI : CatCommSq H₂ eL.functor eR.functor H₃ := ⟨w'⟩
    have hw' : CatCommSq.iso H₂ eL.functor eR.functor H₃ = w' := rfl
    letI : CatCommSq H₃ eL.inverse eR.inverse H₂ := CatCommSq.vInvEquiv _ _ _ _ inferInstance
    let w'' := CatCommSq.iso H₃ eL.inverse eR.inverse H₂
    let α : (L₁ ⋙ eL.functor) ⋙ eL.inverse ≅ L₁ :=
      Functor.associator _ _ _ ≪≫ isoWhiskerLeft L₁ eL.unitIso.symm ≪≫ L₁.rightUnitor
    let β : (R₁ ⋙ eR.functor) ⋙ eR.inverse ≅ R₁ :=
      Functor.associator _ _ _ ≪≫ isoWhiskerLeft R₁ eR.unitIso.symm ≪≫ R₁.rightUnitor
    have : w = (w.vComp w'.hom).vComp' w''.hom α β := NatTrans.ext _ _ (by
      ext X₁
      dsimp
      simp only [vComp'_app, Functor.comp_obj, Iso.trans_inv, isoWhiskerLeft_inv, Iso.symm_inv, assoc,
        NatTrans.comp_app, Functor.id_obj, Functor.rightUnitor_inv_app, whiskerLeft_app, Functor.associator_inv_app,
        comp_id, id_comp, vComp_app, Functor.map_comp, Equivalence.inv_fun_map, Iso.trans_hom, isoWhiskerLeft_hom,
        Iso.symm_hom, Functor.associator_hom_app, Functor.rightUnitor_hom_app, Iso.hom_inv_id_app_assoc]
      convert (comp_id _).symm
      erw [CatCommSq.vInv_iso'_hom_app, hw']
      simp only [assoc, ← eR.inverse.map_comp_assoc]
      erw [Equivalence.counitInv_app_functor, ← NatTrans.naturality_assoc, Iso.hom_inv_id_app,
        comp_id, ← NatTrans.naturality_assoc, Iso.hom_inv_id_app_assoc, ← H₂.map_comp,
        Iso.hom_inv_id_app, H₂.map_id])
    rw [this]
    infer_instance
  · intro
    exact vComp w w'.hom

lemma vComp'_iff_of_equivalences (E : C₂ ≌ C₃) (E' : D₂ ≌ D₃)
    (w' : H₂ ⋙ E'.functor ≅ E.functor ⋙ H₃) {L₁₂ : C₁ ⥤ C₃}
    {R₁₂ : D₁ ⥤ D₃} (eL : L₁ ⋙ E.functor ≅ L₁₂)
    (eR : R₁ ⋙ E'.functor ≅ R₁₂) :
    (w.vComp' w'.hom eL eR).GuitartExact ↔ w.GuitartExact := by
  rw [← vComp_iff_of_equivalences w E E' w', TwoSquare.vComp', whiskerVertical_iff]

end GuitartExact

end TwoSquare

end CategoryTheory
