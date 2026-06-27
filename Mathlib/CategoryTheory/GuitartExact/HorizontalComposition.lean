/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.GuitartExact.Opposite

/-!
# Horizontal composition of Guitart exact squares

In this file, we show that the horizontal composition of Guitart exact squares
is Guitart exact.

-/

@[expose] public section

namespace CategoryTheory

open Category

variable {C₁ C₂ C₃ D₁ D₂ D₃ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
  [Category* D₁] [Category* D₂] [Category* D₃]

namespace TwoSquare

section WhiskerHorizontal

variable {T : C₁ ⥤ D₁} {L : C₁ ⥤ C₂} {R : D₁ ⥤ D₂} {B : C₂ ⥤ D₂} (w : TwoSquare T L R B)
  {T' : C₁ ⥤ D₁} {B' : C₂ ⥤ D₂}

/-- Given `w : TwoSquare T L R B`, one may obtain a 2-square `TwoSquare T' L R B'` if we
provide natural transformations `α : T ⟶ T'` and `β : B' ⟶ B`. -/
@[simps!]
def whiskerHorizontal (α : T' ⟶ T) (β : B ⟶ B') :
    TwoSquare T' L R B' :=
  (w.whiskerTop α).whiskerBottom β

namespace GuitartExact

set_option backward.defeqAttrib.useBackward true in
/-- A 2-square stays Guitart exact if we replace the top and bottom functors
by isomorphic functors. See also `whiskerHorizontal_iff`. -/
lemma whiskerHorizontal [w.GuitartExact] (α : T ≅ T') (β : B ≅ B') :
    (w.whiskerHorizontal α.inv β.hom).GuitartExact := by
  rw [guitartExact_iff_final]
  intro X₂
  let e : costructuredArrowRightwards (w.whiskerHorizontal α.inv β.hom) X₂ ≅
      w.costructuredArrowRightwards X₂ ⋙ (CostructuredArrow.mapIso (β.app X₂)).functor :=
    NatIso.ofComponents (fun f ↦ CostructuredArrow.isoMk (α.symm.app f.left))
  rw [Functor.final_natIso_iff e]
  infer_instance

/-- A 2-square is Guitart exact iff it is so after replacing the top and bottom functors by
isomorphic functors. -/
@[simp]
lemma whiskerHorizontal_iff (α : T ≅ T') (β : B ≅ B') :
    (w.whiskerHorizontal α.inv β.hom).GuitartExact ↔ w.GuitartExact := by
  rw [← guitartExact_op_iff, ← w.guitartExact_op_iff,
    ← whiskerVertical_iff w.op (NatIso.op α.symm) (NatIso.op β.symm)]
  rfl

instance [w.GuitartExact] (α : T' ⟶ T) (β : B ⟶ B')
    [IsIso α] [IsIso β] : (w.whiskerHorizontal α β).GuitartExact :=
  whiskerHorizontal w (asIso α).symm (asIso β)

end GuitartExact

end WhiskerHorizontal

section HorizontalComposition

variable {V₁ : C₁ ⥤ D₁} {T₁ : C₁ ⥤ C₂} {B₁ : D₁ ⥤ D₂} {V₂ : C₂ ⥤ D₂}
  (w : TwoSquare T₁ V₁ V₂ B₁)
  {T₂ : C₂ ⥤ C₃} {B₂ : D₂ ⥤ D₃} {V₃ : C₃ ⥤ D₃}
  (w' : TwoSquare T₂ V₂ V₃ B₂)

/-- The horizontal composition of 2-squares. (Variant where we allow the replacement of
the horizontal compositions by isomorphic functors.) -/
@[simps!]
def hComp' {T₁₂ : C₁ ⥤ C₃} {B₁₂ : D₁ ⥤ D₃} (eT : T₁ ⋙ T₂ ≅ T₁₂) (eB : B₁ ⋙ B₂ ≅ B₁₂) :
    TwoSquare T₁₂ V₁ V₃ B₁₂ :=
  (w ≫ₕ w').whiskerHorizontal eT.inv eB.hom

namespace GuitartExact

set_option backward.defeqAttrib.useBackward true in
instance hComp [w.GuitartExact] [w'.GuitartExact] :
    (w ≫ₕ w').GuitartExact := by
  rw [← guitartExact_op_iff]
  have : (w ≫ₕ w').op = w.op ≫ᵥ w'.op := by ext; simp
  rw [this]
  exact inferInstanceAs (w.op ≫ᵥ w'.op).GuitartExact

instance hComp' {T₁₂ : C₁ ⥤ C₃} {B₁₂ : D₁ ⥤ D₃} (eT : T₁ ⋙ T₂ ≅ T₁₂) (eB : B₁ ⋙ B₂ ≅ B₁₂)
    [w.GuitartExact] [w'.GuitartExact] :
    (w.hComp' w' eT eB).GuitartExact := by
  dsimp only [TwoSquare.hComp']
  infer_instance

set_option backward.defeqAttrib.useBackward true in
/-- The canonical isomorphism between
`w.costructuredArrowRightwards Y₁ ⋙ w'.costructuredArrowRightwards (B₁.obj Y₁)` and
`(w ≫ₕ w').costructuredArrowRightwards Y₁`. -/
def costructuredArrowRightwardsComp (Y₁ : D₁) :
    w.costructuredArrowRightwards Y₁ ⋙ w'.costructuredArrowRightwards (B₁.obj Y₁) ≅
      (w ≫ₕ w').costructuredArrowRightwards Y₁ :=
  NatIso.ofComponents (fun _ => CostructuredArrow.isoMk (Iso.refl _))

lemma of_hComp [B₁.EssSurj] [w.GuitartExact] [(w ≫ₕ w').GuitartExact] :
    w'.GuitartExact := by
  rw [guitartExact_iff_final]
  intro Y₂
  rw [costructuredArrowRightwards_final_iff_of_iso _ (B₁.objObjPreimageIso Y₂).symm]
  have : (w.costructuredArrowRightwards (B₁.objPreimage Y₂) ⋙
      w'.costructuredArrowRightwards (B₁.obj (B₁.objPreimage Y₂))).Final :=
    (Functor.final_of_natIso (costructuredArrowRightwardsComp w w' _).symm :)
  exact Functor.final_of_final_comp (w.costructuredArrowRightwards (B₁.objPreimage Y₂)) _

lemma of_hComp' {T₁₂ : C₁ ⥤ C₃} {B₁₂ : D₁ ⥤ D₃} (eT : T₁ ⋙ T₂ ≅ T₁₂) (eB : B₁ ⋙ B₂ ≅ B₁₂)
    [B₁.EssSurj] [w.GuitartExact] [h : (w.hComp' w' eT eB).GuitartExact] :
    w'.GuitartExact := by
  dsimp [TwoSquare.hComp'] at h
  rw [whiskerHorizontal_iff] at h
  exact of_hComp w w'

lemma hComp_iff_of_essSurj [B₁.EssSurj] [w.GuitartExact] :
    (w ≫ₕ w').GuitartExact ↔ w'.GuitartExact :=
  ⟨fun _ ↦ of_hComp w w', fun _ ↦ inferInstance⟩

lemma hComp'_iff_of_essSurj
    {T₁₂ : C₁ ⥤ C₃} {B₁₂ : D₁ ⥤ D₃} (eT : T₁ ⋙ T₂ ≅ T₁₂) (eB : B₁ ⋙ B₂ ≅ B₁₂)
    [B₁.EssSurj] [w.GuitartExact] :
    (w.hComp' w' eT eB).GuitartExact ↔ w'.GuitartExact :=
  ⟨fun _ ↦ of_hComp' w w' eT eB, fun _ ↦ inferInstance⟩

set_option backward.defeqAttrib.useBackward true in
lemma hComp_iff_of_equivalences (eT : C₂ ≌ C₃) (eB : D₂ ≌ D₃)
    (w' : eT.functor ⋙ V₃ ≅ V₂ ⋙ eB.functor) :
    (w ≫ₕ w'.hom).GuitartExact ↔ w.GuitartExact := by
  let w'' : V₂.op ⋙ eB.op.functor ≅ eT.op.functor ⋙ V₃.op := NatIso.op w'
  have : (w ≫ₕ w'.hom).op = (w.op ≫ᵥ w''.hom) := by ext; simp [w'']
  rw [← guitartExact_op_iff, ← guitartExact_op_iff w,
    ← vComp_iff_of_equivalences _ _ _ w'', this]
  rfl

lemma hComp'_iff_of_equivalences (E : C₂ ≌ C₃) (E' : D₂ ≌ D₃)
    (w' : E.functor ⋙ V₃ ≅ V₂ ⋙ E'.functor)
    {T₁₂ : C₁ ⥤ C₃} {B₁₂ : D₁ ⥤ D₃} (eT : T₁ ⋙ E.functor ≅ T₁₂)
    (eB : B₁ ⋙ E'.functor ≅ B₁₂) :
    (w.hComp' w'.hom eT eB).GuitartExact ↔ w.GuitartExact := by
  rw [← hComp_iff_of_equivalences w E E' w', TwoSquare.hComp', whiskerHorizontal_iff]

end GuitartExact

end HorizontalComposition

end TwoSquare

end CategoryTheory
