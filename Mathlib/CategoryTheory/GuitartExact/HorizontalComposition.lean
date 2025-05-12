/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.GuitartExact.Opposite

/-!
# Horizontal composition of Guitart exact squares

In this file, we show that the horizontal composition of Guitart exact squares
is Guitart exact.

-/

namespace CategoryTheory

open Category

variable {C₁ C₂ C₃ D₁ D₂ D₃ : Type*} [Category C₁] [Category C₂] [Category C₃]
  [Category D₁] [Category D₂] [Category D₃]

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

/-- A 2-square stays Guitart exact if we replace the top and bottom functors
by isomorphic functors. See also `whiskerVertical_iff`. -/
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
  constructor
  · intro h
    have : w = (w.whiskerHorizontal α.inv β.hom).whiskerHorizontal α.symm.inv β.symm.hom := by
      ext
      dsimp
      simp only [whiskerHorizontal_app, assoc, Iso.hom_inv_id_app, comp_id,
        ← Functor.map_comp_assoc, Functor.map_id, id_comp]
    rw [this]
    exact whiskerHorizontal _ α.symm β.symm
  · intro h
    exact whiskerHorizontal w α β

instance [w.GuitartExact] (α : T' ⟶ T) (β : B ⟶ B')
    [IsIso α] [IsIso β] : (w.whiskerHorizontal α β).GuitartExact :=
  whiskerHorizontal w (asIso α).symm (asIso β)

end GuitartExact

end WhiskerHorizontal

namespace GuitartExact

variable {V₁ : C₁ ⥤ D₁} {T₁ : C₁ ⥤ C₂} {B₁ : D₁ ⥤ D₂} {V₂ : C₂ ⥤ D₂}
  (w : TwoSquare T₁ V₁ V₂ B₁)
  {T₂ : C₂ ⥤ C₃} {B₂ : D₂ ⥤ D₃} {V₃ : C₃ ⥤ D₃}
  (w' : TwoSquare T₂ V₂ V₃ B₂)

instance hComp [hw : w.GuitartExact] [hw' : w'.GuitartExact] :
    (w ≫ₕ w').GuitartExact := by
  rw [← guitartExact_op_iff] at hw hw' ⊢
  have : (w ≫ₕ w').op = w.op ≫ᵥ w'.op := by ext; simp
  rw [this]
  infer_instance

/-- The canonical isomorphism between
`w.costructuredArrowRightwards Y₁ ⋙ w'.costructuredArrowRightwards (B₁.obj Y₁)` and
`(w ≫ₕ w').costructuredArrowRightwards Y₁`. -/
def costructuredArrowRightwardsComp (Y₁ : D₁) :
    w.costructuredArrowRightwards Y₁ ⋙ w'.costructuredArrowRightwards (B₁.obj Y₁) ≅
      (w ≫ₕ w').costructuredArrowRightwards Y₁ :=
  NatIso.ofComponents (fun _ => CostructuredArrow.isoMk (Iso.refl _))

lemma of_hComp [B₁.EssSurj] [w.GuitartExact] [(w ≫ₕ w').GuitartExact] : w'.GuitartExact := by
  rw [guitartExact_iff_final]
  intro Y₂
  obtain ⟨Y₁, ⟨e⟩⟩ : ∃ (Y₁ : D₁), Nonempty (B₁.obj Y₁ ≅ Y₂):= ⟨_, ⟨B₁.objObjPreimageIso Y₂⟩⟩
  rw [costructuredArrowRightWards_final_iff_of_iso _ e.symm]
  have := Functor.final_of_natIso (costructuredArrowRightwardsComp w w' Y₁).symm
  exact Functor.final_of_final_comp (w.costructuredArrowRightwards Y₁) _

end GuitartExact

end TwoSquare

end CategoryTheory
