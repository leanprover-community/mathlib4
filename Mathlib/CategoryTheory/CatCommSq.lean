import Mathlib.CategoryTheory.Whiskering

namespace CategoryTheory

variable {C₁ C₂ C₃ C₄ C₅ C₆ : Type _} [Category C₁] [Category C₂] [Category C₃] [Category C₄]
  [Category C₅] [Category C₆]
  (L : C₁ ⥤ C₃) (T : C₁ ⥤ C₂) (R : C₂ ⥤ C₄) (B : C₃ ⥤ C₄)

/-- `CatCommSq L T R B` expresses that there is a 2-commutative square of functors, where
the functors `L`, `T`, `R` and `B` are respectively the left, top, right and bottom functors
of the square. -/
class CatCommSq where
  /-- the isomorphism corresponding to a 2-commutative diagram -/
  iso' : T ⋙ R ≅ L ⋙ B

namespace CatCommSq

/-- Assuming `[CatCommSq L T R B]`, `iso L T R B` is the isomorphism `T ⋙ R ≅ L ⋙ B`
given by the 2-commutative square. -/
def iso [h : CatCommSq L T R B] : T ⋙ R ≅ L ⋙ B := h.iso'

variable {L T R B}

section hcomp

variable (T₁ : C₁ ⥤ C₂) (T₂ : C₂ ⥤ C₃) (V₁ : C₁ ⥤ C₄) (V₂ : C₂ ⥤ C₅) (V₃ : C₃ ⥤ C₆)
  (B₁ : C₄ ⥤ C₅) (B₂ : C₅ ⥤ C₆)
  [CatCommSq V₁ T₁ V₂ B₁] [CatCommSq V₂ T₂ V₃ B₂]

/-- horizontal composition of 2-commutative squares -/
def hComp : CatCommSq V₁ (T₁ ⋙ T₂) V₃ (B₁ ⋙ B₂) :=
  mk (Functor.associator _ _ _ ≪≫ isoWhiskerLeft T₁ (iso V₂ T₂ V₃ B₂) ≪≫
    (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (iso V₁ T₁ V₂ B₁) B₂ ≪≫ Functor.associator _ _ _)

@[simp]
lemma hComp_iso'_hom_app (X : C₁) :
    (hComp T₁ T₂ V₁ V₂ V₃ B₁ B₂).iso'.hom.app X =
      (iso V₂ T₂ V₃ B₂).hom.app (T₁.obj X) ≫ B₂.map ((iso V₁ T₁ V₂ B₁).hom.app X) := by
  dsimp [hComp]
  aesop

@[simp]
lemma hComp_iso'_inv_app (X : C₁) :
    (hComp T₁ T₂ V₁ V₂ V₃ B₁ B₂).iso'.inv.app X =
      B₂.map ((iso V₁ T₁ V₂ B₁).inv.app X) ≫ (iso V₂ T₂ V₃ B₂).inv.app (T₁.obj X) := by
  dsimp [hComp]
  aesop

end hcomp

end CatCommSq

end CategoryTheory
