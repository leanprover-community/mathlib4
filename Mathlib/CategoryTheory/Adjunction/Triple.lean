import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Monad.Adjunction

open CategoryTheory Adjunction

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category C] [Category D]
variable {F H : C ⥤ D} {G : D ⥤ C}
variable (adj₁ : F ⊣ G) (adj₂ : G ⊣ H)

lemma isIso_unit_iff_isIso_counit  :
    IsIso adj₁.unit ↔ IsIso adj₂.counit := by
  let adj : F ⋙ G ⊣ H ⋙ G := adj₁.comp adj₂
  constructor
  · intro h
    let adjId₂ : 𝟭 C ⊣ H ⋙ G := adj.ofNatIsoLeft (asIso adj₁.unit).symm
    exact adj₂.isIso_counit_of_iso (adjId₂.rightAdjointUniq id)
  · intro h
    let adjId₁ : F ⋙ G ⊣ 𝟭 C := adj.ofNatIsoRight (asIso adj₂.counit)
    exact adj₁.isIso_unit_of_iso (adjId₁.leftAdjointUniq id)

noncomputable def fullyFaithfulEquiv : F.FullyFaithful ≃ H.FullyFaithful where
  toFun h :=
    haveI := h.full
    haveI := h.faithful
    haveI : IsIso adj₂.counit := by
      rw [← adj₁.isIso_unit_iff_isIso_counit adj₂]
      infer_instance
    adj₂.fullyFaithfulROfIsIsoCounit
  invFun h :=
    haveI := h.full
    haveI := h.faithful
    haveI : IsIso adj₁.unit := by
      rw [adj₁.isIso_unit_iff_isIso_counit adj₂]
      infer_instance
    adj₁.fullyFaithfulLOfIsIsoUnit
  left_inv h := by apply Subsingleton.elim
  right_inv h := by apply Subsingleton.elim

end CategoryTheory.Adjunction
