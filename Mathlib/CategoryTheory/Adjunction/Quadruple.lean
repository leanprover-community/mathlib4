/-
Copyright (c) 2025 Ben Eltschig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig
-/
import Mathlib.CategoryTheory.Adjunction.Triple

/-!
# Adjoint quadruples

This file concerns adjoint quadruples `L ⊣ F ⊣ G ⊣ R` of functors `L G : C ⥤ D`, `F R : D ⥤ C`.
Currently the only two results are the following:
* When `F` and `R` are fully faithful, the components of the induced natural transformation `G ⟶ L`
  are epic iff the components of the natural transformation `F ⟶ R` are monic.
* When `L` and `G` are fully faithful, the components of the induced natural transformation `L ⟶ G`
  are epic iff the components of the natural transformation `R ⟶ F` are monic.
-/

open CategoryTheory Limits

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category C] [Category D]
variable {L G : C ⥤ D} {F R : D ⥤ C}
variable (adj₁ : L ⊣ F) (adj₂ : F ⊣ G) (adj₃ : G ⊣ R)

section FRFullyFaithful

variable [F.Full] [F.Faithful]

/-- For an adjoint quadruple `L ⊣ F ⊣ G ⊣ R` where `F` and `R` are fully faithful, all components
of the natural transformation `G ⟶ L` are epic iff all components of the natural transformation
`F ⟶ R` are monic. -/
lemma GToL_app_epi_iff_FToR_app_mono :
    (∀ X, Epi ((HToF adj₁ adj₂).app X)) ↔ ∀ X, Mono ((FToH adj₂ adj₃).app X) := by
  simp_rw [FToH_app_mono_iff_unit_app_mono, HToF_eq_counits]
  dsimp; simp only [NatIso.isIso_inv_app, Functor.comp_obj, Functor.id_obj,
    whiskerLeft_app, Category.comp_id, Category.id_comp]
  simp_rw [epi_isIso_comp_iff, epi_iff_forall_injective, mono_iff_forall_injective]
  rw [forall_comm]; refine forall_congr' fun X ↦ forall_congr' fun Y ↦ ?_
  rw [← (adj₁.homEquiv _ _).comp_injective _]
  change (fun g ↦ adj₁.homEquiv _ _ _).Injective ↔ _
  simp_rw [adj₁.homEquiv_naturality_left]
  refine ((adj₁.homEquiv _ _).injective_comp fun f ↦ _).trans ?_
  rw [← ((adj₂.homEquiv _ _).trans (adj₃.homEquiv _ _)).comp_injective _]
  change (fun g ↦ adj₃.homEquiv _ _ (adj₂.homEquiv _ _ _)).Injective ↔ _
  simp_rw [← adj₂.homEquiv_symm_id, ← adj₂.homEquiv_naturality_right_symm]
  simp_rw [← adj₃.homEquiv_id, ← adj₃.homEquiv_naturality_left]
  simp

/-- For an adjoint quadruple `L ⊣ F ⊣ G ⊣ R` where `F` and `R` are fully faithful, their domain
has all pushouts and their codomain has all pullbacks, the natural transformation `G ⟶ L` is epic
iff the natural transformation `F ⟶ R` is monic. -/
lemma GToL_epi_iff_FToR_mono [HasPullbacks C] [HasPushouts D] :
    Epi (HToF adj₁ adj₂) ↔ Mono (FToH adj₂ adj₃) := by
  rw [NatTrans.epi_iff_epi_app, NatTrans.mono_iff_mono_app]
  exact adj₁.GToL_app_epi_iff_FToR_app_mono adj₂ adj₃

end FRFullyFaithful

section LGFullyFaithful

variable [L.Full] [L.Faithful] [G.Full] [G.Faithful]

/-- For an adjoint quadruple `L ⊣ F ⊣ G ⊣ R` where `L` and `G` are fully faithful, all components
of the natural transformation `L ⟶ G` are epic iff all components of the natural transformation
`R ⟶ F` are monic. -/
lemma LToG_app_epi_iff_RToF_app_mono :
    (∀ X, Epi ((FToH adj₁ adj₂).app X)) ↔ ∀ X, Mono ((HToF adj₂ adj₃).app X) := by
  have h := GToL_app_epi_iff_FToR_app_mono adj₃.op adj₂.op adj₁.op
  rw [← (Opposite.equivToOpposite (α := C)).forall_congr_right] at h
  rw [← (Opposite.equivToOpposite (α := D)).forall_congr_right] at h
  simp_rw [Opposite.equivToOpposite_coe, ← HToF_app_op, ← FToH_app_op, op_mono_iff, op_epi_iff] at h
  exact h.symm

/-- For an adjoint quadruple `L ⊣ F ⊣ G ⊣ R` where `L` and `G` are fully faithful, their domain
has all pushouts and their codomain has all pullbacks, the natural transformation `L ⟶ G` is epic
iff the natural transformation `R ⟶ F` is monic. -/
lemma LToG_epi_iff_RToF_mono [HasPullbacks C] [HasPushouts D] :
    Epi (FToH adj₁ adj₂) ↔ Mono (HToF adj₂ adj₃) := by
  rw [NatTrans.epi_iff_epi_app, NatTrans.mono_iff_mono_app]
  exact adj₁.LToG_app_epi_iff_RToF_app_mono adj₂ adj₃

end LGFullyFaithful

end CategoryTheory.Adjunction
