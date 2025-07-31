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

open CategoryTheory Limits Functor Adjunction Triple

variable {C D : Type*} [Category C] [Category D]
variable (L : C ⥤ D) (F : D ⥤ C) (G : C ⥤ D) (R : D ⥤ C)

/-- Structure containing the three adjunctions of an adjoint triple `L ⊣ F ⊣ G ⊣ R`. -/
structure CategoryTheory.Adjunction.Quadruple where
  /-- Adjunction `L ⊣ F` of the adjoint quadruple `L ⊣ F ⊣ G ⊣ H`. -/
  adj₁ : L ⊣ F
  /-- Adjunction `F ⊣ G` of the adjoint quadruple `L ⊣ F ⊣ G ⊣ H`. -/
  adj₂ : F ⊣ G
  /-- Adjunction `G ⊣ R` of the adjoint quadruple `L ⊣ F ⊣ G ⊣ H`. -/
  adj₃ : G ⊣ R

namespace CategoryTheory.Adjunction.Quadruple

variable {L F G R} (q : Quadruple L F G R)

/-- The left part of an adjoint quadruple `L ⊣ F ⊣ G ⊣ R`. -/
@[simps]
def leftTriple : Triple L F G where
  adj₁ := q.adj₁
  adj₂ := q.adj₂

/-- The right part of an adjoint quadruple `L ⊣ F ⊣ G ⊣ R`. -/
@[simps]
def rightTriple : Triple F G R where
  adj₁ := q.adj₂
  adj₂ := q.adj₃

/-- The adjoint quadruple `R.op ⊣ G.op ⊣ F.op ⊣ L.op` dual to an
adjoint quadruple `L ⊣ F ⊣ G ⊣ R`. -/
@[simps]
protected def op : Quadruple R.op G.op F.op L.op where
  adj₁ := q.adj₃.op
  adj₂ := q.adj₂.op
  adj₃ := q.adj₁.op

@[simp]
lemma op_leftTriple : q.op.leftTriple = q.rightTriple.op := rfl

@[simp]
lemma op_rightTriple : q.op.rightTriple = q.leftTriple.op := rfl

section RightFullyFaithful

variable [F.Full] [F.Faithful]

/-- For an adjoint quadruple `L ⊣ F ⊣ G ⊣ R` where `F` and `R` are fully faithful, all components
of the natural transformation `G ⟶ L` are epic iff all components of the natural transformation
`F ⟶ R` are monic. -/
lemma leftTriple_rightToLeft_app_epi_iff_rightTriple_leftToRight_app_mono :
    (∀ X, Epi (q.leftTriple.rightToLeft.app X)) ↔ ∀ X, Mono (q.rightTriple.leftToRight.app X) := by
  simp_rw [Triple.mono_leftToRight_app_iff_mono_adj₂_unit_app, Triple.rightToLeft_eq_counits]
  dsimp; simp only [NatIso.isIso_inv_app, Functor.comp_obj, Functor.id_obj,
    whiskerLeft_app, Category.comp_id, Category.id_comp]
  simp_rw [epi_comp_iff_of_epi, epi_iff_forall_injective, mono_iff_forall_injective]
  rw [forall_comm]; refine forall_congr' fun X ↦ forall_congr' fun Y ↦ ?_
  rw [← (q.adj₁.homEquiv _ _).comp_injective _]
  change (fun g ↦ q.adj₁.homEquiv _ _ _).Injective ↔ _
  simp_rw [q.adj₁.homEquiv_naturality_left]
  refine ((q.adj₁.homEquiv _ _).injective_comp fun f ↦ _).trans ?_
  rw [← ((q.adj₂.homEquiv _ _).trans (q.adj₃.homEquiv _ _)).comp_injective _]
  change (fun g ↦ q.adj₃.homEquiv _ _ (q.adj₂.homEquiv _ _ _)).Injective ↔ _
  simp_rw [← q.adj₂.homEquiv_symm_id, ← q.adj₂.homEquiv_naturality_right_symm]
  simp_rw [← q.adj₃.homEquiv_id, ← q.adj₃.homEquiv_naturality_left]
  simp

/-- For an adjoint quadruple `L ⊣ F ⊣ G ⊣ R` where `F` and `R` are fully faithful, their domain
has all pushouts and their codomain has all pullbacks, the natural transformation `G ⟶ L` is epic
iff the natural transformation `F ⟶ R` is monic. -/
lemma leftTriple_rightToLeft_epi_iff [HasPullbacks C] [HasPushouts D] :
    Epi q.leftTriple.rightToLeft ↔ Mono q.rightTriple.leftToRight := by
  rw [NatTrans.epi_iff_epi_app, NatTrans.mono_iff_mono_app]
  exact q.leftTriple_rightToLeft_app_epi_iff_rightTriple_leftToRight_app_mono

end RightFullyFaithful

section LeftFullyFaithful

variable [L.Full] [L.Faithful] [G.Full] [G.Faithful]

/-- For an adjoint quadruple `L ⊣ F ⊣ G ⊣ R` where `L` and `G` are fully faithful, all components
of the natural transformation `L ⟶ G` are epic iff all components of the natural transformation
`R ⟶ F` are monic. -/
lemma leftTriple_leftToRight_app_epi_iff_rightTriple_rightToLeft_app_mono :
    (∀ X, Epi (q.leftTriple.leftToRight.app X)) ↔ ∀ X, Mono (q.rightTriple.rightToLeft.app X) := by
  have h := q.op.leftTriple_rightToLeft_app_epi_iff_rightTriple_leftToRight_app_mono
  rw [← (Opposite.equivToOpposite (α := C)).forall_congr_right] at h
  rw [← (Opposite.equivToOpposite (α := D)).forall_congr_right] at h
  simp_rw [Opposite.equivToOpposite_coe, op_leftTriple, op_rightTriple, ← rightToLeft_app_op,
    ← leftToRight_app_op, op_mono_iff, op_epi_iff] at h
  exact h.symm

/-- For an adjoint quadruple `L ⊣ F ⊣ G ⊣ R` where `L` and `G` are fully faithful, their domain
has all pushouts and their codomain has all pullbacks, the natural transformation `L ⟶ G` is epic
iff the natural transformation `R ⟶ F` is monic. -/
lemma LToG_epi_iff_RToF_mono [HasPullbacks C] [HasPushouts D] :
    Epi q.leftTriple.leftToRight ↔ Mono q.rightTriple.rightToLeft := by
  rw [NatTrans.epi_iff_epi_app, NatTrans.mono_iff_mono_app]
  exact q.leftTriple_leftToRight_app_epi_iff_rightTriple_rightToLeft_app_mono

end LeftFullyFaithful

end CategoryTheory.Adjunction.Quadruple
