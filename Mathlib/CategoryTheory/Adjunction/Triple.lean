/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Monad.Adjunction
/-!

# Adjoint triples

This file concerns adjoint triples `F ⊣ G ⊣ H` of functors `F H : C ⥤ D`, `G : D ⥤ C`.

Currently, the only result is that `F` is fully faithful if and only if `H` is fully faithful.
-/

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category C] [Category D]
variable {F H : C ⥤ D} {G : D ⥤ C}
variable (adj₁ : F ⊣ G) (adj₂ : G ⊣ H)

lemma isIso_unit_iff_isIso_counit : IsIso adj₁.unit ↔ IsIso adj₂.counit := by
  let adj : F ⋙ G ⊣ H ⋙ G := adj₁.comp adj₂
  constructor
  · intro h
    let idAdj : 𝟭 C ⊣ H ⋙ G := adj.ofNatIsoLeft (asIso adj₁.unit).symm
    exact adj₂.isIso_counit_of_iso (idAdj.rightAdjointUniq id)
  · intro h
    let adjId : F ⋙ G ⊣ 𝟭 C := adj.ofNatIsoRight (asIso adj₂.counit)
    exact adj₁.isIso_unit_of_iso (adjId.leftAdjointUniq id)

/--
Given an adjoint triple `F ⊣ G ⊣ H`, the left adjoint `F` is fully faithful if and only if the
right adjoint `H` is fully faithful.
-/
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
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

end CategoryTheory.Adjunction
