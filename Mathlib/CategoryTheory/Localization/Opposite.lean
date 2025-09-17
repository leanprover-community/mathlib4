/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Localization.Equivalence

/-!

# Localization of the opposite category

If a functor `L : C ⥤ D` is a localization functor for `W : MorphismProperty C`, it
is shown in this file that `L.op : Cᵒᵖ ⥤ Dᵒᵖ` is also a localization functor.

-/


noncomputable section

open CategoryTheory CategoryTheory.Category

namespace CategoryTheory

variable {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {W : MorphismProperty C}

namespace Localization

/-- If `L : C ⥤ D` satisfies the universal property of the localisation
for `W : MorphismProperty C`, then `L.op` also does. -/
def StrictUniversalPropertyFixedTarget.op {E : Type*} [Category E]
    (h : StrictUniversalPropertyFixedTarget L W Eᵒᵖ) :
    StrictUniversalPropertyFixedTarget L.op W.op E where
  inverts := h.inverts.op
  lift F hF := (h.lift F.rightOp hF.rightOp).leftOp
  fac F hF := by
    convert congr_arg Functor.leftOp (h.fac F.rightOp hF.rightOp)
  uniq F₁ F₂ eq := by
    suffices F₁.rightOp = F₂.rightOp by
      rw [← F₁.rightOp_leftOp_eq, ← F₂.rightOp_leftOp_eq, this]
    have eq' := congr_arg Functor.rightOp eq
    exact h.uniq _ _ eq'

instance isLocalization_op : W.Q.op.IsLocalization W.op :=
  Functor.IsLocalization.mk' W.Q.op W.op (strictUniversalPropertyFixedTargetQ W _).op
    (strictUniversalPropertyFixedTargetQ W _).op

end Localization

variable (L W)
variable [L.IsLocalization W]

namespace Functor

instance IsLocalization.op : L.op.IsLocalization W.op :=
  IsLocalization.of_equivalence_target W.Q.op W.op L.op (Localization.equivalenceFromModel L W).op
    (NatIso.op (Localization.qCompEquivalenceFromModelFunctorIso L W).symm)

instance IsLocalization.unop (L : Cᵒᵖ ⥤ Dᵒᵖ) (W : MorphismProperty Cᵒᵖ)
    [L.IsLocalization W] : L.unop.IsLocalization W.unop :=
  have : CatCommSq (opOpEquivalence C).functor L.op L.unop
    (opOpEquivalence D).functor := ⟨Iso.refl _⟩
  of_equivalences L.op W.op L.unop W.unop
    (opOpEquivalence C) (opOpEquivalence D)
    (fun _ _ _ hf ↦ MorphismProperty.le_isoClosure _ _ hf)
    (fun _ _ _ hf ↦ by
      have := Localization.inverts L W _ hf
      dsimp
      infer_instance)

@[simp]
lemma op_iff (L : C ⥤ D) (W : MorphismProperty C) :
    L.op.IsLocalization W.op ↔ L.IsLocalization W :=
  ⟨fun _ ↦ inferInstanceAs (L.op.unop.IsLocalization W.op.unop),
    fun _ ↦ inferInstance⟩

end Functor

namespace Localization

lemma isoOfHom_unop {X Y : Cᵒᵖ} (w : X ⟶ Y) (hw : W.op w) :
    (isoOfHom L.op W.op w hw).unop = (isoOfHom L W w.unop hw) := by ext; rfl

lemma isoOfHom_op_inv {X Y : Cᵒᵖ} (w : X ⟶ Y) (hw : W.op w) :
    (isoOfHom L.op W.op w hw).inv = (isoOfHom L W w.unop hw).inv.op :=
  congr_arg Quiver.Hom.op (congr_arg Iso.inv (isoOfHom_unop L W w hw))

end Localization

end CategoryTheory
