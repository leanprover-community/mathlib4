/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Localization.Predicate

#align_import category_theory.localization.opposite from "leanprover-community/mathlib"@"8efef279998820353694feb6ff5631ed0d309ecc"

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
#align category_theory.localization.strict_universal_property_fixed_target.op CategoryTheory.Localization.StrictUniversalPropertyFixedTarget.op

instance isLocalization_op : W.Q.op.IsLocalization W.op :=
  Functor.IsLocalization.mk' W.Q.op W.op (strictUniversalPropertyFixedTargetQ W _).op
    (strictUniversalPropertyFixedTargetQ W _).op
#align category_theory.localization.is_localization_op CategoryTheory.Localization.isLocalization_op

end Localization

namespace Functor

instance IsLocalization.op [L.IsLocalization W] : L.op.IsLocalization W.op :=
  IsLocalization.of_equivalence_target W.Q.op W.op L.op (Localization.equivalenceFromModel L W).op
    (NatIso.op (Localization.qCompEquivalenceFromModelFunctorIso L W).symm)
#align category_theory.functor.is_localization.op CategoryTheory.Functor.IsLocalization.op

end Functor

end CategoryTheory
