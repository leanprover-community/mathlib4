/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Shift.CommShift
import Mathlib.CategoryTheory.Localization.Linear

/-!
# Localization of the linearity of the shift functors

If `L : C ⥤ D` is a localization functor with respect to `W : MorphismProperty C`
and both `C` and `D` have been equipped with `R`-linear category structures
such that `L` is `R`-linear and the shift functors on `C` are `R`-linear,
then the shift functors on `D` are `R`-linear.

-/

namespace CategoryTheory

namespace Shift

variable (R : Type*) [Ring R] {C : Type _} [Category C] [Preadditive C] [Linear R C]
  {D : Type*} [Category D] [Preadditive D] [Linear R D]
  {M : Type*} [AddMonoid M] [HasShift C M]
  [∀ (n : M), (shiftFunctor C n).Linear R]
  (L : C ⥤ D) (W : MorphismProperty C)

lemma linear_of_localization [L.IsLocalization W] [L.Linear R] [HasShift D M]
    [L.CommShift M] (n : M) : (shiftFunctor D n).Linear R := by
  have : Localization.Lifting L W (shiftFunctor C n ⋙ L) (shiftFunctor D n) :=
    ⟨(L.commShiftIso n).symm⟩
  rw [← Localization.functor_linear_iff L W R (shiftFunctor C n ⋙ L) (shiftFunctor D n)]
  infer_instance

instance [HasShift W.Localization M] [W.Q.CommShift M] [Preadditive W.Localization]
    [Linear R W.Localization] [W.Q.Linear R] (n : M) :
    (shiftFunctor W.Localization n).Linear R := linear_of_localization _ W.Q W _

instance (n : M) [W.HasLocalization] [HasShift W.Localization' M] [W.Q'.CommShift M]
    [Preadditive W.Localization'] [Linear R W.Localization'] [W.Q'.Linear R] :
    (shiftFunctor W.Localization' n).Linear R :=
  linear_of_localization _ W.Q' W _

end Shift

end CategoryTheory
