/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.Linear
import Mathlib.CategoryTheory.Localization.Linear
import Mathlib.CategoryTheory.Shift.Linear

/-!
# The derived category of a linear category is linear

-/

open CategoryTheory Category Limits Pretriangulated ZeroObject Preadditive

universe w v u

variable (R : Type w) [Ring R] (C : Type u) [Category.{v} C] [Abelian C] [Linear R C]
  [HasDerivedCategory C]

namespace DerivedCategory

noncomputable instance : Linear R (DerivedCategory C) :=
  Localization.linear R (DerivedCategory.Qh : _ ⥤ DerivedCategory C)
    (HomotopyCategory.quasiIso C _)

instance : Functor.Linear R (DerivedCategory.Qh : _ ⥤ DerivedCategory C) :=
  Localization.functor_linear _ _ _

instance : Functor.Linear R (DerivedCategory.Q : _ ⥤ DerivedCategory C) :=
  Functor.linear_of_iso _ (quotientCompQhIso C)

instance (n : ℤ) : (shiftFunctor (DerivedCategory C) n).Linear R := by
  rw [← Localization.functor_linear_iff
    Qh (HomotopyCategory.subcategoryAcyclic C).W R
    (shiftFunctor (HomotopyCategory C (ComplexShape.up ℤ)) n ⋙ Qh)
    (shiftFunctor (DerivedCategory C) n)]
  infer_instance

instance (n : ℤ) : Functor.Linear R (CochainComplex.singleFunctor C n) where
  map_smul f r := by
    dsimp [CochainComplex.singleFunctor, CochainComplex.singleFunctors,
      HomologicalComplex.single]
    aesop

instance (n : ℤ) :
    Functor.Linear R (HomotopyCategory.singleFunctor C n) :=
  inferInstanceAs (Functor.Linear R (CochainComplex.singleFunctor C n ⋙
    HomotopyCategory.quotient _ _))

instance (n : ℤ) :
    Functor.Linear R (DerivedCategory.singleFunctor C n) :=
  inferInstanceAs (Functor.Linear R (HomotopyCategory.singleFunctor C n ⋙ Qh))

end DerivedCategory
