import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.Linear
import Mathlib.CategoryTheory.Localization.Linear
import Mathlib.CategoryTheory.Shift.Linear

open CategoryTheory Category Limits Pretriangulated ZeroObject Preadditive

universe w v u

variable (R : Type w) [Ring R] (C : Type u) [Category.{v} C] [Abelian C] [Linear R C]
  [HasDerivedCategory C]

namespace DerivedCategory

noncomputable instance : Linear R (DerivedCategory C) :=
  Localization.linear R (DerivedCategory.Qh : _ ⥤ DerivedCategory C)
    (HomotopyCategory.qis C _)

instance : Functor.Linear R (DerivedCategory.Qh : _ ⥤ DerivedCategory C) :=
  Localization.functor_linear _ _ _

instance : Functor.Linear R (DerivedCategory.Q : _ ⥤ DerivedCategory C) :=
  Functor.linear_of_iso R (quotientCompQhIso C)

instance (n : ℤ) : (shiftFunctor (DerivedCategory C) n).Linear R := by
  rw [← Localization.functor_linear_iff
    Qh (HomotopyCategory.subcategoryAcyclic C).W R
    (shiftFunctor (HomotopyCategory C (ComplexShape.up ℤ)) n ⋙ Qh)
    (shiftFunctor (DerivedCategory C) n)]
  infer_instance

end DerivedCategory
