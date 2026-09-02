/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus

/-!
# ...


-/

@[expose] public section

-- to be moved
namespace CochainComplex.Plus

open CategoryTheory Limits

variable {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]

variable (C) in
noncomputable abbrev singleFunctor (n : ℤ) : C ⥤ CochainComplex.Plus C :=
  ObjectProperty.lift _ (HomologicalComplex.single C (.up ℤ) n) (fun _ ↦ ⟨n, inferInstance⟩)

end CochainComplex.Plus

namespace CategoryTheory

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]

namespace Functor

variable [EnoughInjectives C] (F : C ⥤ D) [F.Additive]

/-- If `F : C ⥤ D` is an additive functor between abelian categories,
with enough injectives in `C`, and `n : ℕ`, this is `n`th right derived
functors of `F`. It is defined using the (total) right derived
functor `F.rightDerivedFunctorPlus` on the bounded below derived categories. -/
noncomputable def rightDerived (n : ℕ) : C ⥤ D :=
  DerivedCategory.Plus.singleFunctor C 0 ⋙ F.rightDerivedFunctorPlus ⋙
    DerivedCategory.Plus.homologyFunctor D n

instance (n : ℕ) : (F.rightDerived n).Additive := by
  dsimp [rightDerived]
  infer_instance

instance (X : C) (n : ℤ) [Injective X] :
    IsIso (F.rightDerivedFunctorPlusUnit.app
      ((CochainComplex.Plus.singleFunctor C n).obj X)) :=
  isIso_rightDerivedFunctorPlusUnit_app_of_isKInjective _ _ (by
    dsimp [CochainComplex.Plus.singleFunctor, ObjectProperty.lift]
    infer_instance)

end Functor

end CategoryTheory
