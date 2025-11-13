/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.Additive
import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# The category of homological complexes is linear

In this file, we define the instance `Linear R (HomologicalComplex C c)` when the
category `C` is `R`-linear.

## TODO

- show lemmas like `HomologicalComplex.homologyMap_smul` (after doing the same
for short complexes in `Mathlib/Algebra/Homology/ShortComplex/Linear.lean`)

-/

open CategoryTheory

variable {R : Type*} [Semiring R] {C D : Type*} [Category C] [Preadditive C]
  [Category D] [Preadditive D] [CategoryTheory.Linear R C] [CategoryTheory.Linear R D]
  {ι : Type*} {c : ComplexShape ι}

namespace HomologicalComplex

variable {X Y : HomologicalComplex C c}

instance : SMul R (X ⟶ Y) where
  smul r f := { f := fun n => r • f.f n }

@[simp]
lemma smul_f_apply (r : R) (f : X ⟶ Y) (n : ι) : (r • f).f n = r • f.f n := rfl

@[simp]
lemma units_smul_f_apply (r : Rˣ) (f : X ⟶ Y) (n : ι) : (r • f).f n = r • f.f n := rfl

instance (X Y : HomologicalComplex C c) : Module R (X ⟶ Y) where
  one_smul a := by cat_disch
  smul_zero := by cat_disch
  smul_add := by cat_disch
  zero_smul := by cat_disch
  add_smul _ _ _ := by ext; apply add_smul
  mul_smul _ _ _ := by ext; apply mul_smul

instance : Linear R (HomologicalComplex C c) where

end HomologicalComplex

instance CategoryTheory.Functor.mapHomologicalComplex_linear
    (F : C ⥤ D) [F.Additive] [Functor.Linear R F] (c : ComplexShape ι) :
    Functor.Linear R (F.mapHomologicalComplex c) where
