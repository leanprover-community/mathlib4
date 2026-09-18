/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.LeftExact

/-!
# Linear categories of sheaves and linear sheafification
-/

@[expose] public section

universe u

open CategoryTheory

namespace CategoryTheory

variable {C : Type*} [Category C] (J : GrothendieckTopology C) (A : Type*) [Category A]
    [Preadditive A]

instance [HasSheafify J A] [Limits.HasBinaryProducts A] : (presheafToSheaf J A).Additive :=
  Functor.additive_of_preserves_binary_products _

variable (R : Type u) [Ring R]

instance [Linear R A] [HasWeakSheafify J A] :
    (presheafToSheaf J A).Linear R where
  map_smul {P Q} f r := by
    apply Sheaf.hom_ext
    rw [show (r • (presheafToSheaf J A).map f).hom =
      r • ((presheafToSheaf J A).map f).hom from
      (sheafToPresheaf J A).map_smul r ((presheafToSheaf J A).map f)]
    apply sheafify_hom_ext _ _ _
      ((presheafToSheaf J A).obj Q).property
    rw [← toSheafify_naturality]
    rw [Linear.comp_smul]
    rw [← toSheafify_naturality]
    rw [← Linear.smul_comp]

end CategoryTheory
