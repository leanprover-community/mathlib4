/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Sites.Sheafification

/-!
# Additivity of sheafification
-/

public section

namespace CategoryTheory

variable {C : Type*} [Category C] (J : GrothendieckTopology C) (A : Type*) [Category A]

instance [Preadditive A] [HasSheafify J A] [Limits.HasBinaryProducts A] :
    (presheafToSheaf J A).Additive :=
  Functor.additive_of_preserves_binary_products _

end CategoryTheory
