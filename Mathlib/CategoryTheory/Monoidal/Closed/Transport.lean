/-
Copyright (c) 2025 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Monoidal.Transport

/-!

# Transporting a closed monoidal structure along an equivalence of categories
-/

open CategoryTheory Monoidal

namespace CategoryTheory.MonoidalClosed

noncomputable instance {C D : Type*} [Category C] [Category D]
    (e : C ≌ D) [MonoidalCategory C] [MonoidalClosed C] :
    MonoidalClosed (Transported e) :=
  MonoidalClosed.ofEquiv _ (equivalenceTransported e).symm.toAdjunction

end CategoryTheory.MonoidalClosed
