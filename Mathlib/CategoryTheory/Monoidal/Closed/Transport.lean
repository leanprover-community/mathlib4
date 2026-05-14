/-
Copyright (c) 2025 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Transport
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Init
import Mathlib.Tactic.CategoryTheory.CategoryStar
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Util.CompileInductive

/-!

# Transporting a closed monoidal structure along an equivalence of categories
-/

public section

open CategoryTheory Monoidal

namespace CategoryTheory.MonoidalClosed

noncomputable instance {C D : Type*} [Category* C] [Category* D]
    (e : C ≌ D) [MonoidalCategory C] [MonoidalClosed C] :
    MonoidalClosed (Transported e) :=
  MonoidalClosed.ofEquiv _ (equivalenceTransported e).symm.toAdjunction

end CategoryTheory.MonoidalClosed
