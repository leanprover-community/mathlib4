/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Util.CompileInductive

/-!
# Closed braided monoidal categories

Interactions between monoidal closed and braided category structures.

-/

@[expose] public section

universe v u u₂ v₂

namespace CategoryTheory

open Category MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

namespace ihom

instance [BraidedCategory C] (A : C) [Closed A] :
    (tensorRight A).IsLeftAdjoint :=
  Functor.isLeftAdjoint_of_iso (BraidedCategory.tensorLeftIsoTensorRight A)

end ihom

end CategoryTheory
