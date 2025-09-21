/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition

/-!
# Monomorphisms in Grothendieck abelian categories

In this file, we show that in a Grothendieck abelian category,
monomorphisms are stable under transfinite composition.

-/

universe w v u

namespace CategoryTheory

namespace IsGrothendieckAbelian

open MorphismProperty

instance {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C] :
    IsStableUnderTransfiniteComposition.{w} (monomorphisms C) := by
  infer_instance

end IsGrothendieckAbelian

end CategoryTheory
