/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

#align_import category_theory.limits.shapes.equivalence from "leanprover-community/mathlib"@"ea74dc9f981009c33b9971f3389509a88c95cf07"

/-!
# Transporting existence of specific limits across equivalences

For now, we only treat the case of initial and terminal objects, but other special shapes can be
added in the future.
-/


open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

theorem hasInitial_of_equivalence (e : D ⥤ C) [e.IsEquivalence] [HasInitial C] : HasInitial D :=
  Adjunction.hasColimitsOfShape_of_equivalence e
#align category_theory.has_initial_of_equivalence CategoryTheory.hasInitial_of_equivalence

theorem Equivalence.hasInitial_iff (e : C ≌ D) : HasInitial C ↔ HasInitial D :=
  ⟨fun (_ : HasInitial C) => hasInitial_of_equivalence e.inverse,
    fun (_ : HasInitial D) => hasInitial_of_equivalence e.functor⟩
#align category_theory.equivalence.has_initial_iff CategoryTheory.Equivalence.hasInitial_iff

theorem hasTerminal_of_equivalence (e : D ⥤ C) [e.IsEquivalence] [HasTerminal C] : HasTerminal D :=
  Adjunction.hasLimitsOfShape_of_equivalence e
#align category_theory.has_terminal_of_equivalence CategoryTheory.hasTerminal_of_equivalence

theorem Equivalence.hasTerminal_iff (e : C ≌ D) : HasTerminal C ↔ HasTerminal D :=
  ⟨fun (_ : HasTerminal C) => hasTerminal_of_equivalence e.inverse,
    fun (_ : HasTerminal D) => hasTerminal_of_equivalence e.functor⟩
#align category_theory.equivalence.has_terminal_iff CategoryTheory.Equivalence.hasTerminal_iff

end CategoryTheory
