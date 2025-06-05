/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Abelian.Basic

/-!
# Monomorphisms are stable under cobase change

In an abelian category `C`, the class of morphism
`monomorphisms C` is stable under cobase change and
`epimorphisms C` is stable under base change.

-/

universe v u

namespace CategoryTheory.Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]

open MorphismProperty

instance : (monomorphisms C).IsStableUnderCobaseChange :=
  IsStableUnderCobaseChange.mk' (fun _ _ _ f g _ hf ↦ by
    simp only [monomorphisms.iff] at hf ⊢
    infer_instance)

instance : (epimorphisms C).IsStableUnderBaseChange :=
  IsStableUnderBaseChange.mk' (fun _ _ _ f g _ hf ↦ by
    simp only [epimorphisms.iff] at hf ⊢
    infer_instance)

end CategoryTheory.Abelian
