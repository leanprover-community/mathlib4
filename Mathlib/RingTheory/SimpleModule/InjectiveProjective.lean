/-
Copyright (c) 2025 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
module

public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.Algebra.Module.Injective
public import Mathlib.Algebra.Module.Projective
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

/-!
If `R` is a semisimple ring, then any `R`-module is both injective and projective.

-/

public section

namespace Module

variable (R : Type*) [Ring R] [IsSemisimpleRing R] (M : Type*) [AddCommGroup M] [Module R M]

theorem injective_of_isSemisimpleRing : Module.Injective R M where
  out X Y _ _ _ _ f hf g :=
    let ⟨h, comp⟩ := IsSemisimpleModule.extension_property f hf g
    ⟨h, fun _ ↦ by rw [← comp, LinearMap.comp_apply]⟩

theorem projective_of_isSemisimpleRing : Module.Projective R M :=
  .of_lifting_property'' (IsSemisimpleModule.lifting_property · · _)

end Module
