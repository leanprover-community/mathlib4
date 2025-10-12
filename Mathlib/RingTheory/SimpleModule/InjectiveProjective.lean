/-
Copyright (c) 2025 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.Algebra.Module.Injective
import Mathlib.Algebra.Module.Projective

/-!
If `R` is a semisimple ring, then any `R`-module is both injective and projective.

-/

namespace Module

variable (R : Type*) [Ring R] [IsSemisimpleRing R] (M : Type*) [AddCommGroup M] [Module R M]

theorem injective_of_isSemisimpleRing : Module.Injective R M where
  out X Y _ _ _ _ f hf g :=
    let ⟨h, comp⟩ := IsSemisimpleModule.extension_property f hf g
    ⟨h, fun _ ↦ by rw [← comp, LinearMap.comp_apply]⟩

theorem projective_of_isSemisimpleRing : Module.Projective R M :=
  .of_lifting_property'' (IsSemisimpleModule.lifting_property · · _)

@[deprecated (since := "2025-09-12")]
alias injective_of_semisimple_ring := injective_of_isSemisimpleRing

@[deprecated (since := "2025-09-12")]
alias projective_of_semisimple_ring := projective_of_isSemisimpleRing

end Module
