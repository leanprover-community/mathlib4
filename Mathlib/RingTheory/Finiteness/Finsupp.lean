/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Algebra.FreeAbelianGroup.Finsupp
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Finiteness of finitely supported functions

-/

open Finsupp

variable {R V} [Semiring R] [AddCommMonoid V] [Module R V] {ι : Type*} [_root_.Finite ι]

instance Module.Finite.finsupp [Module.Finite R V] :
    Module.Finite R (ι →₀ V) :=
  Module.Finite.equiv (Finsupp.linearEquivFunOnFinite R V ι).symm

end

namespace AddMonoidAlgebra
variable {ι R S : Type*} [Finite ι] [Semiring R] [Semiring S] [Module R S] [Module.Finite R S]

instance moduleFinite : Module.Finite R S[ι] := .finsupp

end AddMonoidAlgebra

namespace MonoidAlgebra
variable {ι R S : Type*} [Finite ι] [Semiring R] [Semiring S] [Module R S] [Module.Finite R S]

instance moduleFinite : Module.Finite R (MonoidAlgebra S ι) := .finsupp

end MonoidAlgebra

namespace FreeAbelianGroup
variable {σ : Type*} [Finite σ]

instance : Module.Finite ℤ (FreeAbelianGroup σ) :=
  .of_surjective _ (FreeAbelianGroup.equivFinsupp σ).toIntLinearEquiv.symm.surjective

instance : AddMonoid.FG (FreeAbelianGroup σ) := by
  rw [← AddGroup.fg_iff_addMonoid_fg, ← Module.Finite.iff_addGroup_fg]; infer_instance

end FreeAbelianGroup
