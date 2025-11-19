/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Sigma

/-!
# Finiteness of sigma types
-/

@[expose] public section

variable {α : Type*}

namespace Finite

instance {β : α → Type*} [Finite α] [∀ a, Finite (β a)] : Finite (Σ a, β a) := by
  letI := Fintype.ofFinite α
  letI := fun a => Fintype.ofFinite (β a)
  infer_instance

instance {ι : Sort*} {π : ι → Sort*} [Finite ι] [∀ i, Finite (π i)] : Finite (Σ' i, π i) :=
  of_equiv _ (Equiv.psigmaEquivSigmaPLift π).symm

end Finite
