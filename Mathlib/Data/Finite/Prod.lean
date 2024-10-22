/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Vector

/-!
# Finiteness of products
-/

open scoped Classical

variable {α β : Type*}

namespace Finite

instance [Finite α] [Finite β] : Finite (α × β) := by
  haveI := Fintype.ofFinite α
  haveI := Fintype.ofFinite β
  infer_instance

instance {α β : Sort*} [Finite α] [Finite β] : Finite (PProd α β) :=
  of_equiv _ Equiv.pprodEquivProdPLift.symm

theorem prod_left (β) [Finite (α × β)] [Nonempty β] : Finite α :=
  of_surjective (Prod.fst : α × β → α) Prod.fst_surjective

theorem prod_right (α) [Finite (α × β)] [Nonempty α] : Finite β :=
  of_surjective (Prod.snd : α × β → β) Prod.snd_surjective

end Finite

instance Pi.finite {α : Sort*} {β : α → Sort*} [Finite α] [∀ a, Finite (β a)] :
    Finite (∀ a, β a) := by
  haveI := Fintype.ofFinite (PLift α)
  haveI := fun a => Fintype.ofFinite (PLift (β a))
  exact
    Finite.of_equiv (∀ a : PLift α, PLift (β (Equiv.plift a)))
      (Equiv.piCongr Equiv.plift fun _ => Equiv.plift)

instance [Finite α] {n : ℕ} : Finite (Sym α n) := by
  haveI := Fintype.ofFinite α
  infer_instance
