/-
Copyright (c) 2022 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best
-/
import Mathlib.Data.Finsupp.Single
import Mathlib.Data.Fintype.BigOperators

/-!

# Finiteness and infiniteness of `Finsupp`

Some lemmas on the combination of `Finsupp`, `Fintype` and `Infinite`.

-/

variable {ι α : Type*} [DecidableEq ι] [Fintype ι] [Zero α] [Fintype α]

noncomputable instance Finsupp.fintype : Fintype (ι →₀ α) :=
  Fintype.ofEquiv _ Finsupp.equivFunOnFinite.symm

instance Finsupp.infinite_of_left [Nontrivial α] [Infinite ι] : Infinite (ι →₀ α) :=
  let ⟨_, hm⟩ := exists_ne (0 : α)
  Infinite.of_injective _ <| Finsupp.single_left_injective hm

instance Finsupp.infinite_of_right [Infinite α] [Nonempty ι] : Infinite (ι →₀ α) :=
  Infinite.of_injective (fun i => Finsupp.single (Classical.arbitrary ι) i)
    (Finsupp.single_injective (Classical.arbitrary ι))

variable (ι α) in
@[simp] lemma Fintype.card_finsupp : card (ι →₀ α) = card α ^ card ι := by
  simp [card_congr Finsupp.equivFunOnFinite]
