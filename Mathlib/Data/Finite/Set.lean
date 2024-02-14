/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathlib.Data.Fintype.Card

#align_import data.finite.set from "leanprover-community/mathlib"@"509de852e1de55e1efa8eacfa11df0823f26f226"

/-!
# Lemmas about `Finite` and `Set`s

In this file we prove two lemmas about `Finite` and `Set`s.

## Tags

finiteness, finite sets
-/


open Set

universe u v w

variable {α : Type u} {β : Type v} {ι : Sort w}

theorem Finite.Set.finite_of_finite_image (s : Set α) {f : α → β} (h : s.InjOn f)
    [Finite (f '' s)] : Finite s :=
  Finite.of_equiv _ (Equiv.ofBijective _ h.bijOn_image.bijective).symm
#align finite.set.finite_of_finite_image Finite.Set.finite_of_finite_image

theorem Finite.of_injective_finite_range {f : ι → α} (hf : Function.Injective f)
    [Finite (range f)] : Finite ι :=
  Finite.of_injective (Set.rangeFactorization f) (hf.codRestrict _)
#align finite.of_injective_finite_range Finite.of_injective_finite_range
