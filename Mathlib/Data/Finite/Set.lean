/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

public import Mathlib.Data.Finite.Defs
public import Mathlib.Data.Set.Operations
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

/-!
# Lemmas about `Finite` and `Set`s

In this file we prove two lemmas about `Finite` and `Set`s.

## Tags

finiteness, finite sets
-/

public section


open Set

universe u v w

variable {α : Type u} {β : Type v} {ι : Sort w}

theorem Finite.Set.finite_of_finite_image (s : Set α) {f : α → β} (h : s.InjOn f)
    [Finite (f '' s)] : Finite s :=
  Finite.of_equiv _ (Equiv.ofBijective _ h.bijOn_image.bijective).symm

theorem Finite.of_injective_finite_range {f : ι → α} (hf : Function.Injective f)
    [Finite (range f)] : Finite ι :=
  Finite.of_injective (Set.rangeFactorization f) (hf.codRestrict _)
