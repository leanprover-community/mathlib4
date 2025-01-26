/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Data.Finite.Defs

/-!
# `Finite` and `Infinite` are preserved by `Additive` and `Multiplicative`.
-/

assert_not_exists MonoidWithZero DenselyOrdered

universe u v

variable {α : Type u}

instance [Finite α] : Finite (Additive α) :=
  Finite.of_equiv α (by rfl)

instance [Finite α] : Finite (Multiplicative α) :=
  Finite.of_equiv α (by rfl)

instance [h : Infinite α] : Infinite (Additive α) := h

instance [h : Infinite α] : Infinite (Multiplicative α) := h
