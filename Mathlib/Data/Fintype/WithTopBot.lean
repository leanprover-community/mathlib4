/-
Copyright (c) 2025 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Data.Fintype.Option
public import Mathlib.Order.TypeTags

@[expose] public section

/-!
# Fintype instances for `WithTop α` and `WithBot α`
-/

variable {α : Type*}

instance [Fintype α] : Fintype (WithTop α) :=
  instFintypeOption

instance [Finite α] : Finite (WithTop α) :=
  have := Fintype.ofFinite α
  Finite.of_fintype _

instance [Fintype α] : Fintype (WithBot α) :=
  instFintypeOption

instance [Finite α] : Finite (WithBot α) :=
  have := Fintype.ofFinite α
  Finite.of_fintype _
