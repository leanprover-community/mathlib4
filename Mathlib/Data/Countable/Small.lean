/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Logic.Small.Basic
import Mathlib.Data.Countable.Defs

#align_import data.countable.small from "leanprover-community/mathlib"@"bbeb185db4ccee8ed07dc48449414ebfa39cb821"

/-!
# All countable types are small.

That is, any countable type is equivalent to a type in any universe.
-/


universe w v

instance (priority := 100) small_of_countable (α : Type v) [Countable α] : Small.{w} α :=
  let ⟨_, hf⟩ := exists_injective_nat α
  small_of_injective hf
#align small_of_countable small_of_countable
