/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.Data.Finite.Defs
import Mathlib.Logic.Small.Defs

/-!
# Finite types are small.
-/

universe u v

section

instance (priority := 100) Finite.small {α : Type v} [Finite α] : Small.{u} α := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin α
  exact small_map e

end
