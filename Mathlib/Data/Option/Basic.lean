/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Init.Function
import Mathlib.Data.Option.Defs
import Mathlib.Logic.Basic

namespace Option

theorem some_injective (α : Type _) : Function.Injective (@some α) :=
  fun _ _ => some_inj.mp

/-- `option.map f` is injective if `f` is injective. -/
theorem map_injective {f : α → β} (Hf : Function.Injective f) : Function.Injective (Option.map f)
| none, none, _ => rfl
| some a₁, some a₂, H => by rw [Hf (Option.some.inj H)]

-- theorem join_eq_none {o : Option (Option α)} : o.join = none ↔ o = none ∨ o = some none := by
--   rcases o with _|_|_; simp

#align option.lift_or_get_none_left Option.liftOrGet_none_left
#align option.lift_or_get_none_right Option.liftOrGet_none_right
#align option.lift_or_get_some_some Option.liftOrGet_some_some
