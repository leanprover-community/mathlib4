/-
Copyright (c) 2026 Matt Hunzinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matt Hunzinger
-/
module

public import Mathlib.Order.Causal.Defs

/-!
# Causal stream functions
-/

@[expose] public section

universe u v

variable {α : Type u} {β : Type v}

namespace Stream'

theorem map_causal {f : α → β} : Causal (map f) := by
  intro x y t h
  simpa [map] using congrArg f (h t (Nat.le_refl t))

theorem enum_causal : Causal (enum (α := α)) := by
  intro x y t h
  simpa [enum] using congrArg (fun a => (t, a)) (h t (Nat.le_refl t))

end Stream'
