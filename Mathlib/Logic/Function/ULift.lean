/-
Copyright (c) 2016 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Logic.Function.Defs

/-!
# `ULift` and `PLift`
-/

theorem ULift.down_injective {α : Sort _} : Function.Injective (@ULift.down α)
  | ⟨a⟩, ⟨b⟩, _ => by congr

@[simp] theorem ULift.down_inj {α : Sort _} {a b : ULift α} : a.down = b.down ↔ a = b :=
  ⟨fun h ↦ ULift.down_injective h, fun h ↦ by rw [h]⟩

variable {α : Sort*}

theorem PLift.down_injective : Function.Injective (@PLift.down α)
  | ⟨a⟩, ⟨b⟩, _ => by congr

@[simp] theorem PLift.down_inj {a b : PLift α} : a.down = b.down ↔ a = b :=
  ⟨fun h ↦ PLift.down_injective h, fun h ↦ by rw [h]⟩
