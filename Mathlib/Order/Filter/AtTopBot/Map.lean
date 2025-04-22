/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad, Yury Kudryashov, Patrick Massot
-/
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Order.Filter.Map
import Mathlib.Order.Filter.Tendsto
import Mathlib.Order.Interval.Set.OrderIso

/-!
# Map and comap of `Filter.atTop` and `Filter.atBot`
-/

assert_not_exists Finset

variable {ι ι' α β γ : Type*}

open Set

namespace OrderIso

open Filter

variable [Preorder α] [Preorder β]

@[simp]
theorem comap_atTop (e : α ≃o β) : comap e atTop = atTop := by
  simp [atTop, ← e.surjective.iInf_comp]

@[simp]
theorem comap_atBot (e : α ≃o β) : comap e atBot = atBot :=
  e.dual.comap_atTop

@[simp]
theorem map_atTop (e : α ≃o β) : map (e : α → β) atTop = atTop := by
  rw [← e.comap_atTop, map_comap_of_surjective e.surjective]

@[simp]
theorem map_atBot (e : α ≃o β) : map (e : α → β) atBot = atBot :=
  e.dual.map_atTop

theorem tendsto_atTop (e : α ≃o β) : Tendsto e atTop atTop :=
  e.map_atTop.le

theorem tendsto_atBot (e : α ≃o β) : Tendsto e atBot atBot :=
  e.map_atBot.le

@[simp]
theorem tendsto_atTop_iff {l : Filter γ} {f : γ → α} (e : α ≃o β) :
    Tendsto (fun x => e (f x)) l atTop ↔ Tendsto f l atTop := by
  rw [← e.comap_atTop, tendsto_comap_iff, Function.comp_def]

@[simp]
theorem tendsto_atBot_iff {l : Filter γ} {f : γ → α} (e : α ≃o β) :
    Tendsto (fun x => e (f x)) l atBot ↔ Tendsto f l atBot :=
  e.dual.tendsto_atTop_iff

end OrderIso
