/-
Copyright (c) 2026 Matt Hunzinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matt Hunzinger
-/
module

public import Mathlib.Data.Stream.Defs
public import Mathlib.Order.Defs.PartialOrder

/-!
# Causal stream functions
-/

@[expose] public section

universe u v w

variable {α : Type u} {β : Type v} {δ : Type w}

/-- A stream function is causal if the output at time `t` depends only on inputs up to time `t`. -/
def Causal (f : Stream' α → Stream' β) : Prop :=
  ∀ (x y : Stream' α) (t : ℕ), (∀ s, s ≤ t → x s = y s) → f x t = f y t

instance
    {f : Stream' α → Stream' β}
    [i : Decidable
          (∀ (x y : Stream' α) (t : ℕ),
            (∀ s, s ≤ t → x s = y s) → f x t = f y t)] :
    Decidable (Causal f) := i

theorem causal_id : Causal (id (α:=Stream' α)) := by
  intro x y t h
  exact h t (Nat.le_refl t)

theorem causal_comp
    {f : Stream' α → Stream' β}
    {g : Stream' β → Stream' δ}
    (hf : Causal f)
    (hg : Causal g) :
    Causal (g ∘ f) := by
  intro x y t h
  apply hg
  intro s hs
  apply hf
  intro s' hs'
  exact h s' (Nat.le_trans hs' hs)
