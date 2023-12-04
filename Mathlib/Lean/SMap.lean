/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Lean.Data.SMap

/-!
# Extra functions on Lean.SMap
-/

set_option autoImplicit true

/-- Monadic fold over a staged map. -/
def Lean.SMap.foldM {m : Type w → Type w} [Monad m] [BEq α] [Hashable α]
    (f : σ → α → β → m σ) (init : σ) (map : SMap α β) : m σ := do
  map.map₂.foldlM f (← map.map₁.foldM f init)
