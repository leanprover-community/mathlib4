/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Instances.Sign

/-!
# Signs of continuous functions on connected sets

This file proves that a continuous nonvanishing function has constant sign on a preconnected set.
-/

public section

variable {α β : Type*} [Zero α] [TopologicalSpace α] [LinearOrder α] [OrderTopology α]
  [TopologicalSpace β]

/-- A continuous nonvanishing function has constant sign on a preconnected set. -/
theorem IsPreconnected.sign_eq_of_continuousOn {f : β → α} {s : Set β}
    (hs : IsPreconnected s) (hf : ContinuousOn f s) (h0 : ∀ x ∈ s, f x ≠ 0)
    {x y : β} (hx : x ∈ s) (hy : y ∈ s) : SignType.sign (f x) = SignType.sign (f y) :=
  hs.constant (hf.sign h0) hx hy
