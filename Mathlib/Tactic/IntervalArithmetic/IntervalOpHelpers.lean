/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.Tactic.IntervalArithmetic.Core
public import Mathlib.Tactic.IntervalArithmetic.Interval
public import Mathlib.Topology.Order.Basic
public import Mathlib.Algebra.Order.Group.Defs

/-!
##  Interval Operation Helpers

This file defiens several helpers for proving the inclusion theorems for interval operations.

-/

namespace IntervalArithmetic

open Interval

variable {α β : Type*} {φ : α → β}

section Mono

def strictMonoOp (fLb fUb : α → α) (x : Interval α) :
    Interval α where
  lb := match x.lb with
    | ⊥ => ⊥
    | some ⟨c, a⟩ => some ⟨c, fLb a⟩
  ub := match x.ub with
    | ⊤ => ⊤
    | some ⟨c, a⟩ => some ⟨c, fUb a⟩

theorem mem_strictMonoOp_toSet [PartialOrder β]
    {f : β → β} (hf_mono : StrictMono f) {fLb fUb : α → α}
    (h_lb : ∀ a, φ (fLb a) ≤ f (φ a)) (h_ub : ∀ a, f (φ a) ≤ φ (fUb a))
    {b : β} {x : Interval α} (hbx : b ∈ x.toSet φ) :
    f b ∈ (strictMonoOp fLb fUb x).toSet φ := by
  simp only [strictMonoOp]
  constructor
  · match h : x.lb with
    | ⊥ => simp
    | some ⟨c, a⟩ =>
        simp only [mem_toSet, LowerBound.Bounds, h] at hbx ⊢
        cases c
        · exact lt_of_le_of_lt (h_lb _) (hf_mono hbx.1)
        · exact le_trans (h_lb _) (hf_mono.monotone hbx.1)
  · match h : x.ub with
    | ⊤ => simp
    | some ⟨c, a⟩ =>
        simp only [mem_toSet, UpperBound.Bounds, h] at hbx ⊢
        cases c
        · exact lt_of_lt_of_le (hf_mono hbx.2) (h_ub _)
        · exact le_trans (hf_mono.monotone hbx.2) (h_ub _)

end Mono

end IntervalArithmetic
