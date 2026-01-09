/-
Copyright (c) 2025 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Module.Field
public import Mathlib.Data.NNReal.Defs

/-!
# Specific lemmas about convexity over `ℝ≥0`

This file collects some specific results about convexity over the ring `ℝ≥0`.
Expand as needed.
-/

public section

open Set
open scoped NNReal

namespace NNReal

protected lemma Icc_subset_segment {x y : ℝ≥0} :
    Icc x y ⊆ segment ℝ≥0 x y :=
  Nonneg.Icc_subset_segment

protected lemma segment_eq_Icc {x y : ℝ≥0} (hxy : x ≤ y) :
    segment ℝ≥0 x y = Icc x y :=
  Nonneg.segment_eq_Icc hxy

protected lemma segment_eq_uIcc {x y : ℝ≥0} :
    segment ℝ≥0 x y = uIcc x y :=
  Nonneg.segment_eq_uIcc

protected lemma convex_iff {M : Type*} [AddCommMonoid M] [Module ℝ M] {s : Set M} :
    Convex ℝ≥0 s ↔ Convex ℝ s := by
  refine ⟨fun H ↦ ?_, Convex.lift ℝ≥0⟩
  intro _ hx _ hy a b ha hb hab
  exact H hx hy (a := ⟨a, ha⟩) (b := ⟨b, hb⟩) (zero_le _) (zero_le _) (by ext; simpa)

end NNReal
