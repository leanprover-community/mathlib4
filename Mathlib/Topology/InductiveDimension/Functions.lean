/-
Copyright (c) 2026 Fernando Chu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Chu, Andrew Yang, Felix Pernegger
-/
module

public import Mathlib.Data.ENat.Lattice
public import Mathlib.Topology.InductiveDimension.Classes

import Mathlib.Data.Nat.Cast.Order.Basic

/-!
# Small inductive dimension

This file defines a `WithBot ℕ∞`-valued function which measures the small inductive dimension of a
topological space, and connects it to the `HasSmallInductiveDimensionLT` and
`HasSmallInductiveDimensionLE` typeclasses defined in `Topology.InductiveDimension.Classes`.
-/

public section

open Set Topology TopologicalSpace

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

variable (X) in
/-- The small inductive dimension of a topological space. -/
noncomputable def smallInductiveDimension : WithBot ℕ∞ :=
  sInf {n | ∀ i : ℕ, n < i → HasSmallInductiveDimensionLT X i}

private theorem hasSmallInductiveDimensionLT_of_smallInductiveDimension_lt {n : ℕ}
    (h : smallInductiveDimension X < n) : HasSmallInductiveDimensionLT X n := by
  contrapose! h
  simp only [smallInductiveDimension, le_sInf_iff, mem_ofPred]
  intro a ha
  contrapose! ha
  exact ⟨n, ha, h⟩

private theorem hasSmallInductiveDimensionLE_of_smallInductiveDimension_le {n : ℕ}
    (h : smallInductiveDimension X ≤ n) : HasSmallInductiveDimensionLE X n := by
  apply hasSmallInductiveDimensionLT_of_smallInductiveDimension_lt (h.trans_lt _)
  exact_mod_cast n.lt_add_one

theorem smallInductiveDimension_le_iff {n : ℕ} :
    smallInductiveDimension X ≤ n ↔ HasSmallInductiveDimensionLE X n where
  mp := hasSmallInductiveDimensionLE_of_smallInductiveDimension_le
  mpr h := sInf_le fun m hm ↦ .mono (by simpa [Nat.add_one_le_iff] using hm) h

theorem smallInductiveDimension_lt_iff {n : ℕ} :
    smallInductiveDimension X < n ↔ HasSmallInductiveDimensionLT X n where
  mp := hasSmallInductiveDimensionLT_of_smallInductiveDimension_lt
  mpr h := by
    cases n with
    | zero =>
      rw [smallInductiveDimension, csInf_eq_bot_of_bot_mem]
      · simp
      · exact fun _ _ ↦ h.mono zero_le
    | succ n =>
      apply (smallInductiveDimension_le_iff.2 h).trans_lt
      exact_mod_cast n.lt_add_one

variable (X) in
theorem smallInductiveDimension_le (n : ℕ) [H : HasSmallInductiveDimensionLE X n] :
    smallInductiveDimension X ≤ n :=
  smallInductiveDimension_le_iff.2 H

variable (X) in
theorem smallInductiveDimension_lt (n : ℕ) [H : HasSmallInductiveDimensionLT X n] :
    smallInductiveDimension X < n :=
  smallInductiveDimension_lt_iff.2 H

theorem smallInductiveDimension_eq (n : ℕ)
    (hle : HasSmallInductiveDimensionLE X n) (hlt : ¬ HasSmallInductiveDimensionLT X n) :
    smallInductiveDimension X = n := by
  apply (smallInductiveDimension_le_iff.2 hle).antisymm
  rwa [← not_lt, smallInductiveDimension_lt_iff]

@[simp]
theorem smallInductiveDimension_eq_bot : smallInductiveDimension X = ⊥ ↔ IsEmpty X := by
  simp_rw [← hasSmallInductiveDimensionLT_zero_iff, ← smallInductiveDimension_lt_iff,
    WithBot.lt_coe_bot.symm, bot_eq_zero', Nat.cast_zero, WithBot.coe_zero]

variable (X) in
@[simp]
theorem smallInductiveDimension_of_isEmpty [IsEmpty X] : smallInductiveDimension X = ⊥ :=
  smallInductiveDimension_eq_bot.2 ‹_›

theorem Topology.IsInducing.hasSmallInductiveDimensionLT {f : X → Y} (hf : IsInducing f)
    {n : ℕ} (h : HasSmallInductiveDimensionLT Y n) : HasSmallInductiveDimensionLT X n := by
  induction h generalizing X with
  | zero => exact hasSmallInductiveDimensionLT_zero_iff.2 (Function.isEmpty f)
  | succ n s hs h ih =>
    refine .succ n _ (hf.isTopologicalBasis hs) (forall_mem_image.mpr fun U hU ↦ ?_)
    have : MapsTo f (frontier (f ⁻¹' U)) (frontier U) := hf.continuous.frontier_preimage_subset U
    exact ih U hU (hf.restrict this)

theorem Topology.IsInducing.hasSmallInductiveDimensionLE {f : X → Y} (hf : IsInducing f)
    {n : ℕ} (h : HasSmallInductiveDimensionLE Y n) : HasSmallInductiveDimensionLE X n :=
  hf.hasSmallInductiveDimensionLT h

/-- The small inductive dimension does not increase under inducing maps. -/
theorem Topology.IsInducing.smallInductiveDimension_le {f : X → Y} (hf : IsInducing f) :
    smallInductiveDimension X ≤ smallInductiveDimension Y :=
  sInf_le_sInf fun _ hm i hi ↦ hf.hasSmallInductiveDimensionLT (hm i hi)

/-- The small inductive dimension of a subspace is at most that of the ambient space. -/
theorem smallInductiveDimension_subtype_le {p : X → Prop} :
    smallInductiveDimension {x // p x} ≤ smallInductiveDimension X :=
  Topology.IsInducing.subtypeVal.smallInductiveDimension_le

protected theorem Homeomorph.hasSmallInductiveDimensionLT (f : X ≃ₜ Y) (n : ℕ) :
    HasSmallInductiveDimensionLT X n ↔ HasSmallInductiveDimensionLT Y n :=
  ⟨f.symm.isInducing.hasSmallInductiveDimensionLT, f.isInducing.hasSmallInductiveDimensionLT⟩

protected theorem Homeomorph.hasSmallInductiveDimensionLE (f : X ≃ₜ Y) (n : ℕ) :
    HasSmallInductiveDimensionLE X n ↔ HasSmallInductiveDimensionLE Y n :=
  f.hasSmallInductiveDimensionLT (n + 1)

instance {p : X → Prop} (n : ℕ) [h : HasSmallInductiveDimensionLT X n] :
    HasSmallInductiveDimensionLT (Subtype p) n :=
  Topology.IsInducing.subtypeVal.hasSmallInductiveDimensionLT h

/-- The small inductive dimension is preserved by homeomorphisms. -/
protected theorem Homeomorph.smallInductiveDimension_congr (f : X ≃ₜ Y) :
    smallInductiveDimension X = smallInductiveDimension Y :=
  le_antisymm f.isInducing.smallInductiveDimension_le f.symm.isInducing.smallInductiveDimension_le
