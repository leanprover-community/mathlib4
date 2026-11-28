/-
Copyright (c) 2026 Matthew W. Horn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew W. Horn
-/
module

public import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Knaster-Tarski fixed points on an interval

If `f : α → α` is monotone on `Icc a b` in a conditionally complete lattice and maps `Icc a b`
into itself, then `f` has a least and a greatest fixed point in `Icc a b`.

## Main definitions

* `lfpIcc f a b`, `gfpIcc f a b`: the least and greatest fixed points of `f` in `Icc a b`,
  defined as the infimum of the prefixed points and the supremum of the postfixed points.

## Main results

* `isLeast_lfpIcc`, `isGreatest_gfpIcc`: the Knaster-Tarski theorem on `Icc a b`.
* `iterate_le_lfpIcc`, `gfpIcc_le_iterate`: the orbits of the endpoints bracket the extreme
  fixed points.
* `lfpIcc_le_lfpIcc`, `gfpIcc_le_gfpIcc`: `lfpIcc` and `gfpIcc` are monotone in `f`.

## Implementation notes

`OrderHom.lfp` and `OrderHom.gfp` give these fixed points through `Set.Icc.completeLattice`, but
need a `Fact (a ≤ b)` instance and return elements of the subtype `↥(Icc a b)`. The definitions
here take `MonotoneOn` and `MapsTo` hypotheses and return elements of `α`, which is the convenient
form on intervals of `ℝ`. Without the hypotheses they are junk values.

## Tags

fixed point, Knaster-Tarski, conditionally complete lattice, interval
-/

public section

open Function (IsFixedPt)
open Set

variable {α : Type*} [ConditionallyCompleteLattice α] {f g : α → α} {a b c x : α}

/-- The least fixed point of `f` in `Icc a b`: the infimum of the prefixed points of `f` in
`Icc a b`. This is the least fixed point when `f` is monotone on `Icc a b` and maps `Icc a b` into
itself (`isLeast_lfpIcc`). -/
@[expose] def lfpIcc (f : α → α) (a b : α) : α :=
  sInf {x ∈ Icc a b | f x ≤ x}

/-- The greatest fixed point of `f` in `Icc a b`: the supremum of the postfixed points of `f` in
`Icc a b`. This is the greatest fixed point when `f` is monotone on `Icc a b` and maps `Icc a b`
into itself (`isGreatest_gfpIcc`). -/
@[expose, to_dual existing (reorder := a b)] def gfpIcc (f : α → α) (a b : α) : α :=
  sSup {x ∈ Icc a b | x ≤ f x}

@[to_dual (reorder := a b) (rename := a ↔ b) le_gfpIcc]
theorem lfpIcc_le (hx : x ∈ Icc a b) (hfx : f x ≤ x) : lfpIcc f a b ≤ x :=
  csInf_le ⟨a, fun _ hy ↦ hy.1.1⟩ ⟨hx, hfx⟩

@[to_dual (reorder := a b) (rename := a ↔ b) gfpIcc_le]
theorem le_lfpIcc (hab : a ≤ b) (hf : MapsTo f (Icc a b) (Icc a b))
    (h : ∀ x ∈ Icc a b, f x ≤ x → c ≤ x) : c ≤ lfpIcc f a b :=
  le_csInf ⟨b, right_mem_Icc.mpr hab, (hf (right_mem_Icc.mpr hab)).2⟩ fun _ hx ↦ h _ hx.1 hx.2

/-- `lfpIcc f a b` lies in `Icc a b`. -/
@[to_dual (reorder := a b) (rename := a ↔ b) /-- `gfpIcc f a b` lies in `Icc a b`. -/]
theorem lfpIcc_mem_Icc (hab : a ≤ b) (hf : MapsTo f (Icc a b) (Icc a b)) :
    lfpIcc f a b ∈ Icc a b :=
  ⟨le_lfpIcc hab hf fun _ hx _ ↦ hx.1,
    lfpIcc_le (right_mem_Icc.mpr hab) (hf (right_mem_Icc.mpr hab)).2⟩

/-- `lfpIcc f a b` is a fixed point of `f` when `f` is monotone on `Icc a b` and maps `Icc a b`
into itself. -/
@[to_dual (reorder := a b) (rename := a ↔ b)
  /-- `gfpIcc f a b` is a fixed point of `f` when `f` is monotone on `Icc a b` and maps `Icc a b`
  into itself. -/]
theorem isFixedPt_lfpIcc (hab : a ≤ b) (hm : MonotoneOn f (Icc a b))
    (hf : MapsTo f (Icc a b) (Icc a b)) : IsFixedPt f (lfpIcc f a b) := by
  have hmem : lfpIcc f a b ∈ Icc a b := lfpIcc_mem_Icc hab hf
  have h₁ : f (lfpIcc f a b) ≤ lfpIcc f a b :=
    le_lfpIcc hab hf fun x hx hfx ↦ (hm hmem hx (lfpIcc_le hx hfx)).trans hfx
  exact h₁.antisymm (lfpIcc_le (hf hmem) (hm (hf hmem) hmem h₁))

/-- **Knaster-Tarski on an interval**: `lfpIcc f a b` is the least fixed point of `f` in
`Icc a b`. -/
@[to_dual (reorder := a b) (rename := a ↔ b)
  /-- **Knaster-Tarski on an interval**: `gfpIcc f a b` is the greatest fixed point of `f` in
  `Icc a b`. -/]
theorem isLeast_lfpIcc (hab : a ≤ b) (hm : MonotoneOn f (Icc a b))
    (hf : MapsTo f (Icc a b) (Icc a b)) :
    IsLeast {x ∈ Icc a b | IsFixedPt f x} (lfpIcc f a b) :=
  ⟨⟨lfpIcc_mem_Icc hab hf, isFixedPt_lfpIcc hab hm hf⟩, fun _ hx ↦ lfpIcc_le hx.1 hx.2.eq.le⟩

/-- The least fixed point in `Icc a b` is at most the greatest one. -/
@[to_dual self]
theorem lfpIcc_le_gfpIcc (hab : a ≤ b) (hm : MonotoneOn f (Icc a b))
    (hf : MapsTo f (Icc a b) (Icc a b)) : lfpIcc f a b ≤ gfpIcc f a b :=
  lfpIcc_le (gfpIcc_mem_Icc hab hf) (isFixedPt_gfpIcc hab hm hf).eq.le

/-- The orbit of the left endpoint stays below the least fixed point. -/
@[to_dual (reorder := a b) (rename := a ↔ b) gfpIcc_le_iterate
  /-- The orbit of the right endpoint stays above the greatest fixed point. -/]
theorem iterate_le_lfpIcc (hab : a ≤ b) (hm : MonotoneOn f (Icc a b))
    (hf : MapsTo f (Icc a b) (Icc a b)) (n : ℕ) : f^[n] a ≤ lfpIcc f a b := by
  induction n with
  | zero => exact (lfpIcc_mem_Icc hab hf).1
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (hm (hf.iterate n (left_mem_Icc.mpr hab)) (lfpIcc_mem_Icc hab hf) ih).trans_eq
      (isFixedPt_lfpIcc hab hm hf).eq

/-- `lfpIcc` is monotone in the function: if `f ≤ g` pointwise on `Icc a b`, then
`lfpIcc f a b ≤ lfpIcc g a b`. This compares the defining infima, so it needs no monotonicity. -/
@[to_dual (reorder := a b, f g) (rename := a ↔ b, f ↔ g, hg → hf)
  /-- `gfpIcc` is monotone in the function: if `f ≤ g` pointwise on `Icc a b`, then
  `gfpIcc f a b ≤ gfpIcc g a b`. This compares the defining suprema, so it needs no
  monotonicity. -/]
theorem lfpIcc_le_lfpIcc (hab : a ≤ b) (hg : MapsTo g (Icc a b) (Icc a b))
    (h : ∀ x ∈ Icc a b, f x ≤ g x) : lfpIcc f a b ≤ lfpIcc g a b :=
  csInf_le_csInf ⟨a, fun _ hy ↦ hy.1.1⟩
    ⟨b, right_mem_Icc.mpr hab, (hg (right_mem_Icc.mpr hab)).2⟩
    fun x hx ↦ ⟨hx.1, (h x hx.1).trans hx.2⟩
