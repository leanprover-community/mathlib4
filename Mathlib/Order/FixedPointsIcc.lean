/-
Copyright (c) 2026 Matthew W. Horn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew W. Horn
-/
module

public import Mathlib.Logic.Function.Iterate
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.Interval.Set.Basic

/-!
# Knaster–Tarski fixed points on an interval

The Knaster–Tarski theorem for a plain function `f : α → α` on an interval `Set.Icc a b` of a
conditionally complete lattice: if `f` is monotone on `[a, b]` and maps `[a, b]` into itself, then
`f` has a least and a greatest fixed point in `[a, b]`.

## Main definitions

* `lfpIcc f a b`: the infimum of the prefixed points of `f` in `[a, b]`, i.e. of
  `{x ∈ Set.Icc a b | f x ≤ x}`. Under the hypotheses above this is the least fixed point of `f`
  in `[a, b]`.
* `gfpIcc f a b`: the supremum of the postfixed points of `f` in `[a, b]`. Under the hypotheses
  above this is the greatest fixed point of `f` in `[a, b]`.

## Main results

* `isLeast_lfpIcc` / `isGreatest_gfpIcc`: the Knaster–Tarski theorem on `[a, b]`.
* `iterate_le_lfpIcc` / `gfpIcc_le_iterate`: the orbits of the endpoints bracket the extreme
  fixed points.
* `lfpIcc_le_lfpIcc` / `gfpIcc_le_gfpIcc`: `lfpIcc` and `gfpIcc` are monotone in `f`.

## Implementation notes

Mathlib already has `OrderHom.lfp` and `OrderHom.gfp` on a complete lattice, and `Set.Icc a b` in
a conditionally complete lattice is a complete lattice (`Mathlib.Order.CompleteLatticeIntervals`),
so these results are in principle available by bundling the restriction of `f` as an order hom on
the subtype `↥(Set.Icc a b)`. The definitions here are the unbundled ambient-valued versions: they
take `MonotoneOn` and `Set.MapsTo` hypotheses directly, need no `Fact (a ≤ b)` instance, and
produce elements of `α` rather than of a subtype. This is the form in which the theorem is used on
concrete intervals of `ℝ`.

`lfpIcc` and `gfpIcc` are total. Without the hypotheses, they are the infimum and supremum of
possibly empty sets, hence junk values; every theorem states the hypotheses it needs.

## Tags

fixed point, Knaster-Tarski, conditionally complete lattice, interval
-/

@[expose] public section

open Function (IsFixedPt)
open Set

variable {α : Type*} [ConditionallyCompleteLattice α] {f g : α → α} {a b c x : α}

/-- The least fixed point of `f` on `Set.Icc a b`, realized as the infimum of the prefixed points
of `f` in `[a, b]`. This is a genuine least fixed point when `f` is monotone on `[a, b]` and maps
`[a, b]` into itself (`isLeast_lfpIcc`); otherwise it is a junk value. -/
def lfpIcc (f : α → α) (a b : α) : α :=
  sInf {x ∈ Icc a b | f x ≤ x}

/-- The greatest fixed point of `f` on `Set.Icc a b`, realized as the supremum of the postfixed
points of `f` in `[a, b]`. This is a genuine greatest fixed point when `f` is monotone on `[a, b]`
and maps `[a, b]` into itself (`isGreatest_gfpIcc`); otherwise it is a junk value. -/
def gfpIcc (f : α → α) (a b : α) : α :=
  sSup {x ∈ Icc a b | x ≤ f x}

theorem lfpIcc_le (hx : x ∈ Icc a b) (hfx : f x ≤ x) : lfpIcc f a b ≤ x :=
  csInf_le ⟨a, fun _ hy => hy.1.1⟩ ⟨hx, hfx⟩

theorem le_gfpIcc (hx : x ∈ Icc a b) (hfx : x ≤ f x) : x ≤ gfpIcc f a b :=
  le_csSup ⟨b, fun _ hy => hy.1.2⟩ ⟨hx, hfx⟩

theorem le_lfpIcc (hab : a ≤ b) (hf : MapsTo f (Icc a b) (Icc a b))
    (h : ∀ x ∈ Icc a b, f x ≤ x → c ≤ x) : c ≤ lfpIcc f a b :=
  le_csInf ⟨b, right_mem_Icc.mpr hab, (hf (right_mem_Icc.mpr hab)).2⟩ fun _ hx => h _ hx.1 hx.2

theorem gfpIcc_le (hab : a ≤ b) (hf : MapsTo f (Icc a b) (Icc a b))
    (h : ∀ x ∈ Icc a b, x ≤ f x → x ≤ c) : gfpIcc f a b ≤ c :=
  csSup_le ⟨a, left_mem_Icc.mpr hab, (hf (left_mem_Icc.mpr hab)).1⟩ fun _ hx => h _ hx.1 hx.2

theorem lfpIcc_mem_Icc (hab : a ≤ b) (hf : MapsTo f (Icc a b) (Icc a b)) :
    lfpIcc f a b ∈ Icc a b :=
  ⟨le_lfpIcc hab hf fun _ hx _ => hx.1,
    lfpIcc_le (right_mem_Icc.mpr hab) (hf (right_mem_Icc.mpr hab)).2⟩

theorem gfpIcc_mem_Icc (hab : a ≤ b) (hf : MapsTo f (Icc a b) (Icc a b)) :
    gfpIcc f a b ∈ Icc a b :=
  ⟨le_gfpIcc (left_mem_Icc.mpr hab) (hf (left_mem_Icc.mpr hab)).1,
    gfpIcc_le hab hf fun _ hx _ => hx.2⟩

/-- A function that is monotone on `[a, b]` and maps `[a, b]` into itself fixes `lfpIcc f a b`:
the existence half of `isLeast_lfpIcc`. -/
theorem isFixedPt_lfpIcc (hab : a ≤ b) (hm : MonotoneOn f (Icc a b))
    (hf : MapsTo f (Icc a b) (Icc a b)) : IsFixedPt f (lfpIcc f a b) := by
  have hmem : lfpIcc f a b ∈ Icc a b := lfpIcc_mem_Icc hab hf
  have h₁ : f (lfpIcc f a b) ≤ lfpIcc f a b :=
    le_lfpIcc hab hf fun x hx hfx => (hm hmem hx (lfpIcc_le hx hfx)).trans hfx
  exact h₁.antisymm (lfpIcc_le (hf hmem) (hm (hf hmem) hmem h₁))

/-- A function that is monotone on `[a, b]` and maps `[a, b]` into itself fixes `gfpIcc f a b`:
the existence half of `isGreatest_gfpIcc`. -/
theorem isFixedPt_gfpIcc (hab : a ≤ b) (hm : MonotoneOn f (Icc a b))
    (hf : MapsTo f (Icc a b) (Icc a b)) : IsFixedPt f (gfpIcc f a b) := by
  have hmem : gfpIcc f a b ∈ Icc a b := gfpIcc_mem_Icc hab hf
  have h₁ : gfpIcc f a b ≤ f (gfpIcc f a b) :=
    gfpIcc_le hab hf fun x hx hfx => hfx.trans (hm hx hmem (le_gfpIcc hx hfx))
  exact (le_gfpIcc (hf hmem) (hm hmem (hf hmem) h₁)).antisymm h₁

/-- **Knaster–Tarski on an interval**: `lfpIcc f a b` is the least fixed point of `f` in
`[a, b]`. -/
theorem isLeast_lfpIcc (hab : a ≤ b) (hm : MonotoneOn f (Icc a b))
    (hf : MapsTo f (Icc a b) (Icc a b)) :
    IsLeast {x ∈ Icc a b | IsFixedPt f x} (lfpIcc f a b) :=
  ⟨⟨lfpIcc_mem_Icc hab hf, isFixedPt_lfpIcc hab hm hf⟩, fun _ hx => lfpIcc_le hx.1 hx.2.eq.le⟩

/-- **Knaster–Tarski on an interval**: `gfpIcc f a b` is the greatest fixed point of `f` in
`[a, b]`. -/
theorem isGreatest_gfpIcc (hab : a ≤ b) (hm : MonotoneOn f (Icc a b))
    (hf : MapsTo f (Icc a b) (Icc a b)) :
    IsGreatest {x ∈ Icc a b | IsFixedPt f x} (gfpIcc f a b) :=
  ⟨⟨gfpIcc_mem_Icc hab hf, isFixedPt_gfpIcc hab hm hf⟩, fun _ hx => le_gfpIcc hx.1 hx.2.eq.ge⟩

theorem lfpIcc_le_gfpIcc (hab : a ≤ b) (hm : MonotoneOn f (Icc a b))
    (hf : MapsTo f (Icc a b) (Icc a b)) : lfpIcc f a b ≤ gfpIcc f a b :=
  lfpIcc_le (gfpIcc_mem_Icc hab hf) (isFixedPt_gfpIcc hab hm hf).eq.le

/-- The orbit of the left endpoint stays below the least fixed point. -/
theorem iterate_le_lfpIcc (hab : a ≤ b) (hm : MonotoneOn f (Icc a b))
    (hf : MapsTo f (Icc a b) (Icc a b)) (n : ℕ) : f^[n] a ≤ lfpIcc f a b := by
  induction n with
  | zero => exact (lfpIcc_mem_Icc hab hf).1
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (hm (hf.iterate n (left_mem_Icc.mpr hab)) (lfpIcc_mem_Icc hab hf) ih).trans_eq
      (isFixedPt_lfpIcc hab hm hf).eq

/-- The orbit of the right endpoint stays above the greatest fixed point. -/
theorem gfpIcc_le_iterate (hab : a ≤ b) (hm : MonotoneOn f (Icc a b))
    (hf : MapsTo f (Icc a b) (Icc a b)) (n : ℕ) : gfpIcc f a b ≤ f^[n] b := by
  induction n with
  | zero => exact (gfpIcc_mem_Icc hab hf).2
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (isFixedPt_gfpIcc hab hm hf).eq.ge.trans
      (hm (gfpIcc_mem_Icc hab hf) (hf.iterate n (right_mem_Icc.mpr hab)) ih)

/-- `lfpIcc` is monotone in the function: if `f ≤ g` pointwise on `[a, b]`, then
`lfpIcc f a b ≤ lfpIcc g a b`. This compares the defining infima, so it needs no monotonicity of
`f` or `g`; under the hypotheses of `isLeast_lfpIcc` it compares the least fixed points. -/
theorem lfpIcc_le_lfpIcc (hab : a ≤ b) (hg : MapsTo g (Icc a b) (Icc a b))
    (h : ∀ x ∈ Icc a b, f x ≤ g x) : lfpIcc f a b ≤ lfpIcc g a b :=
  csInf_le_csInf ⟨a, fun _ hy => hy.1.1⟩
    ⟨b, right_mem_Icc.mpr hab, (hg (right_mem_Icc.mpr hab)).2⟩
    fun x hx => ⟨hx.1, (h x hx.1).trans hx.2⟩

/-- `gfpIcc` is monotone in the function: if `f ≤ g` pointwise on `[a, b]`, then
`gfpIcc f a b ≤ gfpIcc g a b`. This compares the defining suprema, so it needs no monotonicity of
`f` or `g`; under the hypotheses of `isGreatest_gfpIcc` it compares the greatest fixed points. -/
theorem gfpIcc_le_gfpIcc (hab : a ≤ b) (hf : MapsTo f (Icc a b) (Icc a b))
    (h : ∀ x ∈ Icc a b, f x ≤ g x) : gfpIcc f a b ≤ gfpIcc g a b :=
  csSup_le_csSup ⟨b, fun _ hy => hy.1.2⟩
    ⟨a, left_mem_Icc.mpr hab, (hf (left_mem_Icc.mpr hab)).1⟩
    fun x hx => ⟨hx.1, hx.2.trans (h x hx.1)⟩
