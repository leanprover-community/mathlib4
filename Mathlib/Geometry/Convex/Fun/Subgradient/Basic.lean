/-
Copyright (c) 2026 Yiming Fu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yiming Fu
-/
module

public import Mathlib.Geometry.Convex.ConvexSpace.Module
public import Mathlib.Geometry.Convex.Fun.Proper
public import Mathlib.Order.Filter.Extr

import Mathlib.Analysis.Convex.Segment

/-!
# Subgradients along a bilinear pairing

Given a pairing `p : M →ₗ[R] N →ₗ[R] R`, a subgradient of `f : M → WithBot (WithTop R)`
at `x` within `s` is a point `y : N` such that `f x` is finite and
`f x + p (z - x) y ≤ f z` for every `z ∈ s`.

## Main results

* `Convexity.isConvexSet_subdifferentialWithin`: subdifferentials are convex.
* `Convexity.IsProper.zero_mem_subdifferential_iff`: Fermat's rule for global minimizers.

## Implementation notes

We allow both infinite values because operations such as infimal convolution may take the value
`⊥`, even when their inputs take values in `WithTop R`.
-/

@[expose] public section

assert_not_exists TopologicalSpace Real

open Set

namespace Convexity

variable {R M N : Type*}

local notation3 "R∞" => WithBot (WithTop R)

section CommRing

variable [CommRing R] [PartialOrder R]
  [AddCommGroup M] [Module R M] [AddCommMonoid N] [Module R N]

/-- The point `y` is a subgradient of `f` along `p` at `x` within `s` if `f x` is finite
and `f x + p (z - x) y ≤ f z` for every `z ∈ s`. This does not require `x ∈ s`. -/
@[mk_iff]
structure HasSubgradientWithinAt (p : M →ₗ[R] N →ₗ[R] R) (f : M → R∞) (y : N)
    (s : Set M) (x : M) : Prop where
  /-- The value at the base point is less than `⊤`. -/
  mem_effectiveDomain : x ∈ effectiveDomain f
  /-- The value at the base point is greater than `⊥`. -/
  bot_lt : ⊥ < f x
  /-- The affine function based at `x` with linear part `p · y` lies below `f` on `s`. -/
  le : ∀ ⦃z⦄, z ∈ s → f x + p (z - x) y ≤ f z

/-- The point `y` is a subgradient of `f` along `p` at `x`. -/
def HasSubgradientAt (p : M →ₗ[R] N →ₗ[R] R) (f : M → R∞) (y : N) (x : M) : Prop :=
  HasSubgradientWithinAt p f y univ x

/-- The set of subgradients of `f` along `p` at `x` within `s`. -/
def subdifferentialWithin (p : M →ₗ[R] N →ₗ[R] R) (f : M → R∞) (s : Set M) (x : M) : Set N :=
  {y | HasSubgradientWithinAt p f y s x}

/-- The set of subgradients of `f` along `p` at `x`. -/
def subdifferential (p : M →ₗ[R] N →ₗ[R] R) (f : M → R∞) (x : M) : Set N :=
  subdifferentialWithin p f univ x

variable {p : M →ₗ[R] N →ₗ[R] R} {f g : M → WithBot (WithTop R)}
  {y y' : N} {s t : Set M} {x : M}

section Subgradient

@[simp]
theorem mem_subdifferentialWithin :
    y ∈ subdifferentialWithin p f s x ↔ HasSubgradientWithinAt p f y s x := Iff.rfl

@[simp]
theorem mem_subdifferential : y ∈ subdifferential p f x ↔ HasSubgradientAt p f y x := Iff.rfl

@[simp]
theorem hasSubgradientWithinAt_univ :
    HasSubgradientWithinAt p f y univ x ↔ HasSubgradientAt p f y x := Iff.rfl

@[simp]
theorem subdifferentialWithin_univ : subdifferentialWithin p f univ x = subdifferential p f x := rfl

theorem HasSubgradientAt.le (hf : HasSubgradientAt p f y x) (z : M) :
    f x + p (z - x) y ≤ f z :=
  HasSubgradientWithinAt.le hf (mem_univ z)

theorem HasSubgradientWithinAt.exists_coe (hf : HasSubgradientWithinAt p f y s x) :
    ∃ r : R, (r : R∞) = f x := by
  lift f x to WithTop R using hf.bot_lt.ne' with a ha
  lift a to R using (WithBot.coe_lt_coe.1 (ha ▸ hf.mem_effectiveDomain)).ne with r
  exact ⟨r, rfl⟩

theorem HasSubgradientAt.isProper (hf : HasSubgradientAt p f y x) : IsProper f := by
  refine ⟨fun z ↦ ?_, x, hf.mem_effectiveDomain⟩
  exact (WithBot.bot_lt_add.2 ⟨hf.bot_lt, WithBot.bot_lt_coe _⟩).trans_le (hf.le z)

theorem IsProper.hasSubgradientWithinAt_iff (hf : IsProper f) (hx : x ∈ effectiveDomain f) :
    HasSubgradientWithinAt p f y s x ↔ ∀ ⦃z⦄, z ∈ s → f x + p (z - x) y ≤ f z :=
  ⟨(·.le), fun h ↦ ⟨hx, hf.bot_lt x, h⟩⟩

theorem IsProper.hasSubgradientAt_iff (hf : IsProper f) :
    HasSubgradientAt p f y x ↔ ∀ z, f x + p (z - x) y ≤ f z := by
  refine ⟨(·.le), fun h ↦ ⟨?_, hf.bot_lt x, fun z _ ↦ h z⟩⟩
  obtain ⟨z, hz⟩ := hf.nonempty_effectiveDomain
  change f x < ⊤
  refine lt_top_iff_ne_top.2 fun hx ↦ ?_
  have hlt := (h z).trans_lt hz
  rw [hx, ← WithBot.coe_top, ← WithBot.coe_add, WithTop.top_add] at hlt
  exact lt_irrefl _ hlt

theorem HasSubgradientWithinAt.mono (hf : HasSubgradientWithinAt p f y s x) (hts : t ⊆ s) :
    HasSubgradientWithinAt p f y t x :=
  ⟨hf.mem_effectiveDomain, hf.bot_lt, fun _ hz ↦ hf.le (hts hz)⟩

theorem HasSubgradientWithinAt.congr (hf : HasSubgradientWithinAt p f y s x)
    (hgf : EqOn g f s) (hx : g x = f x) : HasSubgradientWithinAt p g y s x := by
  refine ⟨show g x < ⊤ from hx ▸ hf.mem_effectiveDomain, hx ▸ hf.bot_lt, fun z hz ↦ ?_⟩
  rw [hx, hgf hz]
  exact hf.le hz

theorem HasSubgradientAt.hasSubgradientWithinAt (hf : HasSubgradientAt p f y x) :
    HasSubgradientWithinAt p f y s x :=
  hf.mono (subset_univ s)

theorem HasSubgradientWithinAt.add [IsOrderedAddMonoid R]
    (hf : HasSubgradientWithinAt p f y s x) (hg : HasSubgradientWithinAt p g y' s x) :
    HasSubgradientWithinAt p (f + g) (y + y') s x := by
  obtain ⟨a, ha⟩ := hf.exists_coe
  obtain ⟨b, hb⟩ := hg.exists_coe
  refine ⟨?_, WithBot.bot_lt_add.2 ⟨hf.bot_lt, hg.bot_lt⟩, fun z hz ↦ ?_⟩
  · change f x + g x < ⊤
    rw [← ha, ← hb]
    exact WithBot.coe_lt_coe.2 (WithTop.coe_lt_top (a + b))
  · change f x + g x + p (z - x) (y + y') ≤ f z + g z
    rw [map_add, WithTop.coe_add, WithBot.coe_add, add_add_add_comm]
    exact add_le_add (hf.le hz) (hg.le hz)

theorem HasSubgradientAt.add [IsOrderedAddMonoid R]
    (hf : HasSubgradientAt p f y x) (hg : HasSubgradientAt p g y' x) :
    HasSubgradientAt p (f + g) (y + y') x :=
  HasSubgradientWithinAt.add hf hg

variable {L : Type*} [AddCommGroup L] [Module R L]

theorem HasSubgradientWithinAt.comp_linearMap (A : L →ₗ[R] M) {x : L}
    (hf : HasSubgradientWithinAt p f y s (A x)) :
    HasSubgradientWithinAt (p.comp A) (f ∘ A) y (A ⁻¹' s) x := by
  refine ⟨hf.mem_effectiveDomain, hf.bot_lt, fun z hz ↦ ?_⟩
  change f (A x) + p (A (z - x)) y ≤ f (A z)
  rw [map_sub]
  exact hf.le hz

theorem HasSubgradientAt.comp_linearMap (A : L →ₗ[R] M) {x : L}
    (hf : HasSubgradientAt p f y (A x)) : HasSubgradientAt (p.comp A) (f ∘ A) y x :=
  HasSubgradientWithinAt.comp_linearMap A hf

@[simp]
theorem hasSubgradientWithinAt_coe_iff {u : M → R} :
    HasSubgradientWithinAt p (u ·) y s x ↔ ∀ ⦃z⦄, z ∈ s → u x + p (z - x) y ≤ u z := by
  simp only [hasSubgradientWithinAt_iff, mem_effectiveDomain, ← WithBot.coe_top,
    WithBot.coe_lt_coe, WithTop.coe_lt_top, WithBot.bot_lt_coe, ← WithBot.coe_add,
    ← WithTop.coe_add, WithBot.coe_le_coe, WithTop.coe_le_coe, true_and]

@[simp]
theorem hasSubgradientAt_coe_iff {u : M → R} :
    HasSubgradientAt p (u ·) y x ↔ ∀ z, u x + p (z - x) y ≤ u z := by
  simp only [HasSubgradientAt, hasSubgradientWithinAt_coe_iff, mem_univ, forall_const]

theorem hasSubgradientWithinAt_const (p : M →ₗ[R] N →ₗ[R] R) (c : R) :
    HasSubgradientWithinAt p (fun _ ↦ c) 0 s x := by
  simp [hasSubgradientWithinAt_coe_iff]

theorem hasSubgradientAt_const (p : M →ₗ[R] N →ₗ[R] R) (c : R) :
    HasSubgradientAt p (fun _ ↦ c) 0 x := hasSubgradientWithinAt_const p c

theorem hasSubgradientWithinAt_pairing (p : M →ₗ[R] N →ₗ[R] R) (y : N) :
    HasSubgradientWithinAt p (p · y) y s x := by
  simp [hasSubgradientWithinAt_coe_iff, map_sub]

theorem hasSubgradientAt_pairing (p : M →ₗ[R] N →ₗ[R] R) (y : N) :
    HasSubgradientAt p (p · y) y x := hasSubgradientWithinAt_pairing p y

@[simp]
theorem hasSubgradientWithinAt_withBot_coe_iff {u : M → WithTop R} :
    HasSubgradientWithinAt p (u ·) y s x ↔
      u x < ⊤ ∧ ∀ ⦃z⦄, z ∈ s → u x + p (z - x) y ≤ u z := by
  simp only [hasSubgradientWithinAt_iff, mem_effectiveDomain, ← WithBot.coe_top,
    WithBot.coe_lt_coe, WithBot.bot_lt_coe, ← WithBot.coe_add, WithBot.coe_le_coe, true_and]

@[simp]
theorem hasSubgradientAt_withBot_coe_iff {u : M → WithTop R} :
    HasSubgradientAt p (u ·) y x ↔ u x < ⊤ ∧ ∀ z, u x + p (z - x) y ≤ u z := by
  simp only [HasSubgradientAt, hasSubgradientWithinAt_withBot_coe_iff, mem_univ, forall_const]

end Subgradient

section Subdifferential

theorem subdifferentialWithin_eq_empty_of_eq_top (hx : f x = ⊤) :
    subdifferentialWithin p f s x = ∅ := by
  simp [subdifferentialWithin, hasSubgradientWithinAt_iff, effectiveDomain, hx]

theorem subdifferentialWithin_eq_empty_of_eq_bot (hx : f x = ⊥) :
    subdifferentialWithin p f s x = ∅ := by
  simp [subdifferentialWithin, hasSubgradientWithinAt_iff, hx]

theorem subdifferential_eq_empty_of_eq_top (hx : f x = ⊤) : subdifferential p f x = ∅ :=
  subdifferentialWithin_eq_empty_of_eq_top hx

theorem subdifferential_eq_empty_of_eq_bot (hx : f x = ⊥) : subdifferential p f x = ∅ :=
  subdifferentialWithin_eq_empty_of_eq_bot hx

end Subdifferential

section Fermat

@[simp]
theorem hasSubgradientWithinAt_zero_iff :
    HasSubgradientWithinAt p f 0 s x ↔ x ∈ effectiveDomain f ∧ ⊥ < f x ∧ IsMinOn f s x := by
  simp [hasSubgradientWithinAt_iff, isMinOn_iff]

@[simp]
theorem hasSubgradientAt_zero_iff :
    HasSubgradientAt p f 0 x ↔ x ∈ effectiveDomain f ∧ ⊥ < f x ∧ IsMinOn f univ x :=
  hasSubgradientWithinAt_zero_iff

/-- **Fermat's rule**: a point minimizes a proper function if and only if zero is a subgradient. -/
theorem IsProper.zero_mem_subdifferential_iff (hf : IsProper f) :
    0 ∈ subdifferential p f x ↔ IsMinOn f univ x := by
  simp [mem_subdifferential, hf.hasSubgradientAt_iff, isMinOn_iff]

end Fermat

end CommRing

section Field

variable [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [AddCommGroup M] [Module R M] [AddCommMonoid N] [Module R N]
  [ConvexSpace R N] [IsModuleConvexSpace R N]

/-- The subdifferential within a set is convex, even when the function is not convex. -/
theorem isConvexSet_subdifferentialWithin
    (p : M →ₗ[R] N →ₗ[R] R) (f : M → R∞) (s : Set M) (x : M) :
    IsConvexSet R (subdifferentialWithin p f s x) := by
  refine .of_convexCombPair_mem fun a b ha hb hab u hu v hv ↦ ?_
  rw [convexCombPair_eq_sum]
  refine ⟨hu.mem_effectiveDomain, hu.bot_lt, fun z hz ↦ ?_⟩
  simp only [map_add, map_smul]
  have hmono : Monotone fun r : R ↦ f x + r :=
    (WithBot.coe_mono.comp WithTop.coe_mono).const_add (f x)
  exact (hmono (Convex.combo_le_max _ _ ha hb hab)).trans
    (hmono.map_max.le.trans (max_le (hu.le hz) (hv.le hz)))

theorem isConvexSet_subdifferential
    (p : M →ₗ[R] N →ₗ[R] R) (f : M → R∞) (x : M) :
    IsConvexSet R (subdifferential p f x) := isConvexSet_subdifferentialWithin p f univ x

end Field

end Convexity
