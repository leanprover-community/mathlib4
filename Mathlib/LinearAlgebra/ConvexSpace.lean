/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Data.Finsupp.SMulWithZero
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Tactic.Bound

/-!
# Convex spaces

This file defines convex spaces as an algebraic structure supporting finite convex combinations.

## Main definitions

* `FiniteProbability R ι`: A finitely supported probability distribution over `ι` with coefficients
  in `R`. The weights are non-negative and sum to 1.
* `ConvexSpace R M`: A typeclass for spaces `M` equipped with an operation of taking convex
  combinations with coefficients in `R`.
* `convexCombo₂`: Binary convex combinations of two points.

## TODO

* Show that an `AffineSpace` is a `ConvexSpace`.
* Show that `lineMap` agrees with `convexCombo₂` where defined.
* Show the usual associativity law for binary convex combinations follows from the `assoc` axiom.
* Decide if the `ext` axiom is necessary (via a counterexample), or derive it from `assoc`.
-/

@[expose] public section

universe u v

noncomputable section

/--
A finitely supported probability distribution over `ι` with coefficients in `R`.
The weights are non-negative and sum to 1.
-/
structure FiniteProbability (R : Type u) [LE R] [AddCommMonoid R] [One R] (ι : Type v)
    extends weights : ι →₀ R where
  /-- All weights are non-negative. -/
  nonneg : ∀ m, 0 ≤ weights m
  /-- The weights sum to 1. -/
  total : weights.sum (fun _ r => r) = 1

namespace FiniteProbability

variable {R : Type u} [PartialOrder R] [Semiring R] [IsStrictOrderedRing R]
  {κ : Type v} {ι : κ → Type v}

open Classical in
/-- The point mass distribution concentrated at `i`. -/
def single {ι : Type v} (i : ι) : FiniteProbability R ι where
  weights := Finsupp.single i 1
  nonneg m := by
    rw [Finsupp.single_apply]
    split
    · exact zero_le_one' R
    · grind
  total := by simp

/-- A probability distribution on `Fin 2` with weights `x` and `y`. -/
-- Is it useful to generalize this to `x y : ι`?
def duple {s t : R} (hs : 0 ≤ s) (ht : 0 ≤ t) (h : s + t = 1) : FiniteProbability R (Fin 2) where
  weights := Finsupp.single 0 s + Finsupp.single 1 t
  nonneg := by
    simp
    grind
  total := by
    simpa [Finsupp.sum_add_index]

/--
Composition of probability distributions.
Given a distribution `f` over `κ` and a family `g` of distributions over `ι k` for each `k : κ`,
produces a distribution over `Σ k, ι k`.
-/
def comp (f : FiniteProbability R κ) (g : (k : κ) → FiniteProbability R (ι k)) :
    FiniteProbability R (Σ k, ι k) where
  weights := f.sum (fun m r => (r • (g m).weights).embDomain <| .sigmaMk m)
  nonneg := by
    intro ⟨k, i⟩
    simp only [Finsupp.sum, Finsupp.coe_finset_sum, Finset.sum_apply]
    refine (Finset.sum_nonneg (fun k hk => ?_))
    simp [Finsupp.embDomain]
    have := f.nonneg
    have := (g k).nonneg
    bound
  total := by
    -- This proof was minimally cleaned up from a proof by Aristotle.
    have h_total : (f.sum fun m r => (r • (g m).weights).embDomain (.sigmaMk m)) =
        (f.sum fun m r => Finsupp.single m r).sum
          fun m r => (r • (g m).weights).embDomain (.sigmaMk m) := by simp
    have h_sum : ∀ m, ((f.weights m • (g m).weights).embDomain (.sigmaMk m)).sum (fun x r => r) =
        f.weights m * (g m).weights.sum (fun x r => r) := by
      intro m
      rw [Finsupp.sum_embDomain]
      simp only [Finsupp.sum, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum _ _ _,
        Finset.sum_subset (show _ ⊆ ((g m).weights.support) from
          fun x hx => by aesop) fun x hx₁ hx₂ => by aesop]
    have h_final : (f.sum fun m r => (r • (g m).weights).embDomain (.sigmaMk m)).sum
        (fun x r => r) = (f.sum fun (m : κ) (r : R) => Finsupp.single m r).sum fun m r => r := by
      rw [h_total, Finsupp.sum_sum_index];
      · have h_g_sum : ∀ m : κ, (g m).weights.sum (fun x r => r) = 1 := by
          intro m
          apply (g m).total
        simp_all only [Finsupp.sum_single, mul_one]
        exact Finset.sum_congr rfl fun m hm => h_sum m
      · exact fun _ => rfl
      · exact fun _ _ _ => rfl
    convert f.total using 1
    convert h_final using 1
    rw [Finsupp.sum_sum_index] <;> aesop

end FiniteProbability

/--
A set equipped with an operation of finite convex combinations,
where the coefficients must be non-negative and sum to 1.
-/
class ConvexSpace (R : Type u) (M : Type v)
    [PartialOrder R] [Semiring R] [IsStrictOrderedRing R] where
  /-- Take a convex combination of a family of points with the given probability distribution. -/
  convexCombination {ι : Type v} (f : FiniteProbability R ι) (xs : ι → M) : M
  /-- Associativity of convex combination. -/
  assoc
    {κ : Type v} (f₀ : FiniteProbability R κ)
    {ι : κ → Type v} (f₁ : (k : κ) → FiniteProbability R (ι k))
    (xs : (k : κ) → (ι k) → M) :
    convexCombination f₀ (fun m => convexCombination (f₁ m) (xs m)) =
      convexCombination (f₀.comp f₁) (fun ⟨k, i⟩ => xs k i)
  /-- A convex combination of a single point is that point. -/
  single {ι : Type v} (i : ι) (x : M) : convexCombination (.single i) (fun _ => x) = x
  /-- Convex combinations are determined by the points with non-zero weights. -/
  -- Perhaps this follows from `assoc`, but I don't see how.
  ext {ι : Type v} (f : FiniteProbability R ι) (xs xs' : ι → M)
    (h : ∀ i, i ∈ f.support → xs i = xs' i) : convexCombination f xs = convexCombination f xs'

open ConvexSpace

variable {R M} [PartialOrder R] [Semiring R] [IsStrictOrderedRing R] [ConvexSpace R M]

/-- Take a convex combination of two points. -/
def convexCombo₂ (s t : R) (hs : 0 ≤ s) (ht : 0 ≤ t) (h : s + t = 1) (x y : M) : M :=
  convexCombination (.duple hs ht h) (fun | 0 => x | 1 => y)

/-- A binary convex combination with weight 0 on the first point returns the second point. -/
proof_wanted convexCombo₂_zero {x y : M} :
  convexCombo₂ (0 : R) 1 (by simp) (by simp) (by simp) x y = y

/-- A binary convex combination with weight 1 on the first point returns the first point. -/
proof_wanted convexCombo₂_one {x y : M} :
  convexCombo₂ (1 : R) 0 (by simp) (by simp) (by simp) x y = x

/-- A convex combination of a point with itself is that point. -/
proof_wanted convexCombo₂_same {s t : R} (hs : 0 ≤ s) (ht : 0 ≤ t) (h : s + t = 1) {x : M} :
  convexCombo₂ s t hs ht h x x = x
