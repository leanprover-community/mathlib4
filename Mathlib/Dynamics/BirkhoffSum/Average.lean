/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Lua Viana Reis, Oliver Butterley
-/
import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.Algebra.Module.Basic

/-!
# Birkhoff average

In this file we define `birkhoffAverage f g n x` to be
$$
\frac{1}{n}\sum_{k=0}^{n-1}g(f^{[k]}(x)),
$$
where `f : α → α` is a self-map on some type `α`,
`g : α → M` is a function from `α` to a module over a division semiring `R`,
and `R` is used to formalize division by `n` as `(n : R)⁻¹ • _`.

While we need an auxiliary division semiring `R` to define `birkhoffAverage`,
the definition does not depend on the choice of `R`,
see `birkhoffAverage_congr_ring`.

-/

open Finset

section birkhoffAverage

variable (R : Type*) {α M : Type*} [DivisionSemiring R] [AddCommMonoid M] [Module R M]

/-- The average value of `g` on the first `n` points of the orbit of `x` under `f`,
i.e. the Birkhoff sum `∑ k ∈ Finset.range n, g (f^[k] x)` divided by `n`.

This average appears in many ergodic theorems
which say that `(birkhoffAverage R f g · x)`
converges to the "space average" `⨍ x, g x ∂μ` as `n → ∞`.

We use an auxiliary `[DivisionSemiring R]` to define division by `n`.
However, the definition does not depend on the choice of `R`,
see `birkhoffAverage_congr_ring`. -/
def birkhoffAverage (f : α → α) (g : α → M) (n : ℕ) (x : α) : M := (n : R)⁻¹ • birkhoffSum f g n x

theorem birkhoffAverage_zero (f : α → α) (g : α → M) (x : α) :
    birkhoffAverage R f g 0 x = 0 := by simp [birkhoffAverage]

@[simp] theorem birkhoffAverage_zero' (f : α → α) (g : α → M) : birkhoffAverage R f g 0 = 0 :=
  funext <| birkhoffAverage_zero _ _ _

theorem birkhoffAverage_one (f : α → α) (g : α → M) (x : α) :
    birkhoffAverage R f g 1 x = g x := by simp [birkhoffAverage]

@[simp]
theorem birkhoffAverage_one' (f : α → α) (g : α → M) : birkhoffAverage R f g 1 = g :=
  funext <| birkhoffAverage_one R f g

theorem map_birkhoffAverage (S : Type*) {F N : Type*}
    [DivisionSemiring S] [AddCommMonoid N] [Module S N] [FunLike F M N]
    [AddMonoidHomClass F M N] (g' : F) (f : α → α) (g : α → M) (n : ℕ) (x : α) :
    g' (birkhoffAverage R f g n x) = birkhoffAverage S f (g' ∘ g) n x := by
  simp only [birkhoffAverage, map_inv_natCast_smul g' R S, map_birkhoffSum]

theorem birkhoffAverage_congr_ring (S : Type*) [DivisionSemiring S] [Module S M]
    (f : α → α) (g : α → M) (n : ℕ) (x : α) :
    birkhoffAverage R f g n x = birkhoffAverage S f g n x :=
  map_birkhoffAverage R S (AddMonoidHom.id M) f g n x

theorem birkhoffAverage_congr_ring' (S : Type*) [DivisionSemiring S] [Module S M] :
    birkhoffAverage (α := α) (M := M) R = birkhoffAverage S := by
  ext; apply birkhoffAverage_congr_ring

theorem Function.IsFixedPt.birkhoffAverage_eq [CharZero R] {f : α → α} {x : α} (h : IsFixedPt f x)
    (g : α → M) {n : ℕ} (hn : n ≠ 0) : birkhoffAverage R f g n x = g x := by
  rw [birkhoffAverage, h.birkhoffSum_eq, ← Nat.cast_smul_eq_nsmul R, inv_smul_smul₀]
  rwa [Nat.cast_ne_zero]

lemma birkhoffAverage_add {f : α → α} {g g' : α → M} :
    birkhoffAverage R f (g + g') = birkhoffAverage R f g + birkhoffAverage R f g' := by
  funext _ x
  simp [birkhoffAverage, birkhoffSum, sum_add_distrib, smul_add]

end birkhoffAverage

section AddCommGroup

variable {R : Type*} {α M : Type*} [DivisionSemiring R] [AddCommGroup M] [Module R M]

lemma birkhoffAverage_neg {f : α → α} {g : α → M} :
    birkhoffAverage R f (-g) = - birkhoffAverage R f g := by
  funext _ x
  simp [birkhoffAverage, birkhoffSum]

lemma birkhoffAverage_sub {f : α → α} {g g' : α → M} :
    birkhoffAverage R f (g - g') = birkhoffAverage R f g - birkhoffAverage R f g' := by
  funext _ x
  simp [birkhoffAverage, birkhoffSum, smul_sub]

/-- Birkhoff average is "almost invariant" under `f`:
the difference between `birkhoffAverage R f g n (f x)` and `birkhoffAverage R f g n x`
is equal to `(n : R)⁻¹ • (g (f^[n] x) - g x)`. -/
theorem birkhoffAverage_apply_sub_birkhoffAverage (f : α → α) (g : α → M) (n : ℕ) (x : α) :
    birkhoffAverage R f g n (f x) - birkhoffAverage R f g n x =
      (n : R)⁻¹ • (g (f^[n] x) - g x) := by
  simp only [birkhoffAverage, birkhoffSum_apply_sub_birkhoffSum, ← smul_sub]

/-- If a function `g` is invariant under a function `f` (i.e., `g ∘ f = g`), then the Birkhoff
average of `g` over `f` for `n` iterations is equal to `g`. Requires that `0 < n`. -/
theorem birkhoffAverage_of_comp_eq [CharZero R] {f : α → α} {g : α → M} (h : g ∘ f = g)
    {n : ℕ} (hn : n ≠ 0) : birkhoffAverage R f g n = g := by
  funext x
  suffices (n : R)⁻¹ • n • g x = g x by simpa [birkhoffAverage, birkhoffSum_of_comp_eq h]
  rw [← Nat.cast_smul_eq_nsmul (R := R), ← mul_smul, inv_mul_cancel₀ (by norm_cast), one_smul]

end AddCommGroup
