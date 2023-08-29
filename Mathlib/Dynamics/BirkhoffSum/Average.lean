/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
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

set_option autoImplicit true

section birkhoffAverage

variable (R : Type*) {α M : Type*} [DivisionSemiring R] [AddCommMonoid M] [Module R M]

/-- The average value of `g` on the first `n` points of the orbit of `x` under `f`,
i.e. the Birkhoff sum `∑ k in Finset.range n, g (f^[k] x)` divided by `n`.

This average appears in many ergodic theorems
which say that `(birkhoffAverage R f g · x)`
converges to the "space average" `⨍ x, g x ∂μ` as `n → ∞`.

We use an auxiliary `[DivisionSemiring R]` to define division by `n`.
However, the definition does not depend on the choice of `R`,
see `birkhoffAverage_congr_ring`. -/
def birkhoffAverage (f : α → α) (g : α → M) (n : ℕ) (x : α) : M := (n : R)⁻¹ • birkhoffSum f g n x

theorem birkhoffAverage_zero (f : α → α) (g : α → M) (x : α) :
    birkhoffAverage R f g 0 x = 0 := by simp [birkhoffAverage]
                                        -- 🎉 no goals

@[simp] theorem birkhoffAverage_zero' (f : α → α) (g : α → M) : birkhoffAverage R f g 0 = 0 :=
  funext <| birkhoffAverage_zero _ _ _

theorem birkhoffAverage_one (f : α → α) (g : α → M) (x : α) :
    birkhoffAverage R f g 1 x = g x := by simp [birkhoffAverage]
                                          -- 🎉 no goals

@[simp]
theorem birkhoffAverage_one' (f : α → α) (g : α → M) : birkhoffAverage R f g 1 = g :=
  funext <| birkhoffAverage_one R f g

theorem map_birkhoffAverage (S : Type*) {F N : Type*}
    [DivisionSemiring S] [AddCommMonoid N] [Module S N]
    [AddMonoidHomClass F M N] (g' : F) (f : α → α) (g : α → M) (n : ℕ) (x : α) :
    g' (birkhoffAverage R f g n x) = birkhoffAverage S f (g' ∘ g) n x := by
  simp only [birkhoffAverage, map_inv_nat_cast_smul g' R S, map_birkhoffSum]
  -- 🎉 no goals

theorem birkhoffAverage_congr_ring (S : Type*) [DivisionSemiring S] [Module S M]
    (f : α → α) (g : α → M) (n : ℕ) (x : α) :
    birkhoffAverage R f g n x = birkhoffAverage S f g n x :=
  map_birkhoffAverage R S (AddMonoidHom.id M) f g n x

theorem birkhoffAverage_congr_ring' (S : Type*) [DivisionSemiring S] [Module S M] :
    birkhoffAverage (α := α) (M := M) R = birkhoffAverage S := by
  ext; apply birkhoffAverage_congr_ring
  -- ⊢ birkhoffAverage R x✝³ x✝² x✝¹ x✝ = birkhoffAverage S x✝³ x✝² x✝¹ x✝
       -- 🎉 no goals

theorem Function.IsFixedPt.birkhoffAverage_eq [CharZero R] {f : α → α} {x : α} (h : IsFixedPt f x)
    (g : α → M) {n : ℕ} (hn : n ≠ 0) : birkhoffAverage R f g n x = g x := by
  rw [birkhoffAverage, h.birkhoffSum_eq, nsmul_eq_smul_cast R, inv_smul_smul₀]
  -- ⊢ ↑n ≠ 0
  rwa [Nat.cast_ne_zero]
  -- 🎉 no goals

end birkhoffAverage

/-- Birkhoff average is "almost invariant" under `f`:
the difference between `birkhoffAverage R f g n (f x)` and `birkhoffAverage R f g n x`
is equal to `(n : R)⁻¹ • (g (f^[n] x) - g x)`. -/
theorem birkhoffAverage_apply_sub_birkhoffAverage (R : Type*) [DivisionRing R]
    [AddCommGroup M] [Module R M] (f : α → α) (g : α → M) (n : ℕ) (x : α) :
    birkhoffAverage R f g n (f x) - birkhoffAverage R f g n x =
      (n : R)⁻¹ • (g (f^[n] x) - g x) := by
  simp only [birkhoffAverage, birkhoffSum_apply_sub_birkhoffSum, ← smul_sub]
  -- 🎉 no goals
