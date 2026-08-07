/-
Copyright (c) 2026 Jay Scambler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jay Scambler
-/
module

public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.Convex.Quasiconvex
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Order.SaddlePoint
public import Mathlib.Topology.Sion

/-!
# Finite zero-sum matrix games: von Neumann's minimax theorem

A finite zero-sum two-player matrix game is specified by a payoff
matrix `M : Matrix (Fin m) (Fin n) ℝ`. The row player chooses a row,
the column player chooses a column, and the row player receives
`M i j` (the column player loses the same amount).

Mixed strategies are probability distributions on the row/column sets,
i.e. members of `stdSimplex ℝ (Fin m)` and `stdSimplex ℝ (Fin n)`. The
expected payoff under a mixed-strategy pair `(x, y)` is the bilinear
form `∑ i, ∑ j, x i * M i j * y j`.

This file specialises `Sion.exists_isSaddlePointOn`
(`Mathlib.Topology.Sion`) to the finite matrix-game case to obtain
**von Neumann's 1928 minimax theorem**: every finite zero-sum matrix
game admits a mixed-strategy saddle point.

## Main results

* `Matrix.payoff`: the expected payoff `∑ i j, x i * M i j * y j`.
* `Matrix.exists_saddle_point`: saddle-point existence in the mathlib
  convention (`a` minimises in `X`, `b` maximises in `Y`).
* `Matrix.exists_mixedNash`: textbook-orientation Nash-equilibrium
  existence (row player maximises, column player minimises).

## Convention note

`Mathlib.Order.SaddlePoint` defines `IsSaddlePointOn X Y f a b` as
`∀ x ∈ X, ∀ y ∈ Y, f a y ≤ f x b`, with `a` minimiser in `X` and
`b` maximiser in `Y`. The textbook matrix-game saddle (row player
maximises, column player minimises) is the opposite convention; a
textbook saddle of `payoff M` is a mathlib saddle of `-payoff M`.
Both forms are recorded below.

## References

* John von Neumann, "Zur Theorie der Gesellschaftsspiele",
  *Mathematische Annalen* 100(1): 295-320, 1928.
* Maurice Sion, "On general minimax theorems",
  *Pacific Journal of Mathematics* 8(1): 171-176, 1958.
-/

namespace Matrix

variable {m n : ℕ}

@[expose] public section

/-- Expected payoff of the mixed-strategy pair `(x, y)` under matrix
`M`: `∑ i, ∑ j, x i * M i j * y j`. -/
def payoff (M : Matrix (Fin m) (Fin n) ℝ) (x : Fin m → ℝ) (y : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, x i * M i j * y j

theorem payoff_continuous_left (M : Matrix (Fin m) (Fin n) ℝ) (y : Fin n → ℝ) :
    Continuous (fun x : Fin m → ℝ => payoff M x y) := by
  unfold payoff
  refine continuous_finsetSum _ fun i _ => ?_
  refine continuous_finsetSum _ fun j _ => ?_
  have h1 : Continuous (fun x : Fin m → ℝ => x i * M i j) :=
    (continuous_apply i).mul continuous_const
  exact h1.mul continuous_const

theorem payoff_continuous_right (M : Matrix (Fin m) (Fin n) ℝ) (x : Fin m → ℝ) :
    Continuous (fun y : Fin n → ℝ => payoff M x y) := by
  unfold payoff
  refine continuous_finsetSum _ fun i _ => ?_
  refine continuous_finsetSum _ fun j _ => ?_
  have hconst : Continuous (fun _ : Fin n → ℝ => x i * M i j) := continuous_const
  exact hconst.mul (continuous_apply j)

theorem payoff_isLinearMap_left (M : Matrix (Fin m) (Fin n) ℝ) (y : Fin n → ℝ) :
    IsLinearMap ℝ (fun x : Fin m → ℝ => payoff M x y) where
  map_add x x' := by
    unfold payoff
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  map_smul c x := by
    unfold payoff
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring

theorem payoff_isLinearMap_right (M : Matrix (Fin m) (Fin n) ℝ) (x : Fin m → ℝ) :
    IsLinearMap ℝ (fun y : Fin n → ℝ => payoff M x y) where
  map_add y y' := by
    unfold payoff
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  map_smul c y := by
    unfold payoff
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring

private theorem stdSimplex_nonempty_aux {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    (stdSimplex ℝ ι).Nonempty :=
  ⟨Pi.single (Classical.arbitrary ι) 1, single_mem_stdSimplex _ _⟩

/-- **Von Neumann's minimax theorem for finite matrix games.** Every
finite zero-sum two-player matrix game admits a mixed-strategy saddle
point in the sense of `IsSaddlePointOn`: there exist `a ∈ stdSimplex ℝ
(Fin m)` and `b ∈ stdSimplex ℝ (Fin n)` such that
`payoff M a y ≤ payoff M x b` for all `(x, y)` in the simplex pair.

The proof specialises `Sion.exists_isSaddlePointOn` to the bilinear
payoff over the standard simplices: convexity, compactness, and
non-emptiness of each simplex are direct, and linearity in each
variable provides continuity, quasi-convexity, and
quasi-concavity. -/
theorem exists_saddle_point [NeZero m] [NeZero n]
    (M : Matrix (Fin m) (Fin n) ℝ) :
    ∃ a ∈ stdSimplex ℝ (Fin m), ∃ b ∈ stdSimplex ℝ (Fin n),
      IsSaddlePointOn (stdSimplex ℝ (Fin m)) (stdSimplex ℝ (Fin n))
        (payoff M) a b := by
  haveI : Nonempty (Fin m) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne m)⟩⟩
  haveI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩⟩
  exact Sion.exists_isSaddlePointOn
    stdSimplex_nonempty_aux
    (convex_stdSimplex ℝ (Fin m))
    (isCompact_stdSimplex ℝ (Fin m))
    (fun y _ => (payoff_continuous_left M y).continuousOn.lowerSemicontinuousOn)
    (fun y _ => (((payoff_isLinearMap_left M y).mk' _).convexOn
                  (convex_stdSimplex ℝ (Fin m))).quasiconvexOn)
    (convex_stdSimplex ℝ (Fin n))
    stdSimplex_nonempty_aux
    (isCompact_stdSimplex ℝ (Fin n))
    (fun x _ => (payoff_continuous_right M x).continuousOn.upperSemicontinuousOn)
    (fun x _ => (((payoff_isLinearMap_right M x).mk' _).concaveOn
                  (convex_stdSimplex ℝ (Fin n))).quasiconcaveOn)

/-- **Mixed Nash equilibrium existence for finite zero-sum games.** In
the textbook orientation (row player maximises payoff, column player
minimises), every finite zero-sum matrix game admits a mixed-strategy
Nash equilibrium: there exist `a` and `b` in the respective simplices
such that no player can strictly improve their payoff by unilaterally
deviating.

Equivalent to `exists_saddle_point` applied to `-payoff M`. -/
theorem exists_mixedNash [NeZero m] [NeZero n]
    (M : Matrix (Fin m) (Fin n) ℝ) :
    ∃ a ∈ stdSimplex ℝ (Fin m), ∃ b ∈ stdSimplex ℝ (Fin n),
      (∀ x ∈ stdSimplex ℝ (Fin m), payoff M x b ≤ payoff M a b) ∧
      (∀ y ∈ stdSimplex ℝ (Fin n), payoff M a b ≤ payoff M a y) := by
  haveI : Nonempty (Fin m) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne m)⟩⟩
  haveI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩⟩
  have neg_lin_left : ∀ y : Fin n → ℝ,
      IsLinearMap ℝ (fun x : Fin m → ℝ => -payoff M x y) := fun y =>
    { map_add := fun x x' => by
        rw [(payoff_isLinearMap_left M y).map_add]; ring
      map_smul := fun c x => by
        rw [(payoff_isLinearMap_left M y).map_smul]; simp [smul_eq_mul] }
  have neg_lin_right : ∀ x : Fin m → ℝ,
      IsLinearMap ℝ (fun y : Fin n → ℝ => -payoff M x y) := fun x =>
    { map_add := fun y y' => by
        rw [(payoff_isLinearMap_right M x).map_add]; ring
      map_smul := fun c y => by
        rw [(payoff_isLinearMap_right M x).map_smul]; simp [smul_eq_mul] }
  have hsaddle : ∃ a ∈ stdSimplex ℝ (Fin m), ∃ b ∈ stdSimplex ℝ (Fin n),
      IsSaddlePointOn (stdSimplex ℝ (Fin m)) (stdSimplex ℝ (Fin n))
        (fun x y => -payoff M x y) a b :=
    Sion.exists_isSaddlePointOn
      stdSimplex_nonempty_aux
      (convex_stdSimplex ℝ (Fin m))
      (isCompact_stdSimplex ℝ (Fin m))
      (fun y _ => ((payoff_continuous_left M y).neg).continuousOn.lowerSemicontinuousOn)
      (fun y _ => (((neg_lin_left y).mk' _).convexOn
                    (convex_stdSimplex ℝ (Fin m))).quasiconvexOn)
      (convex_stdSimplex ℝ (Fin n))
      stdSimplex_nonempty_aux
      (isCompact_stdSimplex ℝ (Fin n))
      (fun x _ => ((payoff_continuous_right M x).neg).continuousOn.upperSemicontinuousOn)
      (fun x _ => (((neg_lin_right x).mk' _).concaveOn
                    (convex_stdSimplex ℝ (Fin n))).quasiconcaveOn)
  obtain ⟨a, ha, b, hb, hsab⟩ := hsaddle
  refine ⟨a, ha, b, hb, ?_, ?_⟩
  · intro x hx
    have h := hsab x hx b hb
    linarith
  · intro y hy
    have h := hsab a ha y hy
    linarith

end

end Matrix
