/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Geometry.Convex.ConvexSpace.AffineMap
public import Mathlib.Tactic.FinCases

/-!
# The cone of an affine map from the standard simplex

Given an affine map `s : StdSimplex R (Fin n) → Y` and `y : Y`, we define
an affine map `s.cone : StdSimplex R (Fin (n + 1))) → Y` which sends
the vertex `0` to `y` and the vertex `i.succ` to the image by `s` of
the `i`th vertex of the standard simplex.

-/

@[expose] public section

namespace Convexity.ConvexSpace

variable {R : Type*} [PartialOrder R] [Semiring R] [IsStrictOrderedRing R]
  {Y Z : Type*} [ConvexSpace R Y] [ConvexSpace R Z]

/-- The cone of an affine map from the standard simplex. -/
noncomputable def AffineMap.cone
    {n : ℕ} (s : ConvexSpace.AffineMap R (StdSimplex R (Fin n)) Y) (y : Y) :
    ConvexSpace.AffineMap R (StdSimplex R (Fin (n + 1))) Y :=
  StdSimplex.affineMapMk (Fin.cases y (fun i ↦ s (.single i)))

lemma AffineMap.cone_def
    {n : ℕ} (s : ConvexSpace.AffineMap R (StdSimplex R (Fin n)) Y) (y : Y) :
    s.cone y = StdSimplex.affineMapMk (Fin.cases y (fun i ↦ s (.single i))) := rfl

@[simp]
lemma AffineMap.cone_single_zero
    {n : ℕ} (s : ConvexSpace.AffineMap R (StdSimplex R (Fin n)) Y) (y : Y) :
    s.cone y (.single 0) = y := by
  simp [cone_def]

@[simp]
lemma AffineMap.cone_single_succ
    {n : ℕ} (s : ConvexSpace.AffineMap R (StdSimplex R (Fin n)) Y) (y : Y) (j : Fin n) :
    s.cone y (.single j.succ) = s (.single j) := by
  simp [cone_def]

@[simp]
lemma AffineMap.cone_mk₁ (y y₀ : Y) :
    (StdSimplex.affineMapMk (R := R) ![y₀]).cone y =
      StdSimplex.affineMapMk ![y, y₀] := by
  rw [cone_def]
  congr
  ext i
  fin_cases i <;> aesop

@[simp]
lemma AffineMap.cone_mk₂ (y y₀ y₁ : Y) :
    (StdSimplex.affineMapMk (R := R) ![y₀, y₁]).cone y =
      StdSimplex.affineMapMk ![y, y₀, y₁] := by
  rw [cone_def]
  congr
  ext i
  fin_cases i <;> aesop

lemma AffineMap.cone_comp {n : ℕ} (φ : ConvexSpace.AffineMap R Y Z)
    (ψ : ConvexSpace.AffineMap R (StdSimplex R (Fin (n + 1))) Y) (y : Y) :
    (φ.comp ψ).cone (φ y) = φ.comp (ψ.cone y) := by
  ext i
  obtain rfl | ⟨i, rfl⟩ := i.eq_zero_or_eq_succ <;> simp

end Convexity.ConvexSpace
