/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplexCategory.DeltaZeroIter
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic

/-!
# Iterations of `δ 0` and `σ 0`

This file introduce morphisms `δ₀Iter i` and `σ₀Iter i` for simplicial objects:
they are obtained as the `i`th iteration of `δ 0` or `σ 0`.

-/

@[expose] public section

universe u

open Simplicial

namespace CategoryTheory.SimplicialObject

variable {C : Type*} [Category* C] (X : SimplicialObject C)

def δ₀Iter {n m : ℕ} (i : ℕ) (hi : n + i = m := by grind) :
    X _⦋m⦌ ⟶ X _⦋n⦌ :=
  X.map (SimplexCategory.δ₀Iter i hi).op

@[simp]
lemma δ₀Iter_zero (n : ℕ) :
    X.δ₀Iter 0 (add_zero n) = 𝟙 _ := by
  simp [δ₀Iter]

@[simp]
lemma δ₀Iter_one (n : ℕ) :
    X.δ₀Iter 1 (n := n) rfl = X.δ 0 := rfl

@[reassoc]
lemma δ₀Iter_succ' (i : ℕ) {n m : ℕ} (h : n + (i + 1) = m := by grind) :
    X.δ₀Iter (i + 1) h = X.δ₀Iter i ≫ X.δ 0 := by
  dsimp [δ, δ₀Iter]
  rw [← Functor.map_comp, ← op_comp, SimplexCategory.δ₀Iter_succ' _ h]

@[reassoc]
lemma δ_δ₀Iter (i : ℕ) {n m : ℕ} (j : Fin (m + 2))
    (hi : n + i = m := by grind) (hj : j.val ≤ i := by grind) :
    X.δ j ≫ X.δ₀Iter i hi = X.δ₀Iter (i + 1) := by
  dsimp [δ, δ₀Iter]
  rw [← Functor.map_comp, ← op_comp, SimplexCategory.δ₀Iter_δ ..]

@[reassoc]
lemma δ_δ₀Iter' {n : ℕ} (i : Fin (n + 2)) (j : ℕ) {m : ℕ}
    (i' : Fin (m + 2)) (h : n + j = m := by grind)
    (hi'' : i'.val = i.val + j := by grind) :
    X.δ i' ≫ X.δ₀Iter j = X.δ₀Iter j ≫ X.δ i := by
  dsimp [δ, δ₀Iter]
  simp only [← Functor.map_comp, ← op_comp, SimplexCategory.δ₀Iter_δ' _ _ _ _ hi'']

@[reassoc]
lemma σ_δ₀Iter (i : ℕ) {n m : ℕ} (j : Fin (m + 1))
    (hi : n + (i + 1) = m + 1 := by grind)
    (hj : j.val ≤ i := by grind) :
    X.σ j ≫ X.δ₀Iter (i + 1) hi  = X.δ₀Iter i := by
  dsimp [σ, δ₀Iter]
  rw [← Functor.map_comp, ← op_comp, SimplexCategory.δ₀Iter_σ ..]

@[reassoc]
def σ_δ₀Iter' (i : ℕ) {n m : ℕ} (j : Fin (m + 1))
    (j' : Fin (n + 1))
    (hi' : n + i = m := by grind)
    (hj' : j.val = j'.val + i := by grind) :
    X.σ j ≫ X.δ₀Iter i = X.δ₀Iter i hi' ≫ X.σ j' := by
  simp [σ, δ₀Iter, ← Functor.map_comp, ← op_comp,
    SimplexCategory.δ₀Iter_σ' i j j' (by grind) (by grind)]

def σ₀Iter {n m : ℕ} (i : ℕ) (hi : n + i = m := by grind) :
    X _⦋n⦌ ⟶ X _⦋m⦌ :=
  X.map (SimplexCategory.σ₀Iter i hi).op

@[simp]
lemma σ₀Iter_zero (n : ℕ) :
    X.σ₀Iter 0 (add_zero n) = 𝟙 _ := by
  simp [σ₀Iter]

@[reassoc]
lemma σ₀Iter_succ (i : ℕ) {n m : ℕ} (h : n + (i + 1) = m := by grind) :
    X.σ₀Iter (i + 1) h = X.σ 0 ≫ X.σ₀Iter i := by
  dsimp [σ, σ₀Iter]
  rw [← Functor.map_comp, ← op_comp, SimplexCategory.σ₀Iter_succ ..]

@[reassoc]
lemma σ₀Iter_δ {n : ℕ} (i : Fin (n + 2)) (j : ℕ) {m : ℕ} (h : m + (j + 1) = n + 1 := by grind)
    (hi' : i.val ≤ j + 1 := by grind) :
    X.σ₀Iter (n := m) (j + 1) h ≫ X.δ i = X.σ₀Iter j := by
  simp only [σ₀Iter, δ, ← Functor.map_comp, ← op_comp, SimplexCategory.δ_σ₀Iter i j h]

@[reassoc]
lemma σ₀Iter_δ' {n : ℕ} (i : Fin (n + 2)) (j : ℕ) {m : ℕ}
    (i' : Fin (m + 2)) (h : m + j = n := by grind)
    (hi' : j < i.val := by grind)
    (hi'' : i.val = i'.val + j := by grind) :
    X.σ₀Iter (n := m + 1) j ≫ X.δ i = X.δ i' ≫ X.σ₀Iter j := by
  simp only [σ₀Iter, δ, ← Functor.map_comp, ← op_comp,
    SimplexCategory.δ_σ₀Iter' i j i']

@[reassoc]
lemma σ₀Iter_σ (i : ℕ) {n m : ℕ} (j : Fin (m + 1)) (hi : n + i = m := by grind)
    (hj : j.val ≤ i := by grind) :
    X.σ₀Iter i hi ≫ X.σ j = X.σ₀Iter (i + 1) := by
  dsimp [σ, σ₀Iter]
  rw [← Functor.map_comp, ← op_comp, SimplexCategory.σ_σ₀Iter ..]

@[reassoc]
lemma σ₀Iter_σ' (i : ℕ) {n m : ℕ} (j : Fin (m + 1)) (j' : Fin (n + 1))
    (hi : n + i = m := by grind)
    (hj : j.val = j'.val + i := by grind) :
    X.σ₀Iter i hi ≫ X.σ j = X.σ j' ≫ X.σ₀Iter i := by
  simp [σ, σ₀Iter, ← Functor.map_comp, ← op_comp,
    SimplexCategory.σ_σ₀Iter' i j j']

end CategoryTheory.SimplicialObject
