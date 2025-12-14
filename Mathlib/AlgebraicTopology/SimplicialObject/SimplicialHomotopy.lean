/-
Copyright (c) 2025 Fabian Odermatt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Odermatt
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic

/-!
# Simplicial homotopies of simplicial objects

This file defines the notion of a combinatorial simplicial homotopy between two morphisms
of simplicial objects.

## Main definitions

* `SimplicialHomotopy f g`: The type of simplicial homotopies between morphisms `f g : X ⟶ Y`.
* `SimplicialHomotopy.refl f`: The constant homotopy from `f` to `f`.

## Implementation notes

The definition follows the combinatorial description of simplicial homotopies.
Given simplicial objects `X Y : SimplicialObject C` and morphisms `f g : X ⟶ Y`,
a simplicial homotopy consists of a family of morphisms `h n i : X _⦋n⦌ ⟶ Y _⦋n+1⦌`
satisfying the simplicial identities involving the faces and degeneracies.

## References

* [nLab, *Simplicial Homotopy*](https://ncatlab.org/nlab/show/simplicial+homotopy)
-/

@[expose] public section

universe v u

noncomputable section

open SimplexCategory Simplicial Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

structure SimplicialHomotopy
    {X Y : SimplicialObject C} (f g : X ⟶ Y) where

  /-- Basic data: `h i : Xₙ ⟶ Yₙ₊₁` for `i = 0..n`. -/
  h (n : ℕ) (i : Fin (n + 1)) : (X _⦋n⦌ ⟶ Y _⦋n+1⦌)

  /-- Endpoint `d₀ h₀ = f`. -/
  d0_h0 (n : ℕ) :
    h n 0 ≫ Y.δ 0 = f.app (op ⦋n⦌)

  /-- Endpoint `d_{n+1} hₙ = g`. -/
  dLast_hLast (n : ℕ) :
    h n (Fin.last n) ≫ Y.δ (Fin.last (n + 1)) = g.app (op ⦋n⦌)

  /- nlab: `dᵢ hⱼ = h_{j'-1} dᵢ` if i < j', let j' = j + 1 -/
  /-- `dᵢ h_{j+1} = hⱼ dᵢ` if i < j + 1. -/
  face_lt (n : ℕ) (i : Fin (n + 2)) (j : Fin (n + 1)) (hij : i < j.succ) :
    h (n + 1) j.succ ≫ Y.δ i.castSucc = X.δ i ≫ h n j

  /- nlab: `dᵢ hⱼ = dⱼ h_{j'-1}` if i = j' ≠ 0, let j' = j + 1 -/
  /-- `d_{j+1} h_{j+1} = d_{j+1} hⱼ` if i = j + 1 -/
  face_eq (n : ℕ) (j : Fin (n + 1)) :
    h (n + 1) j.succ ≫ Y.δ j.succ.castSucc = h (n + 1) j.castSucc ≫ Y.δ j.succ.castSucc

  /- nlab: `dᵢ hⱼ = hⱼ d_{i'-1}` if i' > j + 1, let i' = i + 1 -/
  /-- `d_{i+1} hⱼ = hⱼ dᵢ` if i > j -/
  face_gt (n : ℕ) (i : Fin (n + 2)) (j : Fin (n + 1)) (hji : j.castSucc < i) :
    h (n + 1) j.castSucc ≫ Y.δ i.succ = X.δ i ≫ h n j

  /-- `sᵢ hⱼ = h_{j+1} sᵢ` if i ≤ j. -/
  deg_le (n : ℕ) (i : Fin (n + 1)) (j : Fin (n + 1)) (hij : i ≤ j) :
    h n j ≫ Y.σ i.castSucc = X.σ i ≫ h (n + 1) j.succ

  /- nlab: `sᵢ hⱼ = hⱼ s_{i'-1}` if i' > j, let i' = i + 1 -/
  /-- `s_{i+1} hⱼ = hⱼ sᵢ` if i + 1 > j -/
  deg_gt (n : ℕ) (i : Fin (n + 1)) (j : Fin (n + 1)) (hjk : j.castSucc < i.succ) :
    h n j ≫ Y.σ i.succ = X.σ i ≫ h (n + 1) j.castSucc

namespace SimplicialHomotopy

variable {X Y : SimplicialObject C} {f g : X ⟶ Y}

/-- Two simplicial homotopies are equal if all their underlying maps are equal. -/
@[ext]
lemma ext {H₁ H₂ : SimplicialHomotopy f g}
    (h_eq : ∀ n i, H₁.h n i = H₂.h n i) :
    H₁ = H₂ := by
  cases H₁
  cases H₂
  congr
  ext n i
  exact h_eq n i

/-- Endpoint equation: `d₀ h₀ = f`, i.e. `h n 0 ≫ d₀ = fₙ`. -/
@[simp, reassoc]
lemma h_comp_δ_zero (H : SimplicialHomotopy f g) (n : ℕ) :
    H.h n 0 ≫ Y.δ 0 = f.app (op ⦋n⦌) :=
  H.d0_h0 n

/-- Endpoint equation: `d_{n+1} hₙ = g`, i.e. `h n last ≫ d_last = gₙ`. -/
@[simp, reassoc]
lemma h_comp_δ_last (H : SimplicialHomotopy f g) (n : ℕ) :
    H.h n (Fin.last n) ≫ Y.δ (Fin.last (n+1)) = g.app (op ⦋n⦌) :=
  H.dLast_hLast n

/-- Face equation: `dᵢ ≫ hⱼ = h_{j+1} ≫ dᵢ` for `i < j+1`. -/
@[reassoc (attr := simp)]
lemma δ_comp_h_of_lt (H : SimplicialHomotopy f g) {n : ℕ} {i : Fin (n + 2)} {j : Fin (n + 1)}
    (hij : i < j.succ) :
    X.δ i ≫ H.h n j = H.h (n + 1) j.succ ≫ Y.δ i.castSucc :=
  (H.face_lt n i j hij).symm

/-- Face equation: `dᵢ ≫ hⱼ = hⱼ ≫ d_{i+1}` whenever `j < i`. -/
@[reassoc (attr := simp)]
lemma δ_comp_h_of_gt (H : SimplicialHomotopy f g) {n : ℕ} {i : Fin (n + 2)} {j : Fin (n + 1)}
    (hij : j.castSucc < i) :
    X.δ i ≫ H.h n j = H.h (n + 1) j.castSucc ≫ Y.δ i.succ :=
  (H.face_gt n i j hij).symm

/-- Degeneracy equation: `hⱼ ≫ sᵢ = sᵢ ≫ h_{j+1}` for `i ≤ j`. -/
@[reassoc (attr := simp)]
lemma h_comp_σ_of_le (H : SimplicialHomotopy f g) {n : ℕ} {i : Fin (n + 1)} {j : Fin (n + 1)}
    (hij : i ≤ j) :
    H.h n j ≫ Y.σ i.castSucc = X.σ i ≫ H.h (n + 1) j.succ :=
  H.deg_le n i j hij

/-- Degeneracy equation: `hⱼ ≫ s_{i+1} = sᵢ ≫ hⱼ` for `j ≤ i`). -/
@[reassoc (attr := simp)]
lemma h_comp_σ_of_gt (H : SimplicialHomotopy f g) {n : ℕ} {i : Fin (n + 1)} {j : Fin (n + 1)}
    (hij : j.castSucc < i.succ) :
    H.h n j ≫ Y.σ i.succ = X.σ i ≫ H.h (n + 1) j.castSucc :=
  H.deg_gt n i j hij

/-- The constant homotopy from `f` to `f`. -/
@[simps]
def refl (f : X ⟶ Y) : SimplicialHomotopy f f where
  h n i := X.σ i ≫ f.app (op ⦋n+1⦌)
  d0_h0 n := by
    dsimp only [SimplicialObject.δ, SimplicialObject.σ]
    rw [Category.assoc, ← f.naturality, ← Category.assoc]
    rw [← X.map_comp, ← op_comp]
    rw [← Fin.castSucc_zero]
    rw [SimplexCategory.δ_comp_σ_self]
    rw [op_id, X.map_id, Category.id_comp]

  dLast_hLast n := by
    dsimp only [SimplicialObject.δ, SimplicialObject.σ]
    rw [Category.assoc, ← f.naturality, ← Category.assoc]
    rw [← X.map_comp, ← op_comp]
    rw [← Fin.succ_last, SimplexCategory.δ_comp_σ_succ]
    rw [op_id, X.map_id, Category.id_comp]

  face_lt n i j hij := by
    dsimp only [SimplicialObject.δ, SimplicialObject.σ]
    rw [Category.assoc, ← f.naturality]
    repeat rw [← Category.assoc]
    rw [← X.map_comp, ← X.map_comp, ← op_comp, ← op_comp]
    rw [SimplexCategory.δ_comp_σ_of_le]
    rw [Fin.le_iff_val_le_val]
    exact Nat.le_of_lt_succ hij

  face_eq n j := by
    dsimp only [SimplicialObject.δ, SimplicialObject.σ]
    rw [Category.assoc, ← f.naturality, ← Category.assoc]
    rw [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_σ_self]
    rw [op_id, X.map_id, Category.id_comp]
    rw [Category.assoc, ← f.naturality, ← Category.assoc]
    rw [← X.map_comp, ← op_comp]
    rw [← Fin.succ_castSucc]
    rw [SimplexCategory.δ_comp_σ_succ]
    rw [op_id, X.map_id, Category.id_comp]

  face_gt n i j hij := by
    dsimp only [SimplicialObject.δ, SimplicialObject.σ]
    rw [Category.assoc, ← f.naturality]
    repeat rw [← Category.assoc]
    rw [← X.map_comp, ← X.map_comp, ← op_comp, ← op_comp]
    rw [SimplexCategory.δ_comp_σ_of_gt hij]

  deg_le n i j hij := by
    dsimp only [SimplicialObject.δ, SimplicialObject.σ]
    rw [Category.assoc, ← f.naturality, ← Category.assoc]
    rw [← X.map_comp, ← op_comp]
    rw [SimplexCategory.σ_comp_σ hij]
    rw [op_comp, X.map_comp, Category.assoc]

  deg_gt n i j hij := by
    dsimp only [SimplicialObject.δ, SimplicialObject.σ]
    rw [Category.assoc, ← f.naturality, ← Category.assoc]
    rw [← X.map_comp, ← op_comp]
    rw [← SimplexCategory.σ_comp_σ]
    · rw [op_comp, X.map_comp, Category.assoc]
    rw [Fin.le_iff_val_le_val]
    exact Nat.le_of_lt_succ hij

end SimplicialHomotopy

end CategoryTheory
