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

universe v u v' u'

noncomputable section

open SimplexCategory Simplicial Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- A simplicial homotopy between morphisms `f g : X ⟶ Y` of simplicial objects
consists of a family of morphisms `h n i : X _⦋n⦌ ⟶ Y _⦋n+1⦌` for `i : Fin (n + 1)`,
satisfying compatibility conditions with respect to face and degeneracy maps -/
@[ext]
structure SimplicialHomotopy
    {X Y : SimplicialObject C} (f g : X ⟶ Y) where
  /-- Basic data: `h i : Xₙ ⟶ Yₙ₊₁` for `i = 0..n`. -/
  h {n : ℕ} (i : Fin (n + 1)) : (X _⦋n⦌ ⟶ Y _⦋n+1⦌)
  /-- Endpoint `d₀ h₀ = g`. -/
  h_zero_comp_δ_zero (n : ℕ) : h 0 ≫ Y.δ 0 = g.app (op ⦋n⦌)
  /-- Endpoint `d_{n+1} hₙ = f`. -/
  h_last_comp_δ_last (n : ℕ) : h (Fin.last n) ≫ Y.δ (Fin.last (n + 1)) = f.app (op ⦋n⦌)
  /- nlab: `dᵢ hⱼ = h_{j'-1} dᵢ` if i < j', let j' = j + 1 -/
  /-- `dᵢ h_{j+1} = hⱼ dᵢ` if i < j + 1. -/
  h_succ_comp_δ_castSucc_of_lt {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) (hij : i ≤ j.castSucc) :
    h j.succ ≫ Y.δ i.castSucc = X.δ i ≫ h j
  /- nlab: `dᵢ hⱼ = dⱼ h_{j'-1}` if i = j' ≠ 0, let j' = j + 1 -/
  /-- `d_{j+1} h_{j+1} = d_{j+1} hⱼ` if i = j + 1 -/
  h_succ_comp_δ_castSucc_succ {n : ℕ} (j : Fin (n + 1)) :
    h j.succ ≫ Y.δ j.castSucc.succ = h j.castSucc ≫ Y.δ j.castSucc.succ
  /- nlab: `dᵢ hⱼ = hⱼ d_{i'-1}` if i' > j + 1, let i' = i + 1 -/
  /-- `d_{i+1} hⱼ = hⱼ dᵢ` if i > j -/
  h_castSucc_comp_δ_succ_of_lt {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) (hji : j.castSucc < i) :
    h j.castSucc ≫ Y.δ i.succ = X.δ i ≫ h j
  /-- `sᵢ hⱼ = h_{j+1} sᵢ` if i ≤ j. -/
  h_comp_σ_castSucc_of_le {n : ℕ} (i j : Fin (n + 1)) (hij : i ≤ j) :
    h j ≫ Y.σ i.castSucc = X.σ i ≫ h j.succ
  /- nlab: `sᵢ hⱼ = hⱼ s_{i'-1}` if i' > j, let i' = i + 1 -/
  /-- `s_{i+1} hⱼ = hⱼ sᵢ` if i + 1 > j -/
  h_comp_σ_succ_of_lt {n : ℕ} (i j : Fin (n + 1)) (hji : j ≤ i) :
    h j ≫ Y.σ i.succ = X.σ i ≫ h j.castSucc

namespace SimplicialHomotopy

variable {X Y : SimplicialObject C} {f g : X ⟶ Y}

attribute [reassoc (attr := simp)]
  h_zero_comp_δ_zero h_last_comp_δ_last h_succ_comp_δ_castSucc_of_lt h_succ_comp_δ_castSucc_succ
  h_castSucc_comp_δ_succ_of_lt h_comp_σ_castSucc_of_le h_comp_σ_succ_of_lt

/-- The constant homotopy from `f` to `f`. -/
@[simps]
def refl (f : X ⟶ Y) : SimplicialHomotopy f f where
  h i := X.σ i ≫ f.app _
  h_zero_comp_δ_zero n := by
    have := Y.δ_comp_σ_self (n := n) (i := 0)
    dsimp at this
    simp only [SimplicialObject.σ_naturality, Category.assoc, this, Category.comp_id]
  h_last_comp_δ_last n := by
    have := Y.δ_comp_σ_succ (i := Fin.last n)
    dsimp at this
    simp only [SimplicialObject.σ_naturality, Category.assoc, this, Category.comp_id]
  h_succ_comp_δ_castSucc_of_lt i j hij := by simp [Y.δ_comp_σ_of_le hij]
  h_succ_comp_δ_castSucc_succ j := by
    have h₁ := Y.δ_comp_σ_self (i := j.succ)
    have h₂ := Y.δ_comp_σ_succ (i := j.castSucc)
    dsimp at h₁ h₂
    simp only [SimplicialObject.σ_naturality, Category.assoc, h₁, Category.comp_id, h₂]
  h_castSucc_comp_δ_succ_of_lt i j hji := by simp [Y.δ_comp_σ_of_gt hji]
  h_comp_σ_castSucc_of_le i j hij := by simp [Y.σ_comp_σ hij]
  h_comp_σ_succ_of_lt i j hji := by simp [Y.σ_comp_σ hji]


variable {D : Type u'} [Category.{v'} D]
variable (F : C ⥤ D)

/-- Postcompose a simplicial homotopy with a functor `F : C ⥤ D`. -/
@[simps]
def whiskerRight (H : SimplicialHomotopy f g) :
    SimplicialHomotopy
      (((SimplicialObject.whiskering C D).obj F).map f)
      (((SimplicialObject.whiskering C D).obj F).map g) where
  h i := F.map (H.h i)
  h_zero_comp_δ_zero n := by
    simpa [SimplicialObject.δ] using
      congrArg (fun k => F.map k) (H.h_zero_comp_δ_zero n)
  h_last_comp_δ_last n := by
    simpa [SimplicialObject.δ] using
      congrArg (fun k => F.map k) (H.h_last_comp_δ_last n)
  h_succ_comp_δ_castSucc_of_lt i j hij := by
    simpa [SimplicialObject.δ] using
      congrArg (fun k => F.map k) (H.h_succ_comp_δ_castSucc_of_lt i j hij)
  h_succ_comp_δ_castSucc_succ j := by
    simpa [SimplicialObject.δ] using
      congrArg (fun k => F.map k) (H.h_succ_comp_δ_castSucc_succ j)
  h_castSucc_comp_δ_succ_of_lt i j hji := by
    simpa [SimplicialObject.δ] using
      congrArg (fun k => F.map k) (H.h_castSucc_comp_δ_succ_of_lt i j hji)
  h_comp_σ_castSucc_of_le i j hij := by
    simpa [SimplicialObject.σ] using
      congrArg (fun k => F.map k) (H.h_comp_σ_castSucc_of_le i j hij)
  h_comp_σ_succ_of_lt i j hji := by
    simpa [SimplicialObject.σ] using
      congrArg (fun k => F.map k) (H.h_comp_σ_succ_of_lt i j hji)

/-- Postcompose a simplicial homotopy with a morphism of simplicial objects. -/
@[simps]
def postcomp (H : SimplicialHomotopy f g) {Y' : SimplicialObject C} (p : Y ⟶ Y') :
    SimplicialHomotopy (f ≫ p) (g ≫ p) where
  h i := H.h i ≫ p.app _
  h_zero_comp_δ_zero n := by
    simpa [-h_zero_comp_δ_zero] using H.h_zero_comp_δ_zero n =≫ p.app _
  h_last_comp_δ_last n := by
    simpa [-h_last_comp_δ_last] using H.h_last_comp_δ_last n =≫ p.app _
  h_succ_comp_δ_castSucc_of_lt i j hij := by
    simpa using H.h_succ_comp_δ_castSucc_of_lt i j hij =≫ p.app _
  h_succ_comp_δ_castSucc_succ j := by
    simpa [-h_succ_comp_δ_castSucc_succ] using H.h_succ_comp_δ_castSucc_succ j =≫ p.app _
  h_castSucc_comp_δ_succ_of_lt i j hji := by
    simpa using H.h_castSucc_comp_δ_succ_of_lt i j hji =≫ p.app _
  h_comp_σ_castSucc_of_le i j hij := by
    simpa using H.h_comp_σ_castSucc_of_le i j hij =≫ p.app _
  h_comp_σ_succ_of_lt i j hji := by
    simpa using H.h_comp_σ_succ_of_lt i j hji =≫ p.app _

/-- Precompose a simplicial homotopy with a morphism of simplicial objects. -/
@[simps]
def precomp (H : SimplicialHomotopy f g) {X' : SimplicialObject C} (p : X' ⟶ X) :
    SimplicialHomotopy (p ≫ f) (p ≫ g) where
  h i := p.app _ ≫ H.h i
  h_zero_comp_δ_zero n := by
    simpa [-h_zero_comp_δ_zero] using p.app _ ≫= H.h_zero_comp_δ_zero n
  h_last_comp_δ_last n := by
    simpa [-h_last_comp_δ_last] using p.app _ ≫= H.h_last_comp_δ_last n
  h_succ_comp_δ_castSucc_of_lt i j hij := by
    simpa using p.app _ ≫= H.h_succ_comp_δ_castSucc_of_lt i j hij
  h_succ_comp_δ_castSucc_succ j := by
    simpa [-h_succ_comp_δ_castSucc_succ] using p.app _ ≫= H.h_succ_comp_δ_castSucc_succ j
  h_castSucc_comp_δ_succ_of_lt i j hji := by
    simpa using p.app _ ≫= H.h_castSucc_comp_δ_succ_of_lt i j hji
  h_comp_σ_castSucc_of_le i j hij := by
    simpa using p.app _ ≫= H.h_comp_σ_castSucc_of_le i j hij
  h_comp_σ_succ_of_lt i j hji := by
    simpa using p.app _ ≫= H.h_comp_σ_succ_of_lt i j hji

end SimplicialHomotopy

end CategoryTheory
