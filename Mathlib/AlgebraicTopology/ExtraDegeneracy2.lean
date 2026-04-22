/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import Mathlib.AlgebraicTopology.SimplicialObject.DeltaZeroIter
public import Mathlib.AlgebraicTopology.SimplicialObject.Homotopy

/-!
# Extra-degeneracies for simplicial objects

-/

@[expose] public section

namespace CategoryTheory.SimplicialObject.Augmented

open Simplicial Opposite

variable {C : Type*} [Category C] (X : Augmented C)

@[reassoc (attr := simp)]
lemma δ₀Iter_hom {n m : ℕ} (i : ℕ) (hi : n + i = m := by grind) :
    dsimp% X.left.δ₀Iter i hi ≫ X.hom.app (op ⦋n⦌) =
      X.hom.app (op ⦋m⦌) := by
  simpa using X.hom.naturality (SimplexCategory.δ₀Iter i hi).op

variable {X} (ed : X.ExtraDegeneracy)

namespace ExtraDegeneracy

@[reassoc (attr := simp)]
lemma s'_σ₀Iter (n : ℕ) :
    ed.s' ≫ X.left.σ₀Iter n = ed.section_.app (op ⦋n⦌) := by
  dsimp [section_, SimplicialObject.σ₀Iter]
  congr 3
  subsingleton

namespace homotopyOfExtraDegeneracy

-- Theorem 4.3 in *Contractible simplicial objects*, Barr, Kennison, Raphael

variable {n : ℕ}

def h {n : ℕ} (i : Fin (n + 1)) : X.left _⦋n⦌ ⟶ X.left _⦋n + 1⦌ :=
  X.left.δ₀Iter i.val ≫ ed.s i.rev.val ≫ X.left.σ₀Iter i.val

@[reassoc]
lemma h_eq (i : Fin (n + 1)) (j : ℕ) (hj : j = i.rev.val := by grind) :
    h ed i = X.left.δ₀Iter i.val ≫ ed.s j ≫ X.left.σ₀Iter i.val := by
  subst hj
  rfl

end homotopyOfExtraDegeneracy

open SimplicialObject.Augmented.ExtraDegeneracy in
open homotopyOfExtraDegeneracy in
def homotopyOfExtraDegeneracy :
    SimplicialObject.Homotopy (X.hom ≫ ed.section_) (𝟙 X.left) where
  h := h ed
  h_zero_comp_δ_zero n := by simp [h_eq_assoc ed (0 : Fin (n + 1)) n (by simp)]
  h_last_comp_δ_last n := by
    dsimp
    rw [h_eq_assoc _ _ 0, X.left.σ₀Iter_δ' _ _ 1,
      ed.s₀_comp_δ₁_assoc, X.δ₀Iter_hom_assoc ..]
    simp
  h_succ_comp_δ_castSucc_of_lt {n} i j hij := by
    generalize hk : j.succ.rev = k
    dsimp
    rw [h_eq_assoc _ _ k, h_eq _ _ k]
    dsimp
    rw [X.left.σ₀Iter_δ .., X.left.δ_δ₀Iter_assoc ..]
  h_castSucc_comp_δ_succ_of_lt {n} i j hij := by
    generalize hk : j.rev = k
    obtain ⟨l, hl⟩ : ∃ l, i.val = j + 1 + l := by
      rw [Fin.castSucc_lt_iff_succ_le, Fin.le_def] at hij
      obtain ⟨l, hl⟩ := Nat.le.dest hij
      exact ⟨l, by grind⟩
    have := ed.s_comp_δ k ⟨l + 1, by grind⟩
    dsimp at this ⊢
    rw [h_eq_assoc _ _ (k + 1), h_eq _ _ k,
      X.left.σ₀Iter_δ' _ _ ⟨l + 2, by grind⟩,
      reassoc_of% this, ← X.left.δ_δ₀Iter'_assoc _ _ i]
    dsimp
  h_succ_comp_δ_castSucc_succ {n} i := by
    generalize hk : i.succ.rev = k
    dsimp
    rw [h_eq_assoc _ _ k, h_eq_assoc _ _ (k + 1)]
    dsimp
    rw [X.left.δ₀Iter_succ'_assoc ..,
      X.left.σ₀Iter_δ' i.castSucc.succ i.val (m := k.val + 1)
        (i' := 1) (by grind) (by grind) (by simp; grind), dsimp% ed.s_comp_δ_assoc k.val 0,
      X.left.σ₀Iter_δ ..]
  h_comp_σ_castSucc_of_le {n} i j hij := by
    generalize hk : j.rev = k
    dsimp
    rw [h_eq_assoc _ _ k, h_eq _ _ k]
    dsimp
    rw [X.left.σ_δ₀Iter_assoc .., X.left.σ₀Iter_σ ..]
  h_comp_σ_succ_of_lt {n} i j hij := by
    generalize hk : j.rev = k
    obtain ⟨l, hl⟩ := Nat.le.dest (Fin.le_def.1 hij)
    dsimp
    rw [h_eq_assoc _ _ k, h_eq _ _ (k + 1),
      X.left.σ_δ₀Iter'_assoc _ _ ⟨l, by grind⟩
        (by grind) (by dsimp; grind),
      ← ed.s_comp_σ_assoc,
      X.left.σ₀Iter_σ' j i.succ ⟨l + 1, by grind⟩]
    dsimp

end ExtraDegeneracy

end CategoryTheory.SimplicialObject.Augmented
