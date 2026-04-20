/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import Mathlib.AlgebraicTopology.SimplicialObject.Homotopy

/-!
# Extra-degeneracies for simplicial sets

-/

@[expose] public section

universe u

open CategoryTheory Simplicial Opposite

namespace SimplexCategory

lemma δ_apply {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) :
    dsimp% δ i j = Fin.succAbove i j := rfl

lemma σ_apply {n : ℕ} (i : Fin (n + 1)) (j : Fin (n + 2)) :
    dsimp% σ i j = Fin.predAbove i j := rfl

def δ₀Iter (i : ℕ) {n m : ℕ} (hi : n + i = m := by grind) :
    ⦋n⦌ ⟶ ⦋m⦌ :=
  Hom.mk
    { toFun j := ⟨j + i, by dsimp; grind [j.isLt]⟩
      monotone' _ _ := by grind }

@[simp]
lemma δ₀Iter_zero (n : ℕ) :
    δ₀Iter 0 (add_zero n) = 𝟙 _ := rfl

def σ₀Iter (i : ℕ) {n m : ℕ} (hi : n + i = m := by grind) :
    ⦋m⦌ ⟶ ⦋n⦌ :=
  Hom.mk
    { toFun j :=
        if j.val < i then 0 else ⟨j.val - i, by dsimp; grind⟩
      monotone' _ _ _ := by grind [Fin.zero_le] }

lemma σ₀Iter_coe_eq_of_lt (i : ℕ) {n m : ℕ}
    (j : Fin (m + 1)) (hi : n + i = m := by grind) (hj : j.val < i := by grind) :
    dsimp% (σ₀Iter i hi j).val = 0 := by
  simp [σ₀Iter, Hom.mk, ConcreteCategory.hom, Hom.toOrderHom,
    DFunLike.coe, if_pos hj]

lemma σ₀Iter_coe_eq_of_ge (i : ℕ) {n m : ℕ}
    (j : Fin (m + 1)) (hi : n + i = m := by grind) (hj : i ≤ j.val) :
    dsimp% (σ₀Iter i hi j).val = j.val - i := by
  dsimp [σ₀Iter, Hom.mk, ConcreteCategory.hom, Hom.toOrderHom, DFunLike.coe]
  rw [if_neg (by grind)]

@[simp]
lemma σ₀Iter_zero (n : ℕ) :
    σ₀Iter 0 (add_zero n) = 𝟙 _ := by
  dsimp [σ₀Iter]
  aesop

@[reassoc]
lemma δ_σ₀Iter {n : ℕ} (i : Fin (n + 2)) (j : ℕ) {m : ℕ}
    (i' : Fin (m + 2)) (h : m + j = n := by grind)
    (hi' : j < i.val := by grind)
    (hi'' : i.val = i'.val + j := by grind) :
    δ i ≫ σ₀Iter (n := m + 1) j = σ₀Iter j ≫ δ i' := by
  subst h
  refine ConcreteCategory.hom_ext _ _ (fun k ↦ ?_)
  ext
  dsimp
  rw [dsimp% ConcreteCategory.comp_apply (δ i) (σ₀Iter j),
    dsimp% ConcreteCategory.comp_apply (σ₀Iter j) (δ i'),
    SimplexCategory.δ_apply, SimplexCategory.δ_apply]
  by_cases! hk₁ : Fin.castSucc k < i
  · rw [Fin.succAbove_of_castSucc_lt _ _ (by exact hk₁)]
    by_cases! hk₂ : k.val < j
    · rw [σ₀Iter_coe_eq_of_lt j _ _ (by simpa),
        Fin.succAbove_of_castSucc_lt _ _ ?_,
        Fin.val_castSucc, σ₀Iter_coe_eq_of_lt j _ _ (by simpa)]
      rw [Fin.lt_def, Fin.val_castSucc,
        σ₀Iter_coe_eq_of_lt _ _ (by grind)]
      grind
    · rw [σ₀Iter_coe_eq_of_ge j _ _ (by dsimp; grind),
        Fin.val_castSucc, Fin.succAbove_of_castSucc_lt _ _ ?_,
        Fin.val_castSucc,
        σ₀Iter_coe_eq_of_ge _ _ rfl hk₂]
      rw [Fin.lt_def, Fin.val_castSucc,
        σ₀Iter_coe_eq_of_ge _ _ _ (by grind)]
      grind [Fin.lt_def, Fin.val_castSucc]
  · rw [Fin.succAbove_of_le_castSucc _ _ hk₁]
    by_cases! hk₂ : k.val + 1 < j
    · rw [σ₀Iter_coe_eq_of_lt _ _ _ (by grind),
        Fin.succAbove_of_castSucc_lt _ _ ?_,
        Fin.val_castSucc,
        σ₀Iter_coe_eq_of_lt _ _ _ (by grind)]
      rw [Fin.lt_def, Fin.val_castSucc,
        σ₀Iter_coe_eq_of_lt _ _ _ (by grind)]
      grind
    · rw [σ₀Iter_coe_eq_of_ge _ _ _ (by grind), Fin.val_succ]
      obtain hk₂ | hk₂ := hk₂.eq_or_lt
      · rw [Fin.succAbove_of_castSucc_lt _ _ ?_, Fin.val_castSucc]
        · rw [σ₀Iter_coe_eq_of_lt _ _ _ (by grind), ← hk₂, tsub_self]
        · rw [Fin.lt_def, Fin.val_castSucc,
            σ₀Iter_coe_eq_of_lt _ _ _ (by grind)]
          grind
      · replace hk₂ : j ≤ k.val := by grind
        rw [Fin.succAbove_of_le_castSucc _ _ ?_, Fin.val_succ,
          σ₀Iter_coe_eq_of_ge _ _ _ (by grind)]
        · grind
        · rw [Fin.le_def, Fin.val_castSucc,
            σ₀Iter_coe_eq_of_ge _ _ _ (by grind)]
          grind

end SimplexCategory

namespace CategoryTheory.SimplicialObject

variable {C : Type*} [Category* C] (X : SimplicialObject C)

def δ₀Iter {n m : ℕ} (i : ℕ) (hi : n + i = m := by grind) :
    X _⦋m⦌ ⟶ X _⦋n⦌ :=
  X.map (SimplexCategory.δ₀Iter i hi).op

@[simp]
lemma δ₀Iter_zero (n : ℕ) :
    X.δ₀Iter 0 (add_zero n) = 𝟙 _ := by
  simp [δ₀Iter]

def σ₀Iter {n m : ℕ} (i : ℕ) (hi : n + i = m := by grind) :
    X _⦋n⦌ ⟶ X _⦋m⦌ :=
  X.map (SimplexCategory.σ₀Iter i hi).op

@[simp]
lemma σ₀Iter_zero (n : ℕ) :
    X.σ₀Iter 0 (add_zero n) = 𝟙 _ := by
  simp [σ₀Iter]

@[reassoc]
lemma σ₀Iter_δ {n : ℕ} (i : Fin (n + 2)) (j : ℕ) {m : ℕ}
    (i' : Fin (m + 2)) (h : m + j = n := by grind)
    (hi' : j < i.val := by grind)
    (hi'' : i.val = i'.val + j := by grind) :
    X.σ₀Iter (n := m + 1) j ≫ X.δ i = X.δ i' ≫ X.σ₀Iter j := by
  simp only [σ₀Iter, δ, ← Functor.map_comp, ← op_comp,
    SimplexCategory.δ_σ₀Iter i j i']

end CategoryTheory.SimplicialObject

namespace SSet.Augmented

variable {X : SSet.Augmented.{u}} (ed : X.ExtraDegeneracy)

namespace homotopyOfExtraDegeneracy'

-- Theorem 4.3 in *Contractible simplicial objects*, Barr, Kennison, Raphael

variable {n : ℕ}

def h {n : ℕ} (i : Fin (n + 1)) : X.left _⦋n⦌ ⟶ X.left _⦋n + 1⦌ :=
  X.left.δ₀Iter i.val ≫ ed.s i.rev.val ≫ X.left.σ₀Iter i.val

@[reassoc]
lemma h_eq (i : Fin (n + 1)) (j : ℕ) (hj : j = i.rev.val := by grind) :
    h ed i = X.left.δ₀Iter i.val ≫ ed.s j ≫ X.left.σ₀Iter i.val := by
  subst hj
  rfl

@[simp]
lemma h_zero : h ed (n := n) 0 = ed.s n := by
  simp [h]

end homotopyOfExtraDegeneracy'

--set_option backward.isDefEq.respectTransparency false in
open SimplicialObject.Augmented.ExtraDegeneracy in
open homotopyOfExtraDegeneracy' in
def homotopyOfExtraDegeneracy' :
    SimplicialObject.Homotopy (X.hom ≫ ed.section_) (𝟙 X.left) where
  h := h ed
  h_zero_comp_δ_zero n := by simp
  h_last_comp_δ_last n := by
    induction n with
    | zero => simp [ed.s₀_comp_δ₁]
    | succ n hn =>
      dsimp
      rw [h_eq_assoc _ _ 0, X.left.σ₀Iter_δ _ _ 1,
        ed.s₀_comp_δ₁_assoc]
      dsimp [SimplicialObject.Augmented.ExtraDegeneracy.section_]
      sorry
  h_succ_comp_δ_castSucc_of_lt {n} i j hij := by
    sorry
  h_castSucc_comp_δ_succ_of_lt {n} i j hij := by
    sorry
  h_succ_comp_δ_castSucc_succ {n} i := by
    sorry
  h_comp_σ_castSucc_of_le {n} i j hij := by
    sorry
  h_comp_σ_succ_of_lt {n} i j hij := by
    sorry

end SSet.Augmented
