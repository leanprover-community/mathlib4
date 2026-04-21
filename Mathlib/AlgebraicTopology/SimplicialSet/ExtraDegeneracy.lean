/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import Mathlib.AlgebraicTopology.SimplicialObject.Homotopy

/-!
# Extra-degeneracies for simplicial sets^W^Wsimplicial objects

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
    { toFun j := ⟨j.val + i, by dsimp; grind [j.isLt]⟩
      monotone' _ _ := by grind }

@[simp]
lemma δ₀Iter_zero (n : ℕ) :
    δ₀Iter 0 (add_zero n) = 𝟙 _ := rfl

@[simp]
lemma δ₀Iter_one (n : ℕ) :
    δ₀Iter 1 (n := n) rfl = δ 0 := rfl

lemma δ₀Iter_apply (i : ℕ) {n m : ℕ} (hi : n + i = m := by grind) (j : Fin (n + 1)) :
    dsimp% (δ₀Iter i hi j) = ⟨j.val + i, by dsimp; grind [j.isLt]⟩ := rfl

@[reassoc]
lemma δ₀Iter_succ (i : ℕ) {n m : ℕ} (h : n + i = m := by grind) :
    δ₀Iter (i + 1) = δ₀Iter i h ≫ δ 0 := rfl

@[reassoc]
lemma δ₀Iter_succ' (i : ℕ) {n m : ℕ} (h : n + (i + 1) = m := by grind) :
    δ₀Iter (i + 1) h = δ 0 ≫ δ₀Iter i := by
  refine ConcreteCategory.hom_ext _ _ (fun k ↦ ?_)
  ext
  dsimp
  rw [dsimp% ConcreteCategory.comp_apply (δ 0) (δ₀Iter i), δ_apply,
    δ₀Iter_apply .., δ₀Iter_apply ..]
  dsimp
  grind

lemma δ₀Iter_δ (i : ℕ) {n m : ℕ} (j : Fin (m + 2))
    (hi : n + i = m := by grind) (hj : j.val ≤ i := by grind) :
    δ₀Iter i hi ≫ δ j = δ₀Iter (i + 1) := by
  refine ConcreteCategory.hom_ext _ _ (fun k ↦ ?_)
  ext
  dsimp
  rw [dsimp% ConcreteCategory.comp_apply (δ₀Iter i hi) (δ j), δ_apply,
    δ₀Iter_apply .., δ₀Iter_apply ..,
    Fin.succAbove_of_le_castSucc _ _ (by grind)]
  simp [add_assoc]

@[reassoc]
lemma δ₀Iter_δ' {n : ℕ} (i : Fin (n + 2)) (j : ℕ) {m : ℕ}
    (i' : Fin (m + 2)) (h : n + j = m := by grind)
    (hi'' : i'.val = i.val + j := by grind) :
    δ₀Iter j h ≫ δ i' = δ i ≫ δ₀Iter j := by
  induction j generalizing n m with
  | zero =>
    obtain rfl : n = m := by grind
    obtain rfl : i = i' := by grind
    simp
  | succ j hj =>
    obtain rfl : m = n + j + 1 := by grind
    rw [δ₀Iter_succ'_assoc .., δ₀Iter_succ' ..,
      ← reassoc_of% dsimp% δ_comp_δ (i := 0) (j := i) (by simp),
      ← hj _ i' _ (by grind)]

@[reassoc]
lemma δ₀Iter_σ (i : ℕ) {n m : ℕ} (j : Fin (m + 1))
    (hi : n + (i + 1) = m + 1 := by grind)
    (hj : j.val ≤ i := by grind) :
    δ₀Iter (i + 1) hi ≫ σ j = δ₀Iter i := by
  refine ConcreteCategory.hom_ext _ _ (fun k ↦ ?_)
  ext
  dsimp
  rw [dsimp% ConcreteCategory.comp_apply (δ₀Iter (i + 1)) (σ j),
    δ₀Iter_apply .., δ₀Iter_apply .., σ_apply,
    Fin.predAbove_of_castSucc_lt _ _ (by grind)]
  dsimp

@[reassoc]
lemma δ₀Iter_σ' (i : ℕ) {n m : ℕ} (j : Fin (m + 1))
    (j' : Fin (n + 1))
    (hi' : n + i = m := by grind)
    (hj' : j.val = j'.val + i := by grind) :
    δ₀Iter i ≫ σ j = σ j' ≫ δ₀Iter i hi' := by
  induction i generalizing n m with
  | zero =>
    obtain rfl : n = m := by grind
    obtain rfl : j = j' := by grind
    simp
  | succ i hi =>
    obtain _ | m := m
    · grind
    · obtain ⟨j, rfl⟩ := j.eq_succ_of_ne_zero (by grind)
      rw [δ₀Iter_succ_assoc .., δ₀Iter_succ ..,
        dsimp% δ_comp_σ_of_le (i := 0) (j := j) (by simp),
        reassoc_of% hi j j' (by grind) (by grind)]

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
    (j : Fin (m + 1)) (hi : n + i = m := by grind) (hj : i ≤ j.val := by grind) :
    dsimp% (σ₀Iter i hi j).val = j.val - i := by
  dsimp [σ₀Iter, Hom.mk, ConcreteCategory.hom, Hom.toOrderHom, DFunLike.coe]
  rw [if_neg (by grind)]

lemma σ₀Iter_coe_eq_of_le (i : ℕ) {n m : ℕ}
    (j : Fin (m + 1)) (hi : n + i = m := by grind) (hj : j.val ≤ i := by grind) :
    dsimp% (σ₀Iter i hi j).val = 0 := by
  obtain rfl | hj := hj.eq_or_lt
  · rw [σ₀Iter_coe_eq_of_ge .., tsub_self]
  · exact σ₀Iter_coe_eq_of_lt ..

@[simp]
lemma σ₀Iter_zero (n : ℕ) :
    σ₀Iter 0 (add_zero n) = 𝟙 _ := by
  dsimp [σ₀Iter]
  aesop

@[simp]
lemma σ₀Iter_one (n : ℕ) : σ₀Iter 1 (n := n) rfl = σ 0 := by
  refine ConcreteCategory.hom_ext _ _ (fun k ↦ ?_)
  ext
  dsimp
  obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_eq_succ
  · rw [σ₀Iter_coe_eq_of_lt .., σ_apply,
      Fin.predAbove_of_le_castSucc _ _ (by grind)]
    dsimp
  · rw [σ₀Iter_coe_eq_of_ge .., σ_apply]
    simp

@[reassoc]
lemma σ₀Iter_succ (i : ℕ) {n m : ℕ} (h : n + (i + 1) = m) :
    σ₀Iter (i + 1) h = σ₀Iter i ≫ σ 0 := by
  refine ConcreteCategory.hom_ext _ _ (fun k ↦ ?_)
  ext
  dsimp
  rw [dsimp% ConcreteCategory.comp_apply (σ₀Iter i) (σ 0)]
  by_cases! hk : k.val ≤ i
  · rw [σ₀Iter_coe_eq_of_lt .., σ_apply]
    obtain hk | rfl := hk.lt_or_eq
    · rw [Fin.predAbove_of_le_castSucc _ _ ?_, Fin.coe_castPred,
        σ₀Iter_coe_eq_of_lt ..]
      rw [Fin.le_def, σ₀Iter_coe_eq_of_lt ..]
      simp
    · rw [Fin.predAbove_of_le_castSucc _ _ ?_, Fin.coe_castPred,
        σ₀Iter_coe_eq_of_ge .., tsub_self]
      rw [Fin.le_def, σ₀Iter_coe_eq_of_ge ..]
      simp
  · dsimp
    rw [σ₀Iter_coe_eq_of_ge .., σ_apply,
      Fin.predAbove_of_castSucc_lt _ _ ?_, Fin.val_pred,
      σ₀Iter_coe_eq_of_ge .., Nat.sub_add_eq]
    rw [Fin.lt_def, Fin.castSucc_zero, σ₀Iter_coe_eq_of_ge ..]
    grind

@[reassoc]
lemma δ_σ₀Iter {n : ℕ} (i : Fin (n + 2)) (j : ℕ) {m : ℕ} (h : m + (j + 1) = n + 1 := by grind)
    (hi' : i.val ≤ j + 1 := by grind) :
    δ i ≫ σ₀Iter (j + 1) h = σ₀Iter j := by
  refine ConcreteCategory.hom_ext _ _ (fun k ↦ ?_)
  ext
  dsimp
  rw [dsimp% ConcreteCategory.comp_apply (δ i) (σ₀Iter (j + 1))]
  by_cases! hk : j ≤ k.val
  · rw [σ₀Iter_coe_eq_of_ge j .., δ_apply]
    by_cases! hk' : i ≤ k.castSucc
    · rw [Fin.succAbove_of_le_castSucc _ _ hk', σ₀Iter_coe_eq_of_ge ..]
      simp
    · obtain rfl : j = k.val := by grind [dsimp% Fin.lt_def.1 hk']
      rw [Fin.succAbove_of_castSucc_lt _ _ (by grind),
        σ₀Iter_coe_eq_of_lt .., tsub_self]
  · rw [σ₀Iter_coe_eq_of_lt j .., δ_apply]
    by_cases! hk' : i ≤ k.castSucc
    · rw [Fin.succAbove_of_le_castSucc _ _ hk', σ₀Iter_coe_eq_of_lt ..]
    · rw [Fin.succAbove_of_castSucc_lt _ _ (by grind), σ₀Iter_coe_eq_of_lt ..]

@[reassoc]
lemma δ_σ₀Iter' {n : ℕ} (i : Fin (n + 2)) (j : ℕ) {m : ℕ}
    (i' : Fin (m + 2)) (h : m + j = n := by grind)
    (hi' : j < i.val := by grind)
    (hi'' : i.val = i'.val + j := by grind) :
    δ i ≫ σ₀Iter (n := m + 1) j = σ₀Iter j ≫ δ i' := by
  induction j generalizing n m with
  | zero =>
    obtain rfl : n = m := by grind
    obtain rfl : i = i' := by grind
    simp
  | succ j hj =>
    obtain rfl : n = m + j + 1 := by grind
    rw [σ₀Iter_succ _, σ₀Iter_succ_assoc _,
      reassoc_of% hj _ i'.succ (by grind) (by grind) (by grind),
      dsimp% δ_comp_σ_of_gt (i := i') (j := 0) (by grind)]

@[reassoc]
lemma σ_σ₀Iter (i : ℕ) {n m : ℕ} (j : Fin (m + 1)) (hi : n + i = m := by grind)
    (hj : j.val ≤ i := by grind) :
    σ j ≫ σ₀Iter i hi = σ₀Iter (i + 1) := by
  refine ConcreteCategory.hom_ext _ _ (fun k ↦ ?_)
  ext
  dsimp
  rw [dsimp% ConcreteCategory.comp_apply (σ j) (σ₀Iter i), σ_apply]
  by_cases! hk : i < k.val
  · rw [σ₀Iter_coe_eq_of_ge (i + 1) ..,
      Fin.predAbove_of_castSucc_lt _ _ (by grind),
      σ₀Iter_coe_eq_of_ge ..]
    dsimp
    grind
  · rw [σ₀Iter_coe_eq_of_lt (i + 1) ..]
    rw [σ₀Iter_coe_eq_of_le _ _ _ ?_]
    by_cases! hk' : k ≤ j.castSucc
    · rwa [Fin.predAbove_of_le_castSucc _ _ (by grind)]
    · grind [Fin.predAbove]

@[reassoc]
lemma σ_σ₀Iter' (i : ℕ) {n m : ℕ} (j : Fin (m + 1)) (j' : Fin (n + 1))
    (hi : n + i = m := by grind)
    (hj : j.val = j'.val + i := by grind) :
    σ j ≫ σ₀Iter i hi = σ₀Iter i ≫ σ j' := by
  induction i generalizing n m with
  | zero =>
    obtain rfl : n = m := by grind
    obtain rfl : j = j' := by grind
    simp
  | succ i hi' =>
    rw [σ₀Iter_succ, σ₀Iter_succ_assoc,
      reassoc_of% hi' _ j'.succ (by grind) (by grind),
      ← σ_comp_σ (by simp), Fin.castSucc_zero]

--#exit
end SimplexCategory

namespace CategoryTheory.SimplicialObject

variable {C : Type*} [Category* C]

section

variable (X : SimplicialObject C)

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

end

namespace Augmented

variable (X : Augmented C)

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

end homotopyOfExtraDegeneracy'

open SimplicialObject.Augmented.ExtraDegeneracy in
open homotopyOfExtraDegeneracy' in
def homotopyOfExtraDegeneracy' :
    SimplicialObject.Homotopy (X.hom ≫ ed.section_) (𝟙 X.left) where
  h := h ed
  h_zero_comp_δ_zero n := by simp [h_eq_assoc ed (0 : Fin (n + 1)) n]
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

end Augmented

end CategoryTheory.SimplicialObject
