/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic

/-!
# Iterations of `δ 0` and `σ 0`

This file introduces morphisms `δ₀Iter i` and `σ₀Iter i` in the simplex category:
they are obtained as the `i`th iteration of `δ 0` or `σ 0`.

-/

@[expose] public section

open CategoryTheory Simplicial

namespace SimplexCategory

/-- If `n + i = m`, this is the morphism `⦋n⦌ ⟶ ⦋m⦌` in the simplex category
which is obtained as the `i`th iteration of `δ 0`: it sends `j : Fin (n + 1)` to
`⟨j.val + i, _⟩`. This may also be described as the order embedding
`Fin.addNatOrderEmb i : Fin (n + 1) ↪o Fin (n + 1 + i)`
followed by the order isomorphism `Fin (n + 1 + i) ≃o Fin (m + 1)`. -/
def δ₀Iter (i : ℕ) {n m : ℕ} (hi : n + i = m := by lia) : ⦋n⦌ ⟶ ⦋m⦌ :=
  Hom.mk
    { toFun j := ⟨j.val + i, by lia ⟩
      monotone' _ _ := by grind }

lemma δ₀Iter_apply (i : ℕ) {n m : ℕ} (j : Fin (n + 1)) (hi : n + i = m := by lia) :
    dsimp% (δ₀Iter i hi j) = ⟨j.val + i, by lia⟩ := rfl

@[simp]
lemma δ₀Iter_zero (n : ℕ) :
    δ₀Iter 0 (add_zero n) = 𝟙 _ := rfl

@[simp]
lemma δ₀Iter_one (n : ℕ) :
    δ₀Iter 1 (n := n) rfl = δ 0 := rfl

@[reassoc]
lemma δ₀Iter_succ (i : ℕ) {n m : ℕ} (h : n + i = m := by lia) :
    δ₀Iter (i + 1) = δ₀Iter i h ≫ δ 0 := rfl

@[reassoc]
lemma δ₀Iter_succ' (i : ℕ) {n m : ℕ} (h : n + (i + 1) = m := by lia) :
    δ₀Iter (i + 1) h = δ 0 ≫ δ₀Iter i := by
  refine ConcreteCategory.hom_ext _ _ (fun k ↦ ?_)
  ext
  rw [dsimp% ConcreteCategory.comp_apply (δ 0) (δ₀Iter i), coe_δ,
    δ₀Iter_apply .., δ₀Iter_apply ..]
  dsimp
  lia

lemma δ₀Iter_δ (i : ℕ) {n m : ℕ} (j : Fin (m + 2))
    (hi : n + i = m := by lia) (hj : j.val ≤ i := by grind) :
    δ₀Iter i hi ≫ δ j = δ₀Iter (i + 1) := by
  refine ConcreteCategory.hom_ext _ _ (fun k ↦ ?_)
  ext
  rw [dsimp% ConcreteCategory.comp_apply (δ₀Iter i hi) (δ j), coe_δ,
    δ₀Iter_apply .., δ₀Iter_apply ..,
    Fin.succAbove_of_le_castSucc _ _ (by grind)]
  simp [add_assoc]

@[reassoc]
lemma δ₀Iter_δ' {n : ℕ} (i : Fin (n + 2)) (j : ℕ) {m : ℕ}
    (i' : Fin (m + 2)) (h : n + j = m := by lia)
    (hi'' : i'.val = i.val + j := by grind) :
    δ₀Iter j h ≫ δ i' = δ i ≫ δ₀Iter j := by
  induction j generalizing n m with
  | zero =>
    obtain rfl : n = m := by lia
    obtain rfl : i = i' := by lia
    simp
  | succ j hj =>
    rw [δ₀Iter_succ'_assoc .., δ₀Iter_succ' ..,
      ← reassoc_of% dsimp% δ_comp_δ (i := 0) (j := i) (by simp),
      ← hj _ i' _ (by grind)]

@[reassoc]
lemma δ₀Iter_σ (i : ℕ) {n m : ℕ} (j : Fin (m + 1))
    (hi : n + (i + 1) = m + 1 := by lia)
    (hj : j.val ≤ i := by grind) :
    δ₀Iter (i + 1) hi ≫ σ j = δ₀Iter i := by
  refine ConcreteCategory.hom_ext _ _ (fun k ↦ ?_)
  ext
  rw [dsimp% ConcreteCategory.comp_apply (δ₀Iter (i + 1)) (σ j),
    δ₀Iter_apply .., δ₀Iter_apply .., coe_σ,
    Fin.predAbove_of_castSucc_lt _ _ (by grind)]
  dsimp

@[reassoc]
lemma δ₀Iter_σ' (i : ℕ) {n m : ℕ} (j : Fin (m + 1))
    (j' : Fin (n + 1))
    (hi' : n + i = m := by lia)
    (hj' : j.val = j'.val + i := by grind) :
    δ₀Iter i ≫ σ j = σ j' ≫ δ₀Iter i hi' := by
  induction i generalizing n m with
  | zero =>
    obtain rfl : n = m := by lia
    obtain rfl : j = j' := by lia
    simp
  | succ i hi =>
    obtain _ | m := m
    · grind
    · obtain ⟨j, rfl⟩ := j.eq_succ_of_ne_zero
        (by rintro rfl; dsimp at hj'; lia)
      rw [δ₀Iter_succ_assoc .., δ₀Iter_succ ..,
        dsimp% δ_comp_σ_of_le (i := 0) (j := j) (by simp),
        reassoc_of% hi j j' (by lia) (by grind)]

/-- If `n + i = m`, this is the morphism `⦋m⦌ ⟶ ⦋n⦌` in the simplex category
which is obtained as the `i`th iteration of `σ 0`. -/
def σ₀Iter (i : ℕ) {n m : ℕ} (hi : n + i = m := by lia) : ⦋m⦌ ⟶ ⦋n⦌ :=
  Hom.mk
    { toFun j :=
        if j.val < i then 0 else ⟨j.val - i, by lia⟩
      monotone' _ _ _ := by grind [Fin.zero_le] }

lemma σ₀Iter_coe_eq_of_lt (i : ℕ) {n m : ℕ}
    (j : Fin (m + 1)) (hi : n + i = m := by lia) (hj : j.val < i := by grind) :
    dsimp% (σ₀Iter i hi j).val = 0 := by
  simp [σ₀Iter, Hom.mk, ConcreteCategory.hom, Hom.toOrderHom, if_pos hj]

lemma σ₀Iter_coe_eq_of_ge (i : ℕ) {n m : ℕ}
    (j : Fin (m + 1)) (hi : n + i = m := by lia) (hj : i ≤ j.val := by grind) :
    dsimp% (σ₀Iter i hi j).val = j.val - i := by
  dsimp [σ₀Iter, Hom.mk, ConcreteCategory.hom, Hom.toOrderHom, DFunLike.coe]
  rw [if_neg (by lia)]

lemma σ₀Iter_coe_eq_of_le (i : ℕ) {n m : ℕ}
    (j : Fin (m + 1)) (hi : n + i = m := by lia) (hj : j.val ≤ i := by grind) :
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
  · rw [σ₀Iter_coe_eq_of_lt _ _ _ (by simp), coe_σ,
      Fin.predAbove_of_le_castSucc _ _ (by simp)]
    dsimp
  · rw [σ₀Iter_coe_eq_of_ge .., coe_σ]
    simp

@[reassoc]
lemma σ₀Iter_succ (i : ℕ) {n m : ℕ} (h : n + (i + 1) = m) :
    σ₀Iter (i + 1) h = σ₀Iter i ≫ σ 0 := by
  refine ConcreteCategory.hom_ext _ _ (fun k ↦ ?_)
  ext
  rw [dsimp% ConcreteCategory.comp_apply (σ₀Iter i) (σ 0)]
  by_cases! hk : k.val ≤ i
  · rw [σ₀Iter_coe_eq_of_lt .., coe_σ]
    obtain hk | rfl := hk.lt_or_eq
    · rw [Fin.predAbove_of_le_castSucc _ _ ?_, Fin.coe_castPred,
        σ₀Iter_coe_eq_of_lt ..]
      grind [σ₀Iter_coe_eq_of_lt]
    · rw [Fin.predAbove_of_le_castSucc _ _ ?_, Fin.coe_castPred,
        σ₀Iter_coe_eq_of_ge .., tsub_self]
      grind [σ₀Iter_coe_eq_of_ge]
  · rw [σ₀Iter_coe_eq_of_ge .., coe_σ,
      Fin.predAbove_of_castSucc_lt _ _ ?_, Fin.val_pred,
      σ₀Iter_coe_eq_of_ge .., Nat.sub_add_eq]
    rw [Fin.lt_def, Fin.castSucc_zero, σ₀Iter_coe_eq_of_ge ..,
      Fin.coe_ofNat_eq_mod, Nat.zero_mod]
    lia

@[reassoc]
lemma σ₀Iter_succ' (i : ℕ) {n m : ℕ} (h : n + i = m := by lia) :
    σ₀Iter (i + 1) = σ 0 ≫ σ₀Iter i h := by
  induction i generalizing n m with
  | zero =>
    obtain rfl : n = m := by lia
    simp
  | succ i hi' =>
    rw [σ₀Iter_succ, hi' (by lia), σ₀Iter_succ, Category.assoc]

@[reassoc]
lemma δ_σ₀Iter {n : ℕ} (i : Fin (n + 2)) (j : ℕ) {m : ℕ} (h : m + (j + 1) = n + 1 := by lia)
    (hi' : i.val ≤ j + 1 := by grind) :
    δ i ≫ σ₀Iter (j + 1) h = σ₀Iter j := by
  refine ConcreteCategory.hom_ext _ _ (fun k ↦ ?_)
  ext
  dsimp
  rw [dsimp% ConcreteCategory.comp_apply (δ i) (σ₀Iter (j + 1))]
  by_cases! hk : j ≤ k.val
  · rw [σ₀Iter_coe_eq_of_ge j .., coe_δ]
    by_cases! hk' : i ≤ k.castSucc
    · rw [Fin.succAbove_of_le_castSucc _ _ hk', σ₀Iter_coe_eq_of_ge ..]
      simp
    · obtain rfl : j = k.val := by grind [dsimp% Fin.lt_def.1 hk']
      rw [Fin.succAbove_of_castSucc_lt _ _ (by lia),
        σ₀Iter_coe_eq_of_lt .., tsub_self]
  · rw [σ₀Iter_coe_eq_of_lt j .., coe_δ]
    by_cases! hk' : i ≤ k.castSucc
    · rw [Fin.succAbove_of_le_castSucc _ _ hk', σ₀Iter_coe_eq_of_lt ..]
    · rw [Fin.succAbove_of_castSucc_lt _ _ (by lia), σ₀Iter_coe_eq_of_lt ..]

@[reassoc]
lemma δ_σ₀Iter' {n : ℕ} (i : Fin (n + 2)) (j : ℕ) {m : ℕ}
    (i' : Fin (m + 2)) (h : m + j = n := by lia)
    (hi' : j < i.val := by grind)
    (hi'' : i.val = i'.val + j := by grind) :
    δ i ≫ σ₀Iter (n := m + 1) j = σ₀Iter j ≫ δ i' := by
  induction j generalizing n m with
  | zero =>
    obtain rfl : n = m := by lia
    obtain rfl : i = i' := by lia
    simp
  | succ j hj =>
    rw [σ₀Iter_succ _, σ₀Iter_succ_assoc _,
      reassoc_of% hj _ i'.succ (by lia) (by lia) (by grind),
      dsimp% δ_comp_σ_of_gt (i := i') (j := 0)
        (by rw [Fin.lt_def]; dsimp; lia)]

@[reassoc]
lemma σ_σ₀Iter (i : ℕ) {n m : ℕ} (j : Fin (m + 1)) (hi : n + i = m := by lia)
    (hj : j.val ≤ i := by grind) :
    σ j ≫ σ₀Iter i hi = σ₀Iter (i + 1) := by
  refine ConcreteCategory.hom_ext _ _ (fun k ↦ ?_)
  ext
  rw [dsimp% ConcreteCategory.comp_apply (σ j) (σ₀Iter i), coe_σ]
  by_cases! hk : i < k.val
  · rw [σ₀Iter_coe_eq_of_ge (i + 1) ..,
      Fin.predAbove_of_castSucc_lt _ _ (by grind),
      σ₀Iter_coe_eq_of_ge ..]
    grind
  · rw [σ₀Iter_coe_eq_of_lt (i + 1) ..]
    rw [σ₀Iter_coe_eq_of_le _ _ _ ?_]
    by_cases! hk' : k ≤ j.castSucc
    · rwa [Fin.predAbove_of_le_castSucc _ _ (by lia)]
    · grind [Fin.predAbove]

@[reassoc]
lemma σ_σ₀Iter' (i : ℕ) {n m : ℕ} (j : Fin (m + 1)) (j' : Fin (n + 1))
    (hi : n + i = m := by lia)
    (hj : j.val = j'.val + i := by grind) :
    σ j ≫ σ₀Iter i hi = σ₀Iter i ≫ σ j' := by
  induction i generalizing n m with
  | zero =>
    obtain rfl : n = m := by lia
    obtain rfl : j = j' := by lia
    simp
  | succ i hi' =>
    rw [σ₀Iter_succ, σ₀Iter_succ_assoc,
      reassoc_of% hi' _ j'.succ (by lia) (by grind),
      ← σ_comp_σ (by simp), Fin.castSucc_zero]

@[reassoc (attr := simp)]
lemma δ₀Iter_σ₀Iter (i : ℕ) {n m : ℕ} (hi : n + i = m := by lia) :
    δ₀Iter i hi ≫ σ₀Iter i hi = 𝟙 _ := by
  induction i generalizing n m with
  | zero =>
    obtain rfl : n = m := by lia
    simp
  | succ i hi' =>
    obtain rfl : m = (n + i) + 1 := by lia
    rw [δ₀Iter_succ_assoc .., σ₀Iter_succ',
      dsimp% reassoc_of% δ_comp_σ_self (n := n + i) (i := 0), hi']

instance (i : ℕ) {n m : ℕ} (hi : n + i = m) : Mono (δ₀Iter i hi) :=
  mono_of_mono_fac (δ₀Iter_σ₀Iter i hi)

instance (i : ℕ) {n m : ℕ} (hi : n + i = m) : Epi (σ₀Iter i hi) :=
  epi_of_epi_fac (δ₀Iter_σ₀Iter i hi)

end SimplexCategory
