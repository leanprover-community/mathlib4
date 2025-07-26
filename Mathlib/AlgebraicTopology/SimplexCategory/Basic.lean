/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kim Morrison, Adam Topaz, Joël Riou
-/
import Mathlib.AlgebraicTopology.SimplexCategory.Defs
import Mathlib.Data.Fintype.Sort
import Mathlib.Order.Category.NonemptyFinLinOrd
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-! # Basic properties of the simplex category

In `Mathlib/AlgebraicTopology/SimplexCategory/Defs.lean`, we define the simplex
category with objects `ℕ` and morphisms `n ⟶ m` the monotone maps from
`Fin (n + 1)` to `Fin (m + 1)`.

In this file, we define the generating maps for the simplex category, show that
this category is equivalent to `NonemptyFinLinOrd`, and establish basic
properties of its epimorphisms and monomorphisms.
-/

universe v

open Simplicial CategoryTheory Limits

namespace SimplexCategory

section Init

/-- The constant morphism from ⦋0⦌. -/
def const (x y : SimplexCategory) (i : Fin (y.len + 1)) : x ⟶ y :=
  Hom.mk <| ⟨fun _ => i, by tauto⟩

@[simp]
lemma const_eq_id : const ⦋0⦌ ⦋0⦌ 0 = 𝟙 _ := by aesop

@[simp]
lemma const_apply (x y : SimplexCategory) (i : Fin (y.len + 1)) (a : Fin (x.len + 1)) :
    (const x y i).toOrderHom a = i := rfl

@[simp]
theorem const_comp (x : SimplexCategory) {y z : SimplexCategory}
    (f : y ⟶ z) (i : Fin (y.len + 1)) :
    const x y i ≫ f = const x z (f.toOrderHom i) :=
  rfl

theorem const_fac_thru_zero (n m : SimplexCategory) (i : Fin (m.len + 1)) :
    const n m i = const n ⦋0⦌ 0 ≫ SimplexCategory.const ⦋0⦌ m i := by
  rw [const_comp]; rfl

theorem Hom.ext_zero_left {n : SimplexCategory} (f g : ⦋0⦌ ⟶ n)
    (h0 : f.toOrderHom 0 = g.toOrderHom 0 := by rfl) : f = g := by
  ext i; match i with | 0 => exact h0 ▸ rfl

theorem eq_const_of_zero {n : SimplexCategory} (f : ⦋0⦌ ⟶ n) :
    f = const _ n (f.toOrderHom 0) := by
  ext x; match x with | 0 => rfl

theorem exists_eq_const_of_zero {n : SimplexCategory} (f : ⦋0⦌ ⟶ n) :
    ∃ a, f = const _ n a := ⟨_, eq_const_of_zero _⟩

theorem eq_const_to_zero {n : SimplexCategory} (f : n ⟶ ⦋0⦌) :
    f = const n _ 0 := by
  ext : 3
  apply @Subsingleton.elim (Fin 1)

theorem Hom.ext_one_left {n : SimplexCategory} (f g : ⦋1⦌ ⟶ n)
    (h0 : f.toOrderHom 0 = g.toOrderHom 0 := by rfl)
    (h1 : f.toOrderHom 1 = g.toOrderHom 1 := by rfl) : f = g := by
  ext i
  match i with
  | 0 => exact h0 ▸ rfl
  | 1 => exact h1 ▸ rfl

theorem eq_of_one_to_one (f : ⦋1⦌ ⟶ ⦋1⦌) :
    (∃ a, f = const ⦋1⦌ _ a) ∨ f = 𝟙 _ := by
  match e0 : f.toOrderHom 0, e1 : f.toOrderHom 1 with
  | 0, 0 | 1, 1 =>
    refine .inl ⟨f.toOrderHom 0, ?_⟩
    ext i : 3
    match i with
    | 0 => rfl
    | 1 => exact e1.trans e0.symm
  | 0, 1 =>
    right
    ext i : 3
    match i with
    | 0 => exact e0
    | 1 => exact e1
  | 1, 0 =>
    have := f.toOrderHom.monotone (by decide : (0 : Fin 2) ≤ 1)
    rw [e0, e1] at this
    exact Not.elim (by decide) this

/-- Make a morphism `⦋n⦌ ⟶ ⦋m⦌` from a monotone map between fin's.
This is useful for constructing morphisms between `⦋n⦌` directly
without identifying `n` with `⦋n⦌.len`.
-/
@[simp]
def mkHom {n m : ℕ} (f : Fin (n + 1) →o Fin (m + 1)) : ⦋n⦌ ⟶ ⦋m⦌ :=
  SimplexCategory.Hom.mk f

/-- The morphism `⦋1⦌ ⟶ ⦋n⦌` that picks out a specified `h : i ≤ j` in `Fin (n+1)`. -/
def mkOfLe {n} (i j : Fin (n + 1)) (h : i ≤ j) : ⦋1⦌ ⟶ ⦋n⦌ :=
  SimplexCategory.mkHom {
    toFun := fun | 0 => i | 1 => j
    monotone' := fun
      | 0, 0, _ | 1, 1, _ => le_rfl
      | 0, 1, _ => h
  }

@[simp]
lemma mkOfLe_refl {n} (j : Fin (n + 1)) :
    mkOfLe j j (by omega) = ⦋1⦌.const ⦋n⦌ j := Hom.ext_one_left _ _

/-- The morphism `⦋1⦌ ⟶ ⦋n⦌` that picks out the "diagonal composite" edge -/
def diag (n : ℕ) : ⦋1⦌ ⟶ ⦋n⦌ :=
  mkOfLe 0 (Fin.ofNat (n + 1) n) (Fin.zero_le _)

/-- The morphism `⦋1⦌ ⟶ ⦋n⦌` that picks out the edge spanning the interval from `j` to `j + l`. -/
def intervalEdge {n} (j l : ℕ) (hjl : j + l ≤ n) : ⦋1⦌ ⟶ ⦋n⦌ :=
  mkOfLe ⟨j, (by omega)⟩ ⟨j + l, (by omega)⟩ (Nat.le_add_right j l)

/-- The morphism `⦋1⦌ ⟶ ⦋n⦌` that picks out the arrow `i ⟶ i+1` in `Fin (n+1)`. -/
def mkOfSucc {n} (i : Fin n) : ⦋1⦌ ⟶ ⦋n⦌ :=
  SimplexCategory.mkHom {
    toFun := fun | 0 => i.castSucc | 1 => i.succ
    monotone' := fun
      | 0, 0, _ | 1, 1, _ => le_rfl
      | 0, 1, _ => Fin.castSucc_le_succ i
  }

@[simp]
lemma mkOfSucc_homToOrderHom_zero {n} (i : Fin n) :
    DFunLike.coe (F := Fin 2 →o Fin (n + 1)) (Hom.toOrderHom (mkOfSucc i)) 0 = i.castSucc := rfl

@[simp]
lemma mkOfSucc_homToOrderHom_one {n} (i : Fin n) :
    DFunLike.coe (F := Fin 2 →o Fin (n + 1)) (Hom.toOrderHom (mkOfSucc i)) 1 = i.succ := rfl


/-- The morphism `⦋2⦌ ⟶ ⦋n⦌` that picks out a specified composite of morphisms in `Fin (n+1)`. -/
def mkOfLeComp {n} (i j k : Fin (n + 1)) (h₁ : i ≤ j) (h₂ : j ≤ k) :
    ⦋2⦌ ⟶ ⦋n⦌ :=
  SimplexCategory.mkHom {
    toFun := fun | 0 => i | 1 => j | 2 => k
    monotone' := fun
      | 0, 0, _ | 1, 1, _ | 2, 2, _  => le_rfl
      | 0, 1, _ => h₁
      | 1, 2, _ => h₂
      | 0, 2, _ => Fin.le_trans h₁ h₂
  }

/-- The "inert" morphism associated to a subinterval `j ≤ i ≤ j + l` of `Fin (n + 1)`. -/
def subinterval {n} (j l : ℕ) (hjl : j + l ≤ n) :
    ⦋l⦌ ⟶ ⦋n⦌ :=
  SimplexCategory.mkHom {
    toFun := fun i => ⟨i.1 + j, (by omega)⟩
    monotone' := fun i i' hii' => by simpa only [Fin.mk_le_mk, add_le_add_iff_right] using hii'
  }

lemma const_subinterval_eq {n} (j l : ℕ) (hjl : j + l ≤ n) (i : Fin (l + 1)) :
    ⦋0⦌.const ⦋l⦌ i ≫ subinterval j l hjl =
    ⦋0⦌.const ⦋n⦌ ⟨j + i.1, lt_add_of_lt_add_right (Nat.add_lt_add_left i.2 j) hjl⟩  := by
  rw [const_comp]
  congr
  ext
  dsimp [subinterval]
  rw [add_comm]

@[simp]
lemma mkOfSucc_subinterval_eq {n} (j l : ℕ) (hjl : j + l ≤ n) (i : Fin l) :
    mkOfSucc i ≫ subinterval j l hjl =
    mkOfSucc ⟨j + i.1, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.2 j) hjl⟩ := by
  unfold subinterval mkOfSucc
  ext i
  match i with
  | 0 =>
    simp only [len_mk, Nat.reduceAdd, mkHom, comp_toOrderHom, Hom.toOrderHom_mk,
      OrderHom.mk_comp_mk, Fin.isValue, OrderHom.coe_mk, Function.comp_apply, Fin.castSucc_mk,
      Fin.succ_mk]
    rw [add_comm]
    rfl
  | 1 =>
    simp only [len_mk, Nat.reduceAdd, mkHom, comp_toOrderHom, Hom.toOrderHom_mk,
      OrderHom.mk_comp_mk, Fin.isValue, OrderHom.coe_mk, Function.comp_apply, Fin.castSucc_mk,
      Fin.succ_mk]
    rw [← Nat.add_comm j _]
    rfl

@[simp]
lemma diag_subinterval_eq {n} (j l : ℕ) (hjl : j + l ≤ n) :
    diag l ≫ subinterval j l hjl = intervalEdge j l hjl := by
  unfold subinterval intervalEdge diag mkOfLe
  ext i
  match i with
  | 0 =>
    simp only [len_mk, Nat.reduceAdd, mkHom, comp_toOrderHom,
      Hom.toOrderHom_mk, OrderHom.mk_comp_mk, Fin.isValue, OrderHom.coe_mk, Function.comp_apply]
    rw [Nat.add_comm]
    rfl
  | 1 =>
    simp only [len_mk, Nat.reduceAdd, mkHom, comp_toOrderHom,
      Hom.toOrderHom_mk, OrderHom.mk_comp_mk, Fin.isValue, OrderHom.coe_mk, Function.comp_apply]
    rw [Nat.add_comm]
    simp only [Fin.isValue, Fin.ofNat_eq_cast, Fin.natCast_eq_last]
    rfl

instance (Δ : SimplexCategory) : Subsingleton (Δ ⟶ ⦋0⦌) where
  allEq f g := by ext : 3; apply Subsingleton.elim (α := Fin 1)

theorem hom_zero_zero (f : ⦋0⦌ ⟶ ⦋0⦌) : f = 𝟙 _ := by
  apply Subsingleton.elim

end Init

section Generators

/-!
## Generating maps for the simplex category

TODO: prove that the simplex category is equivalent to
one given by the following generators and relations.
-/

/-- The `i`-th face map from `⦋n⦌` to `⦋n+1⦌` -/
def δ {n} (i : Fin (n + 2)) : ⦋n⦌ ⟶ ⦋n + 1⦌ :=
  mkHom (Fin.succAboveOrderEmb i).toOrderHom

/-- The `i`-th degeneracy map from `⦋n+1⦌` to `⦋n⦌` -/
def σ {n} (i : Fin (n + 1)) : ⦋n + 1⦌ ⟶ ⦋n⦌ :=
  mkHom i.predAboveOrderHom

/-- The generic case of the first simplicial identity -/
theorem δ_comp_δ {n} {i j : Fin (n + 2)} (H : i ≤ j) :
    δ i ≫ δ j.succ = δ j ≫ δ i.castSucc := by
  ext k
  dsimp [δ, Fin.succAbove]
  rcases i with ⟨i, _⟩
  rcases j with ⟨j, _⟩
  rcases k with ⟨k, _⟩
  split_ifs <;> · simp at * <;> omega

theorem δ_comp_δ' {n} {i : Fin (n + 2)} {j : Fin (n + 3)} (H : i.castSucc < j) :
    δ i ≫ δ j =
      δ (j.pred fun (hj : j = 0) => by simp [hj, Fin.not_lt_zero] at H) ≫
        δ (Fin.castSucc i) := by
  rw [← δ_comp_δ]
  · rw [Fin.succ_pred]
  · simpa only [Fin.le_iff_val_le_val, ← Nat.lt_succ_iff, Nat.succ_eq_add_one, ← Fin.val_succ,
      j.succ_pred, Fin.lt_iff_val_lt_val] using H

theorem δ_comp_δ'' {n} {i : Fin (n + 3)} {j : Fin (n + 2)} (H : i ≤ Fin.castSucc j) :
    δ (i.castLT (Nat.lt_of_le_of_lt (Fin.le_iff_val_le_val.mp H) j.is_lt)) ≫ δ j.succ =
      δ j ≫ δ i := by
  rw [δ_comp_δ]
  · rfl
  · exact H

/-- The special case of the first simplicial identity -/
@[reassoc]
theorem δ_comp_δ_self {n} {i : Fin (n + 2)} : δ i ≫ δ i.castSucc = δ i ≫ δ i.succ :=
  (δ_comp_δ (le_refl i)).symm

@[reassoc]
theorem δ_comp_δ_self' {n} {i : Fin (n + 2)} {j : Fin (n + 3)} (H : j = i.castSucc) :
    δ i ≫ δ j = δ i ≫ δ i.succ := by
  subst H
  rw [δ_comp_δ_self]

/-- The second simplicial identity -/
@[reassoc]
theorem δ_comp_σ_of_le {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : i ≤ j.castSucc) :
    δ i.castSucc ≫ σ j.succ = σ j ≫ δ i := by
  ext k : 3
  dsimp [σ, δ]
  rcases le_or_gt i k with (hik | hik)
  · rw [Fin.succAbove_of_le_castSucc _ _ (Fin.castSucc_le_castSucc_iff.mpr hik),
    Fin.succ_predAbove_succ, Fin.succAbove_of_le_castSucc]
    rcases le_or_gt k (j.castSucc) with (hjk | hjk)
    · rwa [Fin.predAbove_of_le_castSucc _ _ hjk, Fin.castSucc_castPred]
    · rw [Fin.le_castSucc_iff, Fin.predAbove_of_castSucc_lt _ _ hjk, Fin.succ_pred]
      exact H.trans_lt hjk
  · rw [Fin.succAbove_of_castSucc_lt _ _ (Fin.castSucc_lt_castSucc_iff.mpr hik)]
    have hjk := H.trans_lt' hik
    rw [Fin.predAbove_of_le_castSucc _ _ (Fin.castSucc_le_castSucc_iff.mpr
      (hjk.trans (Fin.castSucc_lt_succ _)).le),
      Fin.predAbove_of_le_castSucc _ _ hjk.le, Fin.castPred_castSucc, Fin.succAbove_of_castSucc_lt,
      Fin.castSucc_castPred]
    rwa [Fin.castSucc_castPred]

/-- The first part of the third simplicial identity -/
@[reassoc]
theorem δ_comp_σ_self {n} {i : Fin (n + 1)} :
    δ (Fin.castSucc i) ≫ σ i = 𝟙 ⦋n⦌ := by
  rcases i with ⟨i, hi⟩
  ext ⟨j, hj⟩
  simp? at hj says simp only [len_mk] at hj
  dsimp [σ, δ, Fin.predAbove, Fin.succAbove]
  simp only [Fin.lt_iff_val_lt_val, Fin.dite_val, Fin.ite_val, Fin.coe_pred]
  split_ifs
  any_goals simp
  all_goals omega

@[reassoc]
theorem δ_comp_σ_self' {n} {j : Fin (n + 2)} {i : Fin (n + 1)} (H : j = i.castSucc) :
    δ j ≫ σ i = 𝟙 ⦋n⦌ := by
  subst H
  rw [δ_comp_σ_self]

/-- The second part of the third simplicial identity -/
@[reassoc]
theorem δ_comp_σ_succ {n} {i : Fin (n + 1)} : δ i.succ ≫ σ i = 𝟙 ⦋n⦌ := by
  ext j
  rcases i with ⟨i, _⟩
  rcases j with ⟨j, _⟩
  dsimp [δ, σ, Fin.succAbove, Fin.predAbove]
  split_ifs <;> simp <;> simp at * <;> omega

@[reassoc]
theorem δ_comp_σ_succ' {n} {j : Fin (n + 2)} {i : Fin (n + 1)} (H : j = i.succ) :
    δ j ≫ σ i = 𝟙 ⦋n⦌ := by
  subst H
  rw [δ_comp_σ_succ]

/-- The fourth simplicial identity -/
@[reassoc]
theorem δ_comp_σ_of_gt {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : j.castSucc < i) :
    δ i.succ ≫ σ j.castSucc = σ j ≫ δ i := by
  ext k : 3
  dsimp [δ, σ]
  rcases le_or_gt k i with (hik | hik)
  · rw [Fin.succAbove_of_castSucc_lt _ _ (Fin.castSucc_lt_succ_iff.mpr hik)]
    rcases le_or_gt k (j.castSucc) with (hjk | hjk)
    · rw [Fin.predAbove_of_le_castSucc _ _
      (Fin.castSucc_le_castSucc_iff.mpr hjk), Fin.castPred_castSucc,
      Fin.predAbove_of_le_castSucc _ _ hjk, Fin.succAbove_of_castSucc_lt, Fin.castSucc_castPred]
      rw [Fin.castSucc_castPred]
      exact hjk.trans_lt H
    · rw [Fin.predAbove_of_castSucc_lt _ _ (Fin.castSucc_lt_castSucc_iff.mpr hjk),
      Fin.predAbove_of_castSucc_lt _ _ hjk, Fin.succAbove_of_castSucc_lt,
      Fin.castSucc_pred_eq_pred_castSucc]
      rwa [Fin.castSucc_lt_iff_succ_le, Fin.succ_pred]
  · rw [Fin.succAbove_of_le_castSucc _ _ (Fin.succ_le_castSucc_iff.mpr hik)]
    have hjk := H.trans hik
    rw [Fin.predAbove_of_castSucc_lt _ _ hjk, Fin.predAbove_of_castSucc_lt _ _
      (Fin.castSucc_lt_succ_iff.mpr hjk.le),
    Fin.pred_succ, Fin.succAbove_of_le_castSucc, Fin.succ_pred]
    rwa [Fin.le_castSucc_pred_iff]

@[reassoc]
theorem δ_comp_σ_of_gt' {n} {i : Fin (n + 3)} {j : Fin (n + 2)} (H : j.succ < i) :
    δ i ≫ σ j = σ (j.castLT ((add_lt_add_iff_right 1).mp (lt_of_lt_of_le H i.is_le))) ≫
      δ (i.pred fun (hi : i = 0) => by simp only [Fin.not_lt_zero, hi] at H) := by
  rw [← δ_comp_σ_of_gt]
  · simp
  · rw [Fin.castSucc_castLT, ← Fin.succ_lt_succ_iff, Fin.succ_pred]
    exact H

/-- The fifth simplicial identity -/
@[reassoc]
theorem σ_comp_σ {n} {i j : Fin (n + 1)} (H : i ≤ j) :
    σ (Fin.castSucc i) ≫ σ j = σ j.succ ≫ σ i := by
  ext k : 3
  dsimp [σ]
  cases k using Fin.lastCases with
  | last => simp only [len_mk, Fin.predAbove_right_last]
  | cast k =>
    cases k using Fin.cases with
    | zero =>
      ext
      simp
    | succ k =>
      rcases le_or_gt i k with (h | h)
      · simp_rw [Fin.predAbove_of_castSucc_lt i.castSucc _ (Fin.castSucc_lt_castSucc_iff.mpr
        (Fin.castSucc_lt_succ_iff.mpr h)), ← Fin.succ_castSucc, Fin.pred_succ,
        Fin.succ_predAbove_succ]
        rw [Fin.predAbove_of_castSucc_lt i _ (Fin.castSucc_lt_succ_iff.mpr _), Fin.pred_succ]
        rcases le_or_gt k j with (hkj | hkj)
        · rwa [Fin.predAbove_of_le_castSucc _ _ (Fin.castSucc_le_castSucc_iff.mpr hkj),
          Fin.castPred_castSucc]
        · rw [Fin.predAbove_of_castSucc_lt _ _ (Fin.castSucc_lt_castSucc_iff.mpr hkj),
          Fin.le_pred_iff,
          Fin.succ_le_castSucc_iff]
          exact H.trans_lt hkj
      · simp_rw [Fin.predAbove_of_le_castSucc i.castSucc _ (Fin.castSucc_le_castSucc_iff.mpr
        (Fin.succ_le_castSucc_iff.mpr h)), Fin.castPred_castSucc, ← Fin.succ_castSucc,
        Fin.succ_predAbove_succ]
        rw [Fin.predAbove_of_le_castSucc _ k.castSucc
        (Fin.castSucc_le_castSucc_iff.mpr (h.le.trans H)),
        Fin.castPred_castSucc, Fin.predAbove_of_le_castSucc _ k.succ
        (Fin.succ_le_castSucc_iff.mpr (H.trans_lt' h)), Fin.predAbove_of_le_castSucc _ k.succ
        (Fin.succ_le_castSucc_iff.mpr h)]

/--
If `f : ⦋m⦌ ⟶ ⦋n+1⦌` is a morphism and `j` is not in the range of `f`,
then `factor_δ f j` is a morphism `⦋m⦌ ⟶ ⦋n⦌` such that
`factor_δ f j ≫ δ j = f` (as witnessed by `factor_δ_spec`).
-/
def factor_δ {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n + 1⦌) (j : Fin (n + 2)) : ⦋m⦌ ⟶ ⦋n⦌ :=
  f ≫ σ (Fin.predAbove 0 j)

open Fin in
lemma factor_δ_spec {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n + 1⦌) (j : Fin (n + 2))
    (hj : ∀ (k : Fin (m + 1)), f.toOrderHom k ≠ j) :
    factor_δ f j ≫ δ j = f := by
  ext k : 3
  specialize hj k
  dsimp [factor_δ, δ, σ]
  cases j using cases with
  | zero =>
    ext
    unfold predAbove
    simp only [castSucc_zero, lt_self_iff_false, ↓reduceDIte]
    split
    · simp
    · simp only [zero_succAbove, val_succ, coe_castPred]
      simp_all
  | succ j =>
    rw [predAbove_of_castSucc_lt 0 _ (by simp), pred_succ]
    rcases hj.lt_or_gt with (hj | hj)
    · rw [predAbove_of_le_castSucc j _]
      swap
      · exact (le_castSucc_iff.mpr hj)
      · rw [succAbove_of_castSucc_lt]
        swap
        · rwa [castSucc_lt_succ_iff, castPred_le_iff, le_castSucc_iff]
        rw [castSucc_castPred]
    · rw [predAbove_of_castSucc_lt]
      swap
      · exact (castSucc_lt_succ _).trans hj
      rw [succAbove_of_le_castSucc]
      swap
      · rwa [succ_le_castSucc_iff, lt_pred_iff]
      rw [succ_pred]

@[simp]
lemma δ_zero_mkOfSucc {n : ℕ} (i : Fin n) :
    δ 0 ≫ mkOfSucc i = SimplexCategory.const _ ⦋n⦌ i.succ := by
  ext x
  fin_cases x
  rfl

@[simp]
lemma δ_one_mkOfSucc {n : ℕ} (i : Fin n) :
    δ 1 ≫ mkOfSucc i = SimplexCategory.const _ ⦋n⦌ i.castSucc := by
  ext x
  fin_cases x
  aesop

/-- If `i + 1 < j`, `mkOfSucc i ≫ δ j` is the morphism `⦋1⦌ ⟶ ⦋n⦌` that
sends `0` and `1` to `i` and `i + 1`, respectively. -/
lemma mkOfSucc_δ_lt {n : ℕ} {i : Fin n} {j : Fin (n + 2)}
    (h : i.succ.castSucc < j) :
    mkOfSucc i ≫ δ j = mkOfSucc i.castSucc := by
  ext x
  fin_cases x
  · simp [δ, Fin.succAbove_of_castSucc_lt _ _ (Nat.lt_trans _ h)]
  · simp [δ, Fin.succAbove_of_castSucc_lt _ _ h]

/-- If `i + 1 > j`, `mkOfSucc i ≫ δ j` is the morphism `⦋1⦌ ⟶ ⦋n⦌` that
sends `0` and `1` to `i + 1` and `i + 2`, respectively. -/
lemma mkOfSucc_δ_gt {n : ℕ} {i : Fin n} {j : Fin (n + 2)}
    (h : j < i.succ.castSucc) :
    mkOfSucc i ≫ δ j = mkOfSucc i.succ := by
  ext x
  simp only [δ, len_mk, mkHom, comp_toOrderHom, Hom.toOrderHom_mk, OrderHom.comp_coe,
    OrderEmbedding.toOrderHom_coe, Function.comp_apply, Fin.succAboveOrderEmb_apply]
  fin_cases x <;> rw [Fin.succAbove_of_le_castSucc]
  · rfl
  · exact Nat.le_of_lt_succ h
  · rfl
  · exact Nat.le_of_lt h

/-- If `i + 1 = j`, `mkOfSucc i ≫ δ j` is the morphism `⦋1⦌ ⟶ ⦋n⦌` that
sends `0` and `1` to `i` and `i + 2`, respectively. -/
lemma mkOfSucc_δ_eq {n : ℕ} {i : Fin n} {j : Fin (n + 2)}
    (h : j = i.succ.castSucc) :
    mkOfSucc i ≫ δ j = intervalEdge i 2 (by omega) := by
  ext x
  fin_cases x
  · subst h
    simp only [δ, len_mk, Nat.reduceAdd, mkHom, comp_toOrderHom, Hom.toOrderHom_mk,
      Fin.zero_eta, OrderHom.comp_coe, OrderEmbedding.toOrderHom_coe, Function.comp_apply,
      mkOfSucc_homToOrderHom_zero, Fin.succAboveOrderEmb_apply,
      Fin.castSucc_succAbove_castSucc, Fin.succAbove_succ_self]
    rfl
  · simp only [δ, len_mk, Nat.reduceAdd, mkHom, comp_toOrderHom, Hom.toOrderHom_mk, Fin.mk_one,
      OrderHom.comp_coe, OrderEmbedding.toOrderHom_coe, Function.comp_apply,
      mkOfSucc_homToOrderHom_one, Fin.succAboveOrderEmb_apply]
    subst h
    rw [Fin.succAbove_castSucc_self]
    rfl

theorem eq_of_one_to_two (f : ⦋1⦌ ⟶ ⦋2⦌) :
    (∃ i, f = (δ (n := 1) i)) ∨ ∃ a, f = SimplexCategory.const _ _ a := by
  have : f.toOrderHom 0 ≤ f.toOrderHom 1 := f.toOrderHom.monotone (by decide : (0 : Fin 2) ≤ 1)
  match e0 : f.toOrderHom 0, e1 : f.toOrderHom 1 with
  | 1, 2 =>
    refine .inl ⟨0, ?_⟩
    ext i : 3
    match i with
    | 0 => exact e0
    | 1 => exact e1
  | 0, 2 =>
    refine .inl ⟨1, ?_⟩
    ext i : 3
    match i with
    | 0 => exact e0
    | 1 => exact e1
  | 0, 1 =>
    refine .inl ⟨2, ?_⟩
    ext i : 3
    match i with
    | 0 => exact e0
    | 1 => exact e1
  | 0, 0 | 1, 1 | 2, 2 =>
    refine .inr ⟨f.toOrderHom 0, ?_⟩
    ext i : 3
    match i with
    | 0 => rfl
    | 1 => exact e1.trans e0.symm
  | 1, 0 | 2, 0 | 2, 1 =>
    rw [e0, e1] at this
    exact Not.elim (by decide) this

theorem eq_of_one_to_two' (f : ⦋1⦌ ⟶ ⦋2⦌) :
    f = (δ (n := 1) 0) ∨ f = (δ (n := 1) 1) ∨ f = (δ (n := 1) 2) ∨
      ∃ a, f = SimplexCategory.const _ _ a :=
  match eq_of_one_to_two f with
  | .inl ⟨0, h⟩ => .inl h
  | .inl ⟨1, h⟩ => .inr (.inl h)
  | .inl ⟨2, h⟩ => .inr (.inr (.inl h))
  | .inr h => .inr (.inr (.inr h))

end Generators

section Skeleton

/-- The functor that exhibits `SimplexCategory` as skeleton
of `NonemptyFinLinOrd` -/
@[simps obj map]
def skeletalFunctor : SimplexCategory ⥤ NonemptyFinLinOrd where
  obj a := NonemptyFinLinOrd.of (Fin (a.len + 1))
  map f := NonemptyFinLinOrd.ofHom f.toOrderHom

theorem skeletalFunctor.coe_map {Δ₁ Δ₂ : SimplexCategory} (f : Δ₁ ⟶ Δ₂) :
    ↑(skeletalFunctor.map f).hom = f.toOrderHom :=
  rfl

theorem skeletal : Skeletal SimplexCategory := fun X Y ⟨I⟩ => by
  suffices Fintype.card (Fin (X.len + 1)) = Fintype.card (Fin (Y.len + 1)) by
    ext
    simpa
  apply Fintype.card_congr
  exact ((skeletalFunctor ⋙ forget NonemptyFinLinOrd).mapIso I).toEquiv

namespace SkeletalFunctor

instance : skeletalFunctor.Full where
  map_surjective f := ⟨SimplexCategory.Hom.mk f.hom, rfl⟩

instance : skeletalFunctor.Faithful where
  map_injective {_ _ f g} h := by
    ext : 3
    exact CategoryTheory.congr_fun h _

instance : skeletalFunctor.EssSurj where
  mem_essImage X :=
    ⟨mk (Fintype.card X - 1 : ℕ),
      ⟨by
        have aux : Fintype.card X = Fintype.card X - 1 + 1 :=
          (Nat.succ_pred_eq_of_pos <| Fintype.card_pos_iff.mpr ⟨⊥⟩).symm
        let f := monoEquivOfFin X aux
        have hf := (Finset.univ.orderEmbOfFin aux).strictMono
        refine
          { hom := LinOrd.ofHom ⟨f, hf.monotone⟩
            inv := LinOrd.ofHom ⟨f.symm, ?_⟩
            hom_inv_id := by ext; apply f.symm_apply_apply
            inv_hom_id := by ext; apply f.apply_symm_apply }
        intro i j h
        change f.symm i ≤ f.symm j
        rw [← hf.le_iff_le]
        change f (f.symm i) ≤ f (f.symm j)
        simpa only [OrderIso.apply_symm_apply]⟩⟩

noncomputable instance isEquivalence : skeletalFunctor.IsEquivalence where

end SkeletalFunctor

/-- The equivalence that exhibits `SimplexCategory` as skeleton
of `NonemptyFinLinOrd` -/
noncomputable def skeletalEquivalence : SimplexCategory ≌ NonemptyFinLinOrd :=
  Functor.asEquivalence skeletalFunctor

end Skeleton

/-- `SimplexCategory` is a skeleton of `NonemptyFinLinOrd`.
-/
lemma isSkeletonOf :
    IsSkeletonOf NonemptyFinLinOrd SimplexCategory skeletalFunctor where
  skel := skeletal
  eqv := SkeletalFunctor.isEquivalence

section Concrete

instance : ConcreteCategory SimplexCategory (fun i j => Fin (i.len + 1) →o Fin (j.len + 1)) where
  hom := Hom.toOrderHom
  ofHom f := Hom.mk f

instance (x : SimplexCategory) : Fintype (ToType x) :=
  inferInstanceAs (Fintype (Fin _))

instance (x : SimplexCategory) (n : ℕ) : OfNat (ToType x) n :=
  inferInstanceAs (OfNat (Fin _) n)

lemma toType_apply (x : SimplexCategory) : ToType x = Fin (x.len + 1) := rfl

end Concrete

section EpiMono

/-- A morphism in `SimplexCategory` is a monomorphism precisely when it is an injective function
-/
theorem mono_iff_injective {n m : SimplexCategory} {f : n ⟶ m} :
    Mono f ↔ Function.Injective f.toOrderHom := by
  rw [← Functor.mono_map_iff_mono skeletalEquivalence.functor]
  dsimp only [skeletalEquivalence, Functor.asEquivalence_functor]
  simp only [skeletalFunctor_obj, skeletalFunctor_map,
    NonemptyFinLinOrd.mono_iff_injective, NonemptyFinLinOrd.coe_of, ConcreteCategory.hom_ofHom]

/-- A morphism in `SimplexCategory` is an epimorphism if and only if it is a surjective function
-/
theorem epi_iff_surjective {n m : SimplexCategory} {f : n ⟶ m} :
    Epi f ↔ Function.Surjective f.toOrderHom := by
  rw [← Functor.epi_map_iff_epi skeletalEquivalence.functor]
  dsimp only [skeletalEquivalence, Functor.asEquivalence_functor]
  simp only [skeletalFunctor_obj, skeletalFunctor_map,
    NonemptyFinLinOrd.epi_iff_surjective, NonemptyFinLinOrd.coe_of, ConcreteCategory.hom_ofHom]

/-- A monomorphism in `SimplexCategory` must increase lengths -/
theorem len_le_of_mono {x y : SimplexCategory} {f : x ⟶ y} : Mono f → x.len ≤ y.len := by
  intro hyp_f_mono
  have f_inj : Function.Injective f.toOrderHom.toFun := mono_iff_injective.1 hyp_f_mono
  simpa using Fintype.card_le_of_injective f.toOrderHom.toFun f_inj

theorem le_of_mono {n m : ℕ} {f : ⦋n⦌ ⟶ ⦋m⦌} : CategoryTheory.Mono f → n ≤ m :=
  len_le_of_mono

/-- An epimorphism in `SimplexCategory` must decrease lengths -/
theorem len_le_of_epi {x y : SimplexCategory} {f : x ⟶ y} : Epi f → y.len ≤ x.len := by
  intro hyp_f_epi
  have f_surj : Function.Surjective f.toOrderHom.toFun := epi_iff_surjective.1 hyp_f_epi
  simpa using Fintype.card_le_of_surjective f.toOrderHom.toFun f_surj

theorem le_of_epi {n m : ℕ} {f : ⦋n⦌ ⟶ ⦋m⦌} : Epi f → m ≤ n := len_le_of_epi

instance {n : ℕ} {i : Fin (n + 2)} : Mono (δ i) := by
  rw [mono_iff_injective]
  exact Fin.succAbove_right_injective

instance {n : ℕ} {i : Fin (n + 1)} : Epi (σ i) := by
  rw [epi_iff_surjective]
  intro b
  simp only [σ, mkHom, Hom.toOrderHom_mk]
  by_cases h : b ≤ i
  · use b.castSucc
    -- This was not needed before https://github.com/leanprover/lean4/pull/2644
    dsimp
    rw [Fin.predAbove_of_le_castSucc i b.castSucc (by simpa only [Fin.coe_eq_castSucc] using h)]
    simp only [len_mk, Fin.castPred_castSucc]
  · use b.succ
    -- This was not needed before https://github.com/leanprover/lean4/pull/2644
    dsimp
    rw [Fin.predAbove_of_castSucc_lt i b.succ _, Fin.pred_succ]
    rw [not_le] at h
    rw [Fin.lt_iff_val_lt_val] at h ⊢
    simpa only [Fin.val_succ, Fin.coe_castSucc] using Nat.lt.step h

instance : (forget SimplexCategory).ReflectsIsomorphisms :=
  ⟨fun f hf =>
    Iso.isIso_hom
      { hom := f
        inv := Hom.mk
            { toFun := inv ((forget SimplexCategory).map f)
              monotone' := fun y₁ y₂ h => by
                by_cases h' : y₁ < y₂
                · by_contra h''
                  apply not_le.mpr h'
                  convert f.toOrderHom.monotone (le_of_not_ge h'')
                  all_goals
                    exact (congr_hom (Iso.inv_hom_id
                      (asIso ((forget SimplexCategory).map f))) _).symm
                · rw [eq_of_le_of_not_lt h h'] }
        hom_inv_id := by
          ext1
          ext1
          exact Iso.hom_inv_id (asIso ((forget _).map f))
        inv_hom_id := by
          ext1
          ext1
          exact Iso.inv_hom_id (asIso ((forget _).map f)) }⟩

theorem isIso_of_bijective {x y : SimplexCategory} {f : x ⟶ y}
    (hf : Function.Bijective f.toOrderHom.toFun) : IsIso f :=
  haveI : IsIso ((forget SimplexCategory).map f) := (isIso_iff_bijective _).mpr hf
  isIso_of_reflects_iso f (forget SimplexCategory)

/-- An isomorphism in `SimplexCategory` induces an `OrderIso`. -/
@[simp]
def orderIsoOfIso {x y : SimplexCategory} (e : x ≅ y) : Fin (x.len + 1) ≃o Fin (y.len + 1) :=
  Equiv.toOrderIso
    { toFun := e.hom.toOrderHom
      invFun := e.inv.toOrderHom
      left_inv := fun i => by
        simpa only using congr_arg (fun φ => (Hom.toOrderHom φ) i) e.hom_inv_id
      right_inv := fun i => by
        simpa only using congr_arg (fun φ => (Hom.toOrderHom φ) i) e.inv_hom_id }
    e.hom.toOrderHom.monotone e.inv.toOrderHom.monotone

theorem iso_eq_iso_refl {x : SimplexCategory} (e : x ≅ x) : e = Iso.refl x := by
  have h : (Finset.univ : Finset (Fin (x.len + 1))).card = x.len + 1 := Finset.card_fin (x.len + 1)
  have eq₁ := Finset.orderEmbOfFin_unique' h fun i => Finset.mem_univ ((orderIsoOfIso e) i)
  have eq₂ :=
    Finset.orderEmbOfFin_unique' h fun i => Finset.mem_univ ((orderIsoOfIso (Iso.refl x)) i)
  ext : 2
  convert congr_arg (fun φ => (OrderEmbedding.toOrderHom φ)) (eq₁.trans eq₂.symm)
  ext i : 2
  rfl

theorem eq_id_of_isIso {x : SimplexCategory} (f : x ⟶ x) [IsIso f] : f = 𝟙 _ :=
  congr_arg (fun φ : _ ≅ _ => φ.hom) (iso_eq_iso_refl (asIso f))

theorem eq_σ_comp_of_not_injective' {n : ℕ} {Δ' : SimplexCategory} (θ : mk (n + 1) ⟶ Δ')
    (i : Fin (n + 1)) (hi : θ.toOrderHom (Fin.castSucc i) = θ.toOrderHom i.succ) :
    ∃ θ' : mk n ⟶ Δ', θ = σ i ≫ θ' := by
  use δ i.succ ≫ θ
  ext x : 3
  simp only [len_mk, σ, mkHom, comp_toOrderHom, Hom.toOrderHom_mk, OrderHom.comp_coe,
    Function.comp_apply, Fin.predAboveOrderHom_coe]
  by_cases h' : x ≤ Fin.castSucc i
  · rw [Fin.predAbove_of_le_castSucc i x h']
    dsimp [δ]
    rw [Fin.succAbove_of_castSucc_lt _ _ _]
    · rw [Fin.castSucc_castPred]
    · exact (Fin.castSucc_lt_succ_iff.mpr h')
  · simp only [not_le] at h'
    let y := x.pred <| by rintro (rfl : x = 0); simp at h'
    have hy : x = y.succ := (Fin.succ_pred x _).symm
    rw [hy] at h' ⊢
    rw [Fin.predAbove_of_castSucc_lt i y.succ h', Fin.pred_succ]
    by_cases h'' : y = i
    · rw [h'']
      refine hi.symm.trans ?_
      congr 1
      dsimp [δ]
      rw [Fin.succAbove_of_castSucc_lt i.succ]
      exact Fin.lt_succ
    · dsimp [δ]
      rw [Fin.succAbove_of_le_castSucc i.succ _]
      simp only [Fin.lt_iff_val_lt_val, Fin.le_iff_val_le_val, Fin.val_succ, Fin.coe_castSucc,
        Nat.lt_succ_iff, Fin.ext_iff] at h' h'' ⊢
      omega

theorem eq_σ_comp_of_not_injective {n : ℕ} {Δ' : SimplexCategory} (θ : mk (n + 1) ⟶ Δ')
    (hθ : ¬Function.Injective θ.toOrderHom) :
    ∃ (i : Fin (n + 1)) (θ' : mk n ⟶ Δ'), θ = σ i ≫ θ' := by
  simp only [Function.Injective, exists_prop, not_forall] at hθ
  -- as θ is not injective, there exists `x<y` such that `θ x = θ y`
  -- and then, `θ x = θ (x+1)`
  have hθ₂ : ∃ x y : Fin (n + 2), (Hom.toOrderHom θ) x = (Hom.toOrderHom θ) y ∧ x < y := by
    rcases hθ with ⟨x, y, ⟨h₁, h₂⟩⟩
    by_cases h : x < y
    · exact ⟨x, y, ⟨h₁, h⟩⟩
    · refine ⟨y, x, ⟨h₁.symm, ?_⟩⟩
      omega
  rcases hθ₂ with ⟨x, y, ⟨h₁, h₂⟩⟩
  use x.castPred ((Fin.le_last _).trans_lt' h₂).ne
  apply eq_σ_comp_of_not_injective'
  apply le_antisymm
  · exact θ.toOrderHom.monotone (le_of_lt (Fin.castSucc_lt_succ _))
  · rw [Fin.castSucc_castPred, h₁]
    exact θ.toOrderHom.monotone ((Fin.succ_castPred_le_iff _).mpr h₂)

theorem eq_comp_δ_of_not_surjective' {n : ℕ} {Δ : SimplexCategory} (θ : Δ ⟶ mk (n + 1))
    (i : Fin (n + 2)) (hi : ∀ x, θ.toOrderHom x ≠ i) : ∃ θ' : Δ ⟶ mk n, θ = θ' ≫ δ i := by
  use θ ≫ σ (.predAbove (.last n) i)
  ext x : 3
  suffices ∀ j ≠ i, i.succAbove (((Fin.last n).predAbove i).predAbove j) = j by
    dsimp [δ, σ]
    exact .symm <| this _ (hi _)
  intro j hj
  cases i using Fin.lastCases <;> simp [hj]

theorem eq_comp_δ_of_not_surjective {n : ℕ} {Δ : SimplexCategory} (θ : Δ ⟶ mk (n + 1))
    (hθ : ¬Function.Surjective θ.toOrderHom) :
    ∃ (i : Fin (n + 2)) (θ' : Δ ⟶ mk n), θ = θ' ≫ δ i := by
  obtain ⟨i, hi⟩ := not_forall.mp hθ
  use i
  exact eq_comp_δ_of_not_surjective' θ i (not_exists.mp hi)

theorem eq_id_of_mono {x : SimplexCategory} (i : x ⟶ x) [Mono i] : i = 𝟙 _ := by
  suffices IsIso i by
    apply eq_id_of_isIso
  apply isIso_of_bijective
  dsimp
  rw [Fintype.bijective_iff_injective_and_card i.toOrderHom, ← mono_iff_injective,
    eq_self_iff_true, and_true]
  infer_instance

theorem eq_id_of_epi {x : SimplexCategory} (i : x ⟶ x) [Epi i] : i = 𝟙 _ := by
  suffices IsIso i from eq_id_of_isIso _
  apply isIso_of_bijective
  dsimp
  rw [Fintype.bijective_iff_surjective_and_card i.toOrderHom, ← epi_iff_surjective,
    eq_self_iff_true, and_true]
  infer_instance

theorem eq_σ_of_epi {n : ℕ} (θ : mk (n + 1) ⟶ mk n) [Epi θ] : ∃ i : Fin (n + 1), θ = σ i := by
  rcases eq_σ_comp_of_not_injective θ (by
    by_contra h
    simpa using le_of_mono (mono_iff_injective.mpr h)) with ⟨i, θ', h⟩
  use i
  haveI : Epi (σ i ≫ θ') := by
    rw [← h]
    infer_instance
  haveI := CategoryTheory.epi_of_epi (σ i) θ'
  rw [h, eq_id_of_epi θ', Category.comp_id]

theorem eq_δ_of_mono {n : ℕ} (θ : mk n ⟶ mk (n + 1)) [Mono θ] : ∃ i : Fin (n + 2), θ = δ i := by
  rcases eq_comp_δ_of_not_surjective θ (by
    by_contra h
    simpa using le_of_epi (epi_iff_surjective.mpr h)) with ⟨i, θ', h⟩
  use i
  haveI : Mono (θ' ≫ δ i) := by
    rw [← h]
    infer_instance
  haveI := CategoryTheory.mono_of_mono θ' (δ i)
  rw [h, eq_id_of_mono θ', Category.id_comp]

theorem len_lt_of_mono {Δ' Δ : SimplexCategory} (i : Δ' ⟶ Δ) [hi : Mono i] (hi' : Δ ≠ Δ') :
    Δ'.len < Δ.len := by
  rcases lt_or_eq_of_le (len_le_of_mono hi) with (h | h)
  · exact h
  · exfalso
    exact hi' (by ext; exact h.symm)

noncomputable instance : SplitEpiCategory SimplexCategory :=
  skeletalEquivalence.inverse.splitEpiCategoryImpOfIsEquivalence

instance : HasStrongEpiMonoFactorisations SimplexCategory :=
  Functor.hasStrongEpiMonoFactorisations_imp_of_isEquivalence
    SimplexCategory.skeletalEquivalence.inverse

instance : HasStrongEpiImages SimplexCategory :=
  Limits.hasStrongEpiImages_of_hasStrongEpiMonoFactorisations

instance (Δ Δ' : SimplexCategory) (θ : Δ ⟶ Δ') : Epi (factorThruImage θ) :=
  StrongEpi.epi

theorem image_eq {Δ Δ' Δ'' : SimplexCategory} {φ : Δ ⟶ Δ''} {e : Δ ⟶ Δ'} [Epi e] {i : Δ' ⟶ Δ''}
    [Mono i] (fac : e ≫ i = φ) : image φ = Δ' := by
  haveI := strongEpi_of_epi e
  let e := image.isoStrongEpiMono e i fac
  ext
  exact
    le_antisymm (len_le_of_epi (inferInstance : Epi e.hom))
      (len_le_of_mono (inferInstance : Mono e.hom))

theorem image_ι_eq {Δ Δ'' : SimplexCategory} {φ : Δ ⟶ Δ''} {e : Δ ⟶ image φ} [Epi e]
    {i : image φ ⟶ Δ''} [Mono i] (fac : e ≫ i = φ) : image.ι φ = i := by
  haveI := strongEpi_of_epi e
  rw [← image.isoStrongEpiMono_hom_comp_ι e i fac,
    SimplexCategory.eq_id_of_isIso (image.isoStrongEpiMono e i fac).hom, Category.id_comp]

theorem factorThruImage_eq {Δ Δ'' : SimplexCategory} {φ : Δ ⟶ Δ''} {e : Δ ⟶ image φ} [Epi e]
    {i : image φ ⟶ Δ''} [Mono i] (fac : e ≫ i = φ) : factorThruImage φ = e := by
  rw [← cancel_mono i, fac, ← image_ι_eq fac, image.fac]

end EpiMono

/-- This functor `SimplexCategory ⥤ Cat` sends `⦋n⦌` (for `n : ℕ`)
to the category attached to the ordered set `{0, 1, ..., n}` -/
@[simps! obj map]
def toCat : SimplexCategory ⥤ Cat.{0} :=
  SimplexCategory.skeletalFunctor ⋙ forget₂ NonemptyFinLinOrd LinOrd ⋙
      forget₂ LinOrd Lat ⋙ forget₂ Lat PartOrd ⋙
      forget₂ PartOrd Preord ⋙ preordToCat

theorem toCat.obj_eq_Fin (n : ℕ) : toCat.obj ⦋n⦌ = Fin (n + 1) := rfl

instance uniqueHomToZero {Δ : SimplexCategory} : Unique (Δ ⟶ ⦋0⦌) where
  default := Δ.const _ 0
  uniq := eq_const_to_zero

/-- The object `⦋0⦌` is terminal in `SimplexCategory`. -/
def isTerminalZero : IsTerminal (⦋0⦌ : SimplexCategory) :=
  IsTerminal.ofUnique ⦋0⦌

instance : HasTerminal SimplexCategory :=
  IsTerminal.hasTerminal isTerminalZero

/-- The isomorphism between the terminal object in `SimplexCategory` and `⦋0⦌`. -/
noncomputable def topIsoZero : ⊤_ SimplexCategory ≅ ⦋0⦌ :=
  terminalIsoIsTerminal isTerminalZero

end SimplexCategory
