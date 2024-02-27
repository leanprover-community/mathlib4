/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Scott Morrison, Adam Topaz
-/
import Mathlib.Tactic.Linarith
import Mathlib.CategoryTheory.Skeletal
import Mathlib.Data.Fintype.Sort
import Mathlib.Order.Category.NonemptyFinLinOrd
import Mathlib.CategoryTheory.Functor.ReflectsIso
import Mathlib.CategoryTheory.WithTerminal

#align_import algebraic_topology.simplex_category from "leanprover-community/mathlib"@"e8ac6315bcfcbaf2d19a046719c3b553206dac75"

/-! # The simplex category

We construct a skeletal model of the simplex category, with objects `ℕ` and the
morphism `n ⟶ m` being the monotone maps from `Fin (n+1)` to `Fin (m+1)`.

We show that this category is equivalent to `NonemptyFinLinOrd`.

## Remarks

The definitions `SimplexCategory` and `SimplexCategory.Hom` are marked as irreducible.

We provide the following functions to work with these objects:
1. `SimplexCategory.mk` creates an object of `SimplexCategory` out of a natural number.
  Use the notation `[n]` in the `Simplicial` locale.
2. `SimplexCategory.len` gives the "length" of an object of `SimplexCategory`, as a natural.
3. `SimplexCategory.Hom.mk` makes a morphism out of a monotone map between `Fin`'s.
4. `SimplexCategory.Hom.toOrderHom` gives the underlying monotone map associated to a
  term of `SimplexCategory.Hom`.

-/


universe v

open CategoryTheory CategoryTheory.Limits

/-- The simplex category:
* objects are natural numbers `n : ℕ`
* morphisms from `n` to `m` are monotone functions `Fin (n+1) → Fin (m+1)`
-/
def SimplexCategory :=
  ℕ
#align simplex_category SimplexCategory

namespace SimplexCategory

section


-- porting note: the definition of `SimplexCategory` is made irreducible below
/-- Interpret a natural number as an object of the simplex category. -/
def mk (n : ℕ) : SimplexCategory :=
  n
#align simplex_category.mk SimplexCategory.mk

/-- the `n`-dimensional simplex can be denoted `[n]` -/
scoped[Simplicial] notation "[" n "]" => SimplexCategory.mk n

-- TODO: Make `len` irreducible.
/-- The length of an object of `SimplexCategory`. -/
def len (n : SimplexCategory) : ℕ :=
  n
#align simplex_category.len SimplexCategory.len

@[ext]
theorem ext (a b : SimplexCategory) : a.len = b.len → a = b :=
  id
#align simplex_category.ext SimplexCategory.ext

attribute [irreducible] SimplexCategory

open Simplicial

@[simp]
theorem len_mk (n : ℕ) : [n].len = n :=
  rfl
#align simplex_category.len_mk SimplexCategory.len_mk

@[simp]
theorem mk_len (n : SimplexCategory) : ([n.len] : SimplexCategory) = n :=
  rfl
#align simplex_category.mk_len SimplexCategory.mk_len

/-- A recursor for `SimplexCategory`. Use it as `induction Δ using SimplexCategory.rec`. -/
protected def rec {F : SimplexCategory → Sort*} (h : ∀ n : ℕ, F [n]) : ∀ X, F X := fun n =>
  h n.len
#align simplex_category.rec SimplexCategory.rec

-- porting note: removed @[nolint has_nonempty_instance]
/-- Morphisms in the `SimplexCategory`. -/
protected def Hom (a b : SimplexCategory) :=
  Fin (a.len + 1) →o Fin (b.len + 1)
#align simplex_category.hom SimplexCategory.Hom

namespace Hom

/-- Make a morphism in `SimplexCategory` from a monotone map of `Fin`'s. -/
def mk {a b : SimplexCategory} (f : Fin (a.len + 1) →o Fin (b.len + 1)) : SimplexCategory.Hom a b :=
  f
#align simplex_category.hom.mk SimplexCategory.Hom.mk

/-- Recover the monotone map from a morphism in the simplex category. -/
def toOrderHom {a b : SimplexCategory} (f : SimplexCategory.Hom a b) :
    Fin (a.len + 1) →o Fin (b.len + 1) :=
  f
#align simplex_category.hom.to_order_hom SimplexCategory.Hom.toOrderHom

theorem ext' {a b : SimplexCategory} (f g : SimplexCategory.Hom a b) :
    f.toOrderHom = g.toOrderHom → f = g :=
  id
#align simplex_category.hom.ext SimplexCategory.Hom.ext'

attribute [irreducible] SimplexCategory.Hom

@[simp]
theorem mk_toOrderHom {a b : SimplexCategory} (f : SimplexCategory.Hom a b) : mk f.toOrderHom = f :=
  rfl
#align simplex_category.hom.mk_to_order_hom SimplexCategory.Hom.mk_toOrderHom

@[simp]
theorem toOrderHom_mk {a b : SimplexCategory} (f : Fin (a.len + 1) →o Fin (b.len + 1)) :
    (mk f).toOrderHom = f :=
  rfl
#align simplex_category.hom.to_order_hom_mk SimplexCategory.Hom.toOrderHom_mk

theorem mk_toOrderHom_apply {a b : SimplexCategory} (f : Fin (a.len + 1) →o Fin (b.len + 1))
    (i : Fin (a.len + 1)) : (mk f).toOrderHom i = f i :=
  rfl
#align simplex_category.hom.mk_to_order_hom_apply SimplexCategory.Hom.mk_toOrderHom_apply

/-- Identity morphisms of `SimplexCategory`. -/
@[simp]
def id (a : SimplexCategory) : SimplexCategory.Hom a a :=
  mk OrderHom.id
#align simplex_category.hom.id SimplexCategory.Hom.id

/-- Composition of morphisms of `SimplexCategory`. -/
@[simp]
def comp {a b c : SimplexCategory} (f : SimplexCategory.Hom b c) (g : SimplexCategory.Hom a b) :
    SimplexCategory.Hom a c :=
  mk <| f.toOrderHom.comp g.toOrderHom
#align simplex_category.hom.comp SimplexCategory.Hom.comp

end Hom

@[simps]
instance smallCategory : SmallCategory.{0} SimplexCategory where
  Hom n m := SimplexCategory.Hom n m
  id m := SimplexCategory.Hom.id _
  comp f g := SimplexCategory.Hom.comp g f
#align simplex_category.small_category SimplexCategory.smallCategory

-- porting note: added because `Hom.ext'` is not triggered automatically
@[ext]
theorem Hom.ext {a b : SimplexCategory} (f g : a ⟶ b) :
    f.toOrderHom = g.toOrderHom → f = g :=
  Hom.ext' _ _

/-- The constant morphism from [0]. -/
def const (x : SimplexCategory) (i : Fin (x.len + 1)) : ([0] : SimplexCategory) ⟶ x :=
  Hom.mk <| ⟨fun _ => i, by tauto⟩
#align simplex_category.const SimplexCategory.const

-- porting note: removed @[simp] as the linter complains
theorem const_comp (x y : SimplexCategory) (i : Fin (x.len + 1)) (f : x ⟶ y) :
    const x i ≫ f = const y (f.toOrderHom i) :=
  rfl
#align simplex_category.const_comp SimplexCategory.const_comp

/-- Make a morphism `[n] ⟶ [m]` from a monotone map between fin's.
This is useful for constructing morphisms between `[n]` directly
without identifying `n` with `[n].len`.
-/
@[simp]
def mkHom {n m : ℕ} (f : Fin (n + 1) →o Fin (m + 1)) : ([n] : SimplexCategory) ⟶ [m] :=
  SimplexCategory.Hom.mk f
#align simplex_category.mk_hom SimplexCategory.mkHom

theorem hom_zero_zero (f : ([0] : SimplexCategory) ⟶ [0]) : f = 𝟙 _ := by
  ext : 3
  apply @Subsingleton.elim (Fin 1)
#align simplex_category.hom_zero_zero SimplexCategory.hom_zero_zero

end

open Simplicial

section Generators

/-!
## Generating maps for the simplex category

TODO: prove that the simplex category is equivalent to
one given by the following generators and relations.
-/


/-- The `i`-th face map from `[n]` to `[n+1]` -/
def δ {n} (i : Fin (n + 2)) : ([n] : SimplexCategory) ⟶ [n + 1] :=
  mkHom (Fin.succAboveEmb i).toOrderHom
#align simplex_category.δ SimplexCategory.δ

/-- The `i`-th degeneracy map from `[n+1]` to `[n]` -/
def σ {n} (i : Fin (n + 1)) : ([n + 1] : SimplexCategory) ⟶ [n] :=
  mkHom
    { toFun := Fin.predAbove i
      monotone' := Fin.predAbove_right_monotone i }
#align simplex_category.σ SimplexCategory.σ

/-- The generic case of the first simplicial identity -/
theorem δ_comp_δ {n} {i j : Fin (n + 2)} (H : i ≤ j) :
    δ i ≫ δ j.succ = δ j ≫ δ (Fin.castSucc i) := by
  ext k
  dsimp [δ, Fin.succAbove]
  rcases i with ⟨i, _⟩
  rcases j with ⟨j, _⟩
  rcases k with ⟨k, _⟩
  split_ifs <;> · simp at * <;> linarith
#align simplex_category.δ_comp_δ SimplexCategory.δ_comp_δ

theorem δ_comp_δ' {n} {i : Fin (n + 2)} {j : Fin (n + 3)} (H : Fin.castSucc i < j) :
    δ i ≫ δ j =
      δ (j.pred fun (hj : j = 0) => by simp [hj, Fin.not_lt_zero] at H) ≫
        δ (Fin.castSucc i) := by
  rw [← δ_comp_δ]
  · rw [Fin.succ_pred]
  · simpa only [Fin.le_iff_val_le_val, ← Nat.lt_succ_iff, Nat.succ_eq_add_one, ← Fin.val_succ,
      j.succ_pred, Fin.lt_iff_val_lt_val] using H
#align simplex_category.δ_comp_δ' SimplexCategory.δ_comp_δ'

theorem δ_comp_δ'' {n} {i : Fin (n + 3)} {j : Fin (n + 2)} (H : i ≤ Fin.castSucc j) :
    δ (i.castLT (Nat.lt_of_le_of_lt (Fin.le_iff_val_le_val.mp H) j.is_lt)) ≫ δ j.succ =
      δ j ≫ δ i := by
  rw [δ_comp_δ]
  · rfl
  · exact H
#align simplex_category.δ_comp_δ'' SimplexCategory.δ_comp_δ''

/-- The special case of the first simplicial identity -/
@[reassoc]
theorem δ_comp_δ_self {n} {i : Fin (n + 2)} : δ i ≫ δ (Fin.castSucc i) = δ i ≫ δ i.succ :=
  (δ_comp_δ (le_refl i)).symm
#align simplex_category.δ_comp_δ_self SimplexCategory.δ_comp_δ_self

@[reassoc]
theorem δ_comp_δ_self' {n} {i : Fin (n + 2)} {j : Fin (n + 3)} (H : j = Fin.castSucc i) :
    δ i ≫ δ j = δ i ≫ δ i.succ := by
  subst H
  rw [δ_comp_δ_self]
#align simplex_category.δ_comp_δ_self' SimplexCategory.δ_comp_δ_self'

/-- The second simplicial identity -/
@[reassoc]
theorem δ_comp_σ_of_le {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : i ≤ Fin.castSucc j) :
    δ (Fin.castSucc i) ≫ σ j.succ = σ j ≫ δ i := by
  ext k : 3
  dsimp [σ, δ]
  rcases le_or_lt i k with (hik | hik)
  · rw [Fin.succAbove_of_le_castSucc _ _ (Fin.castSucc_le_castSucc_iff.mpr hik),
    Fin.succ_predAbove_succ, Fin.succAbove_of_le_castSucc]
    rcases le_or_lt k (j.castSucc) with (hjk | hjk)
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
#align simplex_category.δ_comp_σ_of_le SimplexCategory.δ_comp_σ_of_le

/-- The first part of the third simplicial identity -/
@[reassoc]
theorem δ_comp_σ_self {n} {i : Fin (n + 1)} :
    δ (Fin.castSucc i) ≫ σ i = 𝟙 ([n] : SimplexCategory) := by
  rcases i with ⟨i, hi⟩
  ext ⟨j, hj⟩
  simp? at hj says simp only [len_mk] at hj
  dsimp [σ, δ, Fin.predAbove, Fin.succAbove]
  simp only [Fin.lt_iff_val_lt_val, Fin.dite_val, Fin.ite_val, Fin.coe_pred, ge_iff_le,
    Fin.coe_castLT, dite_eq_ite]
  split_ifs
  any_goals simp
  all_goals linarith
#align simplex_category.δ_comp_σ_self SimplexCategory.δ_comp_σ_self

@[reassoc]
theorem δ_comp_σ_self' {n} {j : Fin (n + 2)} {i : Fin (n + 1)} (H : j = Fin.castSucc i) :
    δ j ≫ σ i = 𝟙 ([n] : SimplexCategory) := by
  subst H
  rw [δ_comp_σ_self]
#align simplex_category.δ_comp_σ_self' SimplexCategory.δ_comp_σ_self'

/-- The second part of the third simplicial identity -/
@[reassoc]
theorem δ_comp_σ_succ {n} {i : Fin (n + 1)} : δ i.succ ≫ σ i = 𝟙 ([n] : SimplexCategory) := by
  ext j
  rcases i with ⟨i, _⟩
  rcases j with ⟨j, _⟩
  dsimp [δ, σ, Fin.succAbove, Fin.predAbove]
  split_ifs <;> simp <;> simp at * <;> linarith
#align simplex_category.δ_comp_σ_succ SimplexCategory.δ_comp_σ_succ

@[reassoc]
theorem δ_comp_σ_succ' {n} (j : Fin (n + 2)) (i : Fin (n + 1)) (H : j = i.succ) :
    δ j ≫ σ i = 𝟙 ([n] : SimplexCategory) := by
  subst H
  rw [δ_comp_σ_succ]
#align simplex_category.δ_comp_σ_succ' SimplexCategory.δ_comp_σ_succ'

/-- The fourth simplicial identity -/
@[reassoc]
theorem δ_comp_σ_of_gt {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : Fin.castSucc j < i) :
    δ i.succ ≫ σ (Fin.castSucc j) = σ j ≫ δ i := by
  ext k : 3
  dsimp [δ, σ]
  rcases le_or_lt k i with (hik | hik)
  · rw [Fin.succAbove_of_castSucc_lt _ _ (Fin.castSucc_lt_succ_iff.mpr hik)]
    rcases le_or_lt k (j.castSucc) with (hjk | hjk)
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
#align simplex_category.δ_comp_σ_of_gt SimplexCategory.δ_comp_σ_of_gt

@[reassoc]
theorem δ_comp_σ_of_gt' {n} {i : Fin (n + 3)} {j : Fin (n + 2)} (H : j.succ < i) :
    δ i ≫ σ j = σ (j.castLT ((add_lt_add_iff_right 1).mp (lt_of_lt_of_le H i.is_le))) ≫
      δ (i.pred fun (hi : i = 0) => by simp only [Fin.not_lt_zero, hi] at H) := by
  rw [← δ_comp_σ_of_gt]
  · simp
  · rw [Fin.castSucc_castLT, ← Fin.succ_lt_succ_iff, Fin.succ_pred]
    exact H
#align simplex_category.δ_comp_σ_of_gt' SimplexCategory.δ_comp_σ_of_gt'

/-- The fifth simplicial identity -/
@[reassoc]
theorem σ_comp_σ {n} {i j : Fin (n + 1)} (H : i ≤ j) :
    σ (Fin.castSucc i) ≫ σ j = σ j.succ ≫ σ i := by
  ext k : 3
  dsimp [σ]
  cases' k using Fin.lastCases with k
  · simp only [len_mk, Fin.predAbove_right_last]
  · cases' k using Fin.cases with k
    · rw [Fin.castSucc_zero, Fin.predAbove_of_le_castSucc _ 0 (Fin.zero_le _),
      Fin.predAbove_of_le_castSucc _ _ (Fin.zero_le _), Fin.castPred_zero,
      Fin.predAbove_of_le_castSucc _ 0 (Fin.zero_le _),
      Fin.predAbove_of_le_castSucc _ _ (Fin.zero_le _)]
    · rcases le_or_lt i k with (h | h)
      · simp_rw [Fin.predAbove_of_castSucc_lt i.castSucc _ (Fin.castSucc_lt_castSucc_iff.mpr
        (Fin.castSucc_lt_succ_iff.mpr h)), ← Fin.succ_castSucc, Fin.pred_succ,
        Fin.succ_predAbove_succ]
        rw [Fin.predAbove_of_castSucc_lt i _ (Fin.castSucc_lt_succ_iff.mpr _), Fin.pred_succ]
        rcases le_or_lt k j with (hkj | hkj)
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
#align simplex_category.σ_comp_σ SimplexCategory.σ_comp_σ

/--
If `f : [m] ⟶ [n+1]` is a morphism and `j` is not in the range of `f`,
then `factor_δ f j` is a morphism `[m] ⟶ [n]` such that
`factor_δ f j ≫ δ j = f` (as witnessed by `factor_δ_spec`).
-/
def factor_δ {m n : ℕ} (f : ([m] : SimplexCategory) ⟶ [n+1]) (j : Fin (n+2)) :
    ([m] : SimplexCategory) ⟶ [n] :=
  f ≫ σ (Fin.predAbove 0 j)

open Fin in
lemma factor_δ_spec {m n : ℕ} (f : ([m] : SimplexCategory) ⟶ [n+1]) (j : Fin (n+2))
    (hj : ∀ (k : Fin (m+1)), f.toOrderHom k ≠ j) :
    factor_δ f j ≫ δ j = f := by
  ext k : 3
  specialize hj k
  dsimp [factor_δ, δ, σ]
  cases' j using cases with j
  · rw [predAbove_of_le_castSucc _ _ (zero_le _), castPred_zero, predAbove_of_castSucc_lt 0 _
    (castSucc_zero ▸ pos_of_ne_zero hj),
    zero_succAbove, succ_pred]
  · rw [predAbove_of_castSucc_lt 0 _ (castSucc_zero ▸ succ_pos _), pred_succ]
    rcases hj.lt_or_lt with (hj | hj)
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

end Generators

section Skeleton

/-- The functor that exhibits `SimplexCategory` as skeleton
of `NonemptyFinLinOrd` -/
@[simps obj map]
def skeletalFunctor : SimplexCategory ⥤ NonemptyFinLinOrd where
  obj a := NonemptyFinLinOrd.of (Fin (a.len + 1))
  map f := f.toOrderHom
#align simplex_category.skeletal_functor SimplexCategory.skeletalFunctor

theorem skeletalFunctor.coe_map {Δ₁ Δ₂ : SimplexCategory} (f : Δ₁ ⟶ Δ₂) :
    ↑(skeletalFunctor.map f) = f.toOrderHom :=
  rfl
#align simplex_category.skeletal_functor.coe_map SimplexCategory.skeletalFunctor.coe_map

theorem skeletal : Skeletal SimplexCategory := fun X Y ⟨I⟩ => by
  suffices Fintype.card (Fin (X.len + 1)) = Fintype.card (Fin (Y.len + 1)) by
    ext
    simpa
  apply Fintype.card_congr
  exact ((skeletalFunctor ⋙ forget NonemptyFinLinOrd).mapIso I).toEquiv
#align simplex_category.skeletal SimplexCategory.skeletal

namespace SkeletalFunctor

instance : Full skeletalFunctor where
  preimage f := SimplexCategory.Hom.mk f

instance : Faithful skeletalFunctor where
  map_injective {_ _ f g} h := by
    ext1
    exact h

instance : EssSurj skeletalFunctor where
  mem_essImage X :=
    ⟨mk (Fintype.card X - 1 : ℕ),
      ⟨by
        have aux : Fintype.card X = Fintype.card X - 1 + 1 :=
          (Nat.succ_pred_eq_of_pos <| Fintype.card_pos_iff.mpr ⟨⊥⟩).symm
        let f := monoEquivOfFin X aux
        have hf := (Finset.univ.orderEmbOfFin aux).strictMono
        refine'
          { hom := ⟨f, hf.monotone⟩
            inv := ⟨f.symm, _⟩
            hom_inv_id := by ext1; apply f.symm_apply_apply
            inv_hom_id := by ext1; apply f.apply_symm_apply }
        intro i j h
        show f.symm i ≤ f.symm j
        rw [← hf.le_iff_le]
        show f (f.symm i) ≤ f (f.symm j)
        simpa only [OrderIso.apply_symm_apply]⟩⟩

noncomputable instance isEquivalence : IsEquivalence skeletalFunctor :=
  Equivalence.ofFullyFaithfullyEssSurj skeletalFunctor
#align simplex_category.skeletal_functor.is_equivalence SimplexCategory.SkeletalFunctor.isEquivalence

end SkeletalFunctor

/-- The equivalence that exhibits `SimplexCategory` as skeleton
of `NonemptyFinLinOrd` -/
noncomputable def skeletalEquivalence : SimplexCategory ≌ NonemptyFinLinOrd :=
  Functor.asEquivalence skeletalFunctor
#align simplex_category.skeletal_equivalence SimplexCategory.skeletalEquivalence

end Skeleton

/-- `SimplexCategory` is a skeleton of `NonemptyFinLinOrd`.
-/
noncomputable def isSkeletonOf :
    IsSkeletonOf NonemptyFinLinOrd SimplexCategory skeletalFunctor where
  skel := skeletal
  eqv := SkeletalFunctor.isEquivalence
#align simplex_category.is_skeleton_of SimplexCategory.isSkeletonOf

/-- The truncated simplex category. -/
def Truncated (n : ℕ) :=
  FullSubcategory fun a : SimplexCategory => a.len ≤ n
#align simplex_category.truncated SimplexCategory.Truncated

instance (n : ℕ) : SmallCategory.{0} (Truncated n) :=
  FullSubcategory.category _

namespace Truncated

instance {n} : Inhabited (Truncated n) :=
  ⟨⟨[0], by simp⟩⟩

/-- The fully faithful inclusion of the truncated simplex category into the usual
simplex category.
-/
def inclusion {n : ℕ} : SimplexCategory.Truncated n ⥤ SimplexCategory :=
  fullSubcategoryInclusion _
#align simplex_category.truncated.inclusion SimplexCategory.Truncated.inclusion

instance (n : ℕ) : Full (inclusion : Truncated n ⥤ _) := FullSubcategory.full _
instance (n : ℕ) : Faithful (inclusion : Truncated n ⥤ _) := FullSubcategory.faithful _

end Truncated

section Concrete

instance : ConcreteCategory.{0} SimplexCategory where
  forget :=
    { obj := fun i => Fin (i.len + 1)
      map := fun f => f.toOrderHom }
  forget_faithful := ⟨fun h => by ext : 2; exact h⟩

end Concrete

section EpiMono

/-- A morphism in `SimplexCategory` is a monomorphism precisely when it is an injective function
-/
theorem mono_iff_injective {n m : SimplexCategory} {f : n ⟶ m} :
    Mono f ↔ Function.Injective f.toOrderHom := by
  rw [← Functor.mono_map_iff_mono skeletalEquivalence.functor]
  dsimp only [skeletalEquivalence, Functor.asEquivalence_functor]
  simp only [skeletalFunctor_obj, skeletalFunctor_map,
    NonemptyFinLinOrd.mono_iff_injective, NonemptyFinLinOrd.coe_of]
#align simplex_category.mono_iff_injective SimplexCategory.mono_iff_injective

/-- A morphism in `SimplexCategory` is an epimorphism if and only if it is a surjective function
-/
theorem epi_iff_surjective {n m : SimplexCategory} {f : n ⟶ m} :
    Epi f ↔ Function.Surjective f.toOrderHom := by
  rw [← Functor.epi_map_iff_epi skeletalEquivalence.functor]
  dsimp only [skeletalEquivalence, Functor.asEquivalence_functor]
  simp only [skeletalFunctor_obj, skeletalFunctor_map,
    NonemptyFinLinOrd.epi_iff_surjective, NonemptyFinLinOrd.coe_of]
#align simplex_category.epi_iff_surjective SimplexCategory.epi_iff_surjective

/-- A monomorphism in `SimplexCategory` must increase lengths-/
theorem len_le_of_mono {x y : SimplexCategory} {f : x ⟶ y} : Mono f → x.len ≤ y.len := by
  intro hyp_f_mono
  have f_inj : Function.Injective f.toOrderHom.toFun := mono_iff_injective.1 hyp_f_mono
  simpa using Fintype.card_le_of_injective f.toOrderHom.toFun f_inj
#align simplex_category.len_le_of_mono SimplexCategory.len_le_of_mono

theorem le_of_mono {n m : ℕ} {f : ([n] : SimplexCategory) ⟶ [m]} : CategoryTheory.Mono f → n ≤ m :=
  len_le_of_mono
#align simplex_category.le_of_mono SimplexCategory.le_of_mono

/-- An epimorphism in `SimplexCategory` must decrease lengths-/
theorem len_le_of_epi {x y : SimplexCategory} {f : x ⟶ y} : Epi f → y.len ≤ x.len := by
  intro hyp_f_epi
  have f_surj : Function.Surjective f.toOrderHom.toFun := epi_iff_surjective.1 hyp_f_epi
  simpa using Fintype.card_le_of_surjective f.toOrderHom.toFun f_surj
#align simplex_category.len_le_of_epi SimplexCategory.len_le_of_epi

theorem le_of_epi {n m : ℕ} {f : ([n] : SimplexCategory) ⟶ [m]} : Epi f → m ≤ n :=
  len_le_of_epi
#align simplex_category.le_of_epi SimplexCategory.le_of_epi

instance {n : ℕ} {i : Fin (n + 2)} : Mono (δ i) := by
  rw [mono_iff_injective]
  exact Fin.succAbove_right_injective

instance {n : ℕ} {i : Fin (n + 1)} : Epi (σ i) := by
  rw [epi_iff_surjective]
  intro b
  simp only [σ, mkHom, Hom.toOrderHom_mk, OrderHom.coe_mk]
  by_cases h : b ≤ i
  · use b
    -- This was not needed before leanprover/lean4#2644
    dsimp
    rw [Fin.predAbove_of_le_castSucc i b (by simpa only [Fin.coe_eq_castSucc] using h)]
    simp only [len_mk, Fin.coe_eq_castSucc, Fin.castPred_castSucc]
  · use b.succ
    -- This was not needed before leanprover/lean4#2644
    dsimp
    rw [Fin.predAbove_of_castSucc_lt i b.succ _, Fin.pred_succ]
    rw [not_le] at h
    rw [Fin.lt_iff_val_lt_val] at h ⊢
    simpa only [Fin.val_succ, Fin.coe_castSucc] using Nat.lt.step h

instance : ReflectsIsomorphisms (forget SimplexCategory) :=
  ⟨fun f hf =>
    IsIso.of_iso
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
#align simplex_category.is_iso_of_bijective SimplexCategory.isIso_of_bijective

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
#align simplex_category.order_iso_of_iso SimplexCategory.orderIsoOfIso

theorem iso_eq_iso_refl {x : SimplexCategory} (e : x ≅ x) : e = Iso.refl x := by
  have h : (Finset.univ : Finset (Fin (x.len + 1))).card = x.len + 1 := Finset.card_fin (x.len + 1)
  have eq₁ := Finset.orderEmbOfFin_unique' h fun i => Finset.mem_univ ((orderIsoOfIso e) i)
  have eq₂ :=
    Finset.orderEmbOfFin_unique' h fun i => Finset.mem_univ ((orderIsoOfIso (Iso.refl x)) i)
  -- Porting note: the proof was rewritten from this point in #3414 (reenableeta)
  -- It could be investigated again to see if the original can be restored.
  ext x
  replace eq₁ := congr_arg (· x) eq₁
  replace eq₂ := congr_arg (· x) eq₂.symm
  simp_all
#align simplex_category.iso_eq_iso_refl SimplexCategory.iso_eq_iso_refl

theorem eq_id_of_isIso {x : SimplexCategory} (f : x ⟶ x) [IsIso f] : f = 𝟙 _ :=
  congr_arg (fun φ : _ ≅ _ => φ.hom) (iso_eq_iso_refl (asIso f))
#align simplex_category.eq_id_of_is_iso SimplexCategory.eq_id_of_isIso

theorem eq_σ_comp_of_not_injective' {n : ℕ} {Δ' : SimplexCategory} (θ : mk (n + 1) ⟶ Δ')
    (i : Fin (n + 1)) (hi : θ.toOrderHom (Fin.castSucc i) = θ.toOrderHom i.succ) :
    ∃ θ' : mk n ⟶ Δ', θ = σ i ≫ θ' := by
  use δ i.succ ≫ θ
  ext1; ext1; ext1 x
  simp only [Hom.toOrderHom_mk, Function.comp_apply, OrderHom.comp_coe, Hom.comp,
    smallCategory_comp, σ, mkHom, OrderHom.coe_mk]
  by_cases h' : x ≤ Fin.castSucc i
  · -- This was not needed before leanprover/lean4#2644
    dsimp
    rw [Fin.predAbove_of_le_castSucc i x h']
    dsimp [δ]
    erw [Fin.succAbove_of_castSucc_lt _ _ _]
    · rw [Fin.castSucc_castPred]
    · exact (Fin.castSucc_lt_succ_iff.mpr h')
  · simp only [not_le] at h'
    let y := x.pred <| by rintro (rfl : x = 0); simp at h'
    have hy : x = y.succ := (Fin.succ_pred x _).symm
    rw [hy] at h' ⊢
    -- This was not needed before leanprover/lean4#2644
    conv_rhs => dsimp
    rw [Fin.predAbove_of_castSucc_lt i y.succ h', Fin.pred_succ]
    by_cases h'' : y = i
    · rw [h'']
      refine hi.symm.trans ?_
      congr 1
      dsimp [δ]
      erw [Fin.succAbove_of_castSucc_lt i.succ]
      exact Fin.lt_succ
    · dsimp [δ]
      erw [Fin.succAbove_of_le_castSucc i.succ _]
      simp only [Fin.lt_iff_val_lt_val, Fin.le_iff_val_le_val, Fin.val_succ, Fin.coe_castSucc,
        Nat.lt_succ_iff, Fin.ext_iff] at h' h'' ⊢
      cases' Nat.le.dest h' with c hc
      cases c
      · exfalso
        simp only [Nat.zero_eq, add_zero, len_mk, Fin.coe_pred, ge_iff_le] at hc
        rw [hc] at h''
        exact h'' rfl
      · rw [← hc]
        simp only [add_le_add_iff_left, Nat.succ_eq_add_one, le_add_iff_nonneg_left, zero_le]
#align simplex_category.eq_σ_comp_of_not_injective' SimplexCategory.eq_σ_comp_of_not_injective'

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
    · refine' ⟨y, x, ⟨h₁.symm, _⟩⟩
      rcases lt_or_eq_of_le (not_lt.mp h) with h' | h'
      · exact h'
      · exfalso
        exact h₂ h'.symm
  rcases hθ₂ with ⟨x, y, ⟨h₁, h₂⟩⟩
  use x.castPred ((Fin.le_last _).trans_lt' h₂).ne
  apply eq_σ_comp_of_not_injective'
  apply le_antisymm
  · exact θ.toOrderHom.monotone (le_of_lt (Fin.castSucc_lt_succ _))
  · rw [Fin.castSucc_castPred, h₁]
    exact θ.toOrderHom.monotone ((Fin.succ_castPred_le_iff _).mpr h₂)
#align simplex_category.eq_σ_comp_of_not_injective SimplexCategory.eq_σ_comp_of_not_injective

theorem eq_comp_δ_of_not_surjective' {n : ℕ} {Δ : SimplexCategory} (θ : Δ ⟶ mk (n + 1))
    (i : Fin (n + 2)) (hi : ∀ x, θ.toOrderHom x ≠ i) : ∃ θ' : Δ ⟶ mk n, θ = θ' ≫ δ i := by
  by_cases h : i < Fin.last (n + 1)
  · use θ ≫ σ (Fin.castPred i h.ne)
    ext1
    ext1
    ext1 x
    simp only [Hom.toOrderHom_mk, Function.comp_apply, OrderHom.comp_coe, Hom.comp,
      smallCategory_comp]
    by_cases h' : θ.toOrderHom x ≤ i
    · simp only [σ, mkHom, Hom.toOrderHom_mk, OrderHom.coe_mk]
      -- This was not needed before leanprover/lean4#2644
      dsimp
      -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
      erw [Fin.predAbove_of_le_castSucc _ _ (by rwa [Fin.castSucc_castPred])]
      dsimp [δ]
      erw [Fin.succAbove_of_castSucc_lt i]
      · rw [Fin.castSucc_castPred]
      · rw [(hi x).le_iff_lt] at h'
        exact h'
    · simp only [not_le] at h'
      -- The next three tactics used to be a simp only call before leanprover/lean4#2644
      rw [σ, mkHom, Hom.toOrderHom_mk, OrderHom.coe_mk, OrderHom.coe_mk]
      erw [OrderHom.coe_mk]
      erw [Fin.predAbove_of_castSucc_lt _ _ (by rwa [Fin.castSucc_castPred])]
      dsimp [δ]
      rw [Fin.succAbove_of_le_castSucc i _]
      -- This was not needed before leanprover/lean4#2644
      conv_rhs => dsimp
      erw [Fin.succ_pred]
      simpa only [Fin.le_iff_val_le_val, Fin.coe_castSucc, Fin.coe_pred] using
        Nat.le_sub_one_of_lt (Fin.lt_iff_val_lt_val.mp h')
  · obtain rfl := le_antisymm (Fin.le_last i) (not_lt.mp h)
    use θ ≫ σ (Fin.last _)
    ext x : 3
    dsimp [δ, σ]
    simp_rw [Fin.succAbove_last, Fin.predAbove_last_apply]
    erw [dif_neg (hi x)]
    rw [Fin.castSucc_castPred]
#align simplex_category.eq_comp_δ_of_not_surjective' SimplexCategory.eq_comp_δ_of_not_surjective'

theorem eq_comp_δ_of_not_surjective {n : ℕ} {Δ : SimplexCategory} (θ : Δ ⟶ mk (n + 1))
    (hθ : ¬Function.Surjective θ.toOrderHom) :
    ∃ (i : Fin (n + 2)) (θ' : Δ ⟶ mk n), θ = θ' ≫ δ i := by
  cases' not_forall.mp hθ with i hi
  use i
  exact eq_comp_δ_of_not_surjective' θ i (not_exists.mp hi)
#align simplex_category.eq_comp_δ_of_not_surjective SimplexCategory.eq_comp_δ_of_not_surjective

theorem eq_id_of_mono {x : SimplexCategory} (i : x ⟶ x) [Mono i] : i = 𝟙 _ := by
  suffices IsIso i by
    apply eq_id_of_isIso
  apply isIso_of_bijective
  dsimp
  rw [Fintype.bijective_iff_injective_and_card i.toOrderHom, ← mono_iff_injective,
    eq_self_iff_true, and_true_iff]
  infer_instance
#align simplex_category.eq_id_of_mono SimplexCategory.eq_id_of_mono

theorem eq_id_of_epi {x : SimplexCategory} (i : x ⟶ x) [Epi i] : i = 𝟙 _ := by
  suffices IsIso i by
    haveI := this
    apply eq_id_of_isIso
  apply isIso_of_bijective
  dsimp
  rw [Fintype.bijective_iff_surjective_and_card i.toOrderHom, ← epi_iff_surjective,
    eq_self_iff_true, and_true_iff]
  infer_instance
#align simplex_category.eq_id_of_epi SimplexCategory.eq_id_of_epi

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
#align simplex_category.eq_σ_of_epi SimplexCategory.eq_σ_of_epi

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
#align simplex_category.eq_δ_of_mono SimplexCategory.eq_δ_of_mono

theorem len_lt_of_mono {Δ' Δ : SimplexCategory} (i : Δ' ⟶ Δ) [hi : Mono i] (hi' : Δ ≠ Δ') :
    Δ'.len < Δ.len := by
  rcases lt_or_eq_of_le (len_le_of_mono hi) with (h | h)
  · exact h
  · exfalso
    exact hi' (by ext; exact h.symm)
#align simplex_category.len_lt_of_mono SimplexCategory.len_lt_of_mono

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
#align simplex_category.image_eq SimplexCategory.image_eq

theorem image_ι_eq {Δ Δ'' : SimplexCategory} {φ : Δ ⟶ Δ''} {e : Δ ⟶ image φ} [Epi e]
    {i : image φ ⟶ Δ''} [Mono i] (fac : e ≫ i = φ) : image.ι φ = i := by
  haveI := strongEpi_of_epi e
  rw [← image.isoStrongEpiMono_hom_comp_ι e i fac,
    SimplexCategory.eq_id_of_isIso (image.isoStrongEpiMono e i fac).hom, Category.id_comp]
#align simplex_category.image_ι_eq SimplexCategory.image_ι_eq

theorem factorThruImage_eq {Δ Δ'' : SimplexCategory} {φ : Δ ⟶ Δ''} {e : Δ ⟶ image φ} [Epi e]
    {i : image φ ⟶ Δ''} [Mono i] (fac : e ≫ i = φ) : factorThruImage φ = e := by
  rw [← cancel_mono i, fac, ← image_ι_eq fac, image.fac]
#align simplex_category.factor_thru_image_eq SimplexCategory.factorThruImage_eq

end EpiMono

namespace Join

/-- The join of two objects in `SimplexCategory`. -/
@[simp]
def obj (X Y : SimplexCategory) : SimplexCategory := [X.len+Y.len+1]

lemma incl₁_cond (X Y : SimplexCategory) (a : Fin (X.len+1)): a.val < X.len + Y.len + 1 + 1 := by
    have h2 : len X + len Y + 1 + 1 = len Y + 1 + (len X +1) := by
      rw [add_comm (len X) _, add_assoc (len Y) _ _, add_comm (len X) _]
      rw [add_assoc, add_assoc, add_comm (len X)]
      repeat rw [add_assoc]
    simp [h2]
    exact Nat.lt_add_left (len Y + 1) a.prop

lemma incl₂_cond (X Y : SimplexCategory) (a : Fin (Y.len+1)) :
    a.val + X.len +1 < X.len + Y.len +1 + 1 := by
  have h2 : len X + len Y + 1 + 1 = len Y + 1 + (len X +1) := by
    rw [add_comm (len X) _, add_assoc (len Y) _ _, add_comm (len X) _]
    rw [add_assoc, add_assoc, add_comm (len X)]
    repeat rw [add_assoc]
  simp [h2]
  exact Nat.add_succ_lt_add a.prop Nat.le.refl

lemma preimage_incl₂_cond (X Y : SimplexCategory) (a : Fin (X.len+Y.len+1+1)) :
    a.val - (X.len +1) < Y.len +1 := by
  have h1 := a.prop
  simp only [obj, len_mk] at h1
  have h2 : len X + len Y + 1 + 1 = len Y + 1 + (len X +1) := by
    rw [add_comm (len X) _, add_assoc (len Y) _ _, add_comm (len X) _]
    rw [add_assoc, add_assoc, add_comm (len X)]
    repeat rw [add_assoc]
  simp [h2] at h1
  by_cases h: a.val < X.len+1
  rw [Nat.lt_iff_add_one_le]
  simp_all only [add_le_add_iff_right, tsub_le_iff_right]
  exact _root_.le_add_left h.le
  exact (tsub_lt_iff_right (Nat.not_lt.mp h)).mpr h1

/-- The join of two morphisms in `SimplexCategory`. -/
@[simp]
def map {X1 Y1 X2 Y2: SimplexCategory} (η : X1 ⟶ X2) (ε : Y1 ⟶ Y2) : obj X1 Y1 ⟶ obj X2 Y2 :=
  Hom.mk {
    toFun := fun a =>
      if h : a.val <  X1.len+1 then
        ⟨(η.toOrderHom ⟨a.val, h⟩).val, incl₁_cond X2 Y2 (η.toOrderHom ⟨a.val, h⟩)⟩
      else
        ⟨ε.toOrderHom ⟨a.val - (X1.len+1), preimage_incl₂_cond X1 Y1 a⟩ + (X2.len + 1),
         incl₂_cond X2 Y2 (ε.toOrderHom ⟨a.val - (X1.len+1), preimage_incl₂_cond X1 Y1 a⟩)⟩
    monotone' := by
      intro a b h
      simp only [obj, len_mk]
      split_ifs <;> rename_i ha hb
      · exact η.toOrderHom.monotone h
      · exact le_add_left (η.toOrderHom ⟨a.val, ha⟩).prop.le
      · exact (Nat.not_le.mpr hb ((Nat.not_lt.mp ha).trans h)).elim
      · rw [Fin.le_def]
        simp only [add_le_add_iff_right, Fin.val_fin_le]
        exact ε.toOrderHom.monotone' (Nat.sub_le_sub_right h (len X1 + 1))
  }

/-- The functor from `SimplexCategory × SimplexCategory` to `SimplexCategory` representing
the join of objects and morphisms. -/
def func : SimplexCategory × SimplexCategory ⥤ SimplexCategory where
  obj X := obj X.1 X.2
  map η := map η.1 η.2
  map_id X := by
    simp
    apply congrArg
    apply OrderHom.ext
    funext a
    dsimp only [obj, len_mk, OrderHom.coe_mk, prod_id_snd, smallCategory_id, Hom.id,
      Hom.toOrderHom_mk, OrderHom.id_coe, id_eq]
    split_ifs with h
    rfl
    rw [Fin.eq_iff_veq]
    simp
    simp at h
    exact Nat.sub_add_cancel h
  map_comp {X Y Z} f g := by
    simp
    apply congrArg
    apply OrderHom.ext
    funext a
    dsimp
    split_ifs with h1 h2
    rfl
    simp only [Fin.is_lt, not_true_eq_false] at h2
    rename_i h2
    simp only [add_lt_iff_neg_right, not_lt_zero'] at h2
    simp only [add_tsub_cancel_right, Fin.eta]

/-- The inclusion of `X` into the join of `X` and `Y`. -/
def incl₁ (X Y : SimplexCategory) : X ⟶ Join.func.obj (X, Y) :=
   Hom.mk {
    toFun := fun a => ⟨a.val, incl₁_cond X Y a⟩
    monotone' := by
      intro a b h
      exact h
   }

/-- The inclusion of `Y` into the join of `X` and `Y`. -/
def incl₂ (X Y : SimplexCategory) : Y ⟶ Join.func.obj (X, Y) :=
   Hom.mk {
    toFun := fun a => ⟨a.val + X.len + 1, incl₂_cond X Y a ⟩
    monotone' := by
      intro a b h
      simp only [Fin.mk_le_mk, add_le_add_iff_right, Fin.val_fin_le]
      exact h
   }

lemma incl₁_map {X Y : SimplexCategory × SimplexCategory} ( η : X⟶ Y) :
    incl₁ X.1 X.2 ≫ Join.func.map η =  η.1 ≫ incl₁ Y.1 Y.2 := by
  simp [incl₁]
  apply congrArg
  apply OrderHom.ext
  funext a
  simp [func, Fin.eq_iff_veq]
  rfl

lemma incl₂_map {X Y : SimplexCategory × SimplexCategory} ( η : X⟶ Y) :
    incl₂ X.1 X.2 ≫ Join.func.map η =  η.2 ≫ incl₂ Y.1 Y.2 := by
  simp [incl₂]
  apply congrArg
  apply OrderHom.ext
  funext a
  simp [func, Fin.eq_iff_veq]
  change _ = ((Hom.toOrderHom η.2) a).val +len Y.1 +1
  refine add_right_cancel_iff.mpr ?_
  apply congrArg
  apply congrArg
  rw [Fin.eq_iff_veq]
  change a.val + len X.1 +1 - (len X.1 +1) = _
  exact Nat.sub_eq_of_eq_add rfl

end Join

namespace WithInitial
open WithInitial

/-- A function from `WithInitial SimplexCategory` to `ℕ` taking the initial object to `0` and
the object `of x` to `x.len+1`. -/
def len (X : WithInitial SimplexCategory) : ℕ :=
  match X with
  | star => 0
  | of x => Nat.succ x.len

/-- Isomorphic objects have the same length. -/
lemma len_iso {X Y : WithInitial SimplexCategory} (f : X ≅ Y) : len X = len Y := by
  simp [len]
  match X, Y with
  | star, star => rfl
  | of x, of y =>
    simp
    let f' : x ≅  y :=
      {hom := f.hom,
       inv := f.inv,
       hom_inv_id := f.hom_inv_id,
       inv_hom_id := f.inv_hom_id}
    have hm : Mono f'.hom := by exact StrongMono.mono
    have he : Epi f'.hom := by exact StrongEpi.epi
    exact Nat.le_antisymm (len_le_of_mono hm) (len_le_of_epi he)

/-- An isomorphism between objects of equal lengths. -/
def lenIso {X Y : WithInitial SimplexCategory} (h : len X = len Y) : X ≅ Y where
  hom :=
    match X, Y with
    | star, star => 𝟙 _
    | of x, of y => Hom.mk (Fin.castIso h : Fin (len (of x)) →o Fin (len (of y )))
  inv :=
    match X, Y with
    | star, star => 𝟙 _
    | of x, of y => Hom.mk (Fin.castIso h.symm : Fin (len (of y)) →o Fin (len (of x)))

/-- A function from `ℕ` to `WithInitial SimplexCategory` taking `0` to `start` and
 `Nat.succ x` to `of (mk x)`. -/
def mk (i : ℕ) : WithInitial SimplexCategory :=
  match i with
  | Nat.zero => star
  | Nat.succ x => of (SimplexCategory.mk x)

lemma len_mk (i : ℕ) : len (mk i) = i := by
  match i with
  | Nat.zero => rfl
  | Nat.succ x => rfl

/-- Given a morphism `f : X ⟶ Y` in `WithInitial SimplexCategory`, the corresponding ordered
homomorphism from `Fin (len X)` to  `Fin (len Y)`.  -/
def toOrderHom {X Y : WithInitial SimplexCategory} (f : X ⟶ Y) : Fin (len X) →o Fin (len Y) :=
  match X, Y, f with
  | of _, of _, f => f.toOrderHom
  | star, of x, _ => (OrderEmbedding.ofIsEmpty.toOrderHom :  (Fin 0) →o (Fin (len (of x))))
  | star, star, _ => OrderHom.id

lemma toOrderHom_id {Z : WithInitial SimplexCategory} : toOrderHom (𝟙 Z) = OrderHom.id := by
  match Z with
  | of z => rfl
  | star => rfl

lemma toOrderHom_comp {X Y Z: WithInitial SimplexCategory} (f : X ⟶ Y) (g : Y ⟶ Z):
    toOrderHom (f ≫ g) = (toOrderHom g).comp (toOrderHom f) := by
  match X, Y, Z, f, g with
  | star, star, star, f, g => rfl
  | star, star, of z, f, g => rfl
  | star, of y, of z, f, g =>
    apply OrderHom.ext
    exact List.ofFn_inj.mp rfl
  | of x, of y, of z, f, g => rfl

/-- Given an isomorphism `X ≅ Y` the corresponding OrderIso `Fin (len X) ≃o Fin (len Y)`. -/
def toOrderHomIso {X Y : WithInitial SimplexCategory} (f : X ≅ Y) : Fin (len X) ≃o Fin (len Y) where
  toFun := toOrderHom f.hom
  invFun := toOrderHom f.inv
  left_inv := by
    intro s
    change ((toOrderHom f.inv).comp (toOrderHom f.hom)) s = s
    rw [← toOrderHom_comp]
    rw [f.hom_inv_id]
    rw [toOrderHom_id]
    rfl
  right_inv := by
    intro s
    change ((toOrderHom f.hom).comp (toOrderHom f.inv)) s = s
    rw [← toOrderHom_comp]
    rw [f.inv_hom_id]
    rw [toOrderHom_id]
    rfl
  map_rel_iff' := by
    intro a b
    simp
    apply Iff.intro
    intro h1
    by_contra hn
    simp at hn
    have h3 : (toOrderHom f.hom) a = (toOrderHom f.hom) b := by
      rw [Fin.eq_iff_veq]
      exact Nat.le_antisymm h1 ((toOrderHom f.hom).monotone'
        (Fin.succ_le_succ_iff.mp (Nat.le.step hn)))
    apply congrArg (toOrderHom f.inv) at h3
    change ((toOrderHom f.inv).comp (toOrderHom f.hom)) a =
      ((toOrderHom f.inv).comp (toOrderHom f.hom)) b at h3
    rw [← toOrderHom_comp] at h3
    rw [f.hom_inv_id] at h3
    rw [toOrderHom_id] at h3
    simp at h3
    subst h3
    simp_all only [lt_self_iff_false]
    intro h1
    exact (toOrderHom f.hom).monotone' h1

lemma toOrderHomIso_apply {X Y : WithInitial SimplexCategory} (f : X ≅ Y) (a : Fin (len X)) :
    toOrderHom f.hom a = ⟨a, by rw [← len_iso f]; exact a.prop⟩ := by
  rw [Fin.eq_iff_veq]
  exact Fin.coe_orderIso_apply (toOrderHomIso f) a

lemma Hom.exe {X Y : WithInitial SimplexCategory} {f g: X ⟶ Y}
    (h : toOrderHom f = toOrderHom g) : f = g := by
  match X, Y, f with
  | star, star, _ => rfl
  | star, of x , _ => rfl
  | of x, of y, f =>
    simp [toOrderHom] at h
    let f': x ⟶ y := f
    let g': x ⟶ y :=g
    change f' = g'
    exact Hom.ext f' g' h

lemma toOrderHom_of_lenIso_hom {X Y : WithInitial SimplexCategory} (h : len X = len Y) :
    toOrderHom (lenIso h).hom = (Fin.castIso h : Fin (len X) →o Fin (len Y)) := by
  match X, Y with
  | star, star => rfl
  | of x, of y => rfl

lemma toOrderHom_of_lenIso_inv {X Y : WithInitial SimplexCategory} (h : len X = len Y) :
    toOrderHom (lenIso h).inv = (Fin.castIso h.symm : Fin (len Y) →o Fin (len X)) := by
  match X, Y with
  | star, star => rfl
  | of x, of y => rfl

/-- The morphism `X ⟶ Y` generated from an OrderHom `Fin (len X) →o Fin (len Y)`. -/
def homMk {X Y : WithInitial SimplexCategory} (f : Fin (len X) →o Fin (len Y)) : X ⟶ Y :=
  match X, Y, f with
  | star, star, _ => 𝟙 star
  | star, of y, _ => starInitial.to (of y)
  | of _, of _, f => SimplexCategory.Hom.mk f
  | of x, star, f => Fin.elim0 (f ⟨0, Nat.succ_pos (SimplexCategory.len x)⟩)

lemma homMk_id {X  : WithInitial SimplexCategory}: homMk (OrderHom.id ) = 𝟙 X :=
  match X with
  | star => rfl
  | of _ => rfl

lemma homMk_comp {X Y Z : WithInitial SimplexCategory}
    (f : Fin (len X) →o Fin (len Y)) (g : Fin (len Y) →o Fin (len Z)) :
    homMk (g.comp f) = homMk f ≫ homMk g := by
  match X, Y, Z, f, g with
  | star, star, star, f, g => rfl
  | star, star, of _, f, g => rfl
  | star, of _, of _, f, g => rfl
  | of _, of _, of _, f, g => rfl
  | star, of _, star, f, g => rfl
  | of x, star, star, f, g => exact Fin.elim0 (f ⟨0, Nat.succ_pos (SimplexCategory.len x)⟩)
  | of _, of y, star, f, g => exact Fin.elim0 (g ⟨0, Nat.succ_pos (SimplexCategory.len y)⟩)
  | of x, star, of _, f, g => exact Fin.elim0 (f ⟨0, Nat.succ_pos (SimplexCategory.len x)⟩)

lemma toOrderHom_homMk {X Y : WithInitial SimplexCategory} (f : Fin (len X) →o Fin (len Y)) :
    toOrderHom (homMk f)  = f:= by
  match X, Y with
  | star, star =>
    apply OrderHom.ext
    funext a
    exact Fin.elim0 a
  | star, of y =>
    apply OrderHom.ext
    funext a
    exact Fin.elim0 a
  | of x, star =>
    apply OrderHom.ext
    funext a
    exact Fin.elim0 (f a)
  | of x, of y =>
    rfl

/-- The functor from `WithInitial SimplexCategory × WithInitial SimplexCategory` to
`WithInitial SimplexCategory` which concatenates objects and morphisms. -/
def join :
    WithInitial SimplexCategory × WithInitial SimplexCategory ⥤ WithInitial SimplexCategory where
  obj X :=
    match X with
    | (star, star) => star
    | (of x, star) => of x
    | (star, of x) => of x
    | (of x, of y) => of (Join.func.obj (x,y))
  map {X Y} f :=
    match X, Y, f with
    | (star, star), (star, star), _ => 𝟙 star
    | (star, star), (star, of y), _ => starInitial.to (of y)
    | (star, star), (of y, star), _ => starInitial.to (of y)
    | (star, star), (of y1, of y2), _ => starInitial.to (of (Join.func.obj (y1,y2)))
    | (star, of x), (star, of y), f => f.2
    | (of x, star), (of y, star), f => f.1
    | (of x1, of x2), (of y1, of y2), f => Join.func.map f
    | (of x1, star), (of y1, of y2), f => f.1 ≫ (Join.incl₁ y1 y2)
    | (star, of x2), (of y1, of y2), f => f.2 ≫ (Join.incl₂ y1 y2)
  map_id X :=
    match X with
    | (star, star) => rfl
    | (of x, star) => rfl
    | (star, of x) => rfl
    | (of x, of y) => Join.func.map_id (x,y)
  map_comp {X Y Z} f g := by
    match X, Y, Z, f, g with
    | (star, star), (star, star), (star, star), f, g => rfl
    | (star, star), (star, star), (star, of z), f, g => rfl
    | (star, star), (star, star), (of z, star), f, g => rfl
    | (star, star), (star, star), (of z1, of z2), f, g => rfl
    | (star, star), (star, of y), (star, of z), f, g => rfl
    | (star, star), (of y, star), (of z, star), f, g => rfl
    | (star, star), (star, of y), (of z1, of z2), f, g => rfl
    | (star, star), (of y, star), (of z1, of z2), f, g => rfl
    | (star, star), (of y1, of y2), (of z1, of z2), f, g => rfl
    | (star, of x), (star, of y), (star, of z), f, g => rfl
    | (of x, star), (of y, star), (of z, star), f, g => rfl
    | (star, of x), (star, of y), (of z1, of z2), f, g => rfl
    | (of x, star), (of y, star), (of z1, of z2), f, g => rfl
    | (star, of x), (of y1, of y2), (of z1, of z2), f, g =>
       simp
       apply congrArg
       let g' : (y1, y2) ⟶ (z1, z2) := g
       change g'.2 ≫ _ = Join.incl₂ y1 y2 ≫ Join.func.toPrefunctor.map g'
       exact (Join.incl₂_map g').symm
    | (of x, star), (of y1, of y2), (of z1, of z2), f, g =>
       simp
       apply congrArg
       let g' : (y1, y2) ⟶ (z1, z2) := g
       change g'.1 ≫ _ = Join.incl₁ y1 y2 ≫ Join.func.toPrefunctor.map g'
       exact (Join.incl₁_map g').symm
    | (of x1, of x2), (of y1, of y2), (of z1, of z2), f, g =>
       let g' : (y1, y2) ⟶ (z1, z2) := g
       let f' : (x1, x2) ⟶ (y1, y2) := f
       exact Join.func.map_comp f' g'

lemma len_of_join (X : WithInitial SimplexCategory × WithInitial SimplexCategory) :
    len (join.obj X) = (len X.1) + (len X.2) := by
  match X with
  | (star, star) => rfl
  | (star, of x) =>
    simp [join]
    rfl
  | (of x, star) =>
    simp [join]
    rfl
  | (of x, of y) =>
    simp [join, len, Join.func, Nat.succ_eq_add_one]
    omega

lemma len_of_fst_lt_len_of_join_plus_one
    (X : WithInitial SimplexCategory × WithInitial SimplexCategory) :
    len X.1 < Nat.succ (len (join.obj X)) := by
  rw [len_of_join]
  refine Nat.lt_succ.mpr ?_
  exact Nat.le_add_right (len X.1) (len X.2)

lemma len_of_snd_lt_len_of_join_plus_one
    (X : WithInitial SimplexCategory × WithInitial SimplexCategory) :
    len X.2 < Nat.succ (len (join.obj X)) := by
  rw [len_of_join]
  refine Nat.lt_succ.mpr ?_
  exact Nat.le_add_left (len X.2) (len X.1)

lemma sub_fst_lt_snd_if_fst_le {X : WithInitial SimplexCategory × WithInitial SimplexCategory}
    (a :  Fin (len (join.obj X))) (h : len (X.1) ≤ a.val) : a.val - len X.1 < len X.2 := by
  have ha := a.prop
  simp [len_of_join] at ha
  exact Nat.sub_lt_left_of_lt_add h ha

lemma toOrderHom_join_apply_on_lt_fst
    {X Y : WithInitial SimplexCategory × WithInitial SimplexCategory}
    (f : X ⟶ Y) (a : Fin (len (join.obj X))) (ha : a.val < len (X.1)) :
    (toOrderHom (join.map f) a).val = (toOrderHom f.1 ⟨a, ha⟩).val := by
  match X, Y, f with
  | (star, star), (star, star), _ => rfl
  | (star, star), (star, of y), _ =>
    simp [len] at ha
  | (star, star), (of y, star), _ =>  rfl
  | (star, star), (of y1, of y2), f =>
    simp [len] at ha
  | (star, of x), (star, of y), f =>
    simp [len] at ha
  | (of x, star), (of y, star), f => rfl
  | (of x1, of x2), (of y1, of y2), f =>
    simp [toOrderHom, Join.func]
    have hx {n m  : ℕ } (f : Fin n → Fin m ) (mo : Monotone f) (a : Fin  n) :
    (({toFun := f, monotone' := mo } : Fin n →o Fin m) a).val = (f a).val := rfl
    erw [hx]
    split_ifs
    rfl
    rename_i ht
    simp at ha
    exact (ht ha).elim
  | (of x1, star), (of y1, of y2), f => rfl
  | (star, of x2), (of y1, of y2), f =>
    simp [len] at ha

lemma toOrderHom_join_apply_on_fst_le
    {X Y : WithInitial SimplexCategory × WithInitial SimplexCategory}
    (f : X ⟶ Y) (a : Fin (len (join.obj X))) (ha : len (X.1) ≤ a.val) :
    (toOrderHom (join.map f) a).val =
    (toOrderHom f.2 ⟨a.val-len X.1, sub_fst_lt_snd_if_fst_le a ha⟩).val + len Y.1 := by
  simp [join]
  match X, Y, f with
  | (star, star), (star, star), _ => rfl
  | (star, star), (star, of y), _ => rfl
  | (star, star), (of y, star), _ =>
    exact Fin.elim0 a
  | (star, star), (of y1, of y2), f =>
    exact Fin.elim0 a
  | (star, of x), (star, of y), f => rfl
  | (of x, star), (of y, star), f =>
    have hx := sub_fst_lt_snd_if_fst_le a ha
    simp [len] at hx
  | (of x1, of x2), (of y1, of y2), f =>
    simp [toOrderHom, Join.func]
    have hx {n m  : ℕ } (f : Fin n → Fin m ) (mo : Monotone f) (a : Fin  n) :
    (({toFun := f, monotone' := mo } : Fin n →o Fin m) a).val = (f a).val := rfl
    erw [hx]
    split_ifs
    rename_i han
    simp [len] at ha
    rw [Nat.succ_eq_add_one] at ha
    exact ((Nat.not_le.mpr han) ha).elim
    simp [len]
  | (of x1, star), (of y1, of y2), f =>
    have hx := sub_fst_lt_snd_if_fst_le a ha
    simp [len] at hx
  | (star, of x2), (of y1, of y2), f => rfl

lemma toOrderHom_fst_apply {X Y : WithInitial SimplexCategory × WithInitial SimplexCategory}
    (f : X ⟶ Y) (a : Fin (len X.1)) :
    (toOrderHom f.1 a).val = ((toOrderHom (join.map f)) ⟨a.val, by
     rw [len_of_join]; exact Nat.lt_add_right (len X.2) a.prop⟩).val := by
  rw [toOrderHom_join_apply_on_lt_fst f]

lemma toOrderHom_snd_apply {X Y : WithInitial SimplexCategory × WithInitial SimplexCategory}
    (f : X ⟶ Y) (a : Fin (len X.2)) :
    ((toOrderHom f.2) a).val = ((toOrderHom (join.map f)) ⟨a.val + len X.1, by
     rw [len_of_join, add_comm]
     exact Nat.add_lt_add_left a.prop (len X.1)
     ⟩).val - len Y.1:= by
  rw [toOrderHom_join_apply_on_fst_le f]
  simp only [add_tsub_cancel_right, Fin.eta]
  simp only [le_add_iff_nonneg_left, zero_le]

namespace Split

/-- Splits an object `X` into two parts based on an element of `Fin (Nat.succ (len X))`. -/
def obj (X : WithInitial SimplexCategory) (i : Fin (Nat.succ (len X))):
    WithInitial SimplexCategory × WithInitial SimplexCategory := (mk i, mk i.rev)

lemma incl₁_cond {Y : WithInitial SimplexCategory} {p : Fin (Nat.succ (len Y))}
    (a : Fin (len (obj Y p).1)) : a.val < len Y := by
  have ha := a.prop
  unfold obj at ha
  simp [len_mk] at ha
  omega

/-- The inclusion of `Fin (len (obj X i).1)` into `Fin X`. -/
def incl₁ {X : WithInitial SimplexCategory} {i : Fin (Nat.succ (len X))}
    (a : Fin (len (obj X i).1)) : Fin (len X) := ⟨a.val, incl₁_cond a⟩

/-- The preimage of an object in `Fin (len X)` under `incl₁` when it exists. -/
def preimageIncl₁ {X : WithInitial SimplexCategory} {i : Fin (Nat.succ (len X))}
    (a : Fin (len X)) (ha : a.val < len (obj X i).1) : Fin (len (obj X i).1) := ⟨a.val, ha⟩

lemma incl₂_cond  {Y : WithInitial SimplexCategory} {p : Fin (Nat.succ (len Y))}
    (a : Fin (len (obj Y p).2)) :
    a.val + p.val < len Y := by
  have ha := a.prop
  unfold obj at ha
  simp [len_mk] at ha
  omega

/-- The inclusion of `Fin (len (obj X i).2)` into `Fin X`. -/
def incl₂ {X : WithInitial SimplexCategory} {i : Fin (Nat.succ (len X))}
    (a : Fin (len (obj X i).2)) : Fin (len X) := ⟨a.val + i.val, incl₂_cond a⟩

lemma preimageIncl₂_cond  {X : WithInitial SimplexCategory} {i : Fin (Nat.succ (len X))}
    (a : Fin (len X)) (ha : len (obj X i).1 ≤ a.val) :
    a.val - (len (obj X i).1) < len (obj X i).2 := by
  simp_all [obj, len_mk]
  refine lt_tsub_of_add_lt_right ?_
  rw [tsub_add_cancel_iff_le.mpr ha]
  have h := a.prop
  unfold obj at h
  simp [len_mk] at h
  omega

/-- The preimage of an object in `Fin (len X)` under `incl₂` when it exists. -/
def preimageIncl₂ {X : WithInitial SimplexCategory} {i : Fin (Nat.succ (len X))}
    (a : Fin (len X)) (ha : len (obj X i).1 ≤ a.val) :
    Fin (len (obj X i).2) := ⟨a.val - (len (obj X i).1) , preimageIncl₂_cond a ha⟩

/-- An isomorphism between `obj X i` and `obj X j` when `i=j`. -/
def indexEqToIso {X : WithInitial SimplexCategory} {i j : Fin (Nat.succ (len X))}
    (h : i = j) : obj X i ≅ obj X j where
  hom := (homMk (Fin.castIso (by rw [h] : len (obj X i).1 = len (obj X j).1)),
          homMk (Fin.castIso (by rw [h] : len (obj X i).2 = len (obj X j).2)))
  inv := (homMk (Fin.castIso (by rw [h] : len (obj X i).1 = len (obj X j).1).symm),
          homMk (Fin.castIso (by rw [h] : len (obj X i).2 = len (obj X j).2).symm))
  hom_inv_id := by
    simp only [obj, Fin.val_rev, prod_Hom, prod_comp, prod_id, Prod.mk.injEq]
    rw [← homMk_comp, ← homMk_comp]
    change homMk (OrderHom.id) = _ ∧ homMk (OrderHom.id) = _
    simp only [homMk_id, and_self, mk]
  inv_hom_id := by
    simp [obj]
    rw [← homMk_comp, ← homMk_comp]
    change homMk (OrderHom.id) =_ ∧ homMk (OrderHom.id) =_
    simp only [homMk_id, and_self, mk]

lemma indexEqToIso_refl {X : WithInitial SimplexCategory} {i  : Fin (Nat.succ (len X))} :
    indexEqToIso (by rfl : i = i) = Iso.refl (obj X i) := by
  ext
  simp [indexEqToIso]
  change (homMk (OrderHom.id), homMk (OrderHom.id)) =_
  rw [homMk_id, homMk_id, prod_id]

lemma toOrderHom_indexEqToIso_inv_fst_apply {X : WithInitial SimplexCategory}
    {i j : Fin (Nat.succ (len X))} (h : i = j) (a : Fin (len (obj X j).1)) :
    (toOrderHom (indexEqToIso h).inv.1) a = ⟨a.val, by subst h; exact a.prop⟩ := by
  simp [indexEqToIso, toOrderHom_homMk]
  rw [Fin.eq_iff_veq]
  rfl

lemma toOrderHom_indexEqToIso_inv_snd_apply {X : WithInitial SimplexCategory}
    {i j : Fin (Nat.succ (len X))} (h : i = j) (a : Fin (len (obj X j).2)) :
    (toOrderHom (indexEqToIso h).inv.2) a = ⟨a.val, by subst h; exact a.prop⟩ := by
  simp [indexEqToIso, toOrderHom_homMk]
  rw [Fin.eq_iff_veq]
  rfl

lemma indexEqToIso_inv_comp_symm_inv {X : WithInitial SimplexCategory}
    {i j : Fin (Nat.succ (len X))} (h : i = j) :
    (indexEqToIso h).inv ≫ (indexEqToIso h.symm).inv = 𝟙 _ := by
  rw [prod_id]
  simp [indexEqToIso]
  apply And.intro <;>
    apply Hom.exe
    <;> apply OrderHom.ext
    <;> funext a
    <;> rw [toOrderHom_comp, toOrderHom_homMk, toOrderHom_homMk, Fin.eq_iff_veq]
  · have h : (toOrderHom (𝟙 (obj X j).1)) = OrderHom.id := by
      rw [toOrderHom_id]
    simp [h]
    rfl
  · have h : (toOrderHom (𝟙 (obj X j).2)) = OrderHom.id := by
      rw [toOrderHom_id]
    simp [h]
    rfl

lemma join_split_len (X : WithInitial SimplexCategory) (i : Fin (Nat.succ (len X))) :
    len X = len (join.obj (Split.obj X i))  := by
  rw [len_of_join]
  simp [Split.obj]
  rw [len_mk, len_mk]
  omega

/-- An isomorphism between an object and the join of a split of that object. -/
def joinSplitIso (X : WithInitial SimplexCategory) (i : Fin (Nat.succ (len X))) :
    X ≅ join.obj (Split.obj X i) := lenIso (Split.join_split_len X i)

/-- Given a `X` and `Y` in `WithInitial SimplexCategory` and an `i` in `Fin (Nat.succ (len X))`,
the type of split versions of homomorphisms from `Y` to `X`. -/
inductive hom (Y X : WithInitial SimplexCategory) (i : Fin (Nat.succ (len X)))  where
  | split : (p : Fin (Nat.succ (len Y))) → (obj Y p ⟶ obj X i) → hom Y X i

lemma hom_ext (Y X: WithInitial SimplexCategory) (i : Fin (Nat.succ (len X)))
    (s t : hom Y X i) (h1 : s.1 = t.1) (h2 : (indexEqToIso h1).inv ≫ s.2 = t.2) :
    s = t := by
  match s, t with
  | hom.split ps s, hom.split pt t =>
    simp at h1
    subst h1
    congr
    rw [indexEqToIso_refl] at h2
    simp  at h2
    exact h2

/-- Given a morphism `f : X ⟶ Y` and a `i` in `Fin (Nat.succ (len Y))`, the element `p` of
`Fin (Nat.succ (len X))` specifying the value to split `X` at in order to generate a
morphism `obj X p` to `obj Y i` from `f`.  -/
def sourceValue {X Y : WithInitial SimplexCategory} (f : X ⟶ Y) (i : Fin (Nat.succ (len Y))) :
    Fin (Nat.succ (len X)) :=
  let k := Fin.find (fun a => i ≤ (toOrderHom f a).castSucc)
  match k with
  | some k => k.castSucc
  | none => Fin.last (len X)

lemma sourceValue_of_iso_hom {X Y : WithInitial SimplexCategory} (f : Y ≅ X)
    (i : Fin (Nat.succ (len X))) :
    sourceValue f.hom i = ⟨i.val, by rw [len_iso f]; exact i.prop⟩ := by
  simp [sourceValue]
  let k := Fin.find (fun a => i ≤ (toOrderHom f.hom a).castSucc)
  have hk : Fin.find (fun a => i ≤ (toOrderHom f.hom a).castSucc) = k := rfl
  rw [hk]
  match k with
  | some x =>
    rw [Fin.find_eq_some_iff] at hk
    let hkl := hk.left
    rw [toOrderHomIso_apply f] at hkl
    simp [Fin.le_def] at hkl
    let hkr := hk.right ⟨i, Nat.lt_of_le_of_lt hkl x.prop⟩
    rw [toOrderHomIso_apply f] at hkr
    simp [Fin.le_def] at hkr
    simp [Fin.eq_iff_veq]
    exact Nat.le_antisymm hkr hkl
  | none =>
    rw [Fin.find_eq_none_iff] at hk
    ext
    simp only [Fin.val_last]
    match X, Y with
    | star, star =>
      simp [len]
    | of x, of y =>
      have h1 := hk (Fin.last (y.len))
      rw [toOrderHomIso_apply f] at h1
      simp  [Fin.lt_def] at h1
      have ht := Fin.is_le i
      simp [← len_iso f] at ht
      exact Nat.le_antisymm h1 ht

lemma sourceValue_of_iso_inv {X Y : WithInitial SimplexCategory} (f : Y ≅ X)
    (i : Fin (Nat.succ (len Y))) :
    sourceValue f.inv i = ⟨i.val, by rw [← len_iso f]; exact i.prop⟩ := by
  change sourceValue (f.symm).hom i =_
  rw [sourceValue_of_iso_hom]

lemma sourceValue_of_id {X : WithInitial SimplexCategory} (i : Fin (Nat.succ (len X))) :
    sourceValue (𝟙 X) i = i := by
  change sourceValue (Iso.refl X).hom i = i
  rw [sourceValue_of_iso_hom]

lemma toOrderHom_apply_on_lt_sourceValue {X Y : WithInitial SimplexCategory} (f : X ⟶ Y)
    (i : Fin (Nat.succ (len Y)))  (a : Fin (len X)) (ha : a.castSucc < sourceValue f i) :
    ((toOrderHom f) a).castSucc < i := by
  let k := Fin.find (fun a => i ≤ (toOrderHom f a).castSucc)
  have hk : Fin.find (fun a => i ≤ (toOrderHom f a).castSucc) = k := rfl
  simp [sourceValue, hk] at ha
  match k with
  | some k =>
    simp_all
    rw [Fin.find_eq_some_iff] at hk
    exact Fin.not_le.mp ((hk.right a).mt (Fin.not_le.mpr ha))
  | none =>
    simp_all
    rw [Fin.find_eq_none_iff] at hk
    exact Fin.not_le.mp (hk a)

lemma toOrderHom_apply_on_sourceValue_le {X Y : WithInitial SimplexCategory} (f : X ⟶ Y)
    (i : Fin (Nat.succ (len Y)))  (a : Fin (len X)) (ha : sourceValue f i ≤  a.castSucc):
    i ≤ ((toOrderHom f) a).castSucc  := by
  let k := Fin.find (fun a => i ≤ (toOrderHom f a).castSucc)
  have hk : Fin.find (fun a => i ≤ (toOrderHom f a).castSucc) = k := rfl
  simp [sourceValue, hk] at ha
  match k with
  | some k =>
    simp_all
    rw [Fin.find_eq_some_iff] at hk
    exact hk.left.trans ((toOrderHom f).monotone' ha )
  | none =>
    simp_all
    rw [Fin.find_eq_none_iff] at hk
    rw [Fin.eq_iff_veq] at ha
    simp at ha
    omega

lemma toOrderHom_apply_on_lt_sourceValue' {X Y : WithInitial SimplexCategory} {f : X ⟶ Y}
    {i : Fin (Nat.succ (len Y))} {a : Fin (len X)} (ha : a.val < len (obj X (sourceValue f i)).1) :
    ((toOrderHom f) a).val < len (obj Y i).1 := by
  simp_all [obj, len_mk]
  let k := Fin.find (fun a => i ≤ (toOrderHom f a).castSucc)
  have hk : Fin.find (fun a => i ≤ (toOrderHom f a).castSucc) = k := rfl
  simp [sourceValue, hk] at ha
  match k with
  | some k =>
    simp_all
    rw [Fin.find_eq_some_iff] at hk
    exact Fin.not_le.mp ((hk.right a).mt (Fin.not_le.mpr ha))
  | none =>
    simp_all
    rw [Fin.find_eq_none_iff] at hk
    exact Fin.not_le.mp (hk a)

lemma toOrderHom_apply_on_sourceValue_le' {X Y : WithInitial SimplexCategory} {f : X ⟶ Y}
    {i : Fin (Nat.succ (len Y))}  {a : Fin (len X)}
    (ha : len (obj X (sourceValue f i)).1 ≤ a.val) :
    len (obj Y i).1 ≤ ((toOrderHom f) a).val  := by
  simp_all [obj, len_mk]
  let k := Fin.find (fun a => i ≤ (toOrderHom f a).castSucc)
  have hk : Fin.find (fun a => i ≤ (toOrderHom f a).castSucc) = k := rfl
  simp [sourceValue, hk] at ha
  match k with
  | some k =>
    simp_all
    rw [Fin.find_eq_some_iff] at hk
    have hkl := hk.left
    let hm := (toOrderHom f).monotone' ha
    rw [Fin.le_def] at hm hkl
    simp at hm hkl
    exact hkl.trans hm
  | none =>
    simp_all
    rw [Fin.find_eq_none_iff] at hk
    omega

lemma sourceValue_of_comp  {X Y Z: WithInitial SimplexCategory} (f : X ⟶ Y) (g : Y ⟶ Z)
    (i : Fin (Nat.succ (len Z))) :
    sourceValue f (sourceValue g i) = sourceValue (f ≫ g) i := by
  rw [sourceValue, sourceValue, sourceValue]
  repeat apply congrFun
  apply congrArg
  let k := Fin.find fun a ↦ i ≤ Fin.castSucc ((toOrderHom g) a)
  have hk : Fin.find fun a ↦ i ≤ Fin.castSucc ((toOrderHom g) a) = k := rfl
  rw [hk]
  match k with
  | some x =>
    rw [Fin.find_eq_some_iff] at hk
    simp only [Fin.castSucc_le_castSucc_iff, toOrderHom_comp, OrderHom.comp_coe,
      Function.comp_apply]
    let k2 := (Fin.find fun a ↦ x ≤ (toOrderHom f) a)
    have hk2 : (Fin.find fun a ↦ x ≤ (toOrderHom f) a) =k2  := rfl
    rw [hk2]
    match k2 with
    | some x2 =>
      symm
      rw [Fin.find_eq_some_iff]
      rw [Fin.find_eq_some_iff] at hk2
      apply And.intro
      · exact hk.left.trans ((toOrderHom g).monotone' hk2.left )
      · intro j hj
        exact hk2.right j (hk.right ((toOrderHom f) j) hj)
    | none =>
      symm
      rw [Fin.find_eq_none_iff]
      rw [Fin.find_eq_none_iff] at hk2
      intro j
      simp
      by_contra hn
      simp at hn
      exact hk2 j (hk.right ((toOrderHom f) j) hn )
  | none =>
    rw [Fin.find_eq_none_iff] at hk
    simp
    have h1 : Fin.find fun a ↦ Fin.castSucc ((toOrderHom f) a) = Fin.last (len Y) = none := by
      rw [Fin.find_eq_none_iff]
      intro i
      have := ((toOrderHom f) i).prop
      rw [Fin.eq_iff_veq]
      omega
    rw [h1]
    symm
    rw [Fin.find_eq_none_iff, toOrderHom_comp]
    exact fun l => hk ((toOrderHom f) l)

lemma splitValue_of_join {X Y : WithInitial SimplexCategory × WithInitial SimplexCategory}
    (f : X ⟶ Y) : Split.sourceValue (join.map f) ⟨len Y.1, len_of_fst_lt_len_of_join_plus_one Y⟩
    = ⟨len X.1, len_of_fst_lt_len_of_join_plus_one X⟩ := by
  simp only [Split.sourceValue]
  let k :=  Fin.find fun a => ⟨len Y.1, len_of_fst_lt_len_of_join_plus_one Y⟩
    ≤  ((toOrderHom (join.map f)) a).castSucc
  have hk : Fin.find fun a => ⟨len Y.1, len_of_fst_lt_len_of_join_plus_one Y⟩
    ≤  ((toOrderHom (join.map f)) a).castSucc  = k := rfl
  rw [hk]
  match k with
  | some x =>
    rw [Fin.find_eq_some_iff] at hk
    by_cases hX2 : len X.2 = 0
    · let hkl := hk.left
      rw [Fin.le_def] at hkl
      simp at hkl
      have hx := x.prop
      simp only [len_of_join] at hx
      rw [hX2, add_zero] at hx
      rw [toOrderHom_join_apply_on_lt_fst f x hx] at hkl
      exact ((Nat.not_le.mpr ((toOrderHom f.1) ⟨x.val, hx⟩).prop) hkl).elim
    · have hx := @Nat.lt_add_of_pos_right (len X.2) (len X.1) (Nat.pos_of_ne_zero hX2)
      rw [← len_of_join] at hx
      let X1 : Fin (len (join.obj X)) := ⟨len X.1, hx⟩
      have hkr := hk.right X1
      rw [Fin.le_def, Fin.coe_castSucc, toOrderHom_join_apply_on_fst_le] at hkr
      have hkr2 : x ≤ X1 := hkr (Nat.le_add_left (len Y.1) _)
      have hkl := hk.left
      by_cases hlt : x < X1
      · rw [Fin.le_def, Fin.coe_castSucc, toOrderHom_join_apply_on_lt_fst f x hlt] at hkl
        exact ((Nat.not_le.mpr ((toOrderHom f.1) ⟨ x,hlt ⟩).prop) hkl).elim
      · change Fin.castSucc x = Fin.castSucc X1
        refine Fin.castSucc_inj.mpr ?_
        rw [Fin.eq_iff_veq]
        rw [Fin.le_def] at hkr2
        rw [Fin.lt_def, ← Nat.not_le] at  hlt
        simp at hlt hkr2
        exact Nat.le_antisymm hkr2 hlt
      rfl
  | none =>
    rw [Fin.find_eq_none_iff] at hk
    simp at hk
    rw [Fin.eq_iff_veq]
    simp [len_of_join]
    by_contra hX2
    have hx := @Nat.lt_add_of_pos_right (len X.2) (len X.1) (Nat.pos_of_ne_zero hX2)
    rw [← len_of_join] at hx
    refine (Nat.not_le.mpr (Fin.lt_def.mp (hk ⟨len X.1, hx⟩))) ?_
    rw [Fin.coe_castSucc, toOrderHom_join_apply_on_fst_le]
    exact  Nat.le_add_left (len Y.1) _
    rfl

/-- Given a morphism `f : X ⟶ Y`, and an element of `Fin (Nat.succ (len Y))`, the corresponding
morphism between `obj X (sourceValue f i) ` and `obj Y i`. -/
def map {X Y : WithInitial SimplexCategory} (f : X ⟶ Y) (i : Fin (Nat.succ (len Y))) :
    obj X (sourceValue f i) ⟶ obj Y i:=
  (homMk {
    toFun := fun a =>
      preimageIncl₁ (toOrderHom f (incl₁ a)) (toOrderHom_apply_on_lt_sourceValue' (a.prop))
    monotone' := by
      intro a b h
      apply (toOrderHom f).monotone'
      exact h
  },
  homMk {
    toFun := fun a => preimageIncl₂ (toOrderHom f (incl₂ a)) (by
      refine toOrderHom_apply_on_sourceValue_le' ?_
      simp [obj, len_mk, incl₂]
    )
    monotone' := by
      intro a b h
      simp [preimageIncl₂]
      rw [tsub_add_cancel_iff_le.mpr]
      apply (toOrderHom f).monotone'
      simp [incl₂]
      exact h
      apply toOrderHom_apply_on_sourceValue_le'
      simp only [obj, Fin.val_rev, Nat.succ_sub_succ_eq_sub, len_mk, incl₂, le_add_iff_nonneg_left,
        zero_le]
  })

lemma map_id {X : WithInitial SimplexCategory} (i : Fin (Nat.succ (len X))) :
    (indexEqToIso (sourceValue_of_id i)).inv ≫ map (𝟙 X) i = 𝟙 (obj X i) := by
  simp [map, indexEqToIso]
  rw [prod_id, Prod.mk.injEq]
  rw [← homMk_comp, ← homMk_comp, ← @homMk_id (obj X i).1, ← @homMk_id (obj X i).2]
  apply And.intro
  match X with
  | star => rfl
  | of x => rfl
  match X with
  | star =>
    simp_all only [obj, len_mk, Fin.val_rev, Fin.coe_fin_one, add_zero, Fin.eta, tsub_zero,
      preimageIncl₂]
    rfl
  | of x =>
    apply congrArg
    apply OrderHom.ext
    funext a
    rw [Fin.eq_iff_veq]
    simp only [obj, Fin.val_rev, preimageIncl₂, Nat.succ_sub_succ_eq_sub, len_mk, OrderHom.comp_coe,
      Function.comp_apply, OrderHom.id_coe, id_eq]
    change a.val + (sourceValue (𝟙 (of x)) i).val -i = a.val
    rw [sourceValue_of_id i]
    exact Nat.add_sub_cancel ↑a ↑i

lemma map_comp {X Y Z: WithInitial SimplexCategory} (f : X ⟶ Y) (g : Y ⟶ Z)
    (i : Fin (Nat.succ (len Z)))  : map (f ≫ g) i
    =  (indexEqToIso (sourceValue_of_comp f g i)).inv ≫ map f (sourceValue g i) ≫ map g i := by
  match X, Y, Z, f, g with
  | star, star, star, f, g => rfl
  | star, star, of z, f, g => rfl
  | star, of y, of z, f, g => rfl
  | of x, of y, of z, f, g =>
     simp [map, indexEqToIso, ← homMk_comp]
     apply And.intro
     all_goals apply congrArg
     rfl
     apply OrderHom.ext
     funext a
     simp only [obj, Fin.val_rev, preimageIncl₂, toOrderHom_comp, incl₂, OrderHom.comp_coe,
       Function.comp_apply, Nat.succ_sub_succ_eq_sub, len_mk, (sourceValue_of_comp f g i),
       Fin.eq_iff_veq]
     change ((toOrderHom g) ((toOrderHom f) ⟨a.val + (sourceValue (f ≫ g) i).val, _⟩)).val - i.val =
       ((toOrderHom g) ⟨((toOrderHom f) ⟨a.val + (sourceValue (f ≫ g) i).val, _⟩).val
        - (sourceValue g i).val + (sourceValue g i).val, _⟩)  - i.val
     apply congrFun
     repeat apply congrArg
     simp [Fin.eq_iff_veq, ← (sourceValue_of_comp f g i)]
     rw [tsub_add_cancel_of_le]
     apply toOrderHom_apply_on_sourceValue_le
     simp only [Fin.le_def, Fin.castSucc_mk, le_add_iff_nonneg_left, zero_le]

lemma toOrderHom_on_lt_fst_eq {X Y: WithInitial SimplexCategory} (f : Y ⟶ X)
    (i : Fin (Nat.succ (len X))) (a : Fin (len Y))
    (ha : a.val < len (obj Y (sourceValue f i)).1) :
    (toOrderHom f a).val = (toOrderHom (map f i).1 (preimageIncl₁ a ha)).val := by
  simp [map]
  rw [toOrderHom_homMk]
  rfl

lemma toOrderHom_fst_apply {X Y : WithInitial SimplexCategory} (f : Y ⟶ X)
    (i : Fin (Nat.succ (len X))) (a : Fin (len (obj Y (sourceValue f i)).1)) :
    (toOrderHom (map f i).1 a).val = ((toOrderHom f) (incl₁ a)).val := by
  rw [toOrderHom_on_lt_fst_eq f i (incl₁ a)]
  rfl

lemma toOrderHom_on_fst_le_eq {X Y: WithInitial SimplexCategory} (f : Y ⟶ X)
    (i : Fin (Nat.succ (len X))) (a : Fin (len Y))
    (ha : len (obj Y (sourceValue f i)).1 ≤ a.val) :
    (toOrderHom f a).val = (toOrderHom (map f i).2 (preimageIncl₂ a ha)).val + i.val := by
  simp [preimageIncl₂]
  change _= ↑((toOrderHom (map f i).2).toFun _) + i.val
  simp only [map, preimageIncl₂, toOrderHom_homMk, OrderHom.toFun_eq_coe, OrderHom.coe_mk]
  have hx {n m  : ℕ } (f : Fin n → Fin m ) (mo : Monotone f) (a : Fin  n) :
    (({toFun := f, monotone' := mo } : Fin n →o Fin m) a).val = (f a).val := rfl
  nth_rewrite 2 [hx]
  simp only [obj, Fin.val_rev, Nat.succ_sub_succ_eq_sub, len_mk, OrderHom.toFun_eq_coe]
  rw [tsub_add_cancel_iff_le.mpr]
  repeat apply congrArg
  rw [Fin.eq_iff_veq]
  refine (tsub_add_cancel_iff_le.mpr (Nat.not_lt.mp ?_)).symm
  simp [obj, len_mk] at ha
  exact Nat.not_lt.mpr ha
  apply toOrderHom_apply_on_sourceValue_le
  simp only [Fin.le_def, Fin.castSucc_mk, le_add_iff_nonneg_left, zero_le, incl₂]

lemma toOrderHom_snd_apply {X Y : WithInitial SimplexCategory} (f : Y ⟶ X)
    (i : Fin (Nat.succ (len X))) (a : Fin (len (obj Y (sourceValue f i)).2)) :
    (toOrderHom (map f i).2 a).val
    = ((toOrderHom f) (incl₂ a) ).val - i.val := by
  rw [toOrderHom_on_fst_le_eq f i (incl₂ a)]
  simp [incl₂, preimageIncl₂, obj, len_mk]
  simp [incl₂, obj, len_mk]

/-- Given a map `f : Z ⟶ Y`, the corresponding map from `hom Y X i` to `hom Z X i`. -/
def homMap {Y Z : WithInitial SimplexCategory} (X : WithInitial SimplexCategory)
    (i : Fin (Nat.succ (len X))) (f : Z ⟶ Y) (s : hom Y X i) : hom Z X i :=
  hom.split (sourceValue f s.1) (map f s.1 ≫ s.2)

/-- An equivalance between the type `hom X Y i` and the type `Y ⟶ X`. In the forward direction
maps are joined and in the inverse direction maps are split based in the index `i`. -/
def splitJoinUnitEquiv (X Y : WithInitial SimplexCategory) (i : Fin (Nat.succ (len X))) :
    hom Y X i ≃ (Y ⟶ X) where
  toFun s :=
    match s with
    | Split.hom.split p fs =>
    (Split.joinSplitIso Y p).hom ≫ join.map fs ≫ (Split.joinSplitIso X i).inv
  invFun f := Split.hom.split (Split.sourceValue f i) (Split.map f i)
  left_inv := by
    intro s
    have hs : s.1.val =
        (⟨len (Split.obj Y s.1).1, len_of_fst_lt_len_of_join_plus_one (Split.obj Y s.1)⟩
        : Fin _).val := by
      simp only [Split.obj, Fin.val_rev, Nat.succ_sub_succ_eq_sub, len_mk]
    refine Split.hom_ext _ _ _ _ _ ?_ ?_
    simp
    rw [← Split.sourceValue_of_comp, ← Split.sourceValue_of_comp]
    rw [Split.sourceValue_of_iso_hom (Split.joinSplitIso Y s.1)]
    rw [Split.sourceValue_of_iso_inv (Split.joinSplitIso X i)]
    simp [Fin.eq_iff_veq]
    rw [hs, ← (Split.splitValue_of_join s.2)]
    repeat apply congrArg
    simp only [Split.obj, Fin.val_rev, Nat.succ_sub_succ_eq_sub, len_mk]
    apply Prod.ext
    all_goals apply Hom.exe
    rw [prod_comp_fst, toOrderHom_comp]
    apply OrderHom.ext
    funext a
    simp
    rw [Split.toOrderHom_indexEqToIso_inv_fst_apply, Fin.eq_iff_veq, Split.toOrderHom_fst_apply]
    simp [Split.incl₁, toOrderHom_comp, Split.joinSplitIso, toOrderHom_of_lenIso_hom,
      toOrderHom_of_lenIso_inv]
    rw [WithInitial.toOrderHom_fst_apply]
    rw [prod_comp_snd, toOrderHom_comp]
    apply OrderHom.ext
    funext a
    simp
    rw [Split.toOrderHom_indexEqToIso_inv_snd_apply, Fin.eq_iff_veq, Split.toOrderHom_snd_apply]
    simp only [Split.joinSplitIso, toOrderHom_comp, toOrderHom_of_lenIso_inv,
      toOrderHom_of_lenIso_hom, Split.incl₂, OrderHom.comp_coe, OrderHomClass.coe_coe,
      Function.comp_apply, Fin.castIso_apply, Fin.cast_mk, Fin.coe_cast]
    rw [WithInitial.toOrderHom_snd_apply]
    simp [Split.obj, len_mk]
    apply congrFun
    repeat apply congrArg
    simp [Fin.eq_iff_veq, Split.obj, len_mk]
    rw [← Split.sourceValue_of_comp, ← Split.sourceValue_of_comp, Split.sourceValue_of_iso_hom]
    change (Split.sourceValue (join.map s.2) _).val =_
    rw [hs, ← (Split.splitValue_of_join s.2)]
    repeat apply congrArg
    simp [Split.sourceValue_of_iso_inv, Split.obj, len_mk]
  right_inv := by
    intro f
    apply Hom.exe
    rw [toOrderHom_comp, toOrderHom_comp]
    rw [Split.joinSplitIso, Split.joinSplitIso]
    rw [toOrderHom_of_lenIso_hom, toOrderHom_of_lenIso_inv]
    apply OrderHom.ext
    funext a
    rw [Fin.eq_iff_veq]
    simp
    by_cases ha : a.val < len (Split.obj Y (Split.sourceValue f i)).1
    rw [Split.toOrderHom_on_lt_fst_eq f i a ha]
    exact toOrderHom_join_apply_on_lt_fst (Split.map f i)
      (Fin.cast (Split.join_split_len Y (Split.sourceValue f i)) a) ha
    rw [Split.toOrderHom_on_fst_le_eq f i a (Nat.not_lt.mp ha)]
    rw [toOrderHom_join_apply_on_fst_le (Split.map f i) (Fin.cast _ a)]
    simp [Split.obj, len_mk, preimageIncl₂]
    simp_all [obj, len_mk]

lemma splitJoinUnitEquiv_naturality (X : WithInitial SimplexCategory) (i : Fin (Nat.succ (len X)))
    {Z Y : WithInitial SimplexCategory} (f : Z ⟶ Y) :
    ((Split.splitJoinUnitEquiv X Z i).symm).toFun ∘ (CategoryStruct.comp f) =
    (homMap X i f) ∘ ((Split.splitJoinUnitEquiv X Y i).symm).toFun := by
  funext s
  refine Split.hom_ext _ _ _ _ _ ?_ ?_
  exact (Split.sourceValue_of_comp f s i).symm
  simp only [Split.splitJoinUnitEquiv,  Equiv.toFun_as_coe, Equiv.coe_fn_symm_mk,
    Function.comp_apply, homMap,  Fin.val_rev, Prod.mk.injEq]
  rw [Split.map_comp]
  change _ = Split.map f (Split.sourceValue s i) ≫ Split.map s i
  repeat rw [← Category.assoc]
  apply congrFun
  apply congrArg
  have h : Split.map f (Split.sourceValue s i) = 𝟙 _ ≫ Split.map f (Split.sourceValue s i) := by
    simp
  rw [h]
  repeat rw [← Category.assoc]
  apply congrFun
  apply congrArg
  rw [Category.comp_id]
  rw [Split.indexEqToIso_inv_comp_symm_inv]
  rfl

lemma splitJoinUnitEquiv_naturality_equiv (X : WithInitial SimplexCategory)
    (i : Fin (Nat.succ (len X))) {Z Y : WithInitial SimplexCategory} (f : Z ⟶ Y) :
    (Equiv.toIso (Split.splitJoinUnitEquiv X Z i).symm).hom ∘ (CategoryStruct.comp f) =
    (homMap X i f) ∘ (Equiv.toIso (Split.splitJoinUnitEquiv X Y i).symm).hom := by
  exact Split.splitJoinUnitEquiv_naturality X i f

/-- The splitting of an object in `(WithInitial SimplexCategory)ᵒᵖ` into an object of
`(WithInitial SimplexCategory)ᵒᵖ × (WithInitial SimplexCategory)ᵒᵖ`. -/
def objOp (X : (WithInitial SimplexCategory)ᵒᵖ) (i : Fin (Nat.succ (len X.unop))) :
    (WithInitial SimplexCategory)ᵒᵖ × (WithInitial SimplexCategory)ᵒᵖ :=
  (prodOpEquiv (WithInitial SimplexCategory)).functor.obj (Opposite.op (Split.obj X.unop i))

end Split
end WithInitial


/-- This functor `SimplexCategory ⥤ Cat` sends `[n]` (for `n : ℕ`)
to the category attached to the ordered set `{0, 1, ..., n}` -/
@[simps! obj map]
def toCat : SimplexCategory ⥤ Cat.{0} :=
  SimplexCategory.skeletalFunctor ⋙ forget₂ NonemptyFinLinOrd LinOrd ⋙
      forget₂ LinOrd Lat ⋙ forget₂ Lat PartOrd ⋙
      forget₂ PartOrd Preord ⋙ preordToCat
set_option linter.uppercaseLean3 false in
#align simplex_category.to_Cat SimplexCategory.toCat

end SimplexCategory
