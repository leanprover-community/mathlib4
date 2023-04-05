/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Scott Morrison, Adam Topaz

! This file was ported from Lean 3 source module algebraic_topology.simplex_category
! leanprover-community/mathlib commit e8ac6315bcfcbaf2d19a046719c3b553206dac75
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Tactic.Linarith.Default
import Mathbin.CategoryTheory.Skeletal
import Mathbin.Data.Fintype.Sort
import Mathbin.Order.Category.NonemptyFinLinOrd
import Mathbin.CategoryTheory.Functor.ReflectsIsomorphisms

/-! # The simplex category

We construct a skeletal model of the simplex category, with objects `ℕ` and the
morphism `n ⟶ m` being the monotone maps from `fin (n+1)` to `fin (m+1)`.

We show that this category is equivalent to `NonemptyFinLinOrd`.

## Remarks

The definitions `simplex_category` and `simplex_category.hom` are marked as irreducible.

We provide the following functions to work with these objects:
1. `simplex_category.mk` creates an object of `simplex_category` out of a natural number.
  Use the notation `[n]` in the `simplicial` locale.
2. `simplex_category.len` gives the "length" of an object of `simplex_category`, as a natural.
3. `simplex_category.hom.mk` makes a morphism out of a monotone map between `fin`'s.
4. `simplex_category.hom.to_order_hom` gives the underlying monotone map associated to a
  term of `simplex_category.hom`.

-/


universe v

open CategoryTheory CategoryTheory.Limits

/- ./././Mathport/Syntax/Translate/Command.lean:318:31: unsupported: @[derive, irreducible] def -/
/-- The simplex category:
* objects are natural numbers `n : ℕ`
* morphisms from `n` to `m` are monotone functions `fin (n+1) → fin (m+1)`
-/
irreducible_def SimplexCategory :=
  ℕ
#align simplex_category SimplexCategory

namespace SimplexCategory

section

attribute [local semireducible] SimplexCategory

-- TODO: Make `mk` irreducible.
/-- Interpet a natural number as an object of the simplex category. -/
def mk (n : ℕ) : SimplexCategory :=
  n
#align simplex_category.mk SimplexCategory.mk

-- mathport name: simplex_category.mk
scoped[Simplicial] notation "[" n "]" => SimplexCategory.mk n

-- TODO: Make `len` irreducible.
/-- The length of an object of `simplex_category`. -/
def len (n : SimplexCategory) : ℕ :=
  n
#align simplex_category.len SimplexCategory.len

@[ext]
theorem ext (a b : SimplexCategory) : a.len = b.len → a = b :=
  id
#align simplex_category.ext SimplexCategory.ext

@[simp]
theorem len_mk (n : ℕ) : [n].len = n :=
  rfl
#align simplex_category.len_mk SimplexCategory.len_mk

@[simp]
theorem mk_len (n : SimplexCategory) : [n.len] = n :=
  rfl
#align simplex_category.mk_len SimplexCategory.mk_len

/-- A recursor for `simplex_category`. Use it as `induction Δ using simplex_category.rec`. -/
protected def rec {F : ∀ Δ : SimplexCategory, Sort _} (h : ∀ n : ℕ, F [n]) : ∀ X, F X := fun n =>
  h n.len
#align simplex_category.rec SimplexCategory.rec

/-- Morphisms in the simplex_category. -/
@[nolint has_nonempty_instance]
protected irreducible_def Hom (a b : SimplexCategory) :=
  Fin (a.len + 1) →o Fin (b.len + 1)
#align simplex_category.hom SimplexCategory.Hom

namespace Hom

attribute [local semireducible] SimplexCategory.Hom

/-- Make a moprhism in `simplex_category` from a monotone map of fin's. -/
def mk {a b : SimplexCategory} (f : Fin (a.len + 1) →o Fin (b.len + 1)) : SimplexCategory.Hom a b :=
  f
#align simplex_category.hom.mk SimplexCategory.Hom.mk

/-- Recover the monotone map from a morphism in the simplex category. -/
def toOrderHom {a b : SimplexCategory} (f : SimplexCategory.Hom a b) :
    Fin (a.len + 1) →o Fin (b.len + 1) :=
  f
#align simplex_category.hom.to_order_hom SimplexCategory.Hom.toOrderHom

@[ext]
theorem ext {a b : SimplexCategory} (f g : SimplexCategory.Hom a b) :
    f.toOrderHom = g.toOrderHom → f = g :=
  id
#align simplex_category.hom.ext SimplexCategory.Hom.ext

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

/-- Identity morphisms of `simplex_category`. -/
@[simp]
def id (a : SimplexCategory) : SimplexCategory.Hom a a :=
  mk OrderHom.id
#align simplex_category.hom.id SimplexCategory.Hom.id

/-- Composition of morphisms of `simplex_category`. -/
@[simp]
def comp {a b c : SimplexCategory} (f : SimplexCategory.Hom b c) (g : SimplexCategory.Hom a b) :
    SimplexCategory.Hom a c :=
  mk <| f.toOrderHom.comp g.toOrderHom
#align simplex_category.hom.comp SimplexCategory.Hom.comp

end Hom

@[simps]
instance smallCategory : SmallCategory.{0} SimplexCategory
    where
  Hom n m := SimplexCategory.Hom n m
  id m := SimplexCategory.Hom.id _
  comp _ _ _ f g := SimplexCategory.Hom.comp g f
#align simplex_category.small_category SimplexCategory.smallCategory

/-- The constant morphism from [0]. -/
def const (x : SimplexCategory) (i : Fin (x.len + 1)) : [0] ⟶ x :=
  Hom.mk <| ⟨fun _ => i, by tauto⟩
#align simplex_category.const SimplexCategory.const

@[simp]
theorem const_comp (x y : SimplexCategory) (i : Fin (x.len + 1)) (f : x ⟶ y) :
    const x i ≫ f = const y (f.toOrderHom i) :=
  rfl
#align simplex_category.const_comp SimplexCategory.const_comp

/-- Make a morphism `[n] ⟶ [m]` from a monotone map between fin's.
This is useful for constructing morphisms beetween `[n]` directly
without identifying `n` with `[n].len`.
-/
@[simp]
def mkHom {n m : ℕ} (f : Fin (n + 1) →o Fin (m + 1)) : [n] ⟶ [m] :=
  SimplexCategory.Hom.mk f
#align simplex_category.mk_hom SimplexCategory.mkHom

theorem hom_zero_zero (f : [0] ⟶ [0]) : f = 𝟙 _ :=
  by
  ext : 2
  dsimp
  apply Subsingleton.elim
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
def δ {n} (i : Fin (n + 2)) : [n] ⟶ [n + 1] :=
  mkHom (Fin.succAbove i).toOrderHom
#align simplex_category.δ SimplexCategory.δ

/-- The `i`-th degeneracy map from `[n+1]` to `[n]` -/
def σ {n} (i : Fin (n + 1)) : [n + 1] ⟶ [n] :=
  mkHom
    { toFun := Fin.predAbove i
      monotone' := Fin.predAbove_right_monotone i }
#align simplex_category.σ SimplexCategory.σ

/-- The generic case of the first simplicial identity -/
theorem δ_comp_δ {n} {i j : Fin (n + 2)} (H : i ≤ j) : δ i ≫ δ j.succ = δ j ≫ δ i.cast_succ :=
  by
  ext k
  dsimp [δ, Fin.succAbove]
  simp only [OrderEmbedding.toOrderHom_coe, OrderEmbedding.coe_ofStrictMono, Function.comp_apply,
    SimplexCategory.Hom.toOrderHom_mk, OrderHom.comp_coe]
  rcases i with ⟨i, _⟩
  rcases j with ⟨j, _⟩
  rcases k with ⟨k, _⟩
  split_ifs <;> · simp at * <;> linarith
#align simplex_category.δ_comp_δ SimplexCategory.δ_comp_δ

theorem δ_comp_δ' {n} {i : Fin (n + 2)} {j : Fin (n + 3)} (H : i.cast_succ < j) :
    δ i ≫ δ j = δ (j.pred fun hj => by simpa only [hj, Fin.not_lt_zero] using H) ≫ δ i.cast_succ :=
  by
  rw [← δ_comp_δ]
  · rw [Fin.succ_pred]
  ·
    simpa only [Fin.le_iff_val_le_val, ← Nat.lt_succ_iff, Nat.succ_eq_add_one, ← Fin.val_succ,
      j.succ_pred, Fin.lt_iff_val_lt_val] using H
#align simplex_category.δ_comp_δ' SimplexCategory.δ_comp_δ'

theorem δ_comp_δ'' {n} {i : Fin (n + 3)} {j : Fin (n + 2)} (H : i ≤ j.cast_succ) :
    δ (i.cast_lt (Nat.lt_of_le_of_lt (Fin.le_iff_val_le_val.mp H) j.is_lt)) ≫ δ j.succ =
      δ j ≫ δ i :=
  by
  rw [δ_comp_δ]
  · rfl
  · exact H
#align simplex_category.δ_comp_δ'' SimplexCategory.δ_comp_δ''

/-- The special case of the first simplicial identity -/
@[reassoc.1]
theorem δ_comp_δ_self {n} {i : Fin (n + 2)} : δ i ≫ δ i.cast_succ = δ i ≫ δ i.succ :=
  (δ_comp_δ (le_refl i)).symm
#align simplex_category.δ_comp_δ_self SimplexCategory.δ_comp_δ_self

@[reassoc.1]
theorem δ_comp_δ_self' {n} {i : Fin (n + 2)} {j : Fin (n + 3)} (H : j = i.cast_succ) :
    δ i ≫ δ j = δ i ≫ δ i.succ := by
  subst H
  rw [δ_comp_δ_self]
#align simplex_category.δ_comp_δ_self' SimplexCategory.δ_comp_δ_self'

/-- The second simplicial identity -/
@[reassoc.1]
theorem δ_comp_σ_of_le {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : i ≤ j.cast_succ) :
    δ i.cast_succ ≫ σ j.succ = σ j ≫ δ i := by
  ext k
  suffices
    ite (j.succ.cast_succ < ite (k < i) k.cast_succ k.succ) (ite (k < i) (k : ℕ) (k + 1) - 1)
        (ite (k < i) k (k + 1)) =
      ite
        ((if h : (j : ℕ) < k then
              k.pred
                (by
                  rintro rfl
                  exact Nat.not_lt_zero _ h)
            else
              k.cast_lt
                (by
                  cases j
                  cases k
                  simp only [len_mk]
                  linarith)).cast_succ <
          i)
        (ite (j.cast_succ < k) (k - 1) k) (ite (j.cast_succ < k) (k - 1) k + 1)
    by
    dsimp [δ, σ, Fin.succAbove, Fin.predAbove]
    simp [Fin.predAbove, push_cast]
    convert rfl
  rcases i with ⟨i, _⟩
  rcases j with ⟨j, _⟩
  rcases k with ⟨k, _⟩
  simp only [Fin.mk_le_mk, Fin.castSucc_mk] at H
  dsimp
  split_ifs
  -- Most of the goals can now be handled by `linarith`,
  -- but we have to deal with two of them by hand.
  pick_goal 8
  · exact (Nat.succ_pred_eq_of_pos (lt_of_le_of_lt (zero_le _) ‹_›)).symm
  pick_goal 7
  · have : k ≤ i := Nat.le_of_pred_lt ‹_›
    linarith
  -- Hope for the best from `linarith`:
  all_goals try first |rfl|simp at * <;> linarith
#align simplex_category.δ_comp_σ_of_le SimplexCategory.δ_comp_σ_of_le

/-- The first part of the third simplicial identity -/
@[reassoc.1]
theorem δ_comp_σ_self {n} {i : Fin (n + 1)} : δ i.cast_succ ≫ σ i = 𝟙 [n] :=
  by
  ext j
  suffices
    ite (Fin.castSucc i < ite (j < i) (Fin.castSucc j) j.succ) (ite (j < i) (j : ℕ) (j + 1) - 1)
        (ite (j < i) j (j + 1)) =
      j
    by
    dsimp [δ, σ, Fin.succAbove, Fin.predAbove]
    simpa [Fin.predAbove, push_cast]
  rcases i with ⟨i, _⟩
  rcases j with ⟨j, _⟩
  dsimp
  split_ifs <;> · simp at * <;> linarith
#align simplex_category.δ_comp_σ_self SimplexCategory.δ_comp_σ_self

@[reassoc.1]
theorem δ_comp_σ_self' {n} {j : Fin (n + 2)} {i : Fin (n + 1)} (H : j = i.cast_succ) :
    δ j ≫ σ i = 𝟙 [n] := by
  subst H
  rw [δ_comp_σ_self]
#align simplex_category.δ_comp_σ_self' SimplexCategory.δ_comp_σ_self'

/-- The second part of the third simplicial identity -/
@[reassoc.1]
theorem δ_comp_σ_succ {n} {i : Fin (n + 1)} : δ i.succ ≫ σ i = 𝟙 [n] :=
  by
  ext j
  rcases i with ⟨i, _⟩
  rcases j with ⟨j, _⟩
  dsimp [δ, σ, Fin.succAbove, Fin.predAbove]
  simp [Fin.predAbove, push_cast]
  split_ifs <;> · simp at * <;> linarith
#align simplex_category.δ_comp_σ_succ SimplexCategory.δ_comp_σ_succ

@[reassoc.1]
theorem δ_comp_σ_succ' {n} (j : Fin (n + 2)) (i : Fin (n + 1)) (H : j = i.succ) :
    δ j ≫ σ i = 𝟙 [n] := by
  subst H
  rw [δ_comp_σ_succ]
#align simplex_category.δ_comp_σ_succ' SimplexCategory.δ_comp_σ_succ'

/-- The fourth simplicial identity -/
@[reassoc.1]
theorem δ_comp_σ_of_gt {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : j.cast_succ < i) :
    δ i.succ ≫ σ j.cast_succ = σ j ≫ δ i := by
  ext k
  dsimp [δ, σ, Fin.succAbove, Fin.predAbove]
  rcases i with ⟨i, _⟩
  rcases j with ⟨j, _⟩
  rcases k with ⟨k, _⟩
  simp only [Fin.mk_lt_mk, Fin.castSucc_mk] at H
  suffices
    ite (_ < ite (k < i + 1) _ _) _ _ = ite _ (ite (j < k) (k - 1) k) (ite (j < k) (k - 1) k + 1) by
    simpa [apply_dite Fin.castSucc, Fin.predAbove, push_cast]
  split_ifs
  -- Most of the goals can now be handled by `linarith`,
  -- but we have to deal with three of them by hand.
  swap
  · simp only [Fin.mk_lt_mk] at h_1
    simp only [not_lt] at h_2
    simp only [self_eq_add_right, one_ne_zero]
    exact
      lt_irrefl (k - 1)
        (lt_of_lt_of_le (Nat.pred_lt (ne_of_lt (lt_of_le_of_lt (zero_le _) h_1)).symm)
          (le_trans (Nat.le_of_lt_succ h) h_2))
  pick_goal 4
  · simp only [Fin.mk_lt_mk] at h_1
    simp only [not_lt] at h
    simp only [Nat.add_succ_sub_one, add_zero]
    exfalso
    exact lt_irrefl _ (lt_of_le_of_lt (Nat.le_pred_of_lt (Nat.lt_of_succ_le h)) h_3)
  pick_goal 4
  · simp only [Fin.mk_lt_mk] at h_1
    simp only [not_lt] at h_3
    simp only [Nat.add_succ_sub_one, add_zero]
    exact (Nat.succ_pred_eq_of_pos (lt_of_le_of_lt (zero_le _) h_2)).symm
  -- Hope for the best from `linarith`:
  all_goals simp at h_1 h_2⊢ <;> linarith
#align simplex_category.δ_comp_σ_of_gt SimplexCategory.δ_comp_σ_of_gt

@[reassoc.1]
theorem δ_comp_σ_of_gt' {n} {i : Fin (n + 3)} {j : Fin (n + 2)} (H : j.succ < i) :
    δ i ≫ σ j =
      σ
          (j.cast_lt
            ((add_lt_add_iff_right 1).mp
              (lt_of_lt_of_le
                (by simpa only [[anonymous], ← Fin.val_succ] using fin.lt_iff_coe_lt_coe.mp H)
                i.is_le))) ≫
        δ (i.pred fun hi => by simpa only [Fin.not_lt_zero, hi] using H) :=
  by
  rw [← δ_comp_σ_of_gt]
  · simpa only [Fin.succ_pred]
  · rw [Fin.castSucc_cast_lt, ← Fin.succ_lt_succ_iff, Fin.succ_pred]
    exact H
#align simplex_category.δ_comp_σ_of_gt' SimplexCategory.δ_comp_σ_of_gt'

attribute [local simp] Fin.pred_mk

/-- The fifth simplicial identity -/
@[reassoc.1]
theorem σ_comp_σ {n} {i j : Fin (n + 1)} (H : i ≤ j) : σ i.cast_succ ≫ σ j = σ j.succ ≫ σ i :=
  by
  ext k
  dsimp [σ, Fin.predAbove]
  rcases i with ⟨i, _⟩
  rcases j with ⟨j, _⟩
  rcases k with ⟨k, _⟩
  simp only [Fin.mk_le_mk] at H
  -- At this point `simp with push_cast` makes good progress, but neither `simp?` nor `squeeze_simp`
  -- return usable sets of lemmas.
  -- To avoid using a non-terminal simp, we make a `suffices` statement indicating the shape
  -- of the goal we're looking for, and then use `simpa with push_cast`.
  -- I'm not sure this is actually much more robust that a non-terminal simp.
  suffices ite (_ < dite (i < k) _ _) _ _ = ite (_ < dite (j + 1 < k) _ _) _ _ by
    simpa [Fin.predAbove, push_cast]
  split_ifs
  -- `split_ifs` created 12 goals.
  -- Most of them are dealt with `by simp at *; linarith`,
  -- but we pull out two harder ones to do by hand.
  pick_goal 3
  · simp only [not_lt] at h_2
    exact
      False.elim
        (lt_irrefl (k - 1)
          (lt_of_lt_of_le (Nat.pred_lt (id (ne_of_lt (lt_of_le_of_lt (zero_le i) h)).symm))
            (le_trans h_2 (Nat.succ_le_of_lt h_1))))
  pick_goal 3
  · simp only [Subtype.mk_lt_mk, not_lt] at h_1
    exact False.elim (lt_irrefl j (lt_of_lt_of_le (Nat.pred_lt_pred (Nat.succ_ne_zero j) h_2) h_1))
  -- Deal with the rest automatically.
  all_goals simp at * <;> linarith
#align simplex_category.σ_comp_σ SimplexCategory.σ_comp_σ

end Generators

section Skeleton

/-- The functor that exhibits `simplex_category` as skeleton
of `NonemptyFinLinOrd` -/
@[simps obj map]
def skeletalFunctor : SimplexCategory ⥤ NonemptyFinLinOrdCat.{v}
    where
  obj a := NonemptyFinLinOrdCat.of <| ULift (Fin (a.len + 1))
  map a b f := ⟨fun i => ULift.up (f.toOrderHom i.down), fun i j h => f.toOrderHom.Monotone h⟩
  map_id' a := by
    ext
    simp
  map_comp' a b c f g := by
    ext
    simp
#align simplex_category.skeletal_functor SimplexCategory.skeletalFunctor

theorem skeletalFunctor.coe_map {Δ₁ Δ₂ : SimplexCategory} (f : Δ₁ ⟶ Δ₂) :
    coeFn (skeletalFunctor.{v}.map f) = ULift.up ∘ f.toOrderHom ∘ ULift.down :=
  rfl
#align simplex_category.skeletal_functor.coe_map SimplexCategory.skeletalFunctor.coe_map

theorem skeletal : Skeletal SimplexCategory := fun X Y ⟨I⟩ =>
  by
  suffices Fintype.card (Fin (X.len + 1)) = Fintype.card (Fin (Y.len + 1))
    by
    ext
    simpa
  · apply Fintype.card_congr
    refine' equiv.ulift.symm.trans (((skeletal_functor ⋙ forget _).mapIso I).toEquiv.trans _)
    apply Equiv.ulift
#align simplex_category.skeletal SimplexCategory.skeletal

namespace SkeletalFunctor

instance : Full skeletalFunctor.{v}
    where
  Preimage a b f :=
    SimplexCategory.Hom.mk ⟨fun i => (f (ULift.up i)).down, fun i j h => f.Monotone h⟩
  witness' := by
    intro m n f
    dsimp at *
    ext1 ⟨i⟩
    ext1
    ext1
    cases x
    simp

instance : Faithful skeletalFunctor.{v}
    where map_injective' m n f g h := by
    ext1; ext1; ext1 i; apply ULift.up.inj
    change (skeletal_functor.map f) ⟨i⟩ = (skeletal_functor.map g) ⟨i⟩
    rw [h]

instance : EssSurj skeletalFunctor.{v}
    where mem_essImage X :=
    ⟨mk (Fintype.card X - 1 : ℕ),
      ⟨by
        have aux : Fintype.card X = Fintype.card X - 1 + 1 :=
          (Nat.succ_pred_eq_of_pos <| fintype.card_pos_iff.mpr ⟨⊥⟩).symm
        let f := monoEquivOfFin X aux
        have hf := (finset.univ.order_emb_of_fin aux).StrictMono
        refine'
          { Hom := ⟨fun i => f i.down, _⟩
            inv := ⟨fun i => ⟨f.symm i⟩, _⟩
            hom_inv_id' := _
            inv_hom_id' := _ }
        · rintro ⟨i⟩ ⟨j⟩ h
          show f i ≤ f j
          exact hf.monotone h
        · intro i j h
          show f.symm i ≤ f.symm j
          rw [← hf.le_iff_le]
          show f (f.symm i) ≤ f (f.symm j)
          simpa only [OrderIso.apply_symm_apply]
        · ext1
          ext1 ⟨i⟩
          ext1
          exact f.symm_apply_apply i
        · ext1
          ext1 i
          exact f.apply_symm_apply i⟩⟩

noncomputable instance isEquivalence : IsEquivalence skeletalFunctor.{v} :=
  Equivalence.ofFullyFaithfullyEssSurj skeletalFunctor
#align simplex_category.skeletal_functor.is_equivalence SimplexCategory.skeletalFunctor.isEquivalence

end SkeletalFunctor

/-- The equivalence that exhibits `simplex_category` as skeleton
of `NonemptyFinLinOrd` -/
noncomputable def skeletalEquivalence : SimplexCategory ≌ NonemptyFinLinOrdCat.{v} :=
  Functor.asEquivalence skeletalFunctor
#align simplex_category.skeletal_equivalence SimplexCategory.skeletalEquivalence

end Skeleton

/-- `simplex_category` is a skeleton of `NonemptyFinLinOrd`.
-/
noncomputable def isSkeletonOf :
    IsSkeletonOf NonemptyFinLinOrdCat SimplexCategory skeletalFunctor.{v}
    where
  skel := skeletal
  eqv := skeletalFunctor.isEquivalence
#align simplex_category.is_skeleton_of SimplexCategory.isSkeletonOf

/-- The truncated simplex category. -/
def Truncated (n : ℕ) :=
  FullSubcategory fun a : SimplexCategory => a.len ≤ n deriving SmallCategory
#align simplex_category.truncated SimplexCategory.Truncated

namespace Truncated

instance {n} : Inhabited (Truncated n) :=
  ⟨⟨[0], by simp⟩⟩

/-- The fully faithful inclusion of the truncated simplex category into the usual
simplex category.
-/
def inclusion {n : ℕ} : SimplexCategory.Truncated n ⥤ SimplexCategory :=
  fullSubcategoryInclusion _ deriving Full, Faithful
#align simplex_category.truncated.inclusion SimplexCategory.Truncated.inclusion

end Truncated

section Concrete

instance : ConcreteCategory.{0} SimplexCategory
    where
  forget :=
    { obj := fun i => Fin (i.len + 1)
      map := fun i j f => f.toOrderHom }
  forget_faithful := { }

end Concrete

section EpiMono

/-- A morphism in `simplex_category` is a monomorphism precisely when it is an injective function
-/
theorem mono_iff_injective {n m : SimplexCategory} {f : n ⟶ m} :
    Mono f ↔ Function.Injective f.toOrderHom :=
  by
  rw [← functor.mono_map_iff_mono skeletal_equivalence.Functor]
  dsimp only [skeletal_equivalence, functor.as_equivalence_functor]
  rw [NonemptyFinLinOrdCat.mono_iff_injective, skeletal_functor.coe_map,
    Function.Injective.of_comp_iff ULift.up_injective,
    Function.Injective.of_comp_iff' _ ULift.down_bijective]
#align simplex_category.mono_iff_injective SimplexCategory.mono_iff_injective

/-- A morphism in `simplex_category` is an epimorphism if and only if it is a surjective function
-/
theorem epi_iff_surjective {n m : SimplexCategory} {f : n ⟶ m} :
    Epi f ↔ Function.Surjective f.toOrderHom :=
  by
  rw [← functor.epi_map_iff_epi skeletal_equivalence.Functor]
  dsimp only [skeletal_equivalence, functor.as_equivalence_functor]
  rw [NonemptyFinLinOrdCat.epi_iff_surjective, skeletal_functor.coe_map,
    Function.Surjective.of_comp_iff' ULift.up_bijective,
    Function.Surjective.of_comp_iff _ ULift.down_surjective]
#align simplex_category.epi_iff_surjective SimplexCategory.epi_iff_surjective

/-- A monomorphism in `simplex_category` must increase lengths-/
theorem len_le_of_mono {x y : SimplexCategory} {f : x ⟶ y} : Mono f → x.len ≤ y.len :=
  by
  intro hyp_f_mono
  have f_inj : Function.Injective f.to_order_hom.to_fun := mono_iff_injective.elim_left hyp_f_mono
  simpa using Fintype.card_le_of_injective f.to_order_hom.to_fun f_inj
#align simplex_category.len_le_of_mono SimplexCategory.len_le_of_mono

theorem le_of_mono {n m : ℕ} {f : [n] ⟶ [m]} : CategoryTheory.Mono f → n ≤ m :=
  len_le_of_mono
#align simplex_category.le_of_mono SimplexCategory.le_of_mono

/-- An epimorphism in `simplex_category` must decrease lengths-/
theorem len_le_of_epi {x y : SimplexCategory} {f : x ⟶ y} : Epi f → y.len ≤ x.len :=
  by
  intro hyp_f_epi
  have f_surj : Function.Surjective f.to_order_hom.to_fun := epi_iff_surjective.elim_left hyp_f_epi
  simpa using Fintype.card_le_of_surjective f.to_order_hom.to_fun f_surj
#align simplex_category.len_le_of_epi SimplexCategory.len_le_of_epi

theorem le_of_epi {n m : ℕ} {f : [n] ⟶ [m]} : Epi f → m ≤ n :=
  len_le_of_epi
#align simplex_category.le_of_epi SimplexCategory.le_of_epi

instance {n : ℕ} {i : Fin (n + 2)} : Mono (δ i) :=
  by
  rw [mono_iff_injective]
  exact Fin.succAbove_right_injective

instance {n : ℕ} {i : Fin (n + 1)} : Epi (σ i) :=
  by
  rw [epi_iff_surjective]
  intro b
  simp only [σ, mk_hom, hom.to_order_hom_mk, OrderHom.coe_fun_mk]
  by_cases b ≤ i
  · use b
    rw [Fin.predAbove_below i b (by simpa only [Fin.coe_eq_castSucc] using h)]
    simp only [Fin.coe_eq_castSucc, Fin.castPred_castSucc]
  · use b.succ
    rw [Fin.predAbove_above i b.succ _, Fin.pred_succ]
    rw [not_le] at h
    rw [Fin.lt_iff_val_lt_val] at h⊢
    simpa only [Fin.val_succ, Fin.coe_castSucc] using Nat.lt.step h

instance : ReflectsIsomorphisms (forget SimplexCategory) :=
  ⟨by
    intro x y f
    intro
    exact
      is_iso.of_iso
        { Hom := f
          inv :=
            hom.mk
              { toFun := inv ((forget SimplexCategory).map f)
                monotone' := fun y₁ y₂ h => by
                  by_cases h' : y₁ < y₂
                  · by_contra h''
                    have eq := fun i => congr_hom (iso.inv_hom_id (as_iso ((forget _).map f))) i
                    have ineq := f.to_order_hom.monotone' (le_of_not_ge h'')
                    dsimp at ineq
                    erw [Eq, Eq] at ineq
                    exact not_le.mpr h' ineq
                  · rw [eq_of_le_of_not_lt h h'] }
          hom_inv_id' := by
            ext1
            ext1
            exact iso.hom_inv_id (as_iso ((forget _).map f))
          inv_hom_id' := by
            ext1
            ext1
            exact iso.inv_hom_id (as_iso ((forget _).map f)) }⟩

theorem isIso_of_bijective {x y : SimplexCategory} {f : x ⟶ y}
    (hf : Function.Bijective f.toOrderHom.toFun) : IsIso f :=
  haveI : is_iso ((forget SimplexCategory).map f) := (is_iso_iff_bijective _).mpr hf
  is_iso_of_reflects_iso f (forget SimplexCategory)
#align simplex_category.is_iso_of_bijective SimplexCategory.isIso_of_bijective

/-- An isomorphism in `simplex_category` induces an `order_iso`. -/
@[simp]
def orderIsoOfIso {x y : SimplexCategory} (e : x ≅ y) : Fin (x.len + 1) ≃o Fin (y.len + 1) :=
  Equiv.toOrderIso
    { toFun := e.Hom.toOrderHom
      invFun := e.inv.toOrderHom
      left_inv := fun i => by
        simpa only using congr_arg (fun φ => (hom.to_order_hom φ) i) e.hom_inv_id'
      right_inv := fun i => by
        simpa only using congr_arg (fun φ => (hom.to_order_hom φ) i) e.inv_hom_id' }
    e.Hom.toOrderHom.Monotone e.inv.toOrderHom.Monotone
#align simplex_category.order_iso_of_iso SimplexCategory.orderIsoOfIso

theorem iso_eq_iso_refl {x : SimplexCategory} (e : x ≅ x) : e = Iso.refl x :=
  by
  have h : (Finset.univ : Finset (Fin (x.len + 1))).card = x.len + 1 := Finset.card_fin (x.len + 1)
  have eq₁ := Finset.orderEmbOfFin_unique' h fun i => Finset.mem_univ ((order_iso_of_iso e) i)
  have eq₂ :=
    Finset.orderEmbOfFin_unique' h fun i => Finset.mem_univ ((order_iso_of_iso (iso.refl x)) i)
  ext1; ext1
  convert congr_arg (fun φ => OrderEmbedding.toOrderHom φ) (eq₁.trans eq₂.symm)
  ext1; ext1 i
  rfl
#align simplex_category.iso_eq_iso_refl SimplexCategory.iso_eq_iso_refl

theorem eq_id_of_isIso {x : SimplexCategory} (f : x ⟶ x) [hf : IsIso f] : f = 𝟙 _ :=
  congr_arg (fun φ : _ ≅ _ => φ.Hom) (iso_eq_iso_refl (asIso f))
#align simplex_category.eq_id_of_is_iso SimplexCategory.eq_id_of_isIso

theorem eq_σ_comp_of_not_injective' {n : ℕ} {Δ' : SimplexCategory} (θ : mk (n + 1) ⟶ Δ')
    (i : Fin (n + 1)) (hi : θ.toOrderHom i.cast_succ = θ.toOrderHom i.succ) :
    ∃ θ' : mk n ⟶ Δ', θ = σ i ≫ θ' := by
  use δ i.succ ≫ θ
  ext1; ext1; ext1 x
  simp only [hom.to_order_hom_mk, Function.comp_apply, OrderHom.comp_coe, hom.comp,
    small_category_comp, σ, mk_hom, OrderHom.coe_fun_mk]
  by_cases h' : x ≤ i.cast_succ
  · rw [Fin.predAbove_below i x h']
    have eq := Fin.castSucc_castPred (gt_of_gt_of_ge (Fin.castSucc_lt_last i) h')
    erw [Fin.succAbove_below i.succ x.cast_pred _]
    swap
    · rwa [Eq, ← Fin.le_castSucc_iff]
    rw [Eq]
  · simp only [not_le] at h'
    let y :=
      x.pred
        (by
          intro h
          rw [h] at h'
          simpa only [Fin.lt_iff_val_lt_val, Nat.not_lt_zero, Fin.val_zero] using h')
    simp only [show x = y.succ by rw [Fin.succ_pred]] at h'⊢
    rw [Fin.predAbove_above i y.succ h', Fin.pred_succ]
    by_cases h'' : y = i
    · rw [h'']
      convert hi.symm
      erw [Fin.succAbove_below i.succ _]
      exact Fin.lt_succ
    · erw [Fin.succAbove_above i.succ _]
      simp only [Fin.lt_iff_val_lt_val, Fin.le_iff_val_le_val, Fin.val_succ, Fin.coe_castSucc,
        Nat.lt_succ_iff, Fin.ext_iff] at h' h''⊢
      cases' Nat.le.dest h' with c hc
      cases c
      · exfalso
        rw [add_zero] at hc
        rw [hc] at h''
        exact h'' rfl
      · rw [← hc]
        simp only [add_le_add_iff_left, Nat.succ_eq_add_one, le_add_iff_nonneg_left, zero_le]
#align simplex_category.eq_σ_comp_of_not_injective' SimplexCategory.eq_σ_comp_of_not_injective'

theorem eq_σ_comp_of_not_injective {n : ℕ} {Δ' : SimplexCategory} (θ : mk (n + 1) ⟶ Δ')
    (hθ : ¬Function.Injective θ.toOrderHom) : ∃ (i : Fin (n + 1))(θ' : mk n ⟶ Δ'), θ = σ i ≫ θ' :=
  by
  simp only [Function.Injective, exists_prop, not_forall] at hθ
  -- as θ is not injective, there exists `x<y` such that `θ x = θ y`
  -- and then, `θ x = θ (x+1)`
  have hθ₂ : ∃ x y : Fin (n + 2), (hom.to_order_hom θ) x = (hom.to_order_hom θ) y ∧ x < y :=
    by
    rcases hθ with ⟨x, y, ⟨h₁, h₂⟩⟩
    by_cases x < y
    · exact ⟨x, y, ⟨h₁, h⟩⟩
    · refine' ⟨y, x, ⟨h₁.symm, _⟩⟩
      cases' lt_or_eq_of_le (not_lt.mp h) with h' h'
      · exact h'
      · exfalso
        exact h₂ h'.symm
  rcases hθ₂ with ⟨x, y, ⟨h₁, h₂⟩⟩
  let z := x.cast_pred
  use z
  simp only [←
    show z.cast_succ = x from Fin.castSucc_castPred (lt_of_lt_of_le h₂ (Fin.le_last y))] at h₁ h₂
  apply eq_σ_comp_of_not_injective'
  rw [Fin.castSucc_lt_iff_succ_le] at h₂
  apply le_antisymm
  · exact θ.to_order_hom.monotone (le_of_lt (Fin.castSucc_lt_succ z))
  · rw [h₁]
    exact θ.to_order_hom.monotone h₂
#align simplex_category.eq_σ_comp_of_not_injective SimplexCategory.eq_σ_comp_of_not_injective

theorem eq_comp_δ_of_not_surjective' {n : ℕ} {Δ : SimplexCategory} (θ : Δ ⟶ mk (n + 1))
    (i : Fin (n + 2)) (hi : ∀ x, θ.toOrderHom x ≠ i) : ∃ θ' : Δ ⟶ mk n, θ = θ' ≫ δ i :=
  by
  by_cases i < Fin.last (n + 1)
  · use θ ≫ σ (Fin.castPred i)
    ext1
    ext1
    ext1 x
    simp only [hom.to_order_hom_mk, Function.comp_apply, OrderHom.comp_coe, hom.comp,
      small_category_comp]
    by_cases h' : θ.to_order_hom x ≤ i
    · simp only [σ, mk_hom, hom.to_order_hom_mk, OrderHom.coe_fun_mk]
      rw [Fin.predAbove_below (Fin.castPred i) (θ.to_order_hom x)
          (by simpa [Fin.castSucc_castPred h] using h')]
      erw [Fin.succAbove_below i]
      swap
      · simp only [Fin.lt_iff_val_lt_val, Fin.coe_castSucc]
        exact
          lt_of_le_of_lt (Fin.coe_castPred_le_self _)
            (fin.lt_iff_coe_lt_coe.mp ((Ne.le_iff_lt (hi x)).mp h'))
      rw [Fin.castSucc_castPred]
      apply lt_of_le_of_lt h' h
    · simp only [not_le] at h'
      simp only [σ, mk_hom, hom.to_order_hom_mk, OrderHom.coe_fun_mk,
        Fin.predAbove_above (Fin.castPred i) (θ.to_order_hom x)
          (by simpa only [Fin.castSucc_castPred h] using h')]
      erw [Fin.succAbove_above i _, Fin.succ_pred]
      simpa only [Fin.le_iff_val_le_val, Fin.coe_castSucc, Fin.coe_pred] using
        Nat.le_pred_of_lt (fin.lt_iff_coe_lt_coe.mp h')
  · obtain rfl := le_antisymm (Fin.le_last i) (not_lt.mp h)
    use θ ≫ σ (Fin.last _)
    ext1
    ext1
    ext1 x
    simp only [hom.to_order_hom_mk, Function.comp_apply, OrderHom.comp_coe, hom.comp,
      small_category_comp, σ, δ, mk_hom, OrderHom.coe_fun_mk, OrderEmbedding.toOrderHom_coe,
      Fin.predAbove_last, Fin.succAbove_last,
      Fin.castSucc_castPred ((Ne.le_iff_lt (hi x)).mp (Fin.le_last _))]
#align simplex_category.eq_comp_δ_of_not_surjective' SimplexCategory.eq_comp_δ_of_not_surjective'

theorem eq_comp_δ_of_not_surjective {n : ℕ} {Δ : SimplexCategory} (θ : Δ ⟶ mk (n + 1))
    (hθ : ¬Function.Surjective θ.toOrderHom) : ∃ (i : Fin (n + 2))(θ' : Δ ⟶ mk n), θ = θ' ≫ δ i :=
  by
  cases' not_forall.mp hθ with i hi
  use i
  exact eq_comp_δ_of_not_surjective' θ i (not_exists.mp hi)
#align simplex_category.eq_comp_δ_of_not_surjective SimplexCategory.eq_comp_δ_of_not_surjective

theorem eq_id_of_mono {x : SimplexCategory} (i : x ⟶ x) [Mono i] : i = 𝟙 _ :=
  by
  suffices is_iso i by
    haveI := this
    apply eq_id_of_is_iso
  apply is_iso_of_bijective
  dsimp
  rw [Fintype.bijective_iff_injective_and_card i.to_order_hom, ← mono_iff_injective,
    eq_self_iff_true, and_true_iff]
  infer_instance
#align simplex_category.eq_id_of_mono SimplexCategory.eq_id_of_mono

theorem eq_id_of_epi {x : SimplexCategory} (i : x ⟶ x) [Epi i] : i = 𝟙 _ :=
  by
  suffices is_iso i by
    haveI := this
    apply eq_id_of_is_iso
  apply is_iso_of_bijective
  dsimp
  rw [Fintype.bijective_iff_surjective_and_card i.to_order_hom, ← epi_iff_surjective,
    eq_self_iff_true, and_true_iff]
  infer_instance
#align simplex_category.eq_id_of_epi SimplexCategory.eq_id_of_epi

theorem eq_σ_of_epi {n : ℕ} (θ : mk (n + 1) ⟶ mk n) [Epi θ] : ∃ i : Fin (n + 1), θ = σ i :=
  by
  rcases eq_σ_comp_of_not_injective θ _ with ⟨i, θ', h⟩; swap
  · by_contra
    simpa only [Nat.one_ne_zero, add_le_iff_nonpos_right, nonpos_iff_eq_zero] using
      le_of_mono (mono_iff_injective.mpr h)
  use i
  haveI : epi (σ i ≫ θ') := by
    rw [← h]
    infer_instance
  haveI := CategoryTheory.epi_of_epi (σ i) θ'
  rw [h, eq_id_of_epi θ', category.comp_id]
#align simplex_category.eq_σ_of_epi SimplexCategory.eq_σ_of_epi

theorem eq_δ_of_mono {n : ℕ} (θ : mk n ⟶ mk (n + 1)) [Mono θ] : ∃ i : Fin (n + 2), θ = δ i :=
  by
  rcases eq_comp_δ_of_not_surjective θ _ with ⟨i, θ', h⟩; swap
  · by_contra
    simpa only [add_le_iff_nonpos_right, nonpos_iff_eq_zero] using
      le_of_epi (epi_iff_surjective.mpr h)
  use i
  haveI : mono (θ' ≫ δ i) := by
    rw [← h]
    infer_instance
  haveI := CategoryTheory.mono_of_mono θ' (δ i)
  rw [h, eq_id_of_mono θ', category.id_comp]
#align simplex_category.eq_δ_of_mono SimplexCategory.eq_δ_of_mono

theorem len_lt_of_mono {Δ' Δ : SimplexCategory} (i : Δ' ⟶ Δ) [hi : Mono i] (hi' : Δ ≠ Δ') :
    Δ'.len < Δ.len := by
  cases lt_or_eq_of_le (len_le_of_mono hi)
  · exact h
  · exfalso
    exact
      hi'
        (by
          ext
          exact h.symm)
#align simplex_category.len_lt_of_mono SimplexCategory.len_lt_of_mono

noncomputable instance : SplitEpiCategory SimplexCategory :=
  skeletalEquivalence.{0}.inverse.splitEpiCategoryImpOfIsEquivalence

instance : HasStrongEpiMonoFactorisations SimplexCategory :=
  Functor.hasStrongEpiMonoFactorisations_imp_of_isEquivalence
    SimplexCategory.skeletalEquivalence.{0}.inverse

instance : HasStrongEpiImages SimplexCategory :=
  Limits.hasStrongEpiImages_of_hasStrongEpiMonoFactorisations

instance (Δ Δ' : SimplexCategory) (θ : Δ ⟶ Δ') : Epi (factorThruImage θ) :=
  StrongEpi.epi

theorem image_eq {Δ Δ' Δ'' : SimplexCategory} {φ : Δ ⟶ Δ''} {e : Δ ⟶ Δ'} [Epi e] {i : Δ' ⟶ Δ''}
    [Mono i] (fac : e ≫ i = φ) : image φ = Δ' :=
  by
  haveI := strong_epi_of_epi e
  let e := image.iso_strong_epi_mono e i fac
  ext
  exact
    le_antisymm (len_le_of_epi (inferInstance : epi e.hom))
      (len_le_of_mono (inferInstance : mono e.hom))
#align simplex_category.image_eq SimplexCategory.image_eq

theorem image_ι_eq {Δ Δ'' : SimplexCategory} {φ : Δ ⟶ Δ''} {e : Δ ⟶ image φ} [Epi e]
    {i : image φ ⟶ Δ''} [Mono i] (fac : e ≫ i = φ) : image.ι φ = i :=
  by
  haveI := strong_epi_of_epi e
  rw [← image.iso_strong_epi_mono_hom_comp_ι e i fac,
    SimplexCategory.eq_id_of_isIso (image.iso_strong_epi_mono e i fac).Hom, category.id_comp]
#align simplex_category.image_ι_eq SimplexCategory.image_ι_eq

theorem factorThruImage_eq {Δ Δ'' : SimplexCategory} {φ : Δ ⟶ Δ''} {e : Δ ⟶ image φ} [Epi e]
    {i : image φ ⟶ Δ''} [Mono i] (fac : e ≫ i = φ) : factorThruImage φ = e := by
  rw [← cancel_mono i, fac, ← image_ι_eq fac, image.fac]
#align simplex_category.factor_thru_image_eq SimplexCategory.factorThruImage_eq

end EpiMono

/-- This functor `simplex_category ⥤ Cat` sends `[n]` (for `n : ℕ`)
to the category attached to the ordered set `{0, 1, ..., n}` -/
@[simps obj map]
def toCat : SimplexCategory ⥤ Cat.{0} :=
  SimplexCategory.skeletalFunctor ⋙
    forget₂ NonemptyFinLinOrdCat LinOrd ⋙
      forget₂ LinOrd Lat ⋙ forget₂ Lat PartOrd ⋙ forget₂ PartOrd PreordCat ⋙ preordCatToCat
#align simplex_category.to_Cat SimplexCategory.toCat

end SimplexCategory

