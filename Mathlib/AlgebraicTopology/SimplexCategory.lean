/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Scott Morrison, Adam Topaz
-/
import Mathlib.Tactic.Linarith
import Mathlib.CategoryTheory.Skeletal
import Mathlib.Data.Fintype.Sort
import Mathlib.Order.Category.NonemptyFinLinOrdCat
import Mathlib.CategoryTheory.Functor.ReflectsIso

#align_import algebraic_topology.simplex_category from "leanprover-community/mathlib"@"e8ac6315bcfcbaf2d19a046719c3b553206dac75"

/-! # The simplex category

We construct a skeletal model of the simplex category, with objects `ℕ` and the
morphism `n ⟶ m` being the monotone maps from `Fin (n+1)` to `Fin (m+1)`.

We show that this category is equivalent to `NonemptyFinLinOrdCat`.

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
protected def rec {F : ∀ _ : SimplexCategory, Sort*} (h : ∀ n : ℕ, F [n]) : ∀ X, F X := fun n =>
  h n.len
#align simplex_category.rec SimplexCategory.rec

-- porting note: removed @[nolint has_nonempty_instance]
/-- Morphisms in the `SimplexCategory`. -/
protected def Hom (a b : SimplexCategory) :=
  Fin (a.len + 1) →o Fin (b.len + 1)
#align simplex_category.hom SimplexCategory.Hom

namespace Hom

/-- Make a moprhism in `SimplexCategory` from a monotone map of `Fin`'s. -/
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
                            -- 🎉 no goals
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
  -- ⊢ ↑(Hom.toOrderHom f) x✝ = ↑(Hom.toOrderHom (𝟙 [0])) x✝
  apply @Subsingleton.elim (Fin 1)
  -- 🎉 no goals
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
  -- ⊢ ↑(↑(Hom.toOrderHom (δ i ≫ δ (Fin.succ j))) k) = ↑(↑(Hom.toOrderHom (δ j ≫ δ  …
  dsimp [δ, Fin.succAbove]
  -- ⊢ ↑(if ↑(if ↑k < ↑i then Fin.castSucc k else Fin.succ k) < ↑(Fin.succ j) then  …
  rcases i with ⟨i, _⟩
  -- ⊢ ↑(if ↑(if ↑k < ↑{ val := i, isLt := isLt✝ } then Fin.castSucc k else Fin.suc …
  rcases j with ⟨j, _⟩
  -- ⊢ ↑(if ↑(if ↑k < ↑{ val := i, isLt := isLt✝¹ } then Fin.castSucc k else Fin.su …
  rcases k with ⟨k, _⟩
  -- ⊢ ↑(if ↑(if ↑{ val := k, isLt := isLt✝ } < ↑{ val := i, isLt := isLt✝² } then  …
  split_ifs <;> · simp at * <;> linarith
                  -- 🎉 no goals
                  -- ⊢ False
                                -- 🎉 no goals
                  -- ⊢ False
                                -- 🎉 no goals
                  -- ⊢ k = k + 1 + 1
                                -- 🎉 no goals
                  -- ⊢ False
                                -- 🎉 no goals
                  -- 🎉 no goals
                  -- 🎉 no goals
                  -- ⊢ False
                                -- 🎉 no goals
                  -- ⊢ False
                                -- 🎉 no goals
                  -- 🎉 no goals
                  -- 🎉 no goals
                  -- ⊢ False
                                -- 🎉 no goals
                  -- ⊢ k + 1 + 1 = k
                                -- 🎉 no goals
                  -- ⊢ False
                                -- 🎉 no goals
                  -- ⊢ False
                                -- 🎉 no goals
                  -- 🎉 no goals
#align simplex_category.δ_comp_δ SimplexCategory.δ_comp_δ

theorem δ_comp_δ' {n} {i : Fin (n + 2)} {j : Fin (n + 3)} (H : Fin.castSucc i < j) :
    δ i ≫ δ j =
      δ (j.pred <| fun (hj : j = 0) => by simp [hj, Fin.not_lt_zero] at H) ≫
                                          -- 🎉 no goals
        δ (Fin.castSucc i) := by
  rw [← δ_comp_δ]
  -- ⊢ δ i ≫ δ j = δ i ≫ δ (Fin.succ (Fin.pred j (_ : j = 0 → False)))
  · rw [Fin.succ_pred]
    -- 🎉 no goals
  · simpa only [Fin.le_iff_val_le_val, ← Nat.lt_succ_iff, Nat.succ_eq_add_one, ← Fin.val_succ,
      j.succ_pred, Fin.lt_iff_val_lt_val] using H
#align simplex_category.δ_comp_δ' SimplexCategory.δ_comp_δ'

theorem δ_comp_δ'' {n} {i : Fin (n + 3)} {j : Fin (n + 2)} (H : i ≤ Fin.castSucc j) :
    δ (i.castLT (Nat.lt_of_le_of_lt (Fin.le_iff_val_le_val.mp H) j.is_lt)) ≫ δ j.succ =
      δ j ≫ δ i := by
  rw [δ_comp_δ]
  -- ⊢ δ j ≫ δ (Fin.castSucc (Fin.castLT i (_ : ↑i < n + 2))) = δ j ≫ δ i
  · rfl
    -- 🎉 no goals
  · exact H
    -- 🎉 no goals
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
  -- ⊢ δ i ≫ δ (Fin.castSucc i) = δ i ≫ δ (Fin.succ i)
  rw [δ_comp_δ_self]
  -- 🎉 no goals
#align simplex_category.δ_comp_δ_self' SimplexCategory.δ_comp_δ_self'

/-- The second simplicial identity -/
@[reassoc]
theorem δ_comp_σ_of_le {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : i ≤ Fin.castSucc j) :
    δ (Fin.castSucc i) ≫ σ j.succ = σ j ≫ δ i := by
  rcases i with ⟨i, hi⟩
  -- ⊢ δ (Fin.castSucc { val := i, isLt := hi }) ≫ σ (Fin.succ j) = σ j ≫ δ { val : …
  rcases j with ⟨j, hj⟩
  -- ⊢ δ (Fin.castSucc { val := i, isLt := hi }) ≫ σ (Fin.succ { val := j, isLt :=  …
  ext ⟨k, hk⟩
  -- ⊢ ↑(↑(Hom.toOrderHom (δ (Fin.castSucc { val := i, isLt := hi }) ≫ σ (Fin.succ  …
  simp at H hk
  -- ⊢ ↑(↑(Hom.toOrderHom (δ (Fin.castSucc { val := i, isLt := hi }) ≫ σ (Fin.succ  …
  dsimp [σ, δ, Fin.predAbove, Fin.succAbove]
  -- ⊢ ↑(if h : { val := j + 1, isLt := (_ : j + 1 < Nat.succ (n + 1 + 1)) } < if k …
  simp [Fin.lt_iff_val_lt_val, Fin.ite_val, Fin.dite_val]
  -- ⊢ (if j + 1 < if k < i then k else k + 1 then (if k < i then k else k + 1) - 1 …
  split_ifs
  all_goals try simp <;> linarith
  all_goals cases k <;> simp at * <;> linarith
  -- 🎉 no goals
#align simplex_category.δ_comp_σ_of_le SimplexCategory.δ_comp_σ_of_le

/-- The first part of the third simplicial identity -/
@[reassoc]
theorem δ_comp_σ_self {n} {i : Fin (n + 1)} :
    δ (Fin.castSucc i) ≫ σ i = 𝟙 ([n] : SimplexCategory) := by
  rcases i with ⟨i, hi⟩
  -- ⊢ δ (Fin.castSucc { val := i, isLt := hi }) ≫ σ { val := i, isLt := hi } = 𝟙 [n]
  ext ⟨j, hj⟩
  -- ⊢ ↑(↑(Hom.toOrderHom (δ (Fin.castSucc { val := i, isLt := hi }) ≫ σ { val := i …
  simp at hj
  -- ⊢ ↑(↑(Hom.toOrderHom (δ (Fin.castSucc { val := i, isLt := hi }) ≫ σ { val := i …
  dsimp [σ, δ, Fin.predAbove, Fin.succAbove]
  -- ⊢ ↑(if h : { val := i, isLt := (_ : i < Nat.succ (n + 1)) } < if j < i then {  …
  simp [Fin.lt_iff_val_lt_val, Fin.ite_val, Fin.dite_val]
  -- ⊢ (if i < if j < i then j else j + 1 then (if j < i then j else j + 1) - 1 els …
  split_ifs
  any_goals simp
  -- ⊢ j - 1 = j
  all_goals linarith
  -- 🎉 no goals
#align simplex_category.δ_comp_σ_self SimplexCategory.δ_comp_σ_self

@[reassoc]
theorem δ_comp_σ_self' {n} {j : Fin (n + 2)} {i : Fin (n + 1)} (H : j = Fin.castSucc i) :
    δ j ≫ σ i = 𝟙 ([n] : SimplexCategory) := by
  subst H
  -- ⊢ δ (Fin.castSucc i) ≫ σ i = 𝟙 [n]
  rw [δ_comp_σ_self]
  -- 🎉 no goals
#align simplex_category.δ_comp_σ_self' SimplexCategory.δ_comp_σ_self'

/-- The second part of the third simplicial identity -/
@[reassoc]
theorem δ_comp_σ_succ {n} {i : Fin (n + 1)} : δ i.succ ≫ σ i = 𝟙 ([n] : SimplexCategory) := by
  ext j
  -- ⊢ ↑(↑(Hom.toOrderHom (δ (Fin.succ i) ≫ σ i)) j) = ↑(↑(Hom.toOrderHom (𝟙 [n])) j)
  rcases i with ⟨i, _⟩
  -- ⊢ ↑(↑(Hom.toOrderHom (δ (Fin.succ { val := i, isLt := isLt✝ }) ≫ σ { val := i, …
  rcases j with ⟨j, _⟩
  -- ⊢ ↑(↑(Hom.toOrderHom (δ (Fin.succ { val := i, isLt := isLt✝¹ }) ≫ σ { val := i …
  dsimp [δ, σ, Fin.succAbove, Fin.predAbove]
  -- ⊢ ↑(if h : { val := i, isLt := (_ : i < Nat.succ (n + 1)) } < if j < i + 1 the …
  split_ifs <;> simp <;> simp at * <;> linarith
                -- ⊢ j - 1 = j
                -- 🎉 no goals
                -- 🎉 no goals
                -- ⊢ False
                         -- ⊢ j - 1 = j
                         -- ⊢ False
                                       -- 🎉 no goals
                                       -- 🎉 no goals
#align simplex_category.δ_comp_σ_succ SimplexCategory.δ_comp_σ_succ

@[reassoc]
theorem δ_comp_σ_succ' {n} (j : Fin (n + 2)) (i : Fin (n + 1)) (H : j = i.succ) :
    δ j ≫ σ i = 𝟙 ([n] : SimplexCategory) := by
  subst H
  -- ⊢ δ (Fin.succ i) ≫ σ i = 𝟙 [n]
  rw [δ_comp_σ_succ]
  -- 🎉 no goals
#align simplex_category.δ_comp_σ_succ' SimplexCategory.δ_comp_σ_succ'

/-- The fourth simplicial identity -/
@[reassoc]
theorem δ_comp_σ_of_gt {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : Fin.castSucc j < i) :
    δ i.succ ≫ σ (Fin.castSucc j) = σ j ≫ δ i := by
  ext ⟨k, hk⟩
  -- ⊢ ↑(↑(Hom.toOrderHom (δ (Fin.succ i) ≫ σ (Fin.castSucc j))) { val := k, isLt : …
  rcases i with ⟨i, hi⟩
  -- ⊢ ↑(↑(Hom.toOrderHom (δ (Fin.succ { val := i, isLt := hi }) ≫ σ (Fin.castSucc  …
  rcases j with ⟨j, hj⟩
  -- ⊢ ↑(↑(Hom.toOrderHom (δ (Fin.succ { val := i, isLt := hi }) ≫ σ (Fin.castSucc  …
  simp at H hk
  -- ⊢ ↑(↑(Hom.toOrderHom (δ (Fin.succ { val := i, isLt := hi }) ≫ σ (Fin.castSucc  …
  dsimp [δ, σ, Fin.predAbove, Fin.succAbove]
  -- ⊢ ↑(if h : { val := j, isLt := (_ : j < Nat.succ (n + 1 + 1)) } < if k < i + 1 …
  simp [Fin.lt_iff_val_lt_val, Fin.ite_val, Fin.dite_val]
  -- ⊢ (if j < if k < i + 1 then k else k + 1 then (if k < i + 1 then k else k + 1) …
  split_ifs
  all_goals try simp <;> linarith
  all_goals cases k <;> simp at * <;> linarith
  -- 🎉 no goals
#align simplex_category.δ_comp_σ_of_gt SimplexCategory.δ_comp_σ_of_gt

@[reassoc]
theorem δ_comp_σ_of_gt' {n} {i : Fin (n + 3)} {j : Fin (n + 2)} (H : j.succ < i) :
    δ i ≫ σ j = σ (j.castLT ((add_lt_add_iff_right 1).mp (lt_of_lt_of_le H i.is_le))) ≫
      δ (i.pred <| fun (hi : i = 0) => by simp only [Fin.not_lt_zero, hi] at H) := by
                                          -- 🎉 no goals
  rw [← δ_comp_σ_of_gt]
  -- ⊢ δ i ≫ σ j = δ (Fin.succ (Fin.pred i (_ : i = 0 → False))) ≫ σ (Fin.castSucc  …
  · simp
    -- 🎉 no goals
  · rw [Fin.castSucc_castLT, ← Fin.succ_lt_succ_iff, Fin.succ_pred]
    -- ⊢ Fin.succ j < i
    exact H
    -- 🎉 no goals
#align simplex_category.δ_comp_σ_of_gt' SimplexCategory.δ_comp_σ_of_gt'

/-- The fifth simplicial identity -/
@[reassoc]
theorem σ_comp_σ {n} {i j : Fin (n + 1)} (H : i ≤ j) :
    σ (Fin.castSucc i) ≫ σ j = σ j.succ ≫ σ i := by
  ext ⟨k, hk⟩
  -- ⊢ ↑(↑(Hom.toOrderHom (σ (Fin.castSucc i) ≫ σ j)) { val := k, isLt := hk }) = ↑ …
  rcases i with ⟨i, hi⟩
  -- ⊢ ↑(↑(Hom.toOrderHom (σ (Fin.castSucc { val := i, isLt := hi }) ≫ σ j)) { val  …
  rcases j with ⟨j, hj⟩
  -- ⊢ ↑(↑(Hom.toOrderHom (σ (Fin.castSucc { val := i, isLt := hi }) ≫ σ { val := j …
  simp at H hk
  -- ⊢ ↑(↑(Hom.toOrderHom (σ (Fin.castSucc { val := i, isLt := hi }) ≫ σ { val := j …
  dsimp [σ, Fin.predAbove]
  -- ⊢ ↑(if h : { val := j, isLt := (_ : j < Nat.succ (n + 1)) } < if h : { val :=  …
  simp [Fin.lt_iff_val_lt_val, Fin.ite_val]
  -- ⊢ (if j < if i < k then k - 1 else k then (if i < k then k - 1 else k) - 1 els …
  split_ifs
  all_goals try linarith
  -- ⊢ k - 1 - 1 = k - 1
  all_goals cases k <;> simp at *; linarith
  -- 🎉 no goals
#align simplex_category.σ_comp_σ SimplexCategory.σ_comp_σ

end Generators

section Skeleton

/-- The functor that exhibits `SimplexCategory` as skeleton
of `NonemptyFinLinOrdCat` -/
@[simps obj map]
def skeletalFunctor : SimplexCategory ⥤ NonemptyFinLinOrdCat.{v} where
  obj a := NonemptyFinLinOrdCat.of <| ULift (Fin (a.len + 1))
  map f := ⟨fun i => ULift.up (f.toOrderHom i.down), fun i j h => f.toOrderHom.monotone h⟩
#align simplex_category.skeletal_functor SimplexCategory.skeletalFunctor

theorem skeletalFunctor.coe_map {Δ₁ Δ₂ : SimplexCategory} (f : Δ₁ ⟶ Δ₂) :
    ↑(skeletalFunctor.{v}.map f) = ULift.up ∘ f.toOrderHom ∘ ULift.down :=
  rfl
#align simplex_category.skeletal_functor.coe_map SimplexCategory.skeletalFunctor.coe_map

theorem skeletal : Skeletal SimplexCategory := fun X Y ⟨I⟩ => by
  suffices Fintype.card (Fin (X.len + 1)) = Fintype.card (Fin (Y.len + 1)) by
    ext
    simpa
  apply Fintype.card_congr
  -- ⊢ Fin (len X + 1) ≃ Fin (len Y + 1)
  exact Equiv.ulift.symm.trans
    (((skeletalFunctor.{0} ⋙ forget NonemptyFinLinOrdCat).mapIso I).toEquiv.trans Equiv.ulift)
#align simplex_category.skeletal SimplexCategory.skeletal

namespace SkeletalFunctor

instance : Full skeletalFunctor.{v} where
  preimage f :=
    SimplexCategory.Hom.mk ⟨fun i => (f (ULift.up i)).down, fun i j h => f.monotone h⟩

instance : Faithful skeletalFunctor.{v} where
  map_injective {_ _ f g} h := by
    ext x : 3
    -- ⊢ ↑(Hom.toOrderHom f) x = ↑(Hom.toOrderHom g) x
    apply ULift.up_injective.{v}
    -- ⊢ { down := ↑(Hom.toOrderHom f) x } = { down := ↑(Hom.toOrderHom g) x }
    change (skeletalFunctor.{v}.map f) ⟨x⟩ = (skeletalFunctor.map g) ⟨x⟩
    -- ⊢ ↑(skeletalFunctor.map f) { down := x } = ↑(skeletalFunctor.map g) { down :=  …
    rw [h]
    -- 🎉 no goals

instance : EssSurj skeletalFunctor.{v} where
  mem_essImage X :=
    ⟨mk (Fintype.card X - 1 : ℕ),
      ⟨by
        have aux : Fintype.card X = Fintype.card X - 1 + 1 :=
          (Nat.succ_pred_eq_of_pos <| Fintype.card_pos_iff.mpr ⟨⊥⟩).symm
        let f := monoEquivOfFin X aux
        -- ⊢ skeletalFunctor.obj [Fintype.card ↑X - 1] ≅ X
        have hf := (Finset.univ.orderEmbOfFin aux).strictMono
        -- ⊢ skeletalFunctor.obj [Fintype.card ↑X - 1] ≅ X
        refine'
          { hom := ⟨fun i => f i.down, _⟩
            inv := ⟨fun i => ⟨f.symm i⟩, _⟩
            hom_inv_id := _
            inv_hom_id := _ }
        · rintro ⟨i⟩ ⟨j⟩ h
          -- ⊢ (fun i => ↑f i.down) { down := i } ≤ (fun i => ↑f i.down) { down := j }
          show f i ≤ f j
          -- ⊢ ↑f i ≤ ↑f j
          exact hf.monotone h
          -- 🎉 no goals
        · intro i j h
          -- ⊢ (fun i => { down := ↑(OrderIso.symm f) i }) i ≤ (fun i => { down := ↑(OrderI …
          show f.symm i ≤ f.symm j
          -- ⊢ ↑(OrderIso.symm f) i ≤ ↑(OrderIso.symm f) j
          rw [← hf.le_iff_le]
          -- ⊢ ↑(Finset.orderEmbOfFin Finset.univ aux) (↑(OrderIso.symm f) i) ≤ ↑(Finset.or …
          show f (f.symm i) ≤ f (f.symm j)
          -- ⊢ ↑f (↑(OrderIso.symm f) i) ≤ ↑f (↑(OrderIso.symm f) j)
          simpa only [OrderIso.apply_symm_apply]
          -- 🎉 no goals
        · ext1 ⟨i⟩
          -- ⊢ ↑({ toFun := fun i => ↑f i.down, monotone' := (_ : ∀ ⦃a b : ↑(skeletalFuncto …
          exact congr_arg ULift.up (f.symm_apply_apply i)
          -- 🎉 no goals
        · ext1 i
          -- ⊢ ↑({ toFun := fun i => { down := ↑(OrderIso.symm f) i }, monotone' := (_ : ∀  …
          exact f.apply_symm_apply i⟩⟩
          -- 🎉 no goals

noncomputable instance isEquivalence : IsEquivalence skeletalFunctor.{v} :=
  Equivalence.ofFullyFaithfullyEssSurj skeletalFunctor
#align simplex_category.skeletal_functor.is_equivalence SimplexCategory.SkeletalFunctor.isEquivalence

end SkeletalFunctor

/-- The equivalence that exhibits `SimplexCategory` as skeleton
of `NonemptyFinLinOrdCat` -/
noncomputable def skeletalEquivalence : SimplexCategory ≌ NonemptyFinLinOrdCat.{v} :=
  Functor.asEquivalence skeletalFunctor
#align simplex_category.skeletal_equivalence SimplexCategory.skeletalEquivalence

end Skeleton

/-- `SimplexCategory` is a skeleton of `NonemptyFinLinOrdCat`.
-/
noncomputable def isSkeletonOf :
    IsSkeletonOf NonemptyFinLinOrdCat SimplexCategory skeletalFunctor.{v} where
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
            -- 🎉 no goals

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
                                  -- ⊢ ↑(Hom.toOrderHom a₁✝) = ↑(Hom.toOrderHom a₂✝)
                                           -- 🎉 no goals

end Concrete

section EpiMono

/-- A morphism in `SimplexCategory` is a monomorphism precisely when it is an injective function
-/
theorem mono_iff_injective {n m : SimplexCategory} {f : n ⟶ m} :
    Mono f ↔ Function.Injective f.toOrderHom := by
  rw [← Functor.mono_map_iff_mono skeletalEquivalence.functor.{0}]
  -- ⊢ Mono (skeletalEquivalence.functor.map f) ↔ Function.Injective ↑(Hom.toOrderH …
  dsimp only [skeletalEquivalence, Functor.asEquivalence_functor]
  -- ⊢ Mono (skeletalFunctor.map f) ↔ Function.Injective ↑(Hom.toOrderHom f)
  rw [NonemptyFinLinOrdCat.mono_iff_injective, skeletalFunctor.coe_map,
    Function.Injective.of_comp_iff ULift.up_injective,
    Function.Injective.of_comp_iff' _ ULift.down_bijective]
#align simplex_category.mono_iff_injective SimplexCategory.mono_iff_injective

/-- A morphism in `SimplexCategory` is an epimorphism if and only if it is a surjective function
-/
theorem epi_iff_surjective {n m : SimplexCategory} {f : n ⟶ m} :
    Epi f ↔ Function.Surjective f.toOrderHom := by
  rw [← Functor.epi_map_iff_epi skeletalEquivalence.functor.{0}]
  -- ⊢ Epi (skeletalEquivalence.functor.map f) ↔ Function.Surjective ↑(Hom.toOrderH …
  dsimp only [skeletalEquivalence, Functor.asEquivalence_functor]
  -- ⊢ Epi (skeletalFunctor.map f) ↔ Function.Surjective ↑(Hom.toOrderHom f)
  rw [NonemptyFinLinOrdCat.epi_iff_surjective, skeletalFunctor.coe_map,
    Function.Surjective.of_comp_iff' ULift.up_bijective,
    Function.Surjective.of_comp_iff _ ULift.down_surjective]
#align simplex_category.epi_iff_surjective SimplexCategory.epi_iff_surjective

/-- A monomorphism in `SimplexCategory` must increase lengths-/
theorem len_le_of_mono {x y : SimplexCategory} {f : x ⟶ y} : Mono f → x.len ≤ y.len := by
  intro hyp_f_mono
  -- ⊢ len x ≤ len y
  have f_inj : Function.Injective f.toOrderHom.toFun := mono_iff_injective.1 hyp_f_mono
  -- ⊢ len x ≤ len y
  simpa using Fintype.card_le_of_injective f.toOrderHom.toFun f_inj
  -- 🎉 no goals
#align simplex_category.len_le_of_mono SimplexCategory.len_le_of_mono

theorem le_of_mono {n m : ℕ} {f : ([n] : SimplexCategory) ⟶ [m]} : CategoryTheory.Mono f → n ≤ m :=
  len_le_of_mono
#align simplex_category.le_of_mono SimplexCategory.le_of_mono

/-- An epimorphism in `SimplexCategory` must decrease lengths-/
theorem len_le_of_epi {x y : SimplexCategory} {f : x ⟶ y} : Epi f → y.len ≤ x.len := by
  intro hyp_f_epi
  -- ⊢ len y ≤ len x
  have f_surj : Function.Surjective f.toOrderHom.toFun := epi_iff_surjective.1 hyp_f_epi
  -- ⊢ len y ≤ len x
  simpa using Fintype.card_le_of_surjective f.toOrderHom.toFun f_surj
  -- 🎉 no goals
#align simplex_category.len_le_of_epi SimplexCategory.len_le_of_epi

theorem le_of_epi {n m : ℕ} {f : ([n] : SimplexCategory) ⟶ [m]} : Epi f → m ≤ n :=
  len_le_of_epi
#align simplex_category.le_of_epi SimplexCategory.le_of_epi

instance {n : ℕ} {i : Fin (n + 2)} : Mono (δ i) := by
  rw [mono_iff_injective]
  -- ⊢ Function.Injective ↑(Hom.toOrderHom (δ i))
  exact Fin.succAbove_right_injective
  -- 🎉 no goals

instance {n : ℕ} {i : Fin (n + 1)} : Epi (σ i) := by
  rw [epi_iff_surjective]
  -- ⊢ Function.Surjective ↑(Hom.toOrderHom (σ i))
  intro b
  -- ⊢ ∃ a, ↑(Hom.toOrderHom (σ i)) a = b
  simp only [σ, mkHom, Hom.toOrderHom_mk, OrderHom.coe_mk]
  -- ⊢ ∃ a, Fin.predAbove i a = b
  by_cases b ≤ i
  -- ⊢ ∃ a, Fin.predAbove i a = b
  -- ⊢ ∃ a, Fin.predAbove i a = b
  · use b
    -- ⊢ Fin.predAbove i ↑↑b = b
    rw [Fin.predAbove_below i b (by simpa only [Fin.coe_eq_castSucc] using h)]
    -- ⊢ Fin.castPred ↑↑b = b
    simp only [len_mk, Fin.coe_eq_castSucc, Fin.castPred_castSucc]
    -- 🎉 no goals
  · use b.succ
    -- ⊢ Fin.predAbove i (Fin.succ b) = b
    rw [Fin.predAbove_above i b.succ _, Fin.pred_succ]
    -- ⊢ Fin.castSucc i < Fin.succ b
    rw [not_le] at h
    -- ⊢ Fin.castSucc i < Fin.succ b
    rw [Fin.lt_iff_val_lt_val] at h ⊢
    -- ⊢ ↑(Fin.castSucc i) < ↑(Fin.succ b)
    simpa only [Fin.val_succ, Fin.coe_castSucc] using Nat.lt.step h
    -- 🎉 no goals

instance : ReflectsIsomorphisms (forget SimplexCategory) :=
  ⟨fun f hf =>
    IsIso.of_iso
      { hom := f
        inv := Hom.mk
            { toFun := inv ((forget SimplexCategory).map f)
              monotone' := fun y₁ y₂ h => by
                by_cases h' : y₁ < y₂
                -- ⊢ inv ((forget SimplexCategory).map f) y₁ ≤ inv ((forget SimplexCategory).map  …
                · by_contra h''
                  -- ⊢ False
                  apply not_le.mpr h'
                  -- ⊢ y₂ ≤ y₁
                  convert f.toOrderHom.monotone (le_of_not_ge h'')
                  -- ⊢ y₂ = ↑(Hom.toOrderHom f) (inv ((forget SimplexCategory).map f) y₂)
                  all_goals
                    exact (congr_hom (Iso.inv_hom_id
                      (asIso ((forget SimplexCategory).map f))) _).symm
                · rw [eq_of_le_of_not_lt h h'] }
                  -- 🎉 no goals
        hom_inv_id := by
          ext1
          -- ⊢ Hom.toOrderHom (f ≫ Hom.mk { toFun := inv ((forget SimplexCategory).map f),  …
          ext1
          -- ⊢ ↑(Hom.toOrderHom (f ≫ Hom.mk { toFun := inv ((forget SimplexCategory).map f) …
          exact Iso.hom_inv_id (asIso ((forget _).map f))
          -- 🎉 no goals
        inv_hom_id := by
          ext1
          -- ⊢ Hom.toOrderHom (Hom.mk { toFun := inv ((forget SimplexCategory).map f), mono …
          ext1
          -- ⊢ ↑(Hom.toOrderHom (Hom.mk { toFun := inv ((forget SimplexCategory).map f), mo …
          exact Iso.inv_hom_id (asIso ((forget _).map f)) }⟩
          -- 🎉 no goals

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
        -- 🎉 no goals
      right_inv := fun i => by
        simpa only using congr_arg (fun φ => (Hom.toOrderHom φ) i) e.inv_hom_id }
        -- 🎉 no goals
    e.hom.toOrderHom.monotone e.inv.toOrderHom.monotone
#align simplex_category.order_iso_of_iso SimplexCategory.orderIsoOfIso

theorem iso_eq_iso_refl {x : SimplexCategory} (e : x ≅ x) : e = Iso.refl x := by
  have h : (Finset.univ : Finset (Fin (x.len + 1))).card = x.len + 1 := Finset.card_fin (x.len + 1)
  -- ⊢ e = Iso.refl x
  have eq₁ := Finset.orderEmbOfFin_unique' h fun i => Finset.mem_univ ((orderIsoOfIso e) i)
  -- ⊢ e = Iso.refl x
  have eq₂ :=
    Finset.orderEmbOfFin_unique' h fun i => Finset.mem_univ ((orderIsoOfIso (Iso.refl x)) i)
  -- Porting note: the proof was rewritten from this point in #3414 (reenableeta)
  -- It could be investigated again to see if the original can be restored.
  ext x
  -- ⊢ ↑(↑(Hom.toOrderHom e.hom) x) = ↑(↑(Hom.toOrderHom (Iso.refl x✝).hom) x)
  replace eq₁ := congr_arg (· x) eq₁
  -- ⊢ ↑(↑(Hom.toOrderHom e.hom) x) = ↑(↑(Hom.toOrderHom (Iso.refl x✝).hom) x)
  replace eq₂ := congr_arg (· x) eq₂.symm
  -- ⊢ ↑(↑(Hom.toOrderHom e.hom) x) = ↑(↑(Hom.toOrderHom (Iso.refl x✝).hom) x)
  simp_all
  -- 🎉 no goals
#align simplex_category.iso_eq_iso_refl SimplexCategory.iso_eq_iso_refl

theorem eq_id_of_isIso {x : SimplexCategory} (f : x ⟶ x) [IsIso f] : f = 𝟙 _ :=
  congr_arg (fun φ : _ ≅ _ => φ.hom) (iso_eq_iso_refl (asIso f))
#align simplex_category.eq_id_of_is_iso SimplexCategory.eq_id_of_isIso

theorem eq_σ_comp_of_not_injective' {n : ℕ} {Δ' : SimplexCategory} (θ : mk (n + 1) ⟶ Δ')
    (i : Fin (n + 1)) (hi : θ.toOrderHom (Fin.castSucc i) = θ.toOrderHom i.succ) :
    ∃ θ' : mk n ⟶ Δ', θ = σ i ≫ θ' := by
  use δ i.succ ≫ θ
  -- ⊢ θ = σ i ≫ δ (Fin.succ i) ≫ θ
  ext1; ext1; ext1 x
  -- ⊢ Hom.toOrderHom θ = Hom.toOrderHom (σ i ≫ δ (Fin.succ i) ≫ θ)
        -- ⊢ ↑(Hom.toOrderHom θ) = ↑(Hom.toOrderHom (σ i ≫ δ (Fin.succ i) ≫ θ))
              -- ⊢ ↑(Hom.toOrderHom θ) x = ↑(Hom.toOrderHom (σ i ≫ δ (Fin.succ i) ≫ θ)) x
  simp only [Hom.toOrderHom_mk, Function.comp_apply, OrderHom.comp_coe, Hom.comp,
    smallCategory_comp, σ, mkHom, OrderHom.coe_mk]
  by_cases h' : x ≤ Fin.castSucc i
  -- ⊢ ↑(Hom.toOrderHom θ) x = ↑(Hom.toOrderHom θ) (↑(Hom.toOrderHom (δ (Fin.succ i …
  · rw [Fin.predAbove_below i x h']
    -- ⊢ ↑(Hom.toOrderHom θ) x = ↑(Hom.toOrderHom θ) (↑(Hom.toOrderHom (δ (Fin.succ i …
    have eq := Fin.castSucc_castPred (gt_of_gt_of_ge (Fin.castSucc_lt_last i) h')
    -- ⊢ ↑(Hom.toOrderHom θ) x = ↑(Hom.toOrderHom θ) (↑(Hom.toOrderHom (δ (Fin.succ i …
    dsimp [δ]
    -- ⊢ ↑(Hom.toOrderHom θ) x = ↑(Hom.toOrderHom θ) (Fin.succAbove (Fin.succ i) (Fin …
    erw [Fin.succAbove_below i.succ x.castPred _]
    -- ⊢ ↑(Hom.toOrderHom θ) x = ↑(Hom.toOrderHom θ) (Fin.castSucc (Fin.castPred x))
    swap
    -- ⊢ Fin.castSucc (Fin.castPred x) < Fin.succ i
    · rwa [eq, ← Fin.le_castSucc_iff]
      -- 🎉 no goals
    rw [eq]
    -- 🎉 no goals
  · simp only [not_le] at h'
    -- ⊢ ↑(Hom.toOrderHom θ) x = ↑(Hom.toOrderHom θ) (↑(Hom.toOrderHom (δ (Fin.succ i …
    let y := x.pred <| by rintro (rfl : x = 0); simp at h'
    -- ⊢ ↑(Hom.toOrderHom θ) x = ↑(Hom.toOrderHom θ) (↑(Hom.toOrderHom (δ (Fin.succ i …
    have hy : x = y.succ := (Fin.succ_pred x _).symm
    -- ⊢ ↑(Hom.toOrderHom θ) x = ↑(Hom.toOrderHom θ) (↑(Hom.toOrderHom (δ (Fin.succ i …
    rw [hy] at h' ⊢
    -- ⊢ ↑(Hom.toOrderHom θ) (Fin.succ y) = ↑(Hom.toOrderHom θ) (↑(Hom.toOrderHom (δ  …
    rw [Fin.predAbove_above i y.succ h', Fin.pred_succ]
    -- ⊢ ↑(Hom.toOrderHom θ) (Fin.succ y) = ↑(Hom.toOrderHom θ) (↑(Hom.toOrderHom (δ  …
    by_cases h'' : y = i
    -- ⊢ ↑(Hom.toOrderHom θ) (Fin.succ y) = ↑(Hom.toOrderHom θ) (↑(Hom.toOrderHom (δ  …
    · rw [h'']
      -- ⊢ ↑(Hom.toOrderHom θ) (Fin.succ i) = ↑(Hom.toOrderHom θ) (↑(Hom.toOrderHom (δ  …
      refine' hi.symm.trans _
      -- ⊢ ↑(Hom.toOrderHom θ) (Fin.castSucc i) = ↑(Hom.toOrderHom θ) (↑(Hom.toOrderHom …
      congr 1
      -- ⊢ Fin.castSucc i = ↑(Hom.toOrderHom (δ (Fin.succ i))) i
      dsimp [δ]
      -- ⊢ Fin.castSucc i = Fin.succAbove (Fin.succ i) i
      erw [Fin.succAbove_below i.succ]
      -- ⊢ Fin.castSucc i < Fin.succ i
      exact Fin.lt_succ
      -- 🎉 no goals
    · dsimp [δ]
      -- ⊢ ↑(Hom.toOrderHom θ) (Fin.succ (Fin.pred x (_ : x = 0 → False))) = ↑(Hom.toOr …
      erw [Fin.succAbove_above i.succ _]
      -- ⊢ Fin.succ i ≤ Fin.castSucc (Fin.pred x (_ : x = 0 → False))
      simp only [Fin.lt_iff_val_lt_val, Fin.le_iff_val_le_val, Fin.val_succ, Fin.coe_castSucc,
        Nat.lt_succ_iff, Fin.ext_iff] at h' h'' ⊢
      cases' Nat.le.dest h' with c hc
      -- ⊢ ↑i + 1 ≤ ↑(Fin.pred x (_ : x = 0 → False))
      cases c
      -- ⊢ ↑i + 1 ≤ ↑(Fin.pred x (_ : x = 0 → False))
      · exfalso
        -- ⊢ False
        simp only [Nat.zero_eq, add_zero, len_mk, Fin.coe_pred, ge_iff_le] at hc
        -- ⊢ False
        rw [hc] at h''
        -- ⊢ False
        exact h'' rfl
        -- 🎉 no goals
      · rw [← hc]
        -- ⊢ ↑i + 1 ≤ ↑i + Nat.succ n✝
        simp only [add_le_add_iff_left, Nat.succ_eq_add_one, le_add_iff_nonneg_left, zero_le]
        -- 🎉 no goals
#align simplex_category.eq_σ_comp_of_not_injective' SimplexCategory.eq_σ_comp_of_not_injective'

theorem eq_σ_comp_of_not_injective {n : ℕ} {Δ' : SimplexCategory} (θ : mk (n + 1) ⟶ Δ')
    (hθ : ¬Function.Injective θ.toOrderHom) :
    ∃ (i : Fin (n + 1)) (θ' : mk n ⟶ Δ'), θ = σ i ≫ θ' := by
  simp only [Function.Injective, exists_prop, not_forall] at hθ
  -- ⊢ ∃ i θ', θ = σ i ≫ θ'
  -- as θ is not injective, there exists `x<y` such that `θ x = θ y`
  -- and then, `θ x = θ (x+1)`
  have hθ₂ : ∃ x y : Fin (n + 2), (Hom.toOrderHom θ) x = (Hom.toOrderHom θ) y ∧ x < y := by
    rcases hθ with ⟨x, y, ⟨h₁, h₂⟩⟩
    by_cases h : x < y
    · exact ⟨x, y, ⟨h₁, h⟩⟩
    · refine' ⟨y, x, ⟨h₁.symm, _⟩⟩
      cases' lt_or_eq_of_le (not_lt.mp h) with h' h'
      · exact h'
      · exfalso
        exact h₂ h'.symm
  rcases hθ₂ with ⟨x, y, ⟨h₁, h₂⟩⟩
  -- ⊢ ∃ i θ', θ = σ i ≫ θ'
  let z := x.castPred
  -- ⊢ ∃ i θ', θ = σ i ≫ θ'
  use z
  -- ⊢ ∃ θ', θ = σ z ≫ θ'
  rw [← show Fin.castSucc z = x from
    Fin.castSucc_castPred (lt_of_lt_of_le h₂ (Fin.le_last y))] at h₁ h₂
  apply eq_σ_comp_of_not_injective'
  -- ⊢ ↑(Hom.toOrderHom θ) (Fin.castSucc z) = ↑(Hom.toOrderHom θ) (Fin.succ z)
  rw [Fin.castSucc_lt_iff_succ_le] at h₂
  -- ⊢ ↑(Hom.toOrderHom θ) (Fin.castSucc z) = ↑(Hom.toOrderHom θ) (Fin.succ z)
  apply le_antisymm
  -- ⊢ ↑(Hom.toOrderHom θ) (Fin.castSucc z) ≤ ↑(Hom.toOrderHom θ) (Fin.succ z)
  · exact θ.toOrderHom.monotone (le_of_lt (Fin.castSucc_lt_succ z))
    -- 🎉 no goals
  · rw [h₁]
    -- ⊢ ↑(Hom.toOrderHom θ) (Fin.succ z) ≤ ↑(Hom.toOrderHom θ) y
    exact θ.toOrderHom.monotone h₂
    -- 🎉 no goals
#align simplex_category.eq_σ_comp_of_not_injective SimplexCategory.eq_σ_comp_of_not_injective

theorem eq_comp_δ_of_not_surjective' {n : ℕ} {Δ : SimplexCategory} (θ : Δ ⟶ mk (n + 1))
    (i : Fin (n + 2)) (hi : ∀ x, θ.toOrderHom x ≠ i) : ∃ θ' : Δ ⟶ mk n, θ = θ' ≫ δ i := by
  by_cases i < Fin.last (n + 1)
  -- ⊢ ∃ θ', θ = θ' ≫ δ i
  -- ⊢ ∃ θ', θ = θ' ≫ δ i
  · use θ ≫ σ (Fin.castPred i)
    -- ⊢ θ = (θ ≫ σ (Fin.castPred i)) ≫ δ i
    ext1
    -- ⊢ Hom.toOrderHom θ = Hom.toOrderHom ((θ ≫ σ (Fin.castPred i)) ≫ δ i)
    ext1
    -- ⊢ ↑(Hom.toOrderHom θ) = ↑(Hom.toOrderHom ((θ ≫ σ (Fin.castPred i)) ≫ δ i))
    ext1 x
    -- ⊢ ↑(Hom.toOrderHom θ) x = ↑(Hom.toOrderHom ((θ ≫ σ (Fin.castPred i)) ≫ δ i)) x
    simp only [Hom.toOrderHom_mk, Function.comp_apply, OrderHom.comp_coe, Hom.comp,
      smallCategory_comp]
    by_cases h' : θ.toOrderHom x ≤ i
    -- ⊢ ↑(Hom.toOrderHom θ) x = ↑(Hom.toOrderHom (δ i)) (↑(Hom.toOrderHom (σ (Fin.ca …
    · simp only [σ, mkHom, Hom.toOrderHom_mk, OrderHom.coe_mk]
      -- ⊢ ↑(Hom.toOrderHom θ) x = ↑(Hom.toOrderHom (δ i)) (Fin.predAbove (Fin.castPred …
      rw [Fin.predAbove_below (Fin.castPred i) (θ.toOrderHom x)
          (by simpa [Fin.castSucc_castPred h] using h')]
      dsimp [δ]
      -- ⊢ ↑(Hom.toOrderHom θ) x = Fin.succAbove i (Fin.castPred (↑(Hom.toOrderHom θ) x))
      erw [Fin.succAbove_below i]
      -- ⊢ ↑(Hom.toOrderHom θ) x = Fin.castSucc (Fin.castPred (↑(Hom.toOrderHom θ) x))
      swap
      -- ⊢ Fin.castSucc (Fin.castPred (↑(Hom.toOrderHom θ) x)) < i
      · simp only [Fin.lt_iff_val_lt_val, Fin.coe_castSucc]
        -- ⊢ ↑(Fin.castPred (↑(Hom.toOrderHom θ) x)) < ↑i
        exact
          lt_of_le_of_lt (Fin.coe_castPred_le_self _)
            (Fin.lt_iff_val_lt_val.mp ((Ne.le_iff_lt (hi x)).mp h'))
      rw [Fin.castSucc_castPred]
      -- ⊢ ↑(Hom.toOrderHom θ) x < Fin.last (n + 1)
      apply lt_of_le_of_lt h' h
      -- 🎉 no goals
    · simp only [not_le] at h'
      -- ⊢ ↑(Hom.toOrderHom θ) x = ↑(Hom.toOrderHom (δ i)) (↑(Hom.toOrderHom (σ (Fin.ca …
      simp only [σ, mkHom, Hom.toOrderHom_mk, OrderHom.coe_mk,
        Fin.predAbove_above (Fin.castPred i) (θ.toOrderHom x)
          (by simpa only [Fin.castSucc_castPred h] using h')]
      dsimp [δ]
      -- ⊢ ↑(Hom.toOrderHom θ) x = Fin.succAbove i (Fin.pred (↑(Hom.toOrderHom θ) x) (_ …
      erw [Fin.succAbove_above i _, Fin.succ_pred]
      -- ⊢ i ≤ Fin.castSucc (Fin.pred (↑(Hom.toOrderHom θ) x) (_ : ↑(Hom.toOrderHom θ)  …
      simpa only [Fin.le_iff_val_le_val, Fin.coe_castSucc, Fin.coe_pred] using
        Nat.le_pred_of_lt (Fin.lt_iff_val_lt_val.mp h')
  · obtain rfl := le_antisymm (Fin.le_last i) (not_lt.mp h)
    -- ⊢ ∃ θ', θ = θ' ≫ δ (Fin.last (n + 1))
    use θ ≫ σ (Fin.last _)
    -- ⊢ θ = (θ ≫ σ (Fin.last n)) ≫ δ (Fin.last (n + 1))
    ext x : 4
    -- ⊢ ↑(↑(Hom.toOrderHom θ) x) = ↑(↑(Hom.toOrderHom ((θ ≫ σ (Fin.last n)) ≫ δ (Fin …
    dsimp [δ, σ]
    -- ⊢ ↑(↑(Hom.toOrderHom θ) x) = ↑(Fin.succAbove (Fin.last (n + 1)) (Fin.castPred  …
    dsimp only [Fin.castPred]
    -- ⊢ ↑(↑(Hom.toOrderHom θ) x) = ↑(Fin.succAbove (Fin.last (n + 1)) (Fin.predAbove …
    rw [Fin.predAbove_last, Fin.succAbove_last, Fin.castSucc_castPred]
    -- ⊢ ↑(Hom.toOrderHom θ) x < Fin.last (n + 1)
    exact (Ne.le_iff_lt (hi x)).mp (Fin.le_last _)
    -- 🎉 no goals
#align simplex_category.eq_comp_δ_of_not_surjective' SimplexCategory.eq_comp_δ_of_not_surjective'

theorem eq_comp_δ_of_not_surjective {n : ℕ} {Δ : SimplexCategory} (θ : Δ ⟶ mk (n + 1))
    (hθ : ¬Function.Surjective θ.toOrderHom) :
    ∃ (i : Fin (n + 2)) (θ' : Δ ⟶ mk n), θ = θ' ≫ δ i := by
  cases' not_forall.mp hθ with i hi
  -- ⊢ ∃ i θ', θ = θ' ≫ δ i
  use i
  -- ⊢ ∃ θ', θ = θ' ≫ δ i
  exact eq_comp_δ_of_not_surjective' θ i (not_exists.mp hi)
  -- 🎉 no goals
#align simplex_category.eq_comp_δ_of_not_surjective SimplexCategory.eq_comp_δ_of_not_surjective

theorem eq_id_of_mono {x : SimplexCategory} (i : x ⟶ x) [Mono i] : i = 𝟙 _ := by
  suffices IsIso i by
    apply eq_id_of_isIso
  apply isIso_of_bijective
  -- ⊢ Function.Bijective (Hom.toOrderHom i).toFun
  dsimp
  -- ⊢ Function.Bijective ↑(Hom.toOrderHom i)
  rw [Fintype.bijective_iff_injective_and_card i.toOrderHom, ← mono_iff_injective,
    eq_self_iff_true, and_true_iff]
  infer_instance
  -- 🎉 no goals
#align simplex_category.eq_id_of_mono SimplexCategory.eq_id_of_mono

theorem eq_id_of_epi {x : SimplexCategory} (i : x ⟶ x) [Epi i] : i = 𝟙 _ := by
  suffices IsIso i by
    haveI := this
    apply eq_id_of_isIso
  apply isIso_of_bijective
  -- ⊢ Function.Bijective (Hom.toOrderHom i).toFun
  dsimp
  -- ⊢ Function.Bijective ↑(Hom.toOrderHom i)
  rw [Fintype.bijective_iff_surjective_and_card i.toOrderHom, ← epi_iff_surjective,
    eq_self_iff_true, and_true_iff]
  infer_instance
  -- 🎉 no goals
#align simplex_category.eq_id_of_epi SimplexCategory.eq_id_of_epi

theorem eq_σ_of_epi {n : ℕ} (θ : mk (n + 1) ⟶ mk n) [Epi θ] : ∃ i : Fin (n + 1), θ = σ i := by
  rcases eq_σ_comp_of_not_injective θ (by
    by_contra h
    simpa using le_of_mono (mono_iff_injective.mpr h)) with ⟨i, θ', h⟩
  use i
  -- ⊢ θ = σ i
  haveI : Epi (σ i ≫ θ') := by
    rw [← h]
    infer_instance
  haveI := CategoryTheory.epi_of_epi (σ i) θ'
  -- ⊢ θ = σ i
  rw [h, eq_id_of_epi θ', Category.comp_id]
  -- 🎉 no goals
#align simplex_category.eq_σ_of_epi SimplexCategory.eq_σ_of_epi

theorem eq_δ_of_mono {n : ℕ} (θ : mk n ⟶ mk (n + 1)) [Mono θ] : ∃ i : Fin (n + 2), θ = δ i := by
  rcases eq_comp_δ_of_not_surjective θ (by
    by_contra h
    simpa using le_of_epi (epi_iff_surjective.mpr h)) with ⟨i, θ', h⟩
  use i
  -- ⊢ θ = δ i
  haveI : Mono (θ' ≫ δ i) := by
    rw [← h]
    infer_instance
  haveI := CategoryTheory.mono_of_mono θ' (δ i)
  -- ⊢ θ = δ i
  rw [h, eq_id_of_mono θ', Category.id_comp]
  -- 🎉 no goals
#align simplex_category.eq_δ_of_mono SimplexCategory.eq_δ_of_mono

theorem len_lt_of_mono {Δ' Δ : SimplexCategory} (i : Δ' ⟶ Δ) [hi : Mono i] (hi' : Δ ≠ Δ') :
    Δ'.len < Δ.len := by
  rcases lt_or_eq_of_le (len_le_of_mono hi) with (h | h)
  -- ⊢ len Δ' < len Δ
  · exact h
    -- 🎉 no goals
  · exfalso
    -- ⊢ False
    exact hi' (by ext; exact h.symm)
    -- 🎉 no goals
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
    [Mono i] (fac : e ≫ i = φ) : image φ = Δ' := by
  haveI := strongEpi_of_epi e
  -- ⊢ image φ = Δ'
  let e := image.isoStrongEpiMono e i fac
  -- ⊢ image φ = Δ'
  ext
  -- ⊢ len (image φ) = len Δ'
  exact
    le_antisymm (len_le_of_epi (inferInstance : Epi e.hom))
      (len_le_of_mono (inferInstance : Mono e.hom))
#align simplex_category.image_eq SimplexCategory.image_eq

theorem image_ι_eq {Δ Δ'' : SimplexCategory} {φ : Δ ⟶ Δ''} {e : Δ ⟶ image φ} [Epi e]
    {i : image φ ⟶ Δ''} [Mono i] (fac : e ≫ i = φ) : image.ι φ = i := by
  haveI := strongEpi_of_epi e
  -- ⊢ image.ι φ = i
  rw [← image.isoStrongEpiMono_hom_comp_ι e i fac,
    SimplexCategory.eq_id_of_isIso (image.isoStrongEpiMono e i fac).hom, Category.id_comp]
#align simplex_category.image_ι_eq SimplexCategory.image_ι_eq

theorem factorThruImage_eq {Δ Δ'' : SimplexCategory} {φ : Δ ⟶ Δ''} {e : Δ ⟶ image φ} [Epi e]
    {i : image φ ⟶ Δ''} [Mono i] (fac : e ≫ i = φ) : factorThruImage φ = e := by
  rw [← cancel_mono i, fac, ← image_ι_eq fac, image.fac]
  -- 🎉 no goals
#align simplex_category.factor_thru_image_eq SimplexCategory.factorThruImage_eq

end EpiMono

/-- This functor `SimplexCategory ⥤ Cat` sends `[n]` (for `n : ℕ`)
to the category attached to the ordered set `{0, 1, ..., n}` -/
@[simps! obj map]
def toCat : SimplexCategory ⥤ Cat.{0} :=
  SimplexCategory.skeletalFunctor ⋙ forget₂ NonemptyFinLinOrdCat LinOrdCat ⋙
      forget₂ LinOrdCat LatCat ⋙ forget₂ LatCat PartOrdCat ⋙
      forget₂ PartOrdCat PreordCat ⋙ preordCatToCat
set_option linter.uppercaseLean3 false in
#align simplex_category.to_Cat SimplexCategory.toCat

end SimplexCategory
