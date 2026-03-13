/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kim Morrison, Adam Topaz
-/
module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.Order.Fin.Basic
public import Mathlib.Util.Superscript

/-! # The simplex category

We construct a skeletal model of the simplex category, with objects `ℕ` and the
morphisms `n ⟶ m` being the monotone maps from `Fin (n + 1)` to `Fin (m + 1)`.

In `Mathlib/AlgebraicTopology/SimplexCategory/Basic.lean`, we show that this category
is equivalent to `NonemptyFinLinOrd`.

## Remarks

The definitions `SimplexCategory` and `SimplexCategory.Hom` are marked as irreducible.

We provide the following functions to work with these objects:
1. `SimplexCategory.mk` creates an object of `SimplexCategory` out of a natural number.
   Use the notation `⦋n⦌` in the `Simplicial` locale.
2. `SimplexCategory.len` gives the "length" of an object of `SimplexCategory`, as a natural.
3. `SimplexCategory.Hom.mk` makes a morphism out of a monotone map between `Fin`'s.
4. `SimplexCategory.Hom.toOrderHom` gives the underlying monotone map associated to a
   term of `SimplexCategory.Hom`.

## Notation

* `⦋n⦌` denotes the `n`-dimensional simplex. This notation is available with
  `open Simplicial`.
* `⦋m⦌ₙ` denotes the `m`-dimensional simplex in the `n`-truncated simplex category.
  The truncation proof `p : m ≤ n` can also be provided using the syntax `⦋m, p⦌ₙ`.
  This notation is available with `open SimplexCategory.Truncated`.
-/

@[expose] public section

universe v

open CategoryTheory

/-- The simplex category:
* objects are natural numbers `n : ℕ`
* morphisms from `n` to `m` are monotone functions `Fin (n+1) → Fin (m+1)`
-/
def SimplexCategory :=
  ℕ

namespace SimplexCategory

-- The definition of `SimplexCategory` is made irreducible below.
/-- Interpret a natural number as an object of the simplex category. -/
def mk (n : ℕ) : SimplexCategory :=
  n

/-- the `n`-dimensional simplex can be denoted `⦋n⦌` -/
scoped[Simplicial] notation "⦋" n "⦌" => SimplexCategory.mk n

-- TODO: Make `len` irreducible.
/-- The length of an object of `SimplexCategory`. -/
def len (n : SimplexCategory) : ℕ :=
  n

@[ext]
theorem ext (a b : SimplexCategory) : a.len = b.len → a = b :=
  id

attribute [irreducible] SimplexCategory

open Simplicial

@[simp]
theorem len_mk (n : ℕ) : ⦋n⦌.len = n :=
  rfl

@[simp]
theorem mk_len (n : SimplexCategory) : ⦋n.len⦌ = n :=
  rfl

/-- A recursor for `SimplexCategory`. Use it as `induction Δ using SimplexCategory.rec`. -/
protected def rec {F : SimplexCategory → Sort*} (h : ∀ n : ℕ, F ⦋n⦌) : ∀ X, F X := fun n =>
  h n.len

/-- Morphisms in the `SimplexCategory`. -/
protected def Hom (a b : SimplexCategory) :=
  Fin (a.len + 1) →o Fin (b.len + 1)

namespace Hom

/-- Make a morphism in `SimplexCategory` from a monotone map of `Fin`'s. -/
def mk {a b : SimplexCategory} (f : Fin (a.len + 1) →o Fin (b.len + 1)) : SimplexCategory.Hom a b :=
  f

/-- Recover the monotone map from a morphism in the simplex category. -/
def toOrderHom {a b : SimplexCategory} (f : SimplexCategory.Hom a b) :
    Fin (a.len + 1) →o Fin (b.len + 1) :=
  f

theorem ext' {a b : SimplexCategory} (f g : SimplexCategory.Hom a b) :
    f.toOrderHom = g.toOrderHom → f = g :=
  id

attribute [irreducible] SimplexCategory.Hom

@[simp]
theorem mk_toOrderHom {a b : SimplexCategory} (f : SimplexCategory.Hom a b) : mk f.toOrderHom = f :=
  rfl

@[simp]
theorem toOrderHom_mk {a b : SimplexCategory} (f : Fin (a.len + 1) →o Fin (b.len + 1)) :
    (mk f).toOrderHom = f :=
  rfl

theorem mk_toOrderHom_apply {a b : SimplexCategory} (f : Fin (a.len + 1) →o Fin (b.len + 1))
    (i : Fin (a.len + 1)) : (mk f).toOrderHom i = f i :=
  rfl

/-- Identity morphisms of `SimplexCategory`. -/
@[simp]
def id (a : SimplexCategory) : SimplexCategory.Hom a a :=
  mk OrderHom.id

/-- Composition of morphisms of `SimplexCategory`. -/
@[simp]
def comp {a b c : SimplexCategory} (f : SimplexCategory.Hom b c) (g : SimplexCategory.Hom a b) :
    SimplexCategory.Hom a c :=
  mk <| f.toOrderHom.comp g.toOrderHom

end Hom

instance smallCategory : SmallCategory.{0} SimplexCategory where
  Hom n m := SimplexCategory.Hom n m
  id _ := SimplexCategory.Hom.id _
  comp f g := SimplexCategory.Hom.comp g f

@[simp]
lemma id_toOrderHom (a : SimplexCategory) :
    Hom.toOrderHom (𝟙 a) = OrderHom.id := rfl

@[simp]
lemma comp_toOrderHom {a b c : SimplexCategory} (f : a ⟶ b) (g : b ⟶ c) :
    (f ≫ g).toOrderHom = g.toOrderHom.comp f.toOrderHom := rfl

@[ext]
theorem Hom.ext {a b : SimplexCategory} (f g : a ⟶ b) :
    f.toOrderHom = g.toOrderHom → f = g :=
  Hom.ext' _ _

/-- Homs in `SimplexCategory` are equivalent to order-preserving functions of finite linear
orders. -/
def homEquivOrderHom {a b : SimplexCategory} :
    (a ⟶ b) ≃ (Fin (a.len + 1) →o Fin (b.len + 1)) where
  toFun := Hom.toOrderHom
  invFun := Hom.mk

/-- Homs in `SimplexCategory` are equivalent to functors between finite linear orders. -/
def homEquivFunctor {a b : SimplexCategory} :
    (a ⟶ b) ≃ (Fin (a.len + 1) ⥤ Fin (b.len + 1)) :=
  SimplexCategory.homEquivOrderHom.trans OrderHom.equivFunctor

/-- The truncated simplex category. -/
abbrev Truncated (n : ℕ) :=
  ObjectProperty.FullSubcategory fun a : SimplexCategory => a.len ≤ n

namespace Truncated

instance {n} : Inhabited (Truncated n) :=
  ⟨⟨⦋0⦌, by simp⟩⟩

/-- The fully faithful inclusion of the truncated simplex category into the usual
simplex category.
-/
abbrev inclusion (n : ℕ) : SimplexCategory.Truncated n ⥤ SimplexCategory :=
  ObjectProperty.ι _

/-- A proof that the full subcategory inclusion is fully faithful -/
noncomputable def inclusion.fullyFaithful (n : ℕ) :
    (inclusion n : Truncated n ⥤ _).op.FullyFaithful :=
  Functor.FullyFaithful.ofFullyFaithful _

@[ext]
theorem Hom.ext {n} {a b : Truncated n} (f g : a ⟶ b)
    (h : f.hom.toOrderHom = g.hom.toOrderHom) : f = g :=
  ObjectProperty.hom_ext _ (SimplexCategory.Hom.ext _ _ h)

/-- A quick attempt to prove that `⦋m⦌` is `n`-truncated (`⦋m⦌.len ≤ n`). -/
scoped macro "trunc" : tactic =>
  `(tactic| first | assumption | dsimp only [SimplexCategory.len_mk] <;> lia)

open Mathlib.Tactic (subscriptTerm) in
/-- For `m ≤ n`, `⦋m⦌ₙ` is the `m`-dimensional simplex in `Truncated n`. The
proof `p : m ≤ n` can also be provided using the syntax `⦋m, p⦌ₙ`. -/
scoped syntax:max (name := mkNotation)
  "⦋" term ("," term)? "⦌" noWs subscriptTerm : term
scoped macro_rules
  | `(⦋$m:term⦌$n:subscript) =>
    `((⟨SimplexCategory.mk $m, by first | trunc |
      fail "Failed to prove truncation property. Try writing `⦋m, by ...⦌ₙ`."⟩ :
      SimplexCategory.Truncated $n))
  | `(⦋$m:term, $p:term⦌$n:subscript) =>
    `((⟨SimplexCategory.mk $m, $p⟩ : SimplexCategory.Truncated $n))

/-- Make a morphism in `Truncated n` from a morphism in `SimplexCategory`. This
is equivalent to `@id (⦋a⦌ₙ ⟶ ⦋b⦌ₙ) f`. -/
abbrev Hom.tr {n : ℕ} {a b : SimplexCategory} (f : a ⟶ b)
    (ha : a.len ≤ n := by trunc) (hb : b.len ≤ n := by trunc) :
    (⟨a, ha⟩ : Truncated n) ⟶ ⟨b, hb⟩ :=
  ObjectProperty.homMk f

@[simp]
lemma Hom.tr_id {n : ℕ} (a : SimplexCategory) (ha : a.len ≤ n := by trunc) :
    Hom.tr (𝟙 a) ha = 𝟙 _ := rfl

@[reassoc]
lemma Hom.tr_comp {n : ℕ} {a b c : SimplexCategory} (f : a ⟶ b) (g : b ⟶ c)
    (ha : a.len ≤ n := by trunc) (hb : b.len ≤ n := by trunc)
    (hc : c.len ≤ n := by trunc) :
    tr (f ≫ g) = tr f ≫ tr g :=
  rfl

@[reassoc]
lemma Hom.tr_comp' {n : ℕ} {a b c : SimplexCategory} (f : a ⟶ b) {hb : b.len ≤ n}
    {hc : c.len ≤ n} (g : (⟨b, hb⟩ : Truncated n) ⟶ ⟨c, hc⟩) (ha : a.len ≤ n := by trunc) :
    tr (f ≫ g.hom) = tr f ≫ g :=
  rfl

/-- The inclusion of `Truncated n` into `Truncated m` when `n ≤ m`. -/
def incl (n m : ℕ) (h : n ≤ m := by omega) : Truncated n ⥤ Truncated m :=
  ObjectProperty.ιOfLE (fun _ h' ↦ h'.trans h)

/-- For all `n ≤ m`, `inclusion n` factors through `Truncated m`. -/
def inclCompInclusion {n m : ℕ} (h : n ≤ m) :
    incl n m ⋙ inclusion m ≅ inclusion n :=
  Iso.refl _

end Truncated

end SimplexCategory
