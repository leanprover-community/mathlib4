/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kim Morrison, Adam Topaz
-/
import Mathlib.CategoryTheory.Opposites
import Mathlib.Order.Fin.Basic

/-! # The simplex category

We construct a skeletal model of the simplex category, with objects `ℕ` and the
morphisms `n ⟶ m` being the monotone maps from `Fin (n + 1)` to `Fin (m + 1)`.

In `Mathlib.AlgebraicTopology.SimplexCategory.Basic`, we show that this category
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
-/

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

/-- The truncated simplex category. -/
def Truncated (n : ℕ) :=
  FullSubcategory fun a : SimplexCategory => a.len ≤ n

instance (n : ℕ) : SmallCategory.{0} (Truncated n) :=
  FullSubcategory.category _

namespace Truncated

instance {n} : Inhabited (Truncated n) :=
  ⟨⟨⦋0⦌, by simp⟩⟩

/-- The fully faithful inclusion of the truncated simplex category into the usual
simplex category.
-/
def inclusion (n : ℕ) : SimplexCategory.Truncated n ⥤ SimplexCategory :=
  fullSubcategoryInclusion _

instance (n : ℕ) : (inclusion n : Truncated n ⥤ _).Full := FullSubcategory.full _
instance (n : ℕ) : (inclusion n : Truncated n ⥤ _).Faithful := FullSubcategory.faithful _

/-- A proof that the full subcategory inclusion is fully faithful -/
noncomputable def inclusion.fullyFaithful (n : ℕ) :
    (inclusion n : Truncated n ⥤ _).op.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful _

@[ext]
theorem Hom.ext {n} {a b : Truncated n} (f g : a ⟶ b) :
    f.toOrderHom = g.toOrderHom → f = g := SimplexCategory.Hom.ext _ _

end Truncated

end SimplexCategory
