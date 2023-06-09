/-
Copyright (c) 2021 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Kuelshammer

! This file was ported from Lean 3 source module algebra.category.Semigroup.basic
! leanprover-community/mathlib commit 47b51515e69f59bca5cf34ef456e6000fe205a69
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.PEmptyInstances
import Mathlib.Algebra.Hom.Equiv.Basic
import Mathlib.CategoryTheory.ConcreteCategory.BundledHom
import Mathlib.CategoryTheory.Functor.ReflectsIso
import Mathlib.CategoryTheory.Elementwise

/-!
# Category instances for has_mul, has_add, semigroup and add_semigroup

We introduce the bundled categories:
* `Magma`
* `AddMagma`
* `Semigroup`
* `AddSemigroup`
along with the relevant forgetful functors between them.

This closely follows `algebra.category.Mon.basic`.

## TODO

* Limits in these categories
* free/forgetful adjunctions
-/

set_option linter.uppercaseLean3 false

universe u v

open CategoryTheory

/-- The category of magmas and magma morphisms. -/
@[to_additive]
def Magma : Type (u + 1) :=
  Bundled Mul
#align Magma Magma
#align AddMagma AddMagma

/-- The category of additive magmas and additive magma morphisms. -/
add_decl_doc AddMagma

namespace Magma

@[to_additive]
instance bundledHom : BundledHom @MulHom :=
  ⟨@MulHom.toFun, @MulHom.id, @MulHom.comp,
    --Porting note : was `@MulHom.coe_inj` which is deprecated
    by intros; apply @FunLike.coe_injective, by aesop_cat, by aesop_cat⟩
#align Magma.bundled_hom Magma.bundledHom
#align AddMagma.bundled_hom AddMagma.bundledHom

-- Porting note: deriving failed for `ConcreteCategory`,
-- "default handlers have not been implemented yet"
deriving instance LargeCategory for Magma
instance concreteCategory : ConcreteCategory Magma := BundledHom.concreteCategory MulHom

attribute [to_additive] instMagmaLargeCategory Magma.concreteCategory

@[to_additive]
instance : CoeSort Magma (Type _) :=
  Bundled.coeSort

/-- Construct a bundled `Magma` from the underlying type and typeclass. -/
@[to_additive]
def of (M : Type u) [Mul M] : Magma :=
  Bundled.of M
#align Magma.of Magma.of
#align AddMagma.of AddMagma.of

/-- Construct a bundled `AddMagma` from the underlying type and typeclass. -/
add_decl_doc AddMagma.of

/-- Typecheck a `MulHom` as a morphism in `Magma`. -/
@[to_additive]
def ofHom {X Y : Type u} [Mul X] [Mul Y] (f : X →ₙ* Y) : of X ⟶ of Y :=
  f
#align Magma.of_hom Magma.ofHom
#align AddMagma.of_hom AddMagma.ofHom

/-- Typecheck a `AddHom` as a morphism in `AddMagma`. -/
add_decl_doc AddMagma.ofHom

-- Porting note: added these two instances as it wasn't able to find them.
instance {X : Type u} [h : Mul X] : Mul (of X) := h
instance {X Y : Type u} [Mul X] [Mul Y] :
    CoeFun (of X ⟶ of Y) (fun _ => X → Y) :=
  ⟨MulHom.toFun⟩

@[to_additive (attr := simp)]
theorem ofHom_apply {X Y : Type u} [Mul X] [Mul Y] (f : X →ₙ* Y) (x : X) : ofHom f x = f x :=
  rfl
#align Magma.of_hom_apply Magma.ofHom_apply
#align AddMagma.of_hom_apply AddMagma.ofHom_apply

@[to_additive]
instance : Inhabited Magma :=
  ⟨Magma.of PEmpty⟩

@[to_additive]
instance (M : Magma) : Mul M :=
  M.str

@[to_additive (attr := simp)]
theorem coe_of (R : Type u) [Mul R] : (Magma.of R : Type u) = R :=
  rfl
#align Magma.coe_of Magma.coe_of
#align AddMagma.coe_of AddMagma.coe_of

end Magma

/-- The category of semigroups and semigroup morphisms. -/
@[to_additive]
def SemigroupCat : Type (u + 1) :=
  Bundled Semigroup
#align Semigroup SemigroupCat
#align AddSemigroup AddSemigroupCat

/-- The category of additive semigroups and semigroup morphisms. -/
add_decl_doc AddSemigroupCat

namespace SemigroupCat

@[to_additive]
instance : BundledHom.ParentProjection @Semigroup.toMul := ⟨⟩

-- Porting note: deriving failed for `ConcreteCategory`,
-- "default handlers have not been implemented yet"
-- (also, the hack is weird, why does it work?)
deriving instance LargeCategory for SemigroupCat
instance concreteCategory : ConcreteCategory SemigroupCat :=
  BundledHom.concreteCategory (fun _ _ => _)

attribute [to_additive] instSemigroupCatLargeCategory SemigroupCat.concreteCategory

@[to_additive]
instance : CoeSort SemigroupCat (Type _) :=
  Bundled.coeSort

/-- Construct a bundled `Semigroup` from the underlying type and typeclass. -/
@[to_additive]
def of (M : Type u) [Semigroup M] : SemigroupCat :=
  Bundled.of M
#align Semigroup.of SemigroupCat.of
#align AddSemigroup.of AddSemigroupCat.of

/-- Construct a bundled `AddSemigroup` from the underlying type and typeclass. -/
add_decl_doc AddSemigroupCat.of

/-- Typecheck a `mul_hom` as a morphism in `Semigroup`. -/
@[to_additive]
def ofHom {X Y : Type u} [Semigroup X] [Semigroup Y] (f : X →ₙ* Y) : of X ⟶ of Y :=
  f
#align Semigroup.of_hom SemigroupCat.ofHom
#align AddSemigroup.of_hom AddSemigroupCat.ofHom

/-- Typecheck a `add_hom` as a morphism in `AddSemigroup`. -/
add_decl_doc AddSemigroupCat.ofHom

-- Porting note: added these two instances as it wasn't able to find them.
instance {X : Type u} [h : Semigroup X] : Semigroup (of X) := h
instance {X Y : Type u} [Semigroup X] [Semigroup Y] :
    CoeFun (of X ⟶ of Y) (fun _ => X → Y) :=
  ⟨MulHom.toFun⟩

@[to_additive (attr := simp)]
theorem ofHom_apply {X Y : Type u} [Semigroup X] [Semigroup Y] (f : X →ₙ* Y) (x : X) :
    ofHom f x = f x :=
  rfl
#align Semigroup.of_hom_apply SemigroupCat.ofHom_apply
#align AddSemigroup.of_hom_apply AddSemigroupCat.ofHom_apply

@[to_additive]
instance : Inhabited SemigroupCat :=
  ⟨SemigroupCat.of PEmpty⟩

@[to_additive]
instance (M : SemigroupCat) : Semigroup M :=
  M.str

@[to_additive (attr := simp)]
theorem coe_of (R : Type u) [Semigroup R] : (SemigroupCat.of R : Type u) = R :=
  rfl
#align Semigroup.coe_of SemigroupCat.coe_of
#align AddSemigroup.coe_of AddSemigroupCat.coe_of

@[to_additive]
instance hasForgetToMagma : HasForget₂ SemigroupCat Magma :=
  BundledHom.forget₂ _ _
#align Semigroup.has_forget_to_Magma SemigroupCat.hasForgetToMagma
#align AddSemigroup.has_forget_to_AddMagma AddSemigroupCat.hasForgetToAddMagma

end SemigroupCat

variable {X Y : Type u}

section

variable [Mul X] [Mul Y]

/-- Build an isomorphism in the category `Magma` from a `mul_equiv` between `has_mul`s. -/
@[to_additive (attr := simps)
      "Build an isomorphism in the category `AddMagma` from\nan `add_equiv` between `has_add`s."]
def MulEquiv.toMagmaIso (e : X ≃* Y) : Magma.of X ≅ Magma.of Y where
  hom := e.toMulHom
  inv := e.symm.toMulHom
  -- Porting note: both used to be proven automatically
  hom_inv_id := by
    aesop_cat_nonterminal
    sorry
    done
  inv_hom_id := by
    aesop_cat_nonterminal
    sorry
#align mul_equiv.to_Magma_iso MulEquiv.toMagmaIso
#align add_equiv.to_AddMagma_iso AddEquiv.toAddMagmaIso

end

section

variable [Semigroup X] [Semigroup Y]

/-- Build an isomorphism in the category `Semigroup` from a `mul_equiv` between `semigroup`s. -/
@[to_additive (attr := simps)
      "Build an isomorphism in the category\n`AddSemigroup` from an `add_equiv` between `add_semigroup`s."]
def MulEquiv.toSemigroupCatIso (e : X ≃* Y) : SemigroupCat.of X ≅ SemigroupCat.of Y where
  hom := e.toMulHom
  inv := e.symm.toMulHom
  -- Porting note: both used to be proven automatically
  hom_inv_id := by
    aesop_cat_nonterminal
    sorry
    done
  inv_hom_id := by
    aesop_cat_nonterminal
    sorry
#align mul_equiv.to_Semigroup_iso MulEquiv.toSemigroupCatIso
#align add_equiv.to_AddSemigroup_iso AddEquiv.toAddSemigroupCatIso

end

namespace CategoryTheory.Iso

/-- Build a `mul_equiv` from an isomorphism in the category `Magma`. -/
@[to_additive
      "Build an `add_equiv` from an isomorphism in the category\n`AddMagma`."]
def magmaIsoToMulEquiv {X Y : Magma} (i : X ≅ Y) : X ≃* Y where
  toFun := i.hom -- Porting note: TODO/HERE: that's again Quiver `⟶` vs. Function `→`
  invFun := i.inv
  left_inv x := by simp
  right_inv y := by simp
  map_mul' := by simp
#align category_theory.iso.Magma_iso_to_mul_equiv CategoryTheory.Iso.magmaIsoToMulEquiv
#align category_theory.iso.AddMagma_iso_to_add_equiv CategoryTheory.Iso.addMagmaIsoToAddEquiv

/-- Build a `mul_equiv` from an isomorphism in the category `Semigroup`. -/
@[to_additive
  "Build an `add_equiv` from an isomorphism in the category\n`AddSemigroup`."]
def semigroupCatIsoToMulEquiv {X Y : SemigroupCat} (i : X ≅ Y) : X ≃* Y where
  toFun := i.hom
  invFun := i.inv
  left_inv x := by simp
  right_inv y := by simp
  map_mul' := by simp
#align category_theory.iso.Semigroup_iso_to_mul_equiv CategoryTheory.Iso.semigroupCatIsoToMulEquiv
#align category_theory.iso.Semigroup_iso_to_add_equiv CategoryTheory.Iso.addSemigroupCatIsoToAddEquiv

end CategoryTheory.Iso

/-- multiplicative equivalences between `has_mul`s are the same as (isomorphic to) isomorphisms
in `Magma` -/
@[to_additive
      "additive equivalences between `has_add`s are the same\nas (isomorphic to) isomorphisms in `AddMagma`"]
def mulEquivIsoMagmaIso {X Y : Type u} [Mul X] [Mul Y] : X ≃* Y ≅ Magma.of X ≅ Magma.of Y where
  hom e := e.toMagmaIso
  inv i := i.magmaIsoToMulEquiv
  -- Porting note: both used to be proven automatically
  hom_inv_id := by
    aesop_cat_nonterminal
    sorry
    done
  inv_hom_id := by
    aesop_cat_nonterminal
    sorry
#align mul_equiv_iso_Magma_iso mulEquivIsoMagmaIso
#align add_equiv_iso_AddMagma_iso addEquivIsoAddMagmaIso

/-- multiplicative equivalences between `semigroup`s are the same as (isomorphic to) isomorphisms
in `Semigroup` -/
@[to_additive
      "additive equivalences between `add_semigroup`s are\nthe same as (isomorphic to) isomorphisms in `AddSemigroup`"]
def mulEquivIsoSemigroupCatIso {X Y : Type u} [Semigroup X] [Semigroup Y] :
    X ≃* Y ≅ SemigroupCat.of X ≅ SemigroupCat.of Y where
  hom e := e.toSemigroupCatIso
  inv i := i.semigroupCatIsoToMulEquiv
  -- Porting note: both used to be proven automatically
  hom_inv_id := by
    aesop_cat_nonterminal
    sorry
    done
  inv_hom_id := by
    aesop_cat_nonterminal
    sorry
#align mul_equiv_iso_Semigroup_iso mulEquivIsoSemigroupCatIso
#align add_equiv_iso_AddSemigroup_iso addEquivIsoAddSemigroupCatIso

@[to_additive]
instance Magma.forgetReflectsIsos : ReflectsIsomorphisms (forget Magma.{u}) where
  reflects {X Y} f _ := by
    skip
    let i := asIso ((forget Magma).map f)
    let e : X ≃* Y := { f, i.toEquiv with }
    exact ⟨(IsIso.of_iso e.toMagmaIso).1⟩
#align Magma.forget_reflects_isos Magma.forgetReflectsIsos
#align AddMagma.forget_reflects_isos AddMagma.forgetReflectsIsos

@[to_additive]
instance SemigroupCat.forgetReflectsIsos : ReflectsIsomorphisms (forget SemigroupCat.{u}) where
  reflects {X Y} f _ := by
    skip
    let i := asIso ((forget SemigroupCat).map f)
    let e : X ≃* Y := { f, i.toEquiv with }
    exact ⟨(IsIso.of_iso e.toSemigroupCatIso).1⟩
#align Semigroup.forget_reflects_isos SemigroupCat.forgetReflectsIsos
#align AddSemigroup.forget_reflects_isos AddSemigroupCat.forgetReflectsIsos

/-!
Once we've shown that the forgetful functors to type reflect isomorphisms,
we automatically obtain that the `forget₂` functors between our concrete categories
reflect isomorphisms.
-/

example : ReflectsIsomorphisms (forget₂ SemigroupCat Magma) := by infer_instance
