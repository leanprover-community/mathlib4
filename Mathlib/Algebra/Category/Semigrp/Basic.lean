/-
Copyright (c) 2021 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Kuelshammer
-/
import Mathlib.Algebra.PEmptyInstances
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.CategoryTheory.ConcreteCategory.BundledHom
import Mathlib.CategoryTheory.Functor.ReflectsIso

#align_import algebra.category.Semigroup.basic from "leanprover-community/mathlib"@"47b51515e69f59bca5cf34ef456e6000fe205a69"

/-!
# Category instances for `Mul`, `Add`, `Semigroup` and `AddSemigroup`

We introduce the bundled categories:
* `MagmaCat`
* `AddMagmaCat`
* `Semigrp`
* `AddSemigrp`
along with the relevant forgetful functors between them.

This closely follows `Mathlib.Algebra.Category.MonCat.Basic`.

## TODO

* Limits in these categories
* free/forgetful adjunctions
-/

set_option linter.uppercaseLean3 false

universe u v

open CategoryTheory

/-- The category of magmas and magma morphisms. -/
@[to_additive]
def MagmaCat : Type (u + 1) :=
  Bundled Mul
#align Magma MagmaCat
#align AddMagma AddMagmaCat

/-- The category of additive magmas and additive magma morphisms. -/
add_decl_doc AddMagmaCat

namespace MagmaCat

@[to_additive]
instance bundledHom : BundledHom @MulHom :=
  ⟨@MulHom.toFun, @MulHom.id, @MulHom.comp,
    -- Porting note: was `@MulHom.coe_inj` which is deprecated
    by intros; apply @DFunLike.coe_injective, by aesop_cat, by aesop_cat⟩
#align Magma.bundled_hom MagmaCat.bundledHom
#align AddMagma.bundled_hom AddMagmaCat.bundledHom

-- Porting note: deriving failed for `ConcreteCategory`,
-- "default handlers have not been implemented yet"
-- https://github.com/leanprover-community/mathlib4/issues/5020
deriving instance LargeCategory for MagmaCat
instance instConcreteCategory : ConcreteCategory MagmaCat := BundledHom.concreteCategory MulHom

attribute [to_additive] instMagmaCatLargeCategory instConcreteCategory

@[to_additive]
instance : CoeSort MagmaCat Type* where
  coe X := X.α

-- Porting note: Hinting to Lean that `forget R` and `R` are the same
unif_hint forget_obj_eq_coe (R : MagmaCat) where ⊢
  (forget MagmaCat).obj R ≟ R
unif_hint _root_.AddMagmaCat.forget_obj_eq_coe (R : AddMagmaCat) where ⊢
  (forget AddMagmaCat).obj R ≟ R

@[to_additive]
instance (X : MagmaCat) : Mul X := X.str

@[to_additive]
instance instFunLike (X Y : MagmaCat) : FunLike (X ⟶ Y) X Y :=
  inferInstanceAs <| FunLike (X →ₙ* Y) X Y

@[to_additive]
instance instMulHomClass (X Y : MagmaCat) : MulHomClass (X ⟶ Y) X Y :=
  inferInstanceAs <| MulHomClass (X →ₙ* Y) X Y

/-- Construct a bundled `MagmaCat` from the underlying type and typeclass. -/
@[to_additive]
def of (M : Type u) [Mul M] : MagmaCat :=
  Bundled.of M
#align Magma.of MagmaCat.of
#align AddMagma.of AddMagmaCat.of

/-- Construct a bundled `AddMagmaCat` from the underlying type and typeclass. -/
add_decl_doc AddMagmaCat.of

@[to_additive (attr := simp)]
theorem coe_of (R : Type u) [Mul R] : (MagmaCat.of R : Type u) = R :=
  rfl
#align Magma.coe_of MagmaCat.coe_of
#align AddMagma.coe_of AddMagmaCat.coe_of

@[to_additive (attr := simp)]
lemma mulEquiv_coe_eq {X Y : Type _} [Mul X] [Mul Y] (e : X ≃* Y) :
    (@DFunLike.coe (MagmaCat.of X ⟶ MagmaCat.of Y) _ (fun _ => (forget MagmaCat).obj _)
      ConcreteCategory.instFunLike (e : X →ₙ* Y) : X → Y) = ↑e :=
  rfl

/-- Typecheck a `MulHom` as a morphism in `MagmaCat`. -/
@[to_additive]
def ofHom {X Y : Type u} [Mul X] [Mul Y] (f : X →ₙ* Y) : of X ⟶ of Y := f
#align Magma.of_hom MagmaCat.ofHom
#align AddMagma.of_hom AddMagmaCat.ofHom

/-- Typecheck an `AddHom` as a morphism in `AddMagmaCat`. -/
add_decl_doc AddMagmaCat.ofHom

@[to_additive] -- Porting note: simp removed, simpNF says LHS simplifies to itself
theorem ofHom_apply {X Y : Type u} [Mul X] [Mul Y] (f : X →ₙ* Y) (x : X) : ofHom f x = f x :=
  rfl
#align Magma.of_hom_apply MagmaCat.ofHom_apply
#align AddMagma.of_hom_apply AddMagmaCat.ofHom_apply

@[to_additive]
instance : Inhabited MagmaCat :=
  ⟨MagmaCat.of PEmpty⟩

end MagmaCat

/-- The category of semigroups and semigroup morphisms. -/
@[to_additive]
def Semigrp : Type (u + 1) :=
  Bundled Semigroup
#align Semigroup Semigrp
#align AddSemigroup AddSemigrp

/-- The category of additive semigroups and semigroup morphisms. -/
add_decl_doc AddSemigrp

namespace Semigrp

@[to_additive]
instance : BundledHom.ParentProjection @Semigroup.toMul := ⟨⟩

deriving instance LargeCategory for Semigrp

-- Porting note: deriving failed for `ConcreteCategory`,
-- "default handlers have not been implemented yet"
-- https://github.com/leanprover-community/mathlib4/issues/5020
instance instConcreteCategory : ConcreteCategory Semigrp :=
  BundledHom.concreteCategory (fun _ _ => _)

attribute [to_additive] instSemigrpLargeCategory Semigrp.instConcreteCategory

@[to_additive]
instance : CoeSort Semigrp Type* where
  coe X := X.α

-- Porting note: Hinting to Lean that `forget R` and `R` are the same
unif_hint forget_obj_eq_coe (R : Semigrp) where ⊢
  (forget Semigrp).obj R ≟ R
unif_hint _root_.AddSemigrp.forget_obj_eq_coe (R : AddSemigrp) where ⊢
  (forget AddSemigrp).obj R ≟ R

@[to_additive]
instance (X : Semigrp) : Semigroup X := X.str

@[to_additive]
instance instFunLike (X Y : Semigrp) : FunLike (X ⟶ Y) X Y :=
  inferInstanceAs <| FunLike (X →ₙ* Y) X Y

@[to_additive]
instance instMulHomClass (X Y : Semigrp) : MulHomClass (X ⟶ Y) X Y :=
  inferInstanceAs <| MulHomClass (X →ₙ* Y) X Y

/-- Construct a bundled `Semigrp` from the underlying type and typeclass. -/
@[to_additive]
def of (M : Type u) [Semigroup M] : Semigrp :=
  Bundled.of M
#align Semigroup.of Semigrp.of
#align AddSemigroup.of AddSemigrp.of

/-- Construct a bundled `AddSemigrp` from the underlying type and typeclass. -/
add_decl_doc AddSemigrp.of

@[to_additive (attr := simp)]
theorem coe_of (R : Type u) [Semigroup R] : (Semigrp.of R : Type u) = R :=
  rfl
#align Semigroup.coe_of Semigrp.coe_of
#align AddSemigroup.coe_of AddSemigrp.coe_of

@[to_additive (attr := simp)]
lemma mulEquiv_coe_eq {X Y : Type _} [Semigroup X] [Semigroup Y] (e : X ≃* Y) :
    (@DFunLike.coe (Semigrp.of X ⟶ Semigrp.of Y) _ (fun _ => (forget Semigrp).obj _)
      ConcreteCategory.instFunLike (e : X →ₙ* Y) : X → Y) = ↑e :=
  rfl

/-- Typecheck a `MulHom` as a morphism in `Semigrp`. -/
@[to_additive]
def ofHom {X Y : Type u} [Semigroup X] [Semigroup Y] (f : X →ₙ* Y) : of X ⟶ of Y :=
  f
#align Semigroup.of_hom Semigrp.ofHom
#align AddSemigroup.of_hom AddSemigrp.ofHom

/-- Typecheck an `AddHom` as a morphism in `AddSemigrp`. -/
add_decl_doc AddSemigrp.ofHom

@[to_additive] -- Porting note: simp removed, simpNF says LHS simplifies to itself
theorem ofHom_apply {X Y : Type u} [Semigroup X] [Semigroup Y] (f : X →ₙ* Y) (x : X) :
    ofHom f x = f x :=
  rfl
#align Semigroup.of_hom_apply Semigrp.ofHom_apply
#align AddSemigroup.of_hom_apply AddSemigrp.ofHom_apply

@[to_additive]
instance : Inhabited Semigrp :=
  ⟨Semigrp.of PEmpty⟩

@[to_additive]
instance hasForgetToMagmaCat : HasForget₂ Semigrp MagmaCat :=
  BundledHom.forget₂ _ _
#align Semigroup.has_forget_to_Magma Semigrp.hasForgetToMagmaCat
#align AddSemigroup.has_forget_to_AddMagma AddSemigrp.hasForgetToAddMagmaCat

end Semigrp

variable {X Y : Type u}

section

variable [Mul X] [Mul Y]

/-- Build an isomorphism in the category `MagmaCat` from a `MulEquiv` between `Mul`s. -/
@[to_additive (attr := simps)
      "Build an isomorphism in the category `AddMagmaCat` from an `AddEquiv` between `Add`s."]
def MulEquiv.toMagmaCatIso (e : X ≃* Y) : MagmaCat.of X ≅ MagmaCat.of Y where
  hom := e.toMulHom
  inv := e.symm.toMulHom
  hom_inv_id := by
    ext
    simp_rw [comp_apply, toMulHom_eq_coe, MagmaCat.mulEquiv_coe_eq, symm_apply_apply, id_apply]

#align mul_equiv.to_Magma_iso MulEquiv.toMagmaCatIso
#align add_equiv.to_AddMagma_iso AddEquiv.toAddMagmaCatIso

end

section

variable [Semigroup X] [Semigroup Y]

/-- Build an isomorphism in the category `Semigroup` from a `MulEquiv` between `Semigroup`s. -/
@[to_additive (attr := simps)
  "Build an isomorphism in the category
  `AddSemigroup` from an `AddEquiv` between `AddSemigroup`s."]
def MulEquiv.toSemigrpIso (e : X ≃* Y) : Semigrp.of X ≅ Semigrp.of Y where
  hom := e.toMulHom
  inv := e.symm.toMulHom
#align mul_equiv.to_Semigroup_iso MulEquiv.toSemigrpIso
#align add_equiv.to_AddSemigroup_iso AddEquiv.toAddSemigrpIso

end

namespace CategoryTheory.Iso

/-- Build a `MulEquiv` from an isomorphism in the category `MagmaCat`. -/
@[to_additive
      "Build an `AddEquiv` from an isomorphism in the category `AddMagmaCat`."]
def magmaCatIsoToMulEquiv {X Y : MagmaCat} (i : X ≅ Y) : X ≃* Y :=
  MulHom.toMulEquiv i.hom i.inv i.hom_inv_id i.inv_hom_id
#align category_theory.iso.Magma_iso_to_mul_equiv CategoryTheory.Iso.magmaCatIsoToMulEquiv
#align category_theory.iso.AddMagma_iso_to_add_equiv CategoryTheory.Iso.addMagmaCatIsoToAddEquiv

/-- Build a `MulEquiv` from an isomorphism in the category `Semigroup`. -/
@[to_additive
  "Build an `AddEquiv` from an isomorphism in the category `AddSemigroup`."]
def semigrpIsoToMulEquiv {X Y : Semigrp} (i : X ≅ Y) : X ≃* Y :=
  MulHom.toMulEquiv i.hom i.inv i.hom_inv_id i.inv_hom_id
#align category_theory.iso.Semigroup_iso_to_mul_equiv CategoryTheory.Iso.semigrpIsoToMulEquiv
#align category_theory.iso.Semigroup_iso_to_add_equiv CategoryTheory.Iso.addSemigrpIsoToAddEquiv

end CategoryTheory.Iso

/-- multiplicative equivalences between `Mul`s are the same as (isomorphic to) isomorphisms
in `MagmaCat` -/
@[to_additive
    "additive equivalences between `Add`s are the same
    as (isomorphic to) isomorphisms in `AddMagmaCat`"]
def mulEquivIsoMagmaIso {X Y : Type u} [Mul X] [Mul Y] :
    X ≃* Y ≅ MagmaCat.of X ≅ MagmaCat.of Y where
  hom e := e.toMagmaCatIso
  inv i := i.magmaCatIsoToMulEquiv
#align mul_equiv_iso_Magma_iso mulEquivIsoMagmaIso
#align add_equiv_iso_AddMagma_iso addEquivIsoAddMagmaIso

/-- multiplicative equivalences between `Semigroup`s are the same as (isomorphic to) isomorphisms
in `Semigroup` -/
@[to_additive
  "additive equivalences between `AddSemigroup`s are
  the same as (isomorphic to) isomorphisms in `AddSemigroup`"]
def mulEquivIsoSemigrpIso {X Y : Type u} [Semigroup X] [Semigroup Y] :
    X ≃* Y ≅ Semigrp.of X ≅ Semigrp.of Y where
  hom e := e.toSemigrpIso
  inv i := i.semigrpIsoToMulEquiv
#align mul_equiv_iso_Semigroup_iso mulEquivIsoSemigrpIso
#align add_equiv_iso_AddSemigroup_iso addEquivIsoAddSemigrpIso

@[to_additive]
instance MagmaCat.forgetReflectsIsos : (forget MagmaCat.{u}).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget MagmaCat).map f)
    let e : X ≃* Y := { f, i.toEquiv with }
    exact e.toMagmaCatIso.isIso_hom
#align Magma.forget_reflects_isos MagmaCat.forgetReflectsIsos
#align AddMagma.forget_reflects_isos AddMagmaCat.forgetReflectsIsos

@[to_additive]
instance Semigrp.forgetReflectsIsos : (forget Semigrp.{u}).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget Semigrp).map f)
    let e : X ≃* Y := { f, i.toEquiv with }
    exact e.toSemigrpIso.isIso_hom
#align Semigroup.forget_reflects_isos Semigrp.forgetReflectsIsos
#align AddSemigroup.forget_reflects_isos AddSemigrp.forgetReflectsIsos

-- Porting note: this was added in order to ensure that `forget₂ CommMonCat MonCat`
-- automatically reflects isomorphisms
-- we could have used `CategoryTheory.ConcreteCategory.ReflectsIso` alternatively
@[to_additive]
instance Semigrp.forget₂_full : (forget₂ Semigrp MagmaCat).Full where
  map_surjective f := ⟨f, rfl⟩

/-!
Once we've shown that the forgetful functors to type reflect isomorphisms,
we automatically obtain that the `forget₂` functors between our concrete categories
reflect isomorphisms.
-/

example : (forget₂ Semigrp MagmaCat).ReflectsIsomorphisms := inferInstance
