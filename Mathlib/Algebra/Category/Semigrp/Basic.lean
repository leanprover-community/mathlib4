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
* `SemiGrp`
* `AddSemiGrp`
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
    --Porting note: was `@MulHom.coe_inj` which is deprecated
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
instance : CoeSort MagmaCat (Type*) where
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
def SemiGrp : Type (u + 1) :=
  Bundled Semigroup
#align Semigroup SemiGrp
#align AddSemigroup AddSemiGrp

/-- The category of additive semigroups and semigroup morphisms. -/
add_decl_doc AddSemiGrp

namespace SemiGrp

@[to_additive]
instance : BundledHom.ParentProjection @Semigroup.toMul := ⟨⟩

deriving instance LargeCategory for SemiGrp

-- Porting note: deriving failed for `ConcreteCategory`,
-- "default handlers have not been implemented yet"
-- https://github.com/leanprover-community/mathlib4/issues/5020
instance instConcreteCategory : ConcreteCategory SemiGrp :=
  BundledHom.concreteCategory (fun _ _ => _)

attribute [to_additive] instSemiGrpLargeCategory SemiGrp.instConcreteCategory

@[to_additive]
instance : CoeSort SemiGrp (Type*) where
  coe X := X.α

-- Porting note: Hinting to Lean that `forget R` and `R` are the same
unif_hint forget_obj_eq_coe (R : SemiGrp) where ⊢
  (forget SemiGrp).obj R ≟ R
unif_hint _root_.AddSemiGrp.forget_obj_eq_coe (R : AddSemiGrp) where ⊢
  (forget AddSemiGrp).obj R ≟ R

@[to_additive]
instance (X : SemiGrp) : Semigroup X := X.str

@[to_additive]
instance instFunLike (X Y : SemiGrp) : FunLike (X ⟶ Y) X Y :=
  inferInstanceAs <| FunLike (X →ₙ* Y) X Y

@[to_additive]
instance instMulHomClass (X Y : SemiGrp) : MulHomClass (X ⟶ Y) X Y :=
  inferInstanceAs <| MulHomClass (X →ₙ* Y) X Y

/-- Construct a bundled `SemiGrp` from the underlying type and typeclass. -/
@[to_additive]
def of (M : Type u) [Semigroup M] : SemiGrp :=
  Bundled.of M
#align Semigroup.of SemiGrp.of
#align AddSemigroup.of AddSemiGrp.of

/-- Construct a bundled `AddSemiGrp` from the underlying type and typeclass. -/
add_decl_doc AddSemiGrp.of

@[to_additive (attr := simp)]
theorem coe_of (R : Type u) [Semigroup R] : (SemiGrp.of R : Type u) = R :=
  rfl
#align Semigroup.coe_of SemiGrp.coe_of
#align AddSemigroup.coe_of AddSemiGrp.coe_of

@[to_additive (attr := simp)]
lemma mulEquiv_coe_eq {X Y : Type _} [Semigroup X] [Semigroup Y] (e : X ≃* Y) :
    (@DFunLike.coe (SemiGrp.of X ⟶ SemiGrp.of Y) _ (fun _ => (forget SemiGrp).obj _)
      ConcreteCategory.instFunLike (e : X →ₙ* Y) : X → Y) = ↑e :=
  rfl

/-- Typecheck a `MulHom` as a morphism in `SemiGrp`. -/
@[to_additive]
def ofHom {X Y : Type u} [Semigroup X] [Semigroup Y] (f : X →ₙ* Y) : of X ⟶ of Y :=
  f
#align Semigroup.of_hom SemiGrp.ofHom
#align AddSemigroup.of_hom AddSemiGrp.ofHom

/-- Typecheck an `AddHom` as a morphism in `AddSemiGrp`. -/
add_decl_doc AddSemiGrp.ofHom

@[to_additive] -- Porting note: simp removed, simpNF says LHS simplifies to itself
theorem ofHom_apply {X Y : Type u} [Semigroup X] [Semigroup Y] (f : X →ₙ* Y) (x : X) :
    ofHom f x = f x :=
  rfl
#align Semigroup.of_hom_apply SemiGrp.ofHom_apply
#align AddSemigroup.of_hom_apply AddSemiGrp.ofHom_apply

@[to_additive]
instance : Inhabited SemiGrp :=
  ⟨SemiGrp.of PEmpty⟩

@[to_additive]
instance hasForgetToMagmaCat : HasForget₂ SemiGrp MagmaCat :=
  BundledHom.forget₂ _ _
#align Semigroup.has_forget_to_Magma SemiGrp.hasForgetToMagmaCat
#align AddSemigroup.has_forget_to_AddMagma AddSemiGrp.hasForgetToAddMagmaCat

end SemiGrp

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
def MulEquiv.toSemiGrpIso (e : X ≃* Y) : SemiGrp.of X ≅ SemiGrp.of Y where
  hom := e.toMulHom
  inv := e.symm.toMulHom
#align mul_equiv.to_Semigroup_iso MulEquiv.toSemiGrpIso
#align add_equiv.to_AddSemigroup_iso AddEquiv.toAddSemiGrpIso

end

namespace CategoryTheory.Iso

/-- Build a `MulEquiv` from an isomorphism in the category `Magma`. -/
@[to_additive
      "Build an `AddEquiv` from an isomorphism in the category `AddMagma`."]
def magmaCatIsoToMulEquiv {X Y : MagmaCat} (i : X ≅ Y) : X ≃* Y :=
  MulHom.toMulEquiv i.hom i.inv i.hom_inv_id i.inv_hom_id
#align category_theory.iso.Magma_iso_to_mul_equiv CategoryTheory.Iso.magmaCatIsoToMulEquiv
#align category_theory.iso.AddMagma_iso_to_add_equiv CategoryTheory.Iso.addMagmaCatIsoToAddEquiv

/-- Build a `MulEquiv` from an isomorphism in the category `Semigroup`. -/
@[to_additive
  "Build an `AddEquiv` from an isomorphism in the category `AddSemigroup`."]
def semiGrpIsoToMulEquiv {X Y : SemiGrp} (i : X ≅ Y) : X ≃* Y :=
  MulHom.toMulEquiv i.hom i.inv i.hom_inv_id i.inv_hom_id
#align category_theory.iso.Semigroup_iso_to_mul_equiv CategoryTheory.Iso.semiGrpIsoToMulEquiv
#align category_theory.iso.Semigroup_iso_to_add_equiv CategoryTheory.Iso.addSemiGrpIsoToAddEquiv

end CategoryTheory.Iso

/-- multiplicative equivalences between `Mul`s are the same as (isomorphic to) isomorphisms
in `Magma` -/
@[to_additive
    "additive equivalences between `Add`s are the same
    as (isomorphic to) isomorphisms in `AddMagma`"]
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
def mulEquivIsoSemiGrpIso {X Y : Type u} [Semigroup X] [Semigroup Y] :
    X ≃* Y ≅ SemiGrp.of X ≅ SemiGrp.of Y where
  hom e := e.toSemiGrpIso
  inv i := i.semiGrpIsoToMulEquiv
#align mul_equiv_iso_Semigroup_iso mulEquivIsoSemiGrpIso
#align add_equiv_iso_AddSemigroup_iso addEquivIsoAddSemiGrpIso

@[to_additive]
instance MagmaCat.forgetReflectsIsos : ReflectsIsomorphisms (forget MagmaCat.{u}) where
  reflects {X Y} f _ := by
    let i := asIso ((forget MagmaCat).map f)
    let e : X ≃* Y := { f, i.toEquiv with }
    exact ⟨(IsIso.of_iso e.toMagmaCatIso).1⟩
#align Magma.forget_reflects_isos MagmaCat.forgetReflectsIsos
#align AddMagma.forget_reflects_isos AddMagmaCat.forgetReflectsIsos

@[to_additive]
instance SemiGrp.forgetReflectsIsos : ReflectsIsomorphisms (forget SemiGrp.{u}) where
  reflects {X Y} f _ := by
    let i := asIso ((forget SemiGrp).map f)
    let e : X ≃* Y := { f, i.toEquiv with }
    exact ⟨(IsIso.of_iso e.toSemiGrpIso).1⟩
#align Semigroup.forget_reflects_isos SemiGrp.forgetReflectsIsos
#align AddSemigroup.forget_reflects_isos AddSemiGrp.forgetReflectsIsos

-- porting note: this was added in order to ensure that `forget₂ CommMonCat MonCat`
-- automatically reflects isomorphisms
-- we could have used `CategoryTheory.ConcreteCategory.ReflectsIso` alternatively
@[to_additive]
instance SemiGrp.forget₂Full : Full (forget₂ SemiGrp MagmaCat) where preimage f := f

/-!
Once we've shown that the forgetful functors to type reflect isomorphisms,
we automatically obtain that the `forget₂` functors between our concrete categories
reflect isomorphisms.
-/

example : ReflectsIsomorphisms (forget₂ SemiGrp MagmaCat) := inferInstance
