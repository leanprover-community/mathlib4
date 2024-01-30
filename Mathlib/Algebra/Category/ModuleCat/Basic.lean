/-
Copyright (c) 2019 Robert A. Spencer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert A. Spencer, Markus Himmel
-/
import Mathlib.Algebra.Category.GroupCat.Preadditive
import Mathlib.CategoryTheory.Conj
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

#align_import algebra.category.Module.basic from "leanprover-community/mathlib"@"829895f162a1f29d0133f4b3538f4cd1fb5bffd3"

/-!
# The category of `R`-modules

`Module.{v} R` is the category of bundled `R`-modules with carrier in the universe `v`. We show
that it is preadditive and show that being an isomorphism, monomorphism and epimorphism is
equivalent to being a linear equivalence, an injective linear map and a surjective linear map,
respectively.

## Implementation details

To construct an object in the category of `R`-modules from a type `M` with an instance of the
`Module` typeclass, write `of R M`. There is a coercion in the other direction.

Similarly, there is a coercion from morphisms in `Module R` to linear maps.

Porting note: the next two paragraphs should be revised.

Unfortunately, Lean is not smart enough to see that, given an object `M : Module R`, the expression
`of R M`, where we coerce `M` to the carrier type, is definitionally equal to `M` itself.
This means that to go the other direction, i.e., from linear maps/equivalences to (iso)morphisms
in the category of `R`-modules, we have to take care not to inadvertently end up with an
`of R M` where `M` is already an object. Hence, given `f : M →ₗ[R] N`,
* if `M N : Module R`, simply use `f`;
* if `M : Module R` and `N` is an unbundled `R`-module, use `↿f` or `asHomLeft f`;
* if `M` is an unbundled `R`-module and `N : Module R`, use `↾f` or `asHomRight f`;
* if `M` and `N` are unbundled `R`-modules, use `↟f` or `asHom f`.

Similarly, given `f : M ≃ₗ[R] N`, use `toModuleIso`, `toModuleIso'Left`, `toModuleIso'Right`
or `toModuleIso'`, respectively.

The arrow notations are localized, so you may have to `open ModuleCat` (or `open scoped ModuleCat`)
to use them. Note that the notation for `asHomLeft` clashes with the notation used to promote
functions between types to morphisms in the category `Type`, so to avoid confusion, it is probably a
good idea to avoid having the locales `Module` and `CategoryTheory.Type` open at the same time.

If you get an error when trying to apply a theorem and the `convert` tactic produces goals of the
form `M = of R M`, then you probably used an incorrect variant of `asHom` or `toModuleIso`.

-/

set_option linter.uppercaseLean3 false

open CategoryTheory

open CategoryTheory.Limits

open CategoryTheory.Limits.WalkingParallelPair

universe v u

variable (R : Type u) [Ring R]

/-- The category of R-modules and their morphisms.

 Note that in the case of `R = ℤ`, we can not
impose here that the `ℤ`-multiplication field from the module structure is defeq to the one coming
from the `isAddCommGroup` structure (contrary to what we do for all module structures in
mathlib), which creates some difficulties down the road. -/
structure ModuleCat where
  /-- the underlying type of an object in `ModuleCat R` -/
  carrier : Type v
  [isAddCommGroup : AddCommGroup carrier]
  [isModule : Module R carrier]
#align Module ModuleCat

attribute [instance] ModuleCat.isAddCommGroup ModuleCat.isModule

/-- An alias for `ModuleCat.{max u₁ u₂}`, to deal around unification issues.
Since the universe the ring lives in can be inferred, we put that last. -/
@[nolint checkUnivs]
abbrev ModuleCatMax.{v₁, v₂, u₁} (R : Type u₁) [Ring R] := ModuleCat.{max v₁ v₂, u₁} R

namespace ModuleCat

instance : CoeSort (ModuleCat.{v} R) (Type v) :=
  ⟨ModuleCat.carrier⟩

attribute [coe] ModuleCat.carrier

instance moduleCategory : Category.{v, max (v+1) u} (ModuleCat.{v} R) where
  Hom M N := M →ₗ[R] N
  id _ := LinearMap.id
  comp f g := g.comp f
  id_comp _ := LinearMap.id_comp _
  comp_id _ := LinearMap.comp_id _
  assoc f g h := LinearMap.comp_assoc (f := f) (g := g) (h := h)
#align Module.Module_category ModuleCat.moduleCategory

instance {M N : ModuleCat.{v} R} : LinearMapClass (M ⟶ N) R M N :=
  LinearMap.semilinearMapClass

instance moduleConcreteCategory : ConcreteCategory.{v} (ModuleCat.{v} R) where
  forget :=
    { obj := fun R => R
      map := fun f => f.toFun }
  forget_faithful := ⟨fun h => LinearMap.ext (fun x => by
    dsimp at h
    rw [h])⟩
#align Module.Module_concrete_category ModuleCat.moduleConcreteCategory

-- Porting note:
-- One might hope these two instances would not be needed,
-- as we already have `AddCommGroup M` and `Module R M`,
-- but sometimes we seem to need these when rewriting by lemmas about generic concrete categories.
instance {M : ModuleCat.{v} R} : AddCommGroup ((forget (ModuleCat R)).obj M) :=
  (inferInstance : AddCommGroup M)
instance {M : ModuleCat.{v} R} : Module R ((forget (ModuleCat R)).obj M) :=
  (inferInstance : Module R M)

@[ext]
lemma ext {M N : ModuleCat.{v} R} {f₁ f₂ : M ⟶ N} (h : ∀ (x : M), f₁ x = f₂ x) : f₁ = f₂ :=
  DFunLike.ext _ _ h

instance hasForgetToAddCommGroup : HasForget₂ (ModuleCat R) AddCommGroupCat where
  forget₂ :=
    { obj := fun M => AddCommGroupCat.of M
      map := fun f => AddCommGroupCat.ofHom f.toAddMonoidHom }
#align Module.has_forget_to_AddCommGroup ModuleCat.hasForgetToAddCommGroup

/-- The object in the category of R-modules associated to an R-module -/
def of (X : Type v) [AddCommGroup X] [Module R X] : ModuleCat R :=
  ⟨X⟩
#align Module.of ModuleCat.of

@[simp]
theorem forget₂_obj (X : ModuleCat R) :
    (forget₂ (ModuleCat R) AddCommGroupCat).obj X = AddCommGroupCat.of X :=
  rfl
#align Module.forget₂_obj ModuleCat.forget₂_obj

-- Porting note: the simpNF linter correctly doesn't like this.
-- I'm not sure what this is for, actually.
-- If it is really needed, better might be a simp lemma that says
-- `AddCommGroupCat.of (ModuleCat.of R X) = AddCommGroupCat.of X`.
-- @[simp 900]
theorem forget₂_obj_moduleCat_of (X : Type v) [AddCommGroup X] [Module R X] :
    (forget₂ (ModuleCat R) AddCommGroupCat).obj (of R X) = AddCommGroupCat.of X :=
  rfl
#align Module.forget₂_obj_Module_of ModuleCat.forget₂_obj_moduleCat_of

@[simp]
theorem forget₂_map (X Y : ModuleCat R) (f : X ⟶ Y) :
    (forget₂ (ModuleCat R) AddCommGroupCat).map f = LinearMap.toAddMonoidHom f :=
  rfl
#align Module.forget₂_map ModuleCat.forget₂_map

-- Porting note: TODO: `ofHom` and `asHom` are duplicates!

/-- Typecheck a `LinearMap` as a morphism in `Module R`. -/
def ofHom {R : Type u} [Ring R] {X Y : Type v} [AddCommGroup X] [Module R X] [AddCommGroup Y]
    [Module R Y] (f : X →ₗ[R] Y) : of R X ⟶ of R Y :=
  f
#align Module.of_hom ModuleCat.ofHom

@[simp 1100]
theorem ofHom_apply {R : Type u} [Ring R] {X Y : Type v} [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y] (f : X →ₗ[R] Y) (x : X) : ofHom f x = f x :=
  rfl
#align Module.of_hom_apply ModuleCat.ofHom_apply

instance : Inhabited (ModuleCat R) :=
  ⟨of R PUnit⟩

instance ofUnique {X : Type v} [AddCommGroup X] [Module R X] [i : Unique X] : Unique (of R X) :=
  i
#align Module.of_unique ModuleCat.ofUnique

-- Porting note: the simpNF linter complains, but we really need this?!
-- @[simp, nolint simpNF]
theorem coe_of (X : Type v) [AddCommGroup X] [Module R X] : (of R X : Type v) = X :=
  rfl
#align Module.coe_of ModuleCat.coe_of

variable {R}

/-- Forgetting to the underlying type and then building the bundled object returns the original
module. -/
@[simps]
def ofSelfIso (M : ModuleCat R) : ModuleCat.of R M ≅ M where
  hom := 𝟙 M
  inv := 𝟙 M
#align Module.of_self_iso ModuleCat.ofSelfIso

theorem isZero_of_subsingleton (M : ModuleCat R) [Subsingleton M] : IsZero M where
  unique_to X := ⟨⟨⟨(0 : M →ₗ[R] X)⟩, fun f => by
    ext x
    rw [Subsingleton.elim x (0 : M)]
    dsimp
    simp⟩⟩
  unique_from X := ⟨⟨⟨(0 : X →ₗ[R] M)⟩, fun f => by
    ext x
    apply Subsingleton.elim⟩⟩
#align Module.is_zero_of_subsingleton ModuleCat.isZero_of_subsingleton

instance : HasZeroObject (ModuleCat.{v} R) :=
  ⟨⟨of R PUnit, isZero_of_subsingleton _⟩⟩

variable {M N U : ModuleCat.{v} R}

@[simp]
theorem id_apply (m : M) : (𝟙 M : M → M) m = m :=
  rfl
#align Module.id_apply ModuleCat.id_apply

@[simp]
theorem coe_comp (f : M ⟶ N) (g : N ⟶ U) : (f ≫ g : M → U) = g ∘ f :=
  rfl
#align Module.coe_comp ModuleCat.coe_comp

theorem comp_def (f : M ⟶ N) (g : N ⟶ U) : f ≫ g = g.comp f :=
  rfl
#align Module.comp_def ModuleCat.comp_def

-- porting note: added
@[simp] lemma forget_map (f : M ⟶ N) : (forget (ModuleCat R)).map f = (f : M → N) := rfl

end ModuleCat

variable {R}

variable {X₁ X₂ : Type v}

/-- Reinterpreting a linear map in the category of `R`-modules. -/
def ModuleCat.asHom [AddCommGroup X₁] [Module R X₁] [AddCommGroup X₂] [Module R X₂] :
    (X₁ →ₗ[R] X₂) → (ModuleCat.of R X₁ ⟶ ModuleCat.of R X₂) :=
  id
#align Module.as_hom ModuleCat.asHom

/-- Reinterpreting a linear map in the category of `R`-modules -/
scoped[ModuleCat] notation "↟" f:1024 => ModuleCat.asHom f

/-- Reinterpreting a linear map in the category of `R`-modules. -/
def ModuleCat.asHomRight [AddCommGroup X₁] [Module R X₁] {X₂ : ModuleCat.{v} R} :
    (X₁ →ₗ[R] X₂) → (ModuleCat.of R X₁ ⟶ X₂) :=
  id
#align Module.as_hom_right ModuleCat.asHomRight

/-- Reinterpreting a linear map in the category of `R`-modules. -/
scoped[ModuleCat] notation "↾" f:1024 => ModuleCat.asHomRight f

/-- Reinterpreting a linear map in the category of `R`-modules. -/
def ModuleCat.asHomLeft {X₁ : ModuleCat.{v} R} [AddCommGroup X₂] [Module R X₂] :
    (X₁ →ₗ[R] X₂) → (X₁ ⟶ ModuleCat.of R X₂) :=
  id
#align Module.as_hom_left ModuleCat.asHomLeft

/-- Reinterpreting a linear map in the category of `R`-modules. -/
scoped[ModuleCat] notation "↿" f:1024 => ModuleCat.asHomLeft f

section

/-- Build an isomorphism in the category `Module R` from a `LinearEquiv` between `Module`s. -/
@[simps]
def LinearEquiv.toModuleIso {g₁ : AddCommGroup X₁} {g₂ : AddCommGroup X₂} {m₁ : Module R X₁}
    {m₂ : Module R X₂} (e : X₁ ≃ₗ[R] X₂) : ModuleCat.of R X₁ ≅ ModuleCat.of R X₂ where
  hom := (e : X₁ →ₗ[R] X₂)
  inv := (e.symm : X₂ →ₗ[R] X₁)
  hom_inv_id := by ext; apply e.left_inv
  inv_hom_id := by ext; apply e.right_inv
#align linear_equiv.to_Module_iso LinearEquiv.toModuleIso

/-- Build an isomorphism in the category `Module R` from a `LinearEquiv` between `Module`s. -/
abbrev LinearEquiv.toModuleIso' {M N : ModuleCat.{v} R} (i : M ≃ₗ[R] N) : M ≅ N :=
  i.toModuleIso
#align linear_equiv.to_Module_iso' LinearEquiv.toModuleIso'

/-- Build an isomorphism in the category `Module R` from a `linear_equiv` between `module`s. -/
abbrev LinearEquiv.toModuleIso'Left {X₁ : ModuleCat.{v} R} [AddCommGroup X₂] [Module R X₂]
    (e : X₁ ≃ₗ[R] X₂) : X₁ ≅ ModuleCat.of R X₂ :=
  e.toModuleIso
#align linear_equiv.to_Module_iso'_left LinearEquiv.toModuleIso'Left

/-- Build an isomorphism in the category `Module R` from a `linear_equiv` between `module`s. -/
abbrev LinearEquiv.toModuleIso'Right [AddCommGroup X₁] [Module R X₁] {X₂ : ModuleCat.{v} R}
    (e : X₁ ≃ₗ[R] X₂) : ModuleCat.of R X₁ ≅ X₂ :=
  e.toModuleIso
#align linear_equiv.to_Module_iso'_right LinearEquiv.toModuleIso'Right

namespace CategoryTheory.Iso

/-- Build a `linear_equiv` from an isomorphism in the category `Module R`. -/
@[simps]
def toLinearEquiv {X Y : ModuleCat R} (i : X ≅ Y) : X ≃ₗ[R] Y where
  toFun := i.hom
  invFun := i.inv
  left_inv x := by
    -- porting note: was `by tidy`
    change (i.hom ≫ i.inv) x = x
    simp
  right_inv x := by
    -- porting note: was `by tidy`
    change (i.inv ≫ i.hom) x = x
    simp
  map_add' := by simp
  map_smul' := by simp
#align category_theory.iso.to_linear_equiv CategoryTheory.Iso.toLinearEquiv

end CategoryTheory.Iso

/-- linear equivalences between `module`s are the same as (isomorphic to) isomorphisms
in `Module` -/
@[simps]
def linearEquivIsoModuleIso {X Y : Type u} [AddCommGroup X] [AddCommGroup Y] [Module R X]
    [Module R Y] : (X ≃ₗ[R] Y) ≅ ModuleCat.of R X ≅ ModuleCat.of R Y where
  hom e := e.toModuleIso
  inv i := i.toLinearEquiv
#align linear_equiv_iso_Module_iso linearEquivIsoModuleIso

end

namespace ModuleCat

instance {M N : ModuleCat.{v} R} : AddCommGroup (M ⟶ N) := LinearMap.addCommGroup

instance : Preadditive (ModuleCat.{v} R) where
  add_comp P Q R f f' g := by
    ext
    dsimp
    erw [map_add]
    rfl

instance forget₂_addCommGroupCat_additive : (forget₂ (ModuleCat.{v} R) AddCommGroupCat).Additive
    where
#align Module.forget₂_AddCommGroup_additive ModuleCat.forget₂_addCommGroupCat_additive

section

variable {S : Type u} [CommRing S]

instance : Linear S (ModuleCat.{v} S) where
  homModule X Y := LinearMap.module
  smul_comp := by
    intros
    ext
    dsimp
    rw [LinearMap.smul_apply, LinearMap.smul_apply, map_smul]
    rfl

variable {X Y X' Y' : ModuleCat.{v} S}

theorem Iso.homCongr_eq_arrowCongr (i : X ≅ X') (j : Y ≅ Y') (f : X ⟶ Y) :
    Iso.homCongr i j f = LinearEquiv.arrowCongr i.toLinearEquiv j.toLinearEquiv f :=
  rfl
#align Module.iso.hom_congr_eq_arrow_congr ModuleCat.Iso.homCongr_eq_arrowCongr

theorem Iso.conj_eq_conj (i : X ≅ X') (f : End X) :
    Iso.conj i f = LinearEquiv.conj i.toLinearEquiv f :=
  rfl
#align Module.iso.conj_eq_conj ModuleCat.Iso.conj_eq_conj

end

variable (M N : ModuleCat.{v} R)

/-- The scalar multiplication on an object of `ModuleCat R` considered as
a morphism of rings from `R` to the endomorphisms of the underlying abelian group. -/
def smul : R →+* End ((forget₂ (ModuleCat R) AddCommGroupCat).obj M) where
  toFun r :=
    { toFun := fun (m : M) => r • m
      map_zero' := by dsimp; rw [smul_zero]
      map_add' := fun x y => by dsimp; rw [smul_add] }
  map_one' := AddMonoidHom.ext (fun x => by dsimp; rw [one_smul])
  map_zero' := AddMonoidHom.ext (fun x => by dsimp; rw [zero_smul])
  map_mul' r s := AddMonoidHom.ext (fun (x : M) => (smul_smul r s x).symm)
  map_add' r s := AddMonoidHom.ext (fun (x : M) => add_smul r s x)

lemma smul_naturality {M N : ModuleCat.{v} R} (f : M ⟶ N) (r : R) :
    (forget₂ (ModuleCat R) AddCommGroupCat).map f ≫ N.smul r =
      M.smul r ≫ (forget₂ (ModuleCat R) AddCommGroupCat).map f := by
  ext x
  exact (f.map_smul r x).symm

variable (R)

/-- The scalar multiplication on `ModuleCat R` considered as a morphism of rings
to the endomorphisms of the forgetful functor to `AddCommGroupCat)`. -/
@[simps]
def smulNatTrans : R →+* End (forget₂ (ModuleCat R) AddCommGroupCat) where
  toFun r :=
    { app := fun M => M.smul r
      naturality := fun _ _ _ => smul_naturality _ r }
  map_one' := NatTrans.ext _ _ (by aesop_cat)
  map_zero' := NatTrans.ext _ _ (by aesop_cat)
  map_mul' _ _ := NatTrans.ext _ _ (by aesop_cat)
  map_add' _ _ := NatTrans.ext _ _ (by aesop_cat)

variable {R}

/-- Given `A : AddCommGroupCat` and a ring morphism `R →+* End A`, this is a type synonym
for `A`, on which we shall define a structure of `R`-module. -/
@[nolint unusedArguments]
def mkOfSMul' {A : AddCommGroupCat} (_ : R →+* End A) := A

section

variable {A : AddCommGroupCat} (φ : R →+* End A)

instance : AddCommGroup (mkOfSMul' φ) := by
  dsimp only [mkOfSMul']
  infer_instance

instance : SMul R (mkOfSMul' φ) := ⟨fun r (x : A) => (show A ⟶ A from φ r) x⟩

@[simp]
lemma mkOfSMul'_smul (r : R) (x : mkOfSMul' φ) :
    r • x = (show A ⟶ A from φ r) x := rfl

instance : Module R (mkOfSMul' φ) where
  smul_zero _ := map_zero _
  smul_add _ _ _ := map_add _ _ _
  one_smul := by simp
  mul_smul := by simp
  add_smul _ _ _ := by simp; rfl
  zero_smul := by simp

/-- Given `A : AddCommGroupCat` and a ring morphism `R →+* End A`, this is an object in
`ModuleCat R`, whose underlying abelian group is `A` and whose scalar multiplication is
given by `R`. -/
abbrev mkOfSMul := ModuleCat.of R (mkOfSMul' φ)

-- This lemma has always been bad, but lean4#2644 made `simp` start noticing
@[simp, nolint simpNF]
lemma mkOfSMul_smul (r : R) : (mkOfSMul φ).smul r = φ r := rfl

end

section

variable {M N}
  (φ : (forget₂ (ModuleCat R) AddCommGroupCat).obj M ⟶
      (forget₂ (ModuleCat R) AddCommGroupCat).obj N)
  (hφ : ∀ (r : R), φ ≫ N.smul r = M.smul r ≫ φ)

/-- Constructor for morphisms in `ModuleCat R` which takes as inputs
a morphism between the underlying objects in `AddCommGroupCat` and the compatibility
with the scalar multiplication. -/
@[simps]
def homMk : M ⟶ N where
  toFun := φ
  map_add' _ _ := map_add _ _ _
  map_smul' r x := (congr_hom (hφ r) x).symm

lemma forget₂_map_homMk :
    (forget₂ (ModuleCat R) AddCommGroupCat).map (homMk φ hφ) = φ := rfl

end

end ModuleCat
