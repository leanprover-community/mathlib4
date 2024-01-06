/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro, Anne Baanen,
  Frédéric Dupuis, Heather Macbeth
-/
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Ring.CompTypeclasses
import Mathlib.Algebra.Star.Basic
import Mathlib.Data.Set.Pointwise.SMul
import Mathlib.GroupTheory.GroupAction.Hom

#align_import algebra.module.linear_map from "leanprover-community/mathlib"@"cc8e88c7c8c7bc80f91f84d11adb584bf9bd658f"

/-!
# (Semi)linear maps

In this file we define

* `LinearMap σ M M₂`, `M →ₛₗ[σ] M₂` : a semilinear map between two `Module`s. Here,
  `σ` is a `RingHom` from `R` to `R₂` and an `f : M →ₛₗ[σ] M₂` satisfies
  `f (c • x) = (σ c) • (f x)`. We recover plain linear maps by choosing `σ` to be `RingHom.id R`.
  This is denoted by `M →ₗ[R] M₂`. We also add the notation `M →ₗ⋆[R] M₂` for star-linear maps.

* `IsLinearMap R f` : predicate saying that `f : M → M₂` is a linear map. (Note that this
  was not generalized to semilinear maps.)

We then provide `LinearMap` with the following instances:

* `LinearMap.addCommMonoid` and `LinearMap.addCommGroup`: the elementwise addition structures
  corresponding to addition in the codomain
* `LinearMap.distribMulAction` and `LinearMap.module`: the elementwise scalar action structures
  corresponding to applying the action in the codomain.
* `Module.End.semiring` and `Module.End.ring`: the (semi)ring of endomorphisms formed by taking the
  additive structure above with composition as multiplication.

## Implementation notes

To ensure that composition works smoothly for semilinear maps, we use the typeclasses
`RingHomCompTriple`, `RingHomInvPair` and `RingHomSurjective` from
`Mathlib.Algebra.Ring.CompTypeclasses`.

## Notation

* Throughout the file, we denote regular linear maps by `fₗ`, `gₗ`, etc, and semilinear maps
  by `f`, `g`, etc.

## TODO

* Parts of this file have not yet been generalized to semilinear maps (i.e. `CompatibleSMul`)

## Tags

linear map
-/


assert_not_exists Submonoid
assert_not_exists Finset

open Function

universe u u' v w x y z

variable {R R₁ R₂ R₃ k S S₃ T M M₁ M₂ M₃ N₁ N₂ N₃ ι : Type*}

/-- A map `f` between modules over a semiring is linear if it satisfies the two properties
`f (x + y) = f x + f y` and `f (c • x) = c • f x`. The predicate `IsLinearMap R f` asserts this
property. A bundled version is available with `LinearMap`, and should be favored over
`IsLinearMap` most of the time. -/
structure IsLinearMap (R : Type u) {M : Type v} {M₂ : Type w} [Semiring R] [AddCommMonoid M]
  [AddCommMonoid M₂] [Module R M] [Module R M₂] (f : M → M₂) : Prop where
  /-- A linear map preserves addition. -/
  map_add : ∀ x y, f (x + y) = f x + f y
  /-- A linear map preserves scalar multiplication. -/
  map_smul : ∀ (c : R) (x), f (c • x) = c • f x
#align is_linear_map IsLinearMap

section

/-- A map `f` between an `R`-module and an `S`-module over a ring homomorphism `σ : R →+* S`
is semilinear if it satisfies the two properties `f (x + y) = f x + f y` and
`f (c • x) = (σ c) • f x`. Elements of `LinearMap σ M M₂` (available under the notation
`M →ₛₗ[σ] M₂`) are bundled versions of such maps. For plain linear maps (i.e. for which
`σ = RingHom.id R`), the notation `M →ₗ[R] M₂` is available. An unbundled version of plain linear
maps is available with the predicate `IsLinearMap`, but it should be avoided most of the time. -/
structure LinearMap {R S : Type*} [Semiring R] [Semiring S] (σ : R →+* S) (M : Type*)
    (M₂ : Type*) [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module S M₂] extends
    AddHom M M₂ where
  /-- A linear map preserves scalar multiplication.
  We prefer the spelling `_root_.map_smul` instead. -/
  protected map_smul' : ∀ (r : R) (x : M), toFun (r • x) = σ r • toFun x
#align linear_map LinearMap

/-- The `AddHom` underlying a `LinearMap`. -/
add_decl_doc LinearMap.toAddHom
#align linear_map.to_add_hom LinearMap.toAddHom

-- mathport name: «expr →ₛₗ[ ] »
/-- `M →ₛₗ[σ] N` is the type of `σ`-semilinear maps from `M` to `N`. -/
notation:25 M " →ₛₗ[" σ:25 "] " M₂:0 => LinearMap σ M M₂

/-- `M →ₗ[R] N` is the type of `R`-linear maps from `M` to `N`. -/
-- mathport name: «expr →ₗ[ ] »
notation:25 M " →ₗ[" R:25 "] " M₂:0 => LinearMap (RingHom.id R) M M₂

/-- `M →ₗ⋆[R] N` is the type of `R`-conjugate-linear maps from `M` to `N`. -/
-- mathport name: «expr →ₗ⋆[ ] »
notation:25 M " →ₗ⋆[" R:25 "] " M₂:0 => LinearMap (starRingEnd R) M M₂

/-- `SemilinearMapClass F σ M M₂` asserts `F` is a type of bundled `σ`-semilinear maps `M → M₂`.

See also `LinearMapClass F R M M₂` for the case where `σ` is the identity map on `R`.

A map `f` between an `R`-module and an `S`-module over a ring homomorphism `σ : R →+* S`
is semilinear if it satisfies the two properties `f (x + y) = f x + f y` and
`f (c • x) = (σ c) • f x`. -/
class SemilinearMapClass (F : Type*) {R S : outParam (Type*)} [Semiring R] [Semiring S]
  (σ : outParam (R →+* S)) (M M₂ : outParam (Type*)) [AddCommMonoid M] [AddCommMonoid M₂]
  [Module R M] [Module S M₂] extends AddHomClass F M M₂ where
  /-- A semilinear map preserves scalar multiplication up to some ring homomorphism `σ`.
  See also `_root_.map_smul` for the case where `σ` is the identity. -/
  map_smulₛₗ : ∀ (f : F) (r : R) (x : M), f (r • x) = σ r • f x
#align semilinear_map_class SemilinearMapClass

end

-- Porting note: `dangerousInstance` linter has become smarter about `outParam`s
-- `σ` becomes a metavariable but that's fine because it's an `outParam`
-- attribute [nolint dangerousInstance] SemilinearMapClass.toAddHomClass

export SemilinearMapClass (map_smulₛₗ)

attribute [simp] map_smulₛₗ

/-- `LinearMapClass F R M M₂` asserts `F` is a type of bundled `R`-linear maps `M → M₂`.

This is an abbreviation for `SemilinearMapClass F (RingHom.id R) M M₂`.
-/
abbrev LinearMapClass (F : Type*) (R M M₂ : outParam (Type*)) [Semiring R] [AddCommMonoid M]
    [AddCommMonoid M₂] [Module R M] [Module R M₂] :=
  SemilinearMapClass F (RingHom.id R) M M₂
#align linear_map_class LinearMapClass

namespace SemilinearMapClass

variable (F : Type*)
variable [Semiring R] [Semiring S]
variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable [Module R M] [Module R M₂] [Module S M₃]
variable {σ : R →+* S}

-- Porting note: the `dangerousInstance` linter has become smarter about `outParam`s
instance (priority := 100) addMonoidHomClass [SemilinearMapClass F σ M M₃] :
    AddMonoidHomClass F M M₃ :=
  { SemilinearMapClass.toAddHomClass with
    map_zero := fun f ↦
      show f 0 = 0 by
        rw [← zero_smul R (0 : M), map_smulₛₗ]
        simp }

instance (priority := 100) distribMulActionHomClass [LinearMapClass F R M M₂] :
    DistribMulActionHomClass F R M M₂ :=
  { SemilinearMapClass.addMonoidHomClass F with
    map_smul := fun f c x ↦ by rw [map_smulₛₗ, RingHom.id_apply] }

variable {F} (f : F) [i : SemilinearMapClass F σ M M₃]

theorem map_smul_inv {σ' : S →+* R} [RingHomInvPair σ σ'] (c : S) (x : M) :
    c • f x = f (σ' c • x) := by simp
#align semilinear_map_class.map_smul_inv SemilinearMapClass.map_smul_inv

/-- Reinterpret an element of a type of semilinear maps as a semilinear map. -/
abbrev semilinearMap : M →ₛₗ[σ] M₃ where
  toFun := f
  map_add' := map_add f
  map_smul' := map_smulₛₗ f

end SemilinearMapClass

namespace LinearMapClass
variable {F : Type*} [Semiring R] [AddCommMonoid M₁] [AddCommMonoid M₂] [Module R M₁] [Module R M₂]
  (f : F) [LinearMapClass F R M₁ M₂]

/-- Reinterpret an element of a type of linear maps as a linear map. -/
abbrev linearMap : M₁ →ₗ[R] M₂ := SemilinearMapClass.semilinearMap f

end LinearMapClass

namespace LinearMap

section AddCommMonoid

variable [Semiring R] [Semiring S]

section

variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]

variable [AddCommMonoid N₁] [AddCommMonoid N₂] [AddCommMonoid N₃]

variable [Module R M] [Module R M₂] [Module S M₃]

variable {σ : R →+* S}

instance semilinearMapClass : SemilinearMapClass (M →ₛₗ[σ] M₃) σ M M₃ where
  coe f := f.toFun
  coe_injective' f g h := by
    cases f
    cases g
    congr
    apply FunLike.coe_injective'
    exact h
  map_add f := f.map_add'
  map_smulₛₗ := LinearMap.map_smul'
#align linear_map.semilinear_map_class LinearMap.semilinearMapClass

-- Porting note: we don't port specialized `CoeFun` instances if there is `FunLike` instead
#noalign LinearMap.has_coe_to_fun

-- Porting note: adding this instance prevents a timeout in `ext_ring_op`
instance instFunLike {σ : R →+* S} : FunLike (M →ₛₗ[σ] M₃) M (λ _ ↦ M₃) :=
  { AddHomClass.toFunLike with }

/-- The `DistribMulActionHom` underlying a `LinearMap`. -/
def toDistribMulActionHom (f : M →ₗ[R] M₂) : DistribMulActionHom R M M₂ :=
  { f with map_zero' := show f 0 = 0 from map_zero f }
#align linear_map.to_distrib_mul_action_hom LinearMap.toDistribMulActionHom

@[simp]
theorem coe_toAddHom (f : M →ₛₗ[σ] M₃) : ⇑f.toAddHom = f := rfl

-- porting note: no longer a `simp`
theorem toFun_eq_coe {f : M →ₛₗ[σ] M₃} : f.toFun = (f : M → M₃) := rfl
#align linear_map.to_fun_eq_coe LinearMap.toFun_eq_coe

@[ext]
theorem ext {f g : M →ₛₗ[σ] M₃} (h : ∀ x, f x = g x) : f = g :=
  FunLike.ext f g h
#align linear_map.ext LinearMap.ext

/-- Copy of a `LinearMap` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : M →ₛₗ[σ] M₃) (f' : M → M₃) (h : f' = ⇑f) : M →ₛₗ[σ] M₃ where
  toFun := f'
  map_add' := h.symm ▸ f.map_add'
  map_smul' := h.symm ▸ f.map_smul'
#align linear_map.copy LinearMap.copy

@[simp]
theorem coe_copy (f : M →ₛₗ[σ] M₃) (f' : M → M₃) (h : f' = ⇑f) : ⇑(f.copy f' h) = f' :=
  rfl
#align linear_map.coe_copy LinearMap.coe_copy

theorem copy_eq (f : M →ₛₗ[σ] M₃) (f' : M → M₃) (h : f' = ⇑f) : f.copy f' h = f :=
  FunLike.ext' h
#align linear_map.copy_eq LinearMap.copy_eq

initialize_simps_projections LinearMap (toFun → apply)

@[simp]
theorem coe_mk {σ : R →+* S} (f : AddHom M M₃) (h) :
    ((LinearMap.mk f h : M →ₛₗ[σ] M₃) : M → M₃) = f :=
  rfl
#align linear_map.coe_mk LinearMap.coe_mk

-- Porting note: This theorem is new.
@[simp]
theorem coe_addHom_mk {σ : R →+* S} (f : AddHom M M₃) (h) :
    ((LinearMap.mk f h : M →ₛₗ[σ] M₃) : AddHom M M₃) = f :=
  rfl

/-- Identity map as a `LinearMap` -/
def id : M →ₗ[R] M :=
  { DistribMulActionHom.id R with }
#align linear_map.id LinearMap.id

theorem id_apply (x : M) : @id R M _ _ _ x = x :=
  rfl
#align linear_map.id_apply LinearMap.id_apply

@[simp, norm_cast]
theorem id_coe : ((LinearMap.id : M →ₗ[R] M) : M → M) = _root_.id :=
  rfl
#align linear_map.id_coe LinearMap.id_coe

/-- A generalisation of `LinearMap.id` that constructs the identity function
as a `σ`-semilinear map for any ring homomorphism `σ` which we know is the identity. -/
@[simps]
def id' {σ : R →+* R} [RingHomId σ] : M →ₛₗ[σ] M where
  toFun x := x
  map_add' x y := rfl
  map_smul' r x := by
    have := (RingHomId.eq_id : σ = _)
    subst this
    rfl

@[simp, norm_cast]
theorem id'_coe {σ : R →+* R} [RingHomId σ] : ((id' : M →ₛₗ[σ] M) : M → M) = _root_.id :=
  rfl

end

section

variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]

variable [AddCommMonoid N₁] [AddCommMonoid N₂] [AddCommMonoid N₃]

variable [Module R M] [Module R M₂] [Module S M₃]

variable (σ : R →+* S)

variable (fₗ gₗ : M →ₗ[R] M₂) (f g : M →ₛₗ[σ] M₃)

theorem isLinear : IsLinearMap R fₗ :=
  ⟨fₗ.map_add', fₗ.map_smul'⟩
#align linear_map.is_linear LinearMap.isLinear

variable {fₗ gₗ f g σ}

theorem coe_injective : Injective (FunLike.coe : (M →ₛₗ[σ] M₃) → _) :=
  FunLike.coe_injective
#align linear_map.coe_injective LinearMap.coe_injective

protected theorem congr_arg {x x' : M} : x = x' → f x = f x' :=
  FunLike.congr_arg f
#align linear_map.congr_arg LinearMap.congr_arg

/-- If two linear maps are equal, they are equal at each point. -/
protected theorem congr_fun (h : f = g) (x : M) : f x = g x :=
  FunLike.congr_fun h x
#align linear_map.congr_fun LinearMap.congr_fun

theorem ext_iff : f = g ↔ ∀ x, f x = g x :=
  FunLike.ext_iff
#align linear_map.ext_iff LinearMap.ext_iff

@[simp]
theorem mk_coe (f : M →ₛₗ[σ] M₃) (h) : (LinearMap.mk f h : M →ₛₗ[σ] M₃) = f :=
  ext fun _ ↦ rfl
#align linear_map.mk_coe LinearMap.mk_coe

variable (fₗ gₗ f g)

protected theorem map_add (x y : M) : f (x + y) = f x + f y :=
  map_add f x y
#align linear_map.map_add LinearMap.map_add

protected theorem map_zero : f 0 = 0 :=
  map_zero f
#align linear_map.map_zero LinearMap.map_zero

-- Porting note: `simp` wasn't picking up `map_smulₛₗ` for `LinearMap`s without specifying
-- `map_smulₛₗ f`, so we marked this as `@[simp]` in Mathlib3.
-- For Mathlib4, let's try without the `@[simp]` attribute and hope it won't need to be re-enabled.
protected theorem map_smulₛₗ (c : R) (x : M) : f (c • x) = σ c • f x :=
  map_smulₛₗ f c x
#align linear_map.map_smulₛₗ LinearMap.map_smulₛₗ

protected theorem map_smul (c : R) (x : M) : fₗ (c • x) = c • fₗ x :=
  map_smul fₗ c x
#align linear_map.map_smul LinearMap.map_smul

protected theorem map_smul_inv {σ' : S →+* R} [RingHomInvPair σ σ'] (c : S) (x : M) :
    c • f x = f (σ' c • x) := by simp
#align linear_map.map_smul_inv LinearMap.map_smul_inv

@[simp]
theorem map_eq_zero_iff (h : Function.Injective f) {x : M} : f x = 0 ↔ x = 0 :=
  _root_.map_eq_zero_iff f h
#align linear_map.map_eq_zero_iff LinearMap.map_eq_zero_iff

section Pointwise

open Pointwise

variable (M M₃ σ) {F : Type*} (h : F)

@[simp]
theorem _root_.image_smul_setₛₗ [SemilinearMapClass F σ M M₃] (c : R) (s : Set M) :
    h '' (c • s) = σ c • h '' s := by
  apply Set.Subset.antisymm
  · rintro x ⟨y, ⟨z, zs, rfl⟩, rfl⟩
    exact ⟨h z, Set.mem_image_of_mem _ zs, (map_smulₛₗ _ _ _).symm⟩
  · rintro x ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact (Set.mem_image _ _ _).2 ⟨c • z, Set.smul_mem_smul_set hz, map_smulₛₗ _ _ _⟩
#align image_smul_setₛₗ image_smul_setₛₗ

theorem _root_.preimage_smul_setₛₗ [SemilinearMapClass F σ M M₃] {c : R} (hc : IsUnit c)
    (s : Set M₃) :
    h ⁻¹' (σ c • s) = c • h ⁻¹' s := by
  apply Set.Subset.antisymm
  · rintro x ⟨y, ys, hy⟩
    refine' ⟨(hc.unit.inv : R) • x, _, _⟩
    · simp only [← hy, smul_smul, Set.mem_preimage, Units.inv_eq_val_inv, map_smulₛₗ h, ← map_mul,
        IsUnit.val_inv_mul, one_smul, map_one, ys]
    · simp only [smul_smul, IsUnit.mul_val_inv, one_smul, Units.inv_eq_val_inv]
  · rintro x ⟨y, hy, rfl⟩
    refine' ⟨h y, hy, by simp only [RingHom.id_apply, map_smulₛₗ h]⟩
#align preimage_smul_setₛₗ preimage_smul_setₛₗ

variable (R M₂)

theorem _root_.image_smul_set [LinearMapClass F R M M₂] (c : R) (s : Set M) :
    h '' (c • s) = c • h '' s :=
  image_smul_setₛₗ _ _ _ h c s
#align image_smul_set image_smul_set

theorem _root_.preimage_smul_set [LinearMapClass F R M M₂] {c : R} (hc : IsUnit c) (s : Set M₂) :
    h ⁻¹' (c • s) = c • h ⁻¹' s :=
  preimage_smul_setₛₗ _ _ _ h hc s
#align preimage_smul_set preimage_smul_set

end Pointwise

variable (M M₂)

/-- A typeclass for `SMul` structures which can be moved through a `LinearMap`.
This typeclass is generated automatically from an `IsScalarTower` instance, but exists so that
we can also add an instance for `AddCommGroup.intModule`, allowing `z •` to be moved even if
`R` does not support negation.
-/
class CompatibleSMul (R S : Type*) [Semiring S] [SMul R M] [Module S M] [SMul R M₂]
  [Module S M₂] : Prop where
  /-- Scalar multiplication by `R` of `M` can be moved through linear maps. -/
  map_smul : ∀ (fₗ : M →ₗ[S] M₂) (c : R) (x : M), fₗ (c • x) = c • fₗ x
#align linear_map.compatible_smul LinearMap.CompatibleSMul

variable {M M₂}

instance (priority := 100) IsScalarTower.compatibleSMul {R S : Type*} [Semiring S] [SMul R S]
    [SMul R M] [Module S M] [IsScalarTower R S M] [SMul R M₂] [Module S M₂] [IsScalarTower R S M₂] :
    CompatibleSMul M M₂ R S :=
  ⟨fun fₗ c x ↦ by rw [← smul_one_smul S c x, ← smul_one_smul S c (fₗ x), map_smul]⟩
#align linear_map.is_scalar_tower.compatible_smul LinearMap.IsScalarTower.compatibleSMul

@[simp]
theorem map_smul_of_tower {R S : Type*} [Semiring S] [SMul R M] [Module S M] [SMul R M₂]
    [Module S M₂] [CompatibleSMul M M₂ R S] (fₗ : M →ₗ[S] M₂) (c : R) (x : M) :
    fₗ (c • x) = c • fₗ x :=
  CompatibleSMul.map_smul fₗ c x
#align linear_map.map_smul_of_tower LinearMap.map_smul_of_tower

/-- convert a linear map to an additive map -/
def toAddMonoidHom : M →+ M₃ where
  toFun := f
  map_zero' := f.map_zero
  map_add' := f.map_add
#align linear_map.to_add_monoid_hom LinearMap.toAddMonoidHom

@[simp]
theorem toAddMonoidHom_coe : ⇑f.toAddMonoidHom = f :=
  rfl
#align linear_map.to_add_monoid_hom_coe LinearMap.toAddMonoidHom_coe

section RestrictScalars

variable (R)
variable [Module S M] [Module S M₂] [CompatibleSMul M M₂ R S]

/-- If `M` and `M₂` are both `R`-modules and `S`-modules and `R`-module structures
are defined by an action of `R` on `S` (formally, we have two scalar towers), then any `S`-linear
map from `M` to `M₂` is `R`-linear.

See also `LinearMap.map_smul_of_tower`. -/
@[coe] def restrictScalars (fₗ : M →ₗ[S] M₂) : M →ₗ[R] M₂ where
  toFun := fₗ
  map_add' := fₗ.map_add
  map_smul' := fₗ.map_smul_of_tower
#align linear_map.restrict_scalars LinearMap.restrictScalars

-- porting note: generalized from `Algebra` to `CompatibleSMul`
instance coeIsScalarTower : CoeHTCT (M →ₗ[S] M₂) (M →ₗ[R] M₂) :=
  ⟨restrictScalars R⟩
#align linear_map.coe_is_scalar_tower LinearMap.coeIsScalarTower

@[simp, norm_cast]
theorem coe_restrictScalars (f : M →ₗ[S] M₂) : ((f : M →ₗ[R] M₂) : M → M₂) = f :=
  rfl
#align linear_map.coe_restrict_scalars LinearMap.coe_restrictScalars

theorem restrictScalars_apply (fₗ : M →ₗ[S] M₂) (x) : restrictScalars R fₗ x = fₗ x :=
  rfl
#align linear_map.restrict_scalars_apply LinearMap.restrictScalars_apply

theorem restrictScalars_injective :
    Function.Injective (restrictScalars R : (M →ₗ[S] M₂) → M →ₗ[R] M₂) := fun _ _ h ↦
  ext (LinearMap.congr_fun h : _)
#align linear_map.restrict_scalars_injective LinearMap.restrictScalars_injective

@[simp]
theorem restrictScalars_inj (fₗ gₗ : M →ₗ[S] M₂) :
    fₗ.restrictScalars R = gₗ.restrictScalars R ↔ fₗ = gₗ :=
  (restrictScalars_injective R).eq_iff
#align linear_map.restrict_scalars_inj LinearMap.restrictScalars_inj

end RestrictScalars

theorem toAddMonoidHom_injective :
    Function.Injective (toAddMonoidHom : (M →ₛₗ[σ] M₃) → M →+ M₃) := fun fₗ gₗ h ↦
  ext <| (FunLike.congr_fun h : ∀ x, fₗ.toAddMonoidHom x = gₗ.toAddMonoidHom x)
#align linear_map.to_add_monoid_hom_injective LinearMap.toAddMonoidHom_injective

/-- If two `σ`-linear maps from `R` are equal on `1`, then they are equal. -/
@[ext high]
theorem ext_ring {f g : R →ₛₗ[σ] M₃} (h : f 1 = g 1) : f = g :=
  ext fun x ↦ by rw [← mul_one x, ← smul_eq_mul, f.map_smulₛₗ, g.map_smulₛₗ, h]
#align linear_map.ext_ring LinearMap.ext_ring

theorem ext_ring_iff {σ : R →+* R} {f g : R →ₛₗ[σ] M} : f = g ↔ f 1 = g 1 :=
  ⟨fun h ↦ h ▸ rfl, ext_ring⟩
#align linear_map.ext_ring_iff LinearMap.ext_ring_iff

@[ext high]
theorem ext_ring_op {σ : Rᵐᵒᵖ →+* S} {f g : R →ₛₗ[σ] M₃} (h : f (1 : R) = g (1 : R)) :
    f = g :=
  ext fun x ↦ by
    -- Porting note: replaced the oneliner `rw` proof with a partially term-mode proof
    -- because `rw` was giving "motive is type incorrect" errors
    rw [← one_mul x, ← op_smul_eq_mul]
    refine (f.map_smulₛₗ (MulOpposite.op x) 1).trans ?_
    rw [h]
    exact (g.map_smulₛₗ (MulOpposite.op x) 1).symm
#align linear_map.ext_ring_op LinearMap.ext_ring_op

end

/-- Interpret a `RingHom` `f` as an `f`-semilinear map. -/
@[simps]
def _root_.RingHom.toSemilinearMap (f : R →+* S) : R →ₛₗ[f] S :=
  { f with
    map_smul' := f.map_mul }
#align ring_hom.to_semilinear_map RingHom.toSemilinearMap
#align ring_hom.to_semilinear_map_apply RingHom.toSemilinearMap_apply

section

variable [Semiring R₁] [Semiring R₂] [Semiring R₃]
variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable {module_M₁ : Module R₁ M₁} {module_M₂ : Module R₂ M₂} {module_M₃ : Module R₃ M₃}
variable {σ₁₂ : R₁ →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R₁ →+* R₃}
variable [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
variable (f : M₂ →ₛₗ[σ₂₃] M₃) (g : M₁ →ₛₗ[σ₁₂] M₂)

/-- Composition of two linear maps is a linear map -/
def comp : M₁ →ₛₗ[σ₁₃] M₃ where
  toFun := f ∘ g
  map_add' := by simp only [map_add, forall_const, Function.comp_apply]
  map_smul' r x := by simp only [Function.comp_apply, map_smulₛₗ, RingHomCompTriple.comp_apply]
#align linear_map.comp LinearMap.comp

/-- `∘ₗ` is notation for composition of two linear (not semilinear!) maps into a linear map.
This is useful when Lean is struggling to infer the `RingHomCompTriple` instance. -/
notation3:80 (name := compNotation) f:81 " ∘ₗ " g:80 =>
  @LinearMap.comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (RingHom.id _) (RingHom.id _) (RingHom.id _)
    RingHomCompTriple.ids f g

theorem comp_apply (x : M₁) : f.comp g x = f (g x) :=
  rfl
#align linear_map.comp_apply LinearMap.comp_apply

@[simp, norm_cast]
theorem coe_comp : (f.comp g : M₁ → M₃) = f ∘ g :=
  rfl
#align linear_map.coe_comp LinearMap.coe_comp

@[simp]
theorem comp_id : f.comp id = f :=
  LinearMap.ext fun _ ↦ rfl
#align linear_map.comp_id LinearMap.comp_id

@[simp]
theorem id_comp : id.comp f = f :=
  LinearMap.ext fun _ ↦ rfl
#align linear_map.id_comp LinearMap.id_comp

theorem comp_assoc
    {R₄ M₄ : Type*} [Semiring R₄] [AddCommMonoid M₄] [Module R₄ M₄]
    {σ₃₄ : R₃ →+* R₄} {σ₂₄ : R₂ →+* R₄} {σ₁₄ : R₁ →+* R₄}
    [RingHomCompTriple σ₂₃ σ₃₄ σ₂₄] [RingHomCompTriple σ₁₃ σ₃₄ σ₁₄] [RingHomCompTriple σ₁₂ σ₂₄ σ₁₄]
    (f : M₁ →ₛₗ[σ₁₂] M₂) (g : M₂ →ₛₗ[σ₂₃] M₃) (h : M₃ →ₛₗ[σ₃₄] M₄) :
    ((h.comp g : M₂ →ₛₗ[σ₂₄] M₄).comp f : M₁ →ₛₗ[σ₁₄] M₄) = h.comp (g.comp f : M₁ →ₛₗ[σ₁₃] M₃) :=
  rfl
#align linear_map.comp_assoc LinearMap.comp_assoc

variable {f g} {f' : M₂ →ₛₗ[σ₂₃] M₃} {g' : M₁ →ₛₗ[σ₁₂] M₂}

/-- The linear map version of `Function.Surjective.injective_comp_right` -/
lemma _root_.Function.Surjective.injective_linearMapComp_right (hg : Surjective g) :
    Injective fun f : M₂ →ₛₗ[σ₂₃] M₃ ↦ f.comp g :=
  fun _ _ h ↦ ext <| hg.forall.2 (ext_iff.1 h)

@[simp]
theorem cancel_right (hg : Surjective g) : f.comp g = f'.comp g ↔ f = f' :=
  hg.injective_linearMapComp_right.eq_iff
#align linear_map.cancel_right LinearMap.cancel_right

/-- The linear map version of `Function.Injective.comp_left` -/
lemma _root_.Function.Injective.injective_linearMapComp_left (hf : Injective f) :
    Injective fun g : M₁ →ₛₗ[σ₁₂] M₂ ↦ f.comp g :=
  fun g₁ g₂ (h : f.comp g₁ = f.comp g₂) ↦ ext fun x ↦ hf <| by rw [← comp_apply, h, comp_apply]

@[simp]
theorem cancel_left (hf : Injective f) : f.comp g = f.comp g' ↔ g = g' :=
  hf.injective_linearMapComp_left.eq_iff
#align linear_map.cancel_left LinearMap.cancel_left

end

variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]

/-- If a function `g` is a left and right inverse of a linear map `f`, then `g` is linear itself. -/
def inverse [Module R M] [Module S M₂] {σ : R →+* S} {σ' : S →+* R} [RingHomInvPair σ σ']
    (f : M →ₛₗ[σ] M₂) (g : M₂ → M) (h₁ : LeftInverse g f) (h₂ : RightInverse g f) :
    M₂ →ₛₗ[σ'] M := by
  dsimp [LeftInverse, Function.RightInverse] at h₁ h₂
  exact
    { toFun := g
      map_add' := fun x y ↦ by rw [← h₁ (g (x + y)), ← h₁ (g x + g y)]; simp [h₂]
      map_smul' := fun a b ↦ by
        dsimp only
        rw [← h₁ (g (a • b)), ← h₁ (σ' a • g b)]
        simp [h₂] }
#align linear_map.inverse LinearMap.inverse

end AddCommMonoid

section AddCommGroup

variable [Semiring R] [Semiring S] [AddCommGroup M] [AddCommGroup M₂]

variable {module_M : Module R M} {module_M₂ : Module S M₂} {σ : R →+* S}

variable (f : M →ₛₗ[σ] M₂)

protected theorem map_neg (x : M) : f (-x) = -f x :=
  map_neg f x
#align linear_map.map_neg LinearMap.map_neg

protected theorem map_sub (x y : M) : f (x - y) = f x - f y :=
  map_sub f x y
#align linear_map.map_sub LinearMap.map_sub

instance CompatibleSMul.intModule {S : Type*} [Semiring S] [Module S M] [Module S M₂] :
    CompatibleSMul M M₂ ℤ S :=
  ⟨fun fₗ c x ↦ by
    induction c using Int.induction_on with
    | hz => simp
    | hp n ih => simp [add_smul, ih]
    | hn n ih => simp [sub_smul, ih]⟩
#align linear_map.compatible_smul.int_module LinearMap.CompatibleSMul.intModule

instance CompatibleSMul.units {R S : Type*} [Monoid R] [MulAction R M] [MulAction R M₂]
    [Semiring S] [Module S M] [Module S M₂] [CompatibleSMul M M₂ R S] : CompatibleSMul M M₂ Rˣ S :=
  ⟨fun fₗ c x ↦ (CompatibleSMul.map_smul fₗ (c : R) x : _)⟩
#align linear_map.compatible_smul.units LinearMap.CompatibleSMul.units

end AddCommGroup

end LinearMap

namespace Module

/-- `g : R →+* S` is `R`-linear when the module structure on `S` is `Module.compHom S g` . -/
@[simps]
def compHom.toLinearMap {R S : Type*} [Semiring R] [Semiring S] (g : R →+* S) :
    letI := compHom S g; R →ₗ[R] S :=
  letI := compHom S g
  { toFun := (g : R → S)
    map_add' := g.map_add
    map_smul' := g.map_mul }
#align module.comp_hom.to_linear_map Module.compHom.toLinearMap
#align module.comp_hom.to_linear_map_apply Module.compHom.toLinearMap_apply

end Module

namespace DistribMulActionHom

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module R M₂]

/-- A `DistribMulActionHom` between two modules is a linear map. -/
@[coe]
def toLinearMap (fₗ : M →+[R] M₂) : M →ₗ[R] M₂ :=
  { fₗ with }
#align distrib_mul_action_hom.to_linear_map DistribMulActionHom.toLinearMap

instance : CoeTC (M →+[R] M₂) (M →ₗ[R] M₂) :=
  ⟨toLinearMap⟩

-- Porting note: because coercions get unfolded, there is no need for this rewrite
#noalign distrib_mul_action_hom.to_linear_map_eq_coe

-- Porting note: removed @[norm_cast] attribute due to error:
-- norm_cast: badly shaped lemma, rhs can't start with coe
@[simp]
theorem coe_toLinearMap (f : M →+[R] M₂) : ((f : M →ₗ[R] M₂) : M → M₂) = f :=
  rfl
#align distrib_mul_action_hom.coe_to_linear_map DistribMulActionHom.coe_toLinearMap

theorem toLinearMap_injective {f g : M →+[R] M₂} (h : (f : M →ₗ[R] M₂) = (g : M →ₗ[R] M₂)) :
    f = g := by
  ext m
  exact LinearMap.congr_fun h m
#align distrib_mul_action_hom.to_linear_map_injective DistribMulActionHom.toLinearMap_injective

end DistribMulActionHom

namespace IsLinearMap

section AddCommMonoid

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M₂]
variable [Module R M] [Module R M₂]

/-- Convert an `IsLinearMap` predicate to a `LinearMap` -/
def mk' (f : M → M₂) (H : IsLinearMap R f) : M →ₗ[R] M₂ where
  toFun := f
  map_add' := H.1
  map_smul' := H.2
#align is_linear_map.mk' IsLinearMap.mk'

@[simp]
theorem mk'_apply {f : M → M₂} (H : IsLinearMap R f) (x : M) : mk' f H x = f x :=
  rfl
#align is_linear_map.mk'_apply IsLinearMap.mk'_apply

theorem isLinearMap_smul {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] (c : R) :
    IsLinearMap R fun z : M ↦ c • z := by
  refine' IsLinearMap.mk (smul_add c) _
  intro _ _
  simp only [smul_smul, mul_comm]
#align is_linear_map.is_linear_map_smul IsLinearMap.isLinearMap_smul

theorem isLinearMap_smul' {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] (a : M) :
    IsLinearMap R fun c : R ↦ c • a :=
  IsLinearMap.mk (fun x y ↦ add_smul x y a) fun x y ↦ mul_smul x y a
#align is_linear_map.is_linear_map_smul' IsLinearMap.isLinearMap_smul'

variable {f : M → M₂} (lin : IsLinearMap R f)

theorem map_zero : f (0 : M) = (0 : M₂) :=
  (lin.mk' f).map_zero
#align is_linear_map.map_zero IsLinearMap.map_zero

end AddCommMonoid

section AddCommGroup

variable [Semiring R] [AddCommGroup M] [AddCommGroup M₂]
variable [Module R M] [Module R M₂]

theorem isLinearMap_neg : IsLinearMap R fun z : M ↦ -z :=
  IsLinearMap.mk neg_add fun x y ↦ (smul_neg x y).symm
#align is_linear_map.is_linear_map_neg IsLinearMap.isLinearMap_neg

variable {f : M → M₂} (lin : IsLinearMap R f)

theorem map_neg (x : M) : f (-x) = -f x :=
  (lin.mk' f).map_neg x
#align is_linear_map.map_neg IsLinearMap.map_neg

theorem map_sub (x y) : f (x - y) = f x - f y :=
  (lin.mk' f).map_sub x y
#align is_linear_map.map_sub IsLinearMap.map_sub

end AddCommGroup

end IsLinearMap

/-- Linear endomorphisms of a module, with associated ring structure
`Module.End.semiring` and algebra structure `Module.End.algebra`. -/
abbrev Module.End (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] [Module R M] :=
  M →ₗ[R] M
#align module.End Module.End

/-- Reinterpret an additive homomorphism as an `ℕ`-linear map. -/
def AddMonoidHom.toNatLinearMap [AddCommMonoid M] [AddCommMonoid M₂] (f : M →+ M₂) : M →ₗ[ℕ] M₂
    where
  toFun := f
  map_add' := f.map_add
  map_smul' := map_nsmul f
#align add_monoid_hom.to_nat_linear_map AddMonoidHom.toNatLinearMap

theorem AddMonoidHom.toNatLinearMap_injective [AddCommMonoid M] [AddCommMonoid M₂] :
    Function.Injective (@AddMonoidHom.toNatLinearMap M M₂ _ _) := by
  intro f g h
  ext x
  exact LinearMap.congr_fun h x
#align add_monoid_hom.to_nat_linear_map_injective AddMonoidHom.toNatLinearMap_injective

/-- Reinterpret an additive homomorphism as a `ℤ`-linear map. -/
def AddMonoidHom.toIntLinearMap [AddCommGroup M] [AddCommGroup M₂] (f : M →+ M₂) : M →ₗ[ℤ] M₂
    where
  toFun := f
  map_add' := f.map_add
  map_smul' := map_zsmul f
#align add_monoid_hom.to_int_linear_map AddMonoidHom.toIntLinearMap

theorem AddMonoidHom.toIntLinearMap_injective [AddCommGroup M] [AddCommGroup M₂] :
    Function.Injective (@AddMonoidHom.toIntLinearMap M M₂ _ _) := by
  intro f g h
  ext x
  exact LinearMap.congr_fun h x
#align add_monoid_hom.to_int_linear_map_injective AddMonoidHom.toIntLinearMap_injective

@[simp]
theorem AddMonoidHom.coe_toIntLinearMap [AddCommGroup M] [AddCommGroup M₂] (f : M →+ M₂) :
    ⇑f.toIntLinearMap = f :=
  rfl
#align add_monoid_hom.coe_to_int_linear_map AddMonoidHom.coe_toIntLinearMap

/-- Reinterpret an additive homomorphism as a `ℚ`-linear map. -/
def AddMonoidHom.toRatLinearMap [AddCommGroup M] [Module ℚ M] [AddCommGroup M₂] [Module ℚ M₂]
    (f : M →+ M₂) : M →ₗ[ℚ] M₂ :=
  { f with map_smul' := map_rat_smul f }
#align add_monoid_hom.to_rat_linear_map AddMonoidHom.toRatLinearMap

theorem AddMonoidHom.toRatLinearMap_injective [AddCommGroup M] [Module ℚ M] [AddCommGroup M₂]
    [Module ℚ M₂] : Function.Injective (@AddMonoidHom.toRatLinearMap M M₂ _ _ _ _) := by
  intro f g h
  ext x
  exact LinearMap.congr_fun h x
#align add_monoid_hom.to_rat_linear_map_injective AddMonoidHom.toRatLinearMap_injective

@[simp]
theorem AddMonoidHom.coe_toRatLinearMap [AddCommGroup M] [Module ℚ M] [AddCommGroup M₂]
    [Module ℚ M₂] (f : M →+ M₂) : ⇑f.toRatLinearMap = f :=
  rfl
#align add_monoid_hom.coe_to_rat_linear_map AddMonoidHom.coe_toRatLinearMap

namespace LinearMap

section SMul

variable [Semiring R] [Semiring R₂] [Semiring R₃]
variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable [Module R M] [Module R₂ M₂] [Module R₃ M₃]
variable {σ₁₂ : R →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R →+* R₃} [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
variable [Monoid S] [DistribMulAction S M₂] [SMulCommClass R₂ S M₂]
variable [Monoid S₃] [DistribMulAction S₃ M₃] [SMulCommClass R₃ S₃ M₃]
variable [Monoid T] [DistribMulAction T M₂] [SMulCommClass R₂ T M₂]

instance : SMul S (M →ₛₗ[σ₁₂] M₂) :=
  ⟨fun a f ↦
    { toFun := a • (f : M → M₂)
      map_add' := fun x y ↦ by simp only [Pi.smul_apply, f.map_add, smul_add]
      map_smul' := fun c x ↦ by simp [Pi.smul_apply, smul_comm] }⟩

@[simp]
theorem smul_apply (a : S) (f : M →ₛₗ[σ₁₂] M₂) (x : M) : (a • f) x = a • f x :=
  rfl
#align linear_map.smul_apply LinearMap.smul_apply

theorem coe_smul (a : S) (f : M →ₛₗ[σ₁₂] M₂) : (a • f : M →ₛₗ[σ₁₂] M₂) = a • (f : M → M₂) :=
  rfl
#align linear_map.coe_smul LinearMap.coe_smul

instance [SMulCommClass S T M₂] : SMulCommClass S T (M →ₛₗ[σ₁₂] M₂) :=
  ⟨fun _ _ _ ↦ ext fun _ ↦ smul_comm _ _ _⟩

-- example application of this instance: if S -> T -> R are homomorphisms of commutative rings and
-- M and M₂ are R-modules then the S-module and T-module structures on Hom_R(M,M₂) are compatible.
instance [SMul S T] [IsScalarTower S T M₂] : IsScalarTower S T (M →ₛₗ[σ₁₂] M₂) where
  smul_assoc _ _ _ := ext fun _ ↦ smul_assoc _ _ _

instance [DistribMulAction Sᵐᵒᵖ M₂] [SMulCommClass R₂ Sᵐᵒᵖ M₂] [IsCentralScalar S M₂] :
    IsCentralScalar S (M →ₛₗ[σ₁₂] M₂) where
  op_smul_eq_smul _ _ := ext fun _ ↦ op_smul_eq_smul _ _

end SMul

/-! ### Arithmetic on the codomain -/


section Arithmetic

variable [Semiring R₁] [Semiring R₂] [Semiring R₃]
variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable [AddCommGroup N₁] [AddCommGroup N₂] [AddCommGroup N₃]
variable [Module R₁ M] [Module R₂ M₂] [Module R₃ M₃]
variable [Module R₁ N₁] [Module R₂ N₂] [Module R₃ N₃]
variable {σ₁₂ : R₁ →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R₁ →+* R₃} [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

/-- The constant 0 map is linear. -/
instance : Zero (M →ₛₗ[σ₁₂] M₂) :=
  ⟨{  toFun := 0
      map_add' := by simp
      map_smul' := by simp }⟩

@[simp]
theorem zero_apply (x : M) : (0 : M →ₛₗ[σ₁₂] M₂) x = 0 :=
  rfl
#align linear_map.zero_apply LinearMap.zero_apply

@[simp]
theorem comp_zero (g : M₂ →ₛₗ[σ₂₃] M₃) : (g.comp (0 : M →ₛₗ[σ₁₂] M₂) : M →ₛₗ[σ₁₃] M₃) = 0 :=
  ext fun c ↦ by rw [comp_apply, zero_apply, zero_apply, g.map_zero]
#align linear_map.comp_zero LinearMap.comp_zero

@[simp]
theorem zero_comp (f : M →ₛₗ[σ₁₂] M₂) : ((0 : M₂ →ₛₗ[σ₂₃] M₃).comp f : M →ₛₗ[σ₁₃] M₃) = 0 :=
  rfl
#align linear_map.zero_comp LinearMap.zero_comp

instance : Inhabited (M →ₛₗ[σ₁₂] M₂) :=
  ⟨0⟩

@[simp]
theorem default_def : (default : M →ₛₗ[σ₁₂] M₂) = 0 :=
  rfl
#align linear_map.default_def LinearMap.default_def

/-- The sum of two linear maps is linear. -/
instance : Add (M →ₛₗ[σ₁₂] M₂) :=
  ⟨fun f g ↦
    { toFun := f + g
      map_add' := by simp [add_comm, add_left_comm]
      map_smul' := by simp [smul_add] }⟩

@[simp]
theorem add_apply (f g : M →ₛₗ[σ₁₂] M₂) (x : M) : (f + g) x = f x + g x :=
  rfl
#align linear_map.add_apply LinearMap.add_apply

theorem add_comp (f : M →ₛₗ[σ₁₂] M₂) (g h : M₂ →ₛₗ[σ₂₃] M₃) :
    ((h + g).comp f : M →ₛₗ[σ₁₃] M₃) = h.comp f + g.comp f :=
  rfl
#align linear_map.add_comp LinearMap.add_comp

theorem comp_add (f g : M →ₛₗ[σ₁₂] M₂) (h : M₂ →ₛₗ[σ₂₃] M₃) :
    (h.comp (f + g) : M →ₛₗ[σ₁₃] M₃) = h.comp f + h.comp g :=
  ext fun _ ↦ h.map_add _ _
#align linear_map.comp_add LinearMap.comp_add

/-- The type of linear maps is an additive monoid. -/
instance addCommMonoid : AddCommMonoid (M →ₛₗ[σ₁₂] M₂) :=
  FunLike.coe_injective.addCommMonoid _ rfl (fun _ _ ↦ rfl) fun _ _ ↦ rfl

/-- The negation of a linear map is linear. -/
instance : Neg (M →ₛₗ[σ₁₂] N₂) :=
  ⟨fun f ↦
    { toFun := -f
      map_add' := by simp [add_comm]
      map_smul' := by simp }⟩

@[simp]
theorem neg_apply (f : M →ₛₗ[σ₁₂] N₂) (x : M) : (-f) x = -f x :=
  rfl
#align linear_map.neg_apply LinearMap.neg_apply

@[simp]
theorem neg_comp (f : M →ₛₗ[σ₁₂] M₂) (g : M₂ →ₛₗ[σ₂₃] N₃) : (-g).comp f = -g.comp f :=
  rfl
#align linear_map.neg_comp LinearMap.neg_comp

@[simp]
theorem comp_neg (f : M →ₛₗ[σ₁₂] N₂) (g : N₂ →ₛₗ[σ₂₃] N₃) : g.comp (-f) = -g.comp f :=
  ext fun _ ↦ g.map_neg _
#align linear_map.comp_neg LinearMap.comp_neg

/-- The subtraction of two linear maps is linear. -/
instance : Sub (M →ₛₗ[σ₁₂] N₂) :=
  ⟨fun f g ↦
    { toFun := f - g
      map_add' := fun x y ↦ by simp only [Pi.sub_apply, map_add, add_sub_add_comm]
      map_smul' := fun r x ↦ by simp [Pi.sub_apply, map_smul, smul_sub] }⟩

@[simp]
theorem sub_apply (f g : M →ₛₗ[σ₁₂] N₂) (x : M) : (f - g) x = f x - g x :=
  rfl
#align linear_map.sub_apply LinearMap.sub_apply

theorem sub_comp (f : M →ₛₗ[σ₁₂] M₂) (g h : M₂ →ₛₗ[σ₂₃] N₃) :
    (g - h).comp f = g.comp f - h.comp f :=
  rfl
#align linear_map.sub_comp LinearMap.sub_comp

theorem comp_sub (f g : M →ₛₗ[σ₁₂] N₂) (h : N₂ →ₛₗ[σ₂₃] N₃) :
    h.comp (g - f) = h.comp g - h.comp f :=
  ext fun _ ↦ h.map_sub _ _
#align linear_map.comp_sub LinearMap.comp_sub

/-- The type of linear maps is an additive group. -/
instance addCommGroup : AddCommGroup (M →ₛₗ[σ₁₂] N₂) :=
  FunLike.coe_injective.addCommGroup _ rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) fun _ _ ↦ rfl

end Arithmetic

section Actions

variable [Semiring R] [Semiring R₂] [Semiring R₃]
variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable [Module R M] [Module R₂ M₂] [Module R₃ M₃]
variable {σ₁₂ : R →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R →+* R₃} [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

section SMul

variable [Monoid S] [DistribMulAction S M₂] [SMulCommClass R₂ S M₂]
variable [Monoid S₃] [DistribMulAction S₃ M₃] [SMulCommClass R₃ S₃ M₃]
variable [Monoid T] [DistribMulAction T M₂] [SMulCommClass R₂ T M₂]

instance : DistribMulAction S (M →ₛₗ[σ₁₂] M₂)
    where
  one_smul _ := ext fun _ ↦ one_smul _ _
  mul_smul _ _ _ := ext fun _ ↦ mul_smul _ _ _
  smul_add _ _ _ := ext fun _ ↦ smul_add _ _ _
  smul_zero _ := ext fun _ ↦ smul_zero _

theorem smul_comp (a : S₃) (g : M₂ →ₛₗ[σ₂₃] M₃) (f : M →ₛₗ[σ₁₂] M₂) :
    (a • g).comp f = a • g.comp f :=
  rfl
#align linear_map.smul_comp LinearMap.smul_comp

-- TODO: generalize this to semilinear maps
theorem comp_smul [Module R M₂] [Module R M₃] [SMulCommClass R S M₂] [DistribMulAction S M₃]
    [SMulCommClass R S M₃] [CompatibleSMul M₃ M₂ S R] (g : M₃ →ₗ[R] M₂) (a : S) (f : M →ₗ[R] M₃) :
    g.comp (a • f) = a • g.comp f :=
  ext fun _ ↦ g.map_smul_of_tower _ _
#align linear_map.comp_smul LinearMap.comp_smul

end SMul

section Module

variable [Semiring S] [Module S M₂] [SMulCommClass R₂ S M₂]

instance module : Module S (M →ₛₗ[σ₁₂] M₂) where
  add_smul _ _ _ := ext fun _ ↦ add_smul _ _ _
  zero_smul _ := ext fun _ ↦ zero_smul _ _

instance [NoZeroSMulDivisors S M₂] : NoZeroSMulDivisors S (M →ₛₗ[σ₁₂] M₂) :=
  coe_injective.noZeroSMulDivisors _ rfl coe_smul

end Module

end Actions

/-!
### Monoid structure of endomorphisms
-/


section Endomorphisms

variable [Semiring R] [AddCommMonoid M] [AddCommGroup N₁] [Module R M] [Module R N₁]

instance : One (Module.End R M) :=
  ⟨LinearMap.id⟩

instance : Mul (Module.End R M) :=
  ⟨LinearMap.comp⟩

theorem one_eq_id : (1 : Module.End R M) = id :=
  rfl
#align linear_map.one_eq_id LinearMap.one_eq_id

theorem mul_eq_comp (f g : Module.End R M) : f * g = f.comp g :=
  rfl
#align linear_map.mul_eq_comp LinearMap.mul_eq_comp

@[simp]
theorem one_apply (x : M) : (1 : Module.End R M) x = x :=
  rfl
#align linear_map.one_apply LinearMap.one_apply

@[simp]
theorem mul_apply (f g : Module.End R M) (x : M) : (f * g) x = f (g x) :=
  rfl
#align linear_map.mul_apply LinearMap.mul_apply

theorem coe_one : ⇑(1 : Module.End R M) = _root_.id :=
  rfl
#align linear_map.coe_one LinearMap.coe_one

theorem coe_mul (f g : Module.End R M) : ⇑(f * g) = f ∘ g :=
  rfl
#align linear_map.coe_mul LinearMap.coe_mul

instance _root_.Module.End.monoid : Monoid (Module.End R M) where
  mul := (· * ·)
  one := (1 : M →ₗ[R] M)
  mul_assoc f g h := LinearMap.ext fun x ↦ rfl
  mul_one := comp_id
  one_mul := id_comp
#align module.End.monoid Module.End.monoid

instance _root_.Module.End.semiring : Semiring (Module.End R M) :=
  { AddMonoidWithOne.unary, Module.End.monoid, LinearMap.addCommMonoid with
    mul_zero := comp_zero
    zero_mul := zero_comp
    left_distrib := fun _ _ _ ↦ comp_add _ _ _
    right_distrib := fun _ _ _ ↦ add_comp _ _ _
    natCast := fun n ↦ n • (1 : M →ₗ[R] M)
    natCast_zero := zero_smul ℕ (1 : M →ₗ[R] M)
    natCast_succ := fun n ↦ (AddMonoid.nsmul_succ n (1 : M →ₗ[R] M)).trans (add_comm _ _) }
#align module.End.semiring Module.End.semiring

/-- See also `Module.End.natCast_def`. -/
@[simp]
theorem _root_.Module.End.natCast_apply (n : ℕ) (m : M) : (↑n : Module.End R M) m = n • m :=
  rfl
#align module.End.nat_cast_apply Module.End.natCast_apply

@[simp]
theorem _root_.Module.End.ofNat_apply (n : ℕ) [n.AtLeastTwo] (m : M) :
    (no_index (OfNat.ofNat n) : Module.End R M) m = OfNat.ofNat n • m :=
  rfl

instance _root_.Module.End.ring : Ring (Module.End R N₁) :=
  { Module.End.semiring, LinearMap.addCommGroup with
    intCast := fun z ↦ z • (1 : N₁ →ₗ[R] N₁)
    intCast_ofNat := ofNat_zsmul _
    intCast_negSucc := negSucc_zsmul _ }
#align module.End.ring Module.End.ring

/-- See also `Module.End.intCast_def`. -/
@[simp]
theorem _root_.Module.End.intCast_apply (z : ℤ) (m : N₁) : (z : Module.End R N₁) m = z • m :=
  rfl
#align module.End.int_cast_apply Module.End.intCast_apply

section

variable [Monoid S] [DistribMulAction S M] [SMulCommClass R S M]

instance _root_.Module.End.isScalarTower :
    IsScalarTower S (Module.End R M) (Module.End R M) :=
  ⟨smul_comp⟩
#align module.End.is_scalar_tower Module.End.isScalarTower

instance _root_.Module.End.smulCommClass [SMul S R] [IsScalarTower S R M] :
    SMulCommClass S (Module.End R M) (Module.End R M) :=
  ⟨fun s _ _ ↦ (comp_smul _ s _).symm⟩
#align module.End.smul_comm_class Module.End.smulCommClass

instance _root_.Module.End.smulCommClass' [SMul S R] [IsScalarTower S R M] :
    SMulCommClass (Module.End R M) S (Module.End R M) :=
  SMulCommClass.symm _ _ _
#align module.End.smul_comm_class' Module.End.smulCommClass'

theorem _root_.Module.End_isUnit_apply_inv_apply_of_isUnit
    {f : Module.End R M} (h : IsUnit f) (x : M) :
    f (h.unit.inv x) = x :=
  show (f * h.unit.inv) x = x by simp
#align module.End_is_unit_apply_inv_apply_of_is_unit Module.End_isUnit_apply_inv_apply_of_isUnit

theorem _root_.Module.End_isUnit_inv_apply_apply_of_isUnit
    {f : Module.End R M} (h : IsUnit f) (x : M) :
    h.unit.inv (f x) = x :=
  (by simp : (h.unit.inv * f) x = x)
#align module.End_is_unit_inv_apply_apply_of_is_unit Module.End_isUnit_inv_apply_apply_of_isUnit

theorem coe_pow (f : M →ₗ[R] M) (n : ℕ) : ⇑(f ^ n) = f^[n] := hom_coe_pow _ rfl (fun _ _ ↦ rfl) _ _
#align linear_map.coe_pow LinearMap.coe_pow

theorem pow_apply (f : M →ₗ[R] M) (n : ℕ) (m : M) : (f ^ n) m = f^[n] m := congr_fun (coe_pow f n) m
#align linear_map.pow_apply LinearMap.pow_apply

theorem pow_map_zero_of_le {f : Module.End R M} {m : M} {k l : ℕ} (hk : k ≤ l)
    (hm : (f ^ k) m = 0) : (f ^ l) m = 0 := by
  rw [← tsub_add_cancel_of_le hk, pow_add, mul_apply, hm, map_zero]
#align linear_map.pow_map_zero_of_le LinearMap.pow_map_zero_of_le

theorem commute_pow_left_of_commute
    [Semiring R₂] [AddCommMonoid M₂] [Module R₂ M₂] {σ₁₂ : R →+* R₂}
    {f : M →ₛₗ[σ₁₂] M₂} {g : Module.End R M} {g₂ : Module.End R₂ M₂}
    (h : g₂.comp f = f.comp g) (k : ℕ) : (g₂ ^ k).comp f = f.comp (g ^ k) := by
  induction' k with k ih
  · simp only [Nat.zero_eq, pow_zero, one_eq_id, id_comp, comp_id]
  · rw [pow_succ, pow_succ, LinearMap.mul_eq_comp, LinearMap.comp_assoc, ih, ← LinearMap.comp_assoc,
      h, LinearMap.comp_assoc, LinearMap.mul_eq_comp]
#align linear_map.commute_pow_left_of_commute LinearMap.commute_pow_left_of_commute

@[simp]
theorem id_pow (n : ℕ) : (id : M →ₗ[R] M) ^ n = id :=
  one_pow n
#align linear_map.id_pow LinearMap.id_pow

variable {f' : M →ₗ[R] M}

theorem iterate_succ (n : ℕ) : f' ^ (n + 1) = comp (f' ^ n) f' := by rw [pow_succ', mul_eq_comp]
#align linear_map.iterate_succ LinearMap.iterate_succ

theorem iterate_surjective (h : Surjective f') : ∀ n : ℕ, Surjective (f' ^ n)
  | 0 => surjective_id
  | n + 1 => by
    rw [iterate_succ]
    exact (iterate_surjective h n).comp h
#align linear_map.iterate_surjective LinearMap.iterate_surjective

theorem iterate_injective (h : Injective f') : ∀ n : ℕ, Injective (f' ^ n)
  | 0 => injective_id
  | n + 1 => by
    rw [iterate_succ]
    exact (iterate_injective h n).comp h
#align linear_map.iterate_injective LinearMap.iterate_injective

theorem iterate_bijective (h : Bijective f') : ∀ n : ℕ, Bijective (f' ^ n)
  | 0 => bijective_id
  | n + 1 => by
    rw [iterate_succ]
    exact (iterate_bijective h n).comp h
#align linear_map.iterate_bijective LinearMap.iterate_bijective

theorem injective_of_iterate_injective {n : ℕ} (hn : n ≠ 0) (h : Injective (f' ^ n)) :
    Injective f' := by
  rw [← Nat.succ_pred_eq_of_pos (pos_iff_ne_zero.mpr hn), iterate_succ, coe_comp] at h
  exact h.of_comp
#align linear_map.injective_of_iterate_injective LinearMap.injective_of_iterate_injective

theorem surjective_of_iterate_surjective {n : ℕ} (hn : n ≠ 0) (h : Surjective (f' ^ n)) :
    Surjective f' := by
  rw [← Nat.succ_pred_eq_of_pos (pos_iff_ne_zero.mpr hn), pow_succ, coe_mul] at h
  exact Surjective.of_comp h
#align linear_map.surjective_of_iterate_surjective LinearMap.surjective_of_iterate_surjective

end

/-! ### Action by a module endomorphism. -/


/-- The tautological action by `Module.End R M` (aka `M →ₗ[R] M`) on `M`.

This generalizes `Function.End.applyMulAction`. -/
instance applyModule : Module (Module.End R M) M where
  smul := (· <| ·)
  smul_zero := LinearMap.map_zero
  smul_add := LinearMap.map_add
  add_smul := LinearMap.add_apply
  zero_smul := (LinearMap.zero_apply : ∀ m, (0 : M →ₗ[R] M) m = 0)
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
#align linear_map.apply_module LinearMap.applyModule

@[simp]
protected theorem smul_def (f : Module.End R M) (a : M) : f • a = f a :=
  rfl
#align linear_map.smul_def LinearMap.smul_def

/-- `LinearMap.applyModule` is faithful. -/
instance apply_faithfulSMul : FaithfulSMul (Module.End R M) M :=
  ⟨LinearMap.ext⟩
#align linear_map.apply_has_faithful_smul LinearMap.apply_faithfulSMul

instance apply_smulCommClass : SMulCommClass R (Module.End R M) M where
  smul_comm r e m := (e.map_smul r m).symm
#align linear_map.apply_smul_comm_class LinearMap.apply_smulCommClass

instance apply_smulCommClass' : SMulCommClass (Module.End R M) R M where
  smul_comm := LinearMap.map_smul
#align linear_map.apply_smul_comm_class' LinearMap.apply_smulCommClass'

instance apply_isScalarTower {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] :
    IsScalarTower R (Module.End R M) M :=
  ⟨fun _ _ _ ↦ rfl⟩
#align linear_map.apply_is_scalar_tower LinearMap.apply_isScalarTower

end Endomorphisms

end LinearMap

/-! ### Actions as module endomorphisms -/


namespace DistribMulAction

variable (R M) [Semiring R] [AddCommMonoid M] [Module R M]

variable [Monoid S] [DistribMulAction S M] [SMulCommClass S R M]

/-- Each element of the monoid defines a linear map.

This is a stronger version of `DistribMulAction.toAddMonoidHom`. -/
@[simps]
def toLinearMap (s : S) : M →ₗ[R] M where
  toFun := HSMul.hSMul s
  map_add' := smul_add s
  map_smul' _ _ := smul_comm _ _ _
#align distrib_mul_action.to_linear_map DistribMulAction.toLinearMap
#align distrib_mul_action.to_linear_map_apply DistribMulAction.toLinearMap_apply

/-- Each element of the monoid defines a module endomorphism.

This is a stronger version of `DistribMulAction.toAddMonoidEnd`. -/
@[simps]
def toModuleEnd : S →* Module.End R M where
  toFun := toLinearMap R M
  map_one' := LinearMap.ext <| one_smul _
  map_mul' _ _ := LinearMap.ext <| mul_smul _ _
#align distrib_mul_action.to_module_End DistribMulAction.toModuleEnd
#align distrib_mul_action.to_module_End_apply DistribMulAction.toModuleEnd_apply

end DistribMulAction

namespace Module

variable (R M) [Semiring R] [AddCommMonoid M] [Module R M]

variable [Semiring S] [Module S M] [SMulCommClass S R M]

/-- Each element of the semiring defines a module endomorphism.

This is a stronger version of `DistribMulAction.toModuleEnd`. -/
@[simps]
def toModuleEnd : S →+* Module.End R M :=
  { DistribMulAction.toModuleEnd R M with
    toFun := DistribMulAction.toLinearMap R M
    map_zero' := LinearMap.ext <| zero_smul S
    map_add' := fun _ _ ↦ LinearMap.ext <| add_smul _ _ }
#align module.to_module_End Module.toModuleEnd
#align module.to_module_End_apply Module.toModuleEnd_apply

/-- The canonical (semi)ring isomorphism from `Rᵐᵒᵖ` to `Module.End R R` induced by the right
multiplication. -/
@[simps]
def moduleEndSelf : Rᵐᵒᵖ ≃+* Module.End R R :=
  { Module.toModuleEnd R R with
    toFun := DistribMulAction.toLinearMap R R
    invFun := fun f ↦ MulOpposite.op (f 1)
    left_inv := mul_one
    right_inv := fun _ ↦ LinearMap.ext_ring <| one_mul _ }
#align module.module_End_self Module.moduleEndSelf
#align module.module_End_self_apply Module.moduleEndSelf_apply

/-- The canonical (semi)ring isomorphism from `R` to `Module.End Rᵐᵒᵖ R` induced by the left
multiplication. -/
@[simps]
def moduleEndSelfOp : R ≃+* Module.End Rᵐᵒᵖ R :=
  { Module.toModuleEnd _ _ with
    toFun := DistribMulAction.toLinearMap _ _
    invFun := fun f ↦ f 1
    left_inv := mul_one
    right_inv := fun _ ↦ LinearMap.ext_ring_op <| mul_one _ }
#align module.module_End_self_op Module.moduleEndSelfOp
#align module.module_End_self_op_symm_apply Module.moduleEndSelfOp_symm_apply
#align module.module_End_self_op_apply Module.moduleEndSelfOp_apply

theorem End.natCast_def (n : ℕ) [AddCommMonoid N₁] [Module R N₁] :
    (↑n : Module.End R N₁) = Module.toModuleEnd R N₁ n :=
  rfl
#align module.End.nat_cast_def Module.End.natCast_def

theorem End.intCast_def (z : ℤ) [AddCommGroup N₁] [Module R N₁] :
    (z : Module.End R N₁) = Module.toModuleEnd R N₁ z :=
  rfl
#align module.End.int_cast_def Module.End.intCast_def

end Module

namespace LinearMap

section AddCommMonoid

section SMulRight

variable [Semiring R] [Semiring R₂] [AddCommMonoid M] [AddCommMonoid M₁] [Module R M] [Module R M₁]
variable [Semiring S] [Module R S] [Module S M] [IsScalarTower R S M]

/-- When `f` is an `R`-linear map taking values in `S`, then `fun ↦ b, f b • x` is an `R`-linear
map. -/
def smulRight (f : M₁ →ₗ[R] S) (x : M) : M₁ →ₗ[R] M where
  toFun b := f b • x
  map_add' x y := by dsimp only; rw [f.map_add, add_smul]
  map_smul' b y := by dsimp; rw [map_smul, smul_assoc]
#align linear_map.smul_right LinearMap.smulRight

@[simp]
theorem coe_smulRight (f : M₁ →ₗ[R] S) (x : M) : (smulRight f x : M₁ → M) = fun c => f c • x :=
  rfl
#align linear_map.coe_smul_right LinearMap.coe_smulRight

theorem smulRight_apply (f : M₁ →ₗ[R] S) (x : M) (c : M₁) : smulRight f x c = f c • x :=
  rfl
#align linear_map.smul_right_apply LinearMap.smulRight_apply

@[simp]
lemma smulRight_zero (f : M₁ →ₗ[R] S) : f.smulRight (0 : M) = 0 := by ext; simp

@[simp]
lemma zero_smulRight (x : M) : (0 : M₁ →ₗ[R] S).smulRight x = 0 := by ext; simp

@[simp]
lemma smulRight_apply_eq_zero_iff {f : M₁ →ₗ[R] S} {x : M} [NoZeroSMulDivisors S M] :
    f.smulRight x = 0 ↔ f = 0 ∨ x = 0 := by
  rcases eq_or_ne x 0 with rfl | hx; simp
  refine ⟨fun h ↦ Or.inl ?_, fun h ↦ by simp [h.resolve_right hx]⟩
  ext v
  replace h : f v • x = 0 := by simpa only [LinearMap.zero_apply] using LinearMap.congr_fun h v
  rw [smul_eq_zero] at h
  tauto

end SMulRight

end AddCommMonoid

section Module

variable [Semiring R] [Semiring S] [AddCommMonoid M] [AddCommMonoid M₂]
variable [Module R M] [Module R M₂] [Module S M₂] [SMulCommClass R S M₂]

variable (S)

/-- Applying a linear map at `v : M`, seen as `S`-linear map from `M →ₗ[R] M₂` to `M₂`.

 See `LinearMap.applyₗ` for a version where `S = R`. -/
@[simps]
def applyₗ' : M →+ (M →ₗ[R] M₂) →ₗ[S] M₂ where
  toFun v :=
    { toFun := fun f => f v
      map_add' := fun f g => f.add_apply g v
      map_smul' := fun x f => f.smul_apply x v }
  map_zero' := LinearMap.ext fun f => f.map_zero
  map_add' _ _ := LinearMap.ext fun f => f.map_add _ _
#align linear_map.applyₗ' LinearMap.applyₗ'

end Module

section CommSemiring

variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable [Module R M] [Module R M₂] [Module R M₃]
variable (f g : M →ₗ[R] M₂)

/-- Composition by `f : M₂ → M₃` is a linear map from the space of linear maps `M → M₂`
to the space of linear maps `M₂ → M₃`. -/
def compRight (f : M₂ →ₗ[R] M₃) : (M →ₗ[R] M₂) →ₗ[R] M →ₗ[R] M₃ where
  toFun := f.comp
  map_add' _ _ := LinearMap.ext fun _ => map_add f _ _
  map_smul' _ _ := LinearMap.ext fun _ => map_smul f _ _
#align linear_map.comp_right LinearMap.compRight

@[simp]
theorem compRight_apply (f : M₂ →ₗ[R] M₃) (g : M →ₗ[R] M₂) : compRight f g = f.comp g :=
  rfl
#align linear_map.comp_right_apply LinearMap.compRight_apply

/-- Applying a linear map at `v : M`, seen as a linear map from `M →ₗ[R] M₂` to `M₂`.
See also `LinearMap.applyₗ'` for a version that works with two different semirings.

This is the `LinearMap` version of `toAddMonoidHom.eval`. -/
@[simps]
def applyₗ : M →ₗ[R] (M →ₗ[R] M₂) →ₗ[R] M₂ :=
  { applyₗ' R with
    toFun := fun v => { applyₗ' R v with toFun := fun f => f v }
    map_smul' := fun _ _ => LinearMap.ext fun f => map_smul f _ _ }
#align linear_map.applyₗ LinearMap.applyₗ

/--
The family of linear maps `M₂ → M` parameterised by `f ∈ M₂ → R`, `x ∈ M`, is linear in `f`, `x`.
-/
def smulRightₗ : (M₂ →ₗ[R] R) →ₗ[R] M →ₗ[R] M₂ →ₗ[R] M where
  toFun f :=
    { toFun := LinearMap.smulRight f
      map_add' := fun m m' => by
        ext
        apply smul_add
      map_smul' := fun c m => by
        ext
        apply smul_comm }
  map_add' f f' := by
    ext
    apply add_smul
  map_smul' c f := by
    ext
    apply mul_smul
#align linear_map.smul_rightₗ LinearMap.smulRightₗ

@[simp]
theorem smulRightₗ_apply (f : M₂ →ₗ[R] R) (x : M) (c : M₂) :
    (smulRightₗ : (M₂ →ₗ[R] R) →ₗ[R] M →ₗ[R] M₂ →ₗ[R] M) f x c = f c • x :=
  rfl
#align linear_map.smul_rightₗ_apply LinearMap.smulRightₗ_apply

end CommSemiring

end LinearMap
