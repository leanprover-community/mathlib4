/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro, Anne Baanen,
  Frédéric Dupuis, Heather Macbeth
-/
module

public import Mathlib.Algebra.Group.Hom.Instances
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.RingHom
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.GroupTheory.GroupAction.Hom

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

## Implementation notes

To ensure that composition works smoothly for semilinear maps, we use the typeclasses
`RingHomCompTriple`, `RingHomInvPair` and `RingHomSurjective` from
`Mathlib/Algebra/Ring/CompTypeclasses.lean`.

## Notation

* Throughout the file, we denote regular linear maps by `fₗ`, `gₗ`, etc, and semilinear maps
  by `f`, `g`, etc.

## TODO

* Parts of this file have not yet been generalized to semilinear maps (i.e. `CompatibleSMul`)

## Tags

linear map
-/

@[expose] public section


assert_not_exists TrivialStar DomMulAct Pi.module WCovBy.image Field

open Function

universe u u' v w

variable {R R₁ R₂ R₃ S S₃ T M M₁ M₂ M₃ N₂ N₃ : Type*}

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

section

/-- A map `f` between an `R`-module and an `S`-module over a ring homomorphism `σ : R →+* S`
is semilinear if it satisfies the two properties `f (x + y) = f x + f y` and
`f (c • x) = (σ c) • f x`. Elements of `LinearMap σ M M₂` (available under the notation
`M →ₛₗ[σ] M₂`) are bundled versions of such maps. For plain linear maps (i.e. for which
`σ = RingHom.id R`), the notation `M →ₗ[R] M₂` is available. An unbundled version of plain linear
maps is available with the predicate `IsLinearMap`, but it should be avoided most of the time. -/
structure LinearMap {R S : Type*} [Semiring R] [Semiring S] (σ : R →+* S) (M : Type*)
    (M₂ : Type*) [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module S M₂] extends
    AddHom M M₂, MulActionHom σ M M₂

/-- The `MulActionHom` underlying a `LinearMap`. -/
add_decl_doc LinearMap.toMulActionHom

/-- The `AddHom` underlying a `LinearMap`. -/
add_decl_doc LinearMap.toAddHom

/-- `M →ₛₗ[σ] N` is the type of `σ`-semilinear maps from `M` to `N`. -/
notation:25 M " →ₛₗ[" σ:25 "] " M₂:0 => LinearMap σ M M₂

/-- `M →ₗ[R] N` is the type of `R`-linear maps from `M` to `N`. -/
notation:25 M " →ₗ[" R:25 "] " M₂:0 => LinearMap (RingHom.id R) M M₂

/-- `SemilinearMapClass F σ M M₂` asserts `F` is a type of bundled `σ`-semilinear maps `M → M₂`.

See also `LinearMapClass F R M M₂` for the case where `σ` is the identity map on `R`.

A map `f` between an `R`-module and an `S`-module over a ring homomorphism `σ : R →+* S`
is semilinear if it satisfies the two properties `f (x + y) = f x + f y` and
`f (c • x) = (σ c) • f x`. -/
class SemilinearMapClass (F : Type*) {R S : outParam Type*} [Semiring R] [Semiring S]
    (σ : outParam (R →+* S)) (M M₂ : outParam Type*) [AddCommMonoid M] [AddCommMonoid M₂]
    [Module R M] [Module S M₂] [FunLike F M M₂] : Prop
    extends AddHomClass F M M₂, MulActionSemiHomClass F σ M M₂

end

-- `map_smulₛₗ` should be `@[simp]` but doesn't fire due to https://github.com/leanprover/lean4/pull/3701.
-- attribute [simp] map_smulₛₗ

/-- `LinearMapClass F R M M₂` asserts `F` is a type of bundled `R`-linear maps `M → M₂`.

This is an abbreviation for `SemilinearMapClass F (RingHom.id R) M M₂`.
-/
abbrev LinearMapClass (F : Type*) (R : outParam Type*) (M M₂ : Type*)
    [Semiring R] [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module R M₂]
    [FunLike F M M₂] :=
  SemilinearMapClass F (RingHom.id R) M M₂

protected lemma LinearMapClass.map_smul {R M M₂ : outParam Type*} [Semiring R] [AddCommMonoid M]
    [AddCommMonoid M₂] [Module R M] [Module R M₂]
    {F : Type*} [FunLike F M M₂] [LinearMapClass F R M M₂] (f : F) (r : R) (x : M) :
    f (r • x) = r • f x := by rw [map_smul]

namespace SemilinearMapClass

variable (F : Type*)
variable [Semiring R] [Semiring S]
variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable [Module R M] [Module R M₂] [Module S M₃]
variable {σ : R →+* S}

instance (priority := 100) instAddMonoidHomClass [FunLike F M M₃] [SemilinearMapClass F σ M M₃] :
    AddMonoidHomClass F M M₃ :=
  { SemilinearMapClass.toAddHomClass with
    map_zero := fun f ↦
      show f 0 = 0 by
        rw [← zero_smul R (0 : M), map_smulₛₗ]
        simp }

instance (priority := 100) distribMulActionSemiHomClass
    [FunLike F M M₃] [SemilinearMapClass F σ M M₃] :
    DistribMulActionSemiHomClass F σ M M₃ :=
  { SemilinearMapClass.toAddHomClass with
    map_smulₛₗ := fun f c x ↦ by rw [map_smulₛₗ] }

variable {F} (f : F) [FunLike F M M₃] [SemilinearMapClass F σ M M₃]

theorem map_smul_inv {σ' : S →+* R} [RingHomInvPair σ σ'] (c : S) (x : M) :
    c • f x = f (σ' c • x) := by simp [map_smulₛₗ _]

/-- Reinterpret an element of a type of semilinear maps as a semilinear map. -/
@[coe]
def semilinearMap : M →ₛₗ[σ] M₃ where
  toFun := f
  map_add' := map_add f
  map_smul' := map_smulₛₗ f

/-- Reinterpret an element of a type of semilinear maps as a semilinear map. -/
instance instCoeToSemilinearMap : CoeHead F (M →ₛₗ[σ] M₃) where
  coe f := semilinearMap f

end SemilinearMapClass

namespace LinearMapClass
variable {F : Type*} [Semiring R] [AddCommMonoid M₁] [AddCommMonoid M₂] [Module R M₁] [Module R M₂]
  (f : F) [FunLike F M₁ M₂] [LinearMapClass F R M₁ M₂]

/-- Reinterpret an element of a type of linear maps as a linear map. -/
abbrev linearMap : M₁ →ₗ[R] M₂ := SemilinearMapClass.semilinearMap f

/-- Reinterpret an element of a type of linear maps as a linear map. -/
instance instCoeToLinearMap : CoeHead F (M₁ →ₗ[R] M₂) where
  coe f := SemilinearMapClass.semilinearMap f

end LinearMapClass

namespace LinearMap

section AddCommMonoid

variable [Semiring R] [Semiring S]

section

variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable [Module R M] [Module R M₂] [Module S M₃]
variable {σ : R →+* S}

instance instFunLike : FunLike (M →ₛₗ[σ] M₃) M M₃ where
  coe f := f.toFun
  coe_injective' f g h := by
    cases f
    cases g
    congr
    apply DFunLike.coe_injective'
    exact h

instance semilinearMapClass : SemilinearMapClass (M →ₛₗ[σ] M₃) σ M M₃ where
  map_add f := f.map_add'
  map_smulₛₗ := LinearMap.map_smul'

@[simp, norm_cast]
lemma coe_coe {F : Type*} [FunLike F M M₃] [SemilinearMapClass F σ M M₃] {f : F} :
    ⇑(f : M →ₛₗ[σ] M₃) = f :=
  rfl

/-- The `DistribMulActionHom` underlying a `LinearMap`. -/
def toDistribMulActionHom (f : M →ₛₗ[σ] M₃) : DistribMulActionHom σ.toMonoidHom M M₃ :=
  { f with map_zero' := show f 0 = 0 from map_zero f }

@[simp]
theorem coe_toAddHom (f : M →ₛₗ[σ] M₃) : ⇑f.toAddHom = f := rfl

@[simp]
theorem toFun_eq_coe {f : M →ₛₗ[σ] M₃} : f.toFun = (f : M → M₃) := rfl

@[ext]
theorem ext {f g : M →ₛₗ[σ] M₃} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

/-- Copy of a `LinearMap` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : M →ₛₗ[σ] M₃) (f' : M → M₃) (h : f' = ⇑f) : M →ₛₗ[σ] M₃ where
  toFun := f'
  map_add' := h.symm ▸ f.map_add'
  map_smul' := h.symm ▸ f.map_smul'

@[simp]
theorem coe_copy (f : M →ₛₗ[σ] M₃) (f' : M → M₃) (h : f' = ⇑f) : ⇑(f.copy f' h) = f' :=
  rfl

theorem copy_eq (f : M →ₛₗ[σ] M₃) (f' : M → M₃) (h : f' = ⇑f) : f.copy f' h = f :=
  DFunLike.ext' h

initialize_simps_projections LinearMap (toFun → apply)

@[simp]
theorem coe_mk {σ : R →+* S} (f : AddHom M M₃) (h) :
    ((LinearMap.mk f h : M →ₛₗ[σ] M₃) : M → M₃) = f :=
  rfl

@[simp]
theorem coe_addHom_mk {σ : R →+* S} (f : AddHom M M₃) (h) :
    ((LinearMap.mk f h : M →ₛₗ[σ] M₃) : AddHom M M₃) = f :=
  rfl

theorem coe_semilinearMap {F : Type*} [FunLike F M M₃] [SemilinearMapClass F σ M M₃] (f : F) :
    ((f : M →ₛₗ[σ] M₃) : M → M₃) = f :=
  rfl

theorem toLinearMap_injective {F : Type*} [FunLike F M M₃] [SemilinearMapClass F σ M M₃]
    {f g : F} (h : (f : M →ₛₗ[σ] M₃) = (g : M →ₛₗ[σ] M₃)) :
    f = g := by
  apply DFunLike.ext
  intro m
  exact DFunLike.congr_fun h m

/-- Identity map as a `LinearMap` -/
def id : M →ₗ[R] M :=
  { DistribMulActionHom.id R with toFun := _root_.id }

theorem id_apply (x : M) : @id R M _ _ _ x = x :=
  rfl

@[simp, norm_cast]
theorem id_coe : ((LinearMap.id : M →ₗ[R] M) : M → M) = _root_.id :=
  rfl

/-- A generalisation of `LinearMap.id` that constructs the identity function
as a `σ`-semilinear map for any ring homomorphism `σ` which we know is the identity. -/
@[simps]
def id' {σ : R →+* R} [RingHomId σ] : M →ₛₗ[σ] M where
  toFun x := x
  map_add' _ _ := rfl
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
variable [Module R M] [Module R M₂] [Module S M₃]
variable (σ : R →+* S)
variable (fₗ : M →ₗ[R] M₂) (f g : M →ₛₗ[σ] M₃)

theorem isLinear : IsLinearMap R fₗ :=
  ⟨fₗ.map_add', fₗ.map_smul'⟩

variable {fₗ f g σ}

theorem coe_injective : Injective (DFunLike.coe : (M →ₛₗ[σ] M₃) → _) :=
  DFunLike.coe_injective

protected theorem congr_arg {x x' : M} : x = x' → f x = f x' :=
  DFunLike.congr_arg f

/-- If two linear maps are equal, they are equal at each point. -/
protected theorem congr_fun (h : f = g) (x : M) : f x = g x :=
  DFunLike.congr_fun h x

@[simp] lemma mk_coe (f : M →ₛₗ[σ] M₃) (h) : (mk f h : M →ₛₗ[σ] M₃) = f := rfl
@[simp] lemma mk_coe' (f : M →ₛₗ[σ] M₃) (h) : (mk f.toAddHom h : M →ₛₗ[σ] M₃) = f := rfl

variable (fₗ f g)

protected theorem map_add (x y : M) : f (x + y) = f x + f y :=
  map_add f x y

protected theorem map_zero : f 0 = 0 :=
  map_zero f

-- Porting note: `simp` wasn't picking up `map_smulₛₗ` for `LinearMap`s without specifying
-- `map_smulₛₗ f`, so we marked this as `@[simp]` in Mathlib3.
-- For Mathlib4, let's try without the `@[simp]` attribute and hope it won't need to be re-enabled.
-- This has to be re-tagged as `@[simp]` in https://github.com/leanprover-community/mathlib4/pull/8386 (see also https://github.com/leanprover/lean4/issues/3107).
@[simp]
protected theorem map_smulₛₗ (c : R) (x : M) : f (c • x) = σ c • f x :=
  map_smulₛₗ f c x

protected theorem map_smul (c : R) (x : M) : fₗ (c • x) = c • fₗ x :=
  map_smul fₗ c x

protected theorem map_smul_inv {σ' : S →+* R} [RingHomInvPair σ σ'] (c : S) (x : M) :
    c • f x = f (σ' c • x) := by simp

@[simp]
protected theorem map_eq_zero_iff (h : Function.Injective f) {x : M} : f x = 0 ↔ x = 0 :=
  _root_.map_eq_zero_iff f h

variable (M M₂)

/-- A typeclass for `SMul` structures which can be moved through a `LinearMap`.
This typeclass is generated automatically from an `IsScalarTower` instance, but exists so that
we can also add an instance for `AddCommGroup.toIntModule`, allowing `z •` to be moved even if
`S` does not support negation.
-/
class CompatibleSMul (R S : Type*) [Semiring S] [SMul R M] [Module S M] [SMul R M₂]
  [Module S M₂] : Prop where
  /-- Scalar multiplication by `R` of `M` can be moved through linear maps. -/
  map_smul : ∀ (fₗ : M →ₗ[S] M₂) (c : R) (x : M), fₗ (c • x) = c • fₗ x

variable {M M₂}

section

variable {R S : Type*} [Semiring S] [SMul R M] [Module S M] [SMul R M₂] [Module S M₂]

instance (priority := 100) IsScalarTower.compatibleSMul [SMul R S]
    [IsScalarTower R S M] [IsScalarTower R S M₂] :
    CompatibleSMul M M₂ R S :=
  ⟨fun fₗ c x ↦ by rw [← smul_one_smul S c x, ← smul_one_smul S c (fₗ x), map_smul]⟩

instance IsScalarTower.compatibleSMul' [SMul R S] [IsScalarTower R S M] :
    CompatibleSMul S M R S where
  map_smul := (IsScalarTower.smulHomClass R S M (S →ₗ[S] M)).map_smulₛₗ

@[simp]
theorem map_smul_of_tower [CompatibleSMul M M₂ R S] (fₗ : M →ₗ[S] M₂) (c : R) (x : M) :
    fₗ (c • x) = c • fₗ x :=
  CompatibleSMul.map_smul fₗ c x

theorem _root_.LinearMapClass.map_smul_of_tower {F : Type*} [CompatibleSMul M M₂ R S]
    [FunLike F M M₂] [LinearMapClass F S M M₂] (fₗ : F) (c : R) (x : M) :
    fₗ (c • x) = c • fₗ x :=
  LinearMap.CompatibleSMul.map_smul (fₗ : M →ₗ[S] M₂) c x

variable (R R) in
theorem isScalarTower_of_injective [SMul R S] [CompatibleSMul M M₂ R S] [IsScalarTower R S M₂]
    (f : M →ₗ[S] M₂) (hf : Function.Injective f) : IsScalarTower R S M where
  smul_assoc r s _ := hf <| by rw [f.map_smul_of_tower r, map_smul, map_smul, smul_assoc]

@[simp] lemma _root_.map_zsmul_unit {F M N : Type*}
    [AddGroup M] [AddGroup N] [FunLike F M N] [AddMonoidHomClass F M N]
    (f : F) (c : ℤˣ) (m : M) :
    f (c • m) = c • f m := by
  simp [Units.smul_def]

end

variable (R) in
theorem isLinearMap_of_compatibleSMul [Module S M] [Module S M₂] [CompatibleSMul M M₂ R S]
    (f : M →ₗ[S] M₂) : IsLinearMap R f where
  map_add := map_add f
  map_smul := map_smul_of_tower f

/-- Convert a linear map to an additive monoid hom. -/
-- See note [implicit instance arguments]
def toAddMonoidHom {modM₁ : Module R M₁} {modM₂ : Module S M₂} {σ : R →+* S} (f : M₁ →ₛₗ[σ] M₂) :
    M₁ →+ M₂ where
  toFun := f
  map_zero' := f.map_zero
  map_add' := f.map_add

omit [Module R M₂] in
@[simp]
lemma toAddMonoidHom_coe {modM₁ : Module R M₁} {modM₂ : Module S M₂} {σ : R →+* S}
    (f : M₁ →ₛₗ[σ] M₂) : ⇑f.toAddMonoidHom = f := rfl

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

instance coeIsScalarTower : CoeHTCT (M →ₗ[S] M₂) (M →ₗ[R] M₂) :=
  ⟨restrictScalars R⟩

@[simp, norm_cast]
theorem coe_restrictScalars (f : M →ₗ[S] M₂) : ((f : M →ₗ[R] M₂) : M → M₂) = f :=
  rfl

@[simp]
lemma restrictScalars_self (f : M →ₗ[R] M₂) : f.restrictScalars R = f := rfl

theorem restrictScalars_apply (fₗ : M →ₗ[S] M₂) (x) : restrictScalars R fₗ x = fₗ x :=
  rfl

theorem restrictScalars_injective :
    Function.Injective (restrictScalars R : (M →ₗ[S] M₂) → M →ₗ[R] M₂) := fun _ _ h ↦
  ext (LinearMap.congr_fun h :)

@[simp]
theorem restrictScalars_inj (fₗ gₗ : M →ₗ[S] M₂) :
    fₗ.restrictScalars R = gₗ.restrictScalars R ↔ fₗ = gₗ :=
  (restrictScalars_injective R).eq_iff

@[simp]
lemma restrictScalars_id [CompatibleSMul M M R S] :
    (id (R := S) (M := M)).restrictScalars R = id := rfl

end RestrictScalars

theorem toAddMonoidHom_injective :
    Function.Injective (toAddMonoidHom : (M →ₛₗ[σ] M₃) → M →+ M₃) := fun fₗ gₗ h ↦
  ext <| (DFunLike.congr_fun h : ∀ x, fₗ.toAddMonoidHom x = gₗ.toAddMonoidHom x)

/-- If two `σ`-linear maps from `R` are equal on `1`, then they are equal. -/
@[ext high]
theorem ext_ring {f g : R →ₛₗ[σ] M₃} (h : f 1 = g 1) : f = g :=
  ext fun x ↦ by rw [← mul_one x, ← smul_eq_mul, f.map_smulₛₗ, g.map_smulₛₗ, h]

end

/-- Interpret a `RingHom` `f` as an `f`-semilinear map. -/
@[simps]
def _root_.RingHom.toSemilinearMap (f : R →+* S) : R →ₛₗ[f] S :=
  { f with
    map_smul' := f.map_mul }

@[simp] theorem _root_.RingHom.coe_toSemilinearMap (f : R →+* S) : ⇑f.toSemilinearMap = f := rfl

section

variable [Semiring R₁] [Semiring R₂] [Semiring R₃]
variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable {module_M₁ : Module R₁ M₁} {module_M₂ : Module R₂ M₂} {module_M₃ : Module R₃ M₃}
variable {σ₁₂ : R₁ →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R₁ →+* R₃}

/-- Composition of two linear maps is a linear map -/
def comp [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] (f : M₂ →ₛₗ[σ₂₃] M₃) (g : M₁ →ₛₗ[σ₁₂] M₂) :
    M₁ →ₛₗ[σ₁₃] M₃ where
  toFun := f ∘ g
  map_add' := by simp only [map_add, forall_const, Function.comp_apply]
  -- Note that https://github.com/leanprover-community/mathlib4/pull/8386 changed `map_smulₛₗ` to `map_smulₛₗ _`
  map_smul' r x := by simp only [Function.comp_apply, map_smulₛₗ _, RingHomCompTriple.comp_apply]

variable [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
variable (f : M₂ →ₛₗ[σ₂₃] M₃) (g : M₁ →ₛₗ[σ₁₂] M₂)

/-- `∘ₗ` is notation for composition of two linear (not semilinear!) maps into a linear map.
This is useful when Lean is struggling to infer the `RingHomCompTriple` instance. -/
notation3:80 (name := compNotation) f:81 " ∘ₗ " g:80 =>
  LinearMap.comp (σ₁₂ := RingHom.id _) (σ₂₃ := RingHom.id _) (σ₁₃ := RingHom.id _) f g

@[inherit_doc] infixr:90 " ∘ₛₗ " => comp

theorem comp_apply (x : M₁) : f.comp g x = f (g x) :=
  rfl

@[simp, norm_cast]
theorem coe_comp : (f.comp g : M₁ → M₃) = f ∘ g :=
  rfl

@[simp]
theorem comp_id : f.comp id = f :=
  rfl

@[simp]
theorem id_comp : id.comp f = f :=
  rfl

theorem comp_assoc
    {R₄ M₄ : Type*} [Semiring R₄] [AddCommMonoid M₄] [Module R₄ M₄]
    {σ₃₄ : R₃ →+* R₄} {σ₂₄ : R₂ →+* R₄} {σ₁₄ : R₁ →+* R₄}
    [RingHomCompTriple σ₂₃ σ₃₄ σ₂₄] [RingHomCompTriple σ₁₃ σ₃₄ σ₁₄] [RingHomCompTriple σ₁₂ σ₂₄ σ₁₄]
    (f : M₁ →ₛₗ[σ₁₂] M₂) (g : M₂ →ₛₗ[σ₂₃] M₃) (h : M₃ →ₛₗ[σ₃₄] M₄) :
    ((h.comp g : M₂ →ₛₗ[σ₂₄] M₄).comp f : M₁ →ₛₗ[σ₁₄] M₄) = h.comp (g.comp f : M₁ →ₛₗ[σ₁₃] M₃) :=
  rfl

variable {f g} {f' : M₂ →ₛₗ[σ₂₃] M₃} {g' : M₁ →ₛₗ[σ₁₂] M₂}

/-- The linear map version of `Function.Surjective.injective_comp_right` -/
lemma _root_.Function.Surjective.injective_linearMapComp_right (hg : Surjective g) :
    Injective fun f : M₂ →ₛₗ[σ₂₃] M₃ ↦ f.comp g :=
  fun _ _ h ↦ ext <| hg.forall.2 (LinearMap.ext_iff.1 h)

@[simp]
theorem cancel_right (hg : Surjective g) : f.comp g = f'.comp g ↔ f = f' :=
  hg.injective_linearMapComp_right.eq_iff

/-- The linear map version of `Function.Injective.comp_left` -/
lemma _root_.Function.Injective.injective_linearMapComp_left (hf : Injective f) :
    Injective fun g : M₁ →ₛₗ[σ₁₂] M₂ ↦ f.comp g :=
  fun g₁ g₂ (h : f.comp g₁ = f.comp g₂) ↦ ext fun x ↦ hf <| by rw [← comp_apply, h, comp_apply]

theorem surjective_comp_left_of_exists_rightInverse {σ₃₂ : R₃ →+* R₂}
    [RingHomInvPair σ₂₃ σ₃₂] [RingHomCompTriple σ₁₃ σ₃₂ σ₁₂]
    (hf : ∃ f' : M₃ →ₛₗ[σ₃₂] M₂, f.comp f' = .id) :
    Surjective fun g : M₁ →ₛₗ[σ₁₂] M₂ ↦ f.comp g := by
  intro h
  obtain ⟨f', hf'⟩ := hf
  refine ⟨f'.comp h, ?_⟩
  simp_rw [← comp_assoc, hf', id_comp]

@[simp]
theorem cancel_left (hf : Injective f) : f.comp g = f.comp g' ↔ g = g' :=
  hf.injective_linearMapComp_left.eq_iff

end

variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable [Module R M] [Module S M₂] {σ : R →+* S} {σ' : S →+* R} [RingHomInvPair σ σ']

/-- If a function `g` is a left and right inverse of a linear map `f`, then `g` is linear itself. -/
def inverse (f : M →ₛₗ[σ] M₂) (g : M₂ → M) (h₁ : LeftInverse g f) (h₂ : RightInverse g f) :
    M₂ →ₛₗ[σ'] M := by
  dsimp [LeftInverse, Function.RightInverse] at h₁ h₂
  exact
    { toFun := g
      map_add' := fun x y ↦ by rw [← h₁ (g (x + y)), ← h₁ (g x + g y)]; simp [h₂]
      map_smul' := fun a b ↦ by
        rw [← h₁ (g (a • b)), ← h₁ (σ' a • g b)]
        simp [h₂] }

variable (f : M →ₛₗ[σ] M₂) (g : M₂ →ₛₗ[σ'] M) (h : g.comp f = .id)

include h

theorem injective_of_comp_eq_id : Injective f :=
  .of_comp (f := g) <| by simp_rw [← coe_comp, h, id_coe, bijective_id.1]

theorem surjective_of_comp_eq_id : Surjective g :=
  .of_comp (g := f) <| by simp_rw [← coe_comp, h, id_coe, bijective_id.2]

end AddCommMonoid

section AddCommGroup

variable [Semiring R] [Semiring S] [AddCommGroup M] [AddCommGroup M₂]
variable {module_M : Module R M} {module_M₂ : Module S M₂} {σ : R →+* S}
variable (f : M →ₛₗ[σ] M₂)

protected theorem map_neg (x : M) : f (-x) = -f x :=
  map_neg f x

protected theorem map_sub (x y : M) : f (x - y) = f x - f y :=
  map_sub f x y

instance CompatibleSMul.intModule {S : Type*} [Semiring S] [Module S M] [Module S M₂] :
    CompatibleSMul M M₂ ℤ S :=
  ⟨fun fₗ c x ↦ by
    induction c with
    | zero => simp
    | succ n ih => simp [add_smul]
    | pred n ih => simp [sub_smul]⟩

instance CompatibleSMul.units {R S : Type*} [Monoid R] [MulAction R M] [MulAction R M₂]
    [Semiring S] [Module S M] [Module S M₂] [CompatibleSMul M M₂ R S] : CompatibleSMul M M₂ Rˣ S :=
  ⟨fun fₗ c x ↦ (CompatibleSMul.map_smul fₗ (c : R) x :)⟩

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

end Module

namespace DistribMulActionHom

variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable [Semiring R] [Module R M] [Semiring S] [Module S M₂] [Module R M₃]
variable {σ : R →+* S}

instance : SemilinearMapClass (M →ₑ+[σ.toMonoidHom] M₂) σ M M₂ where

/-- A `DistribMulActionHom` between two modules is a linear map. -/
instance : LinearMapClass (M →+[R] M₃) R M M₃ where

@[simp]
theorem coe_toLinearMap (f : M →ₑ+[σ.toMonoidHom] M₂) : ((f : M →ₛₗ[σ] M₂) : M → M₂) = f :=
  rfl

theorem toLinearMap_injective {f g : M →ₑ+[σ.toMonoidHom] M₂}
    (h : (f : M →ₛₗ[σ] M₂) = (g : M →ₛₗ[σ] M₂)) :
    f = g := by
  ext m
  exact LinearMap.congr_fun h m

end DistribMulActionHom

namespace IsLinearMap

section AddCommMonoid

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M₂]
variable [Module R M] [Module R M₂]

/-- Convert an `IsLinearMap` predicate to a `LinearMap` -/
def mk' (f : M → M₂) (lin : IsLinearMap R f) : M →ₗ[R] M₂ where
  toFun := f
  map_add' := lin.1
  map_smul' := lin.2

@[simp]
theorem mk'_apply {f : M → M₂} (lin : IsLinearMap R f) (x : M) : mk' f lin x = f x :=
  rfl

theorem isLinearMap_smul {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] (c : R) :
    IsLinearMap R fun z : M ↦ c • z := by
  refine IsLinearMap.mk (smul_add c) ?_
  intro _ _
  simp only [smul_smul, mul_comm]

theorem isLinearMap_smul' {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] (a : M) :
    IsLinearMap R fun c : R ↦ c • a :=
  IsLinearMap.mk (fun x y ↦ add_smul x y a) fun x y ↦ mul_smul x y a

theorem map_zero {f : M → M₂} (lin : IsLinearMap R f) : f (0 : M) = (0 : M₂) :=
  (lin.mk' f).map_zero

end AddCommMonoid

section AddCommGroup

variable [Semiring R] [AddCommGroup M] [AddCommGroup M₂]
variable [Module R M] [Module R M₂]

theorem isLinearMap_neg : IsLinearMap R fun z : M ↦ -z :=
  IsLinearMap.mk neg_add fun x y ↦ (smul_neg x y).symm

theorem map_neg {f : M → M₂} (lin : IsLinearMap R f) (x : M) : f (-x) = -f x :=
  (lin.mk' f).map_neg x

theorem map_sub {f : M → M₂} (lin : IsLinearMap R f) (x y : M) : f (x - y) = f x - f y :=
  (lin.mk' f).map_sub x y

end AddCommGroup

end IsLinearMap

/-- Reinterpret an additive homomorphism as an `ℕ`-linear map. -/
def AddMonoidHom.toNatLinearMap [AddCommMonoid M] [AddCommMonoid M₂] (f : M →+ M₂) :
    M →ₗ[ℕ] M₂ where
  toFun := f
  map_add' := f.map_add
  map_smul' := map_nsmul f

theorem AddMonoidHom.toNatLinearMap_injective [AddCommMonoid M] [AddCommMonoid M₂] :
    Function.Injective (@AddMonoidHom.toNatLinearMap M M₂ _ _) := by
  intro f g h
  ext x
  exact LinearMap.congr_fun h x

@[simp]
theorem AddMonoidHom.coe_toNatLinearMap [AddCommMonoid M] [AddCommMonoid M₂] (f : M →+ M₂) :
    ⇑f.toNatLinearMap = f :=
  rfl

/-- Reinterpret an additive homomorphism as a `ℤ`-linear map. -/
def AddMonoidHom.toIntLinearMap [AddCommGroup M] [AddCommGroup M₂] (f : M →+ M₂) : M →ₗ[ℤ] M₂ where
  toFun := f
  map_add' := f.map_add
  map_smul' := map_zsmul f

theorem AddMonoidHom.toIntLinearMap_injective [AddCommGroup M] [AddCommGroup M₂] :
    Function.Injective (@AddMonoidHom.toIntLinearMap M M₂ _ _) := by
  intro f g h
  ext x
  exact LinearMap.congr_fun h x

@[simp]
theorem AddMonoidHom.coe_toIntLinearMap [AddCommGroup M] [AddCommGroup M₂] (f : M →+ M₂) :
    ⇑f.toIntLinearMap = f :=
  rfl

namespace LinearMap

section SMul

variable [Semiring R] [Semiring R₂]
variable [AddCommMonoid M] [AddCommMonoid M₂]
variable [Module R M] [Module R₂ M₂]
variable {σ₁₂ : R →+* R₂}
variable [DistribSMul S M₂] [SMulCommClass R₂ S M₂]
variable [DistribSMul T M₂] [SMulCommClass R₂ T M₂]

instance : SMul S (M →ₛₗ[σ₁₂] M₂) :=
  ⟨fun a f ↦
    { toFun := a • (f : M → M₂)
      map_add' := fun x y ↦ by simp only [Pi.smul_apply, f.map_add, smul_add]
      map_smul' := fun c x ↦ by simp [Pi.smul_apply, smul_comm] }⟩

@[simp]
theorem smul_apply (a : S) (f : M →ₛₗ[σ₁₂] M₂) (x : M) : (a • f) x = a • f x :=
  rfl

@[simp]
theorem coe_smul (a : S) (f : M →ₛₗ[σ₁₂] M₂) : (a • f : M →ₛₗ[σ₁₂] M₂) = a • (f : M → M₂) :=
  rfl

instance [SMulCommClass S T M₂] : SMulCommClass S T (M →ₛₗ[σ₁₂] M₂) :=
  ⟨fun _ _ _ ↦ ext fun _ ↦ smul_comm _ _ _⟩

-- example application of this instance: if S -> T -> R are homomorphisms of commutative rings and
-- M and M₂ are R-modules then the S-module and T-module structures on Hom_R(M,M₂) are compatible.
instance [SMul S T] [IsScalarTower S T M₂] : IsScalarTower S T (M →ₛₗ[σ₁₂] M₂) where
  smul_assoc _ _ _ := ext fun _ ↦ smul_assoc _ _ _

instance [DistribSMul Sᵐᵒᵖ M₂] [SMulCommClass R₂ Sᵐᵒᵖ M₂] [IsCentralScalar S M₂] :
    IsCentralScalar S (M →ₛₗ[σ₁₂] M₂) where
  op_smul_eq_smul _ _ := ext fun _ ↦ op_smul_eq_smul _ _

end SMul

/-! ### Arithmetic on the codomain -/

section Arithmetic

variable [Semiring R₁] [Semiring R₂] [Semiring R₃]
variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable [AddCommGroup N₂] [AddCommGroup N₃]
variable [Module R₁ M] [Module R₂ M₂] [Module R₃ M₃]
variable [Module R₂ N₂] [Module R₃ N₃]
variable {σ₁₂ : R₁ →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R₁ →+* R₃} [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

/-- The constant 0 map is linear. -/
instance : Zero (M →ₛₗ[σ₁₂] M₂) :=
  ⟨{  toFun := 0
      map_add' := by simp
      map_smul' := by simp }⟩

@[simp] lemma coe_zero_iff (f : M →ₛₗ[σ₁₂] M₂) : ⇑f = 0 ↔ f = 0 := by
  aesop

@[simp]
theorem zero_apply (x : M) : (0 : M →ₛₗ[σ₁₂] M₂) x = 0 :=
  rfl

@[simp]
theorem comp_zero (g : M₂ →ₛₗ[σ₂₃] M₃) : (g.comp (0 : M →ₛₗ[σ₁₂] M₂) : M →ₛₗ[σ₁₃] M₃) = 0 :=
  ext fun c ↦ by rw [comp_apply, zero_apply, zero_apply, g.map_zero]

@[simp]
theorem zero_comp (f : M →ₛₗ[σ₁₂] M₂) : ((0 : M₂ →ₛₗ[σ₂₃] M₃).comp f : M →ₛₗ[σ₁₃] M₃) = 0 :=
  rfl

instance : Inhabited (M →ₛₗ[σ₁₂] M₂) :=
  ⟨0⟩

@[simp]
theorem default_def : (default : M →ₛₗ[σ₁₂] M₂) = 0 :=
  rfl

instance uniqueOfLeft [Subsingleton M] : Unique (M →ₛₗ[σ₁₂] M₂) :=
  { (inferInstance : Inhabited (M →ₛₗ[σ₁₂] M₂)) with
    uniq := fun f => ext fun x => by rw [Subsingleton.elim x 0, map_zero, map_zero] }

instance uniqueOfRight [Subsingleton M₂] : Unique (M →ₛₗ[σ₁₂] M₂) :=
  coe_injective.unique

theorem ne_zero_of_injective [Nontrivial M] {f : M →ₛₗ[σ₁₂] M₂} (hf : Injective f) : f ≠ 0 :=
  have ⟨x, ne⟩ := exists_ne (0 : M)
  fun h ↦ hf.ne ne <| by simp [h]

theorem ne_zero_of_surjective [Nontrivial M₂] {f : M →ₛₗ[σ₁₂] M₂} (hf : Surjective f) : f ≠ 0 := by
  have ⟨y, ne⟩ := exists_ne (0 : M₂)
  obtain ⟨x, rfl⟩ := hf y
  exact fun h ↦ ne congr($h x)

/-- The sum of two linear maps is linear. -/
instance : Add (M →ₛₗ[σ₁₂] M₂) :=
  ⟨fun f g ↦
    { toFun := f + g
      map_add' := by simp [add_comm, add_left_comm]
      map_smul' := by simp [smul_add] }⟩

@[simp]
theorem add_apply (f g : M →ₛₗ[σ₁₂] M₂) (x : M) : (f + g) x = f x + g x :=
  rfl

theorem add_comp (f : M →ₛₗ[σ₁₂] M₂) (g h : M₂ →ₛₗ[σ₂₃] M₃) :
    ((h + g).comp f : M →ₛₗ[σ₁₃] M₃) = h.comp f + g.comp f :=
  rfl

theorem comp_add (f g : M →ₛₗ[σ₁₂] M₂) (h : M₂ →ₛₗ[σ₂₃] M₃) :
    (h.comp (f + g) : M →ₛₗ[σ₁₃] M₃) = h.comp f + h.comp g :=
  ext fun _ ↦ h.map_add _ _

/-- The type of linear maps is an additive monoid. -/
instance addCommMonoid : AddCommMonoid (M →ₛₗ[σ₁₂] M₂) :=
  DFunLike.coe_injective.addCommMonoid _ rfl (fun _ _ ↦ rfl) fun _ _ ↦ rfl

/-- The negation of a linear map is linear. -/
instance : Neg (M →ₛₗ[σ₁₂] N₂) :=
  ⟨fun f ↦
    { toFun := -f
      map_add' := by simp [add_comm]
      map_smul' := by simp }⟩

@[simp] protected theorem coe_neg (f : M →ₛₗ[σ₁₂] N₂) : ⇑(-f) = -⇑f := rfl

@[simp]
theorem neg_apply (f : M →ₛₗ[σ₁₂] N₂) (x : M) : (-f) x = -f x :=
  rfl

@[simp]
theorem neg_comp (f : M →ₛₗ[σ₁₂] M₂) (g : M₂ →ₛₗ[σ₂₃] N₃) : (-g).comp f = -g.comp f :=
  rfl

@[simp]
theorem comp_neg (f : M →ₛₗ[σ₁₂] N₂) (g : N₂ →ₛₗ[σ₂₃] N₃) : g.comp (-f) = -g.comp f :=
  ext fun _ ↦ g.map_neg _

/-- The subtraction of two linear maps is linear. -/
instance : Sub (M →ₛₗ[σ₁₂] N₂) :=
  ⟨fun f g ↦
    { toFun := f - g
      map_add' := fun x y ↦ by simp only [Pi.sub_apply, map_add, add_sub_add_comm]
      map_smul' := fun r x ↦ by simp [Pi.sub_apply, smul_sub] }⟩

@[simp]
theorem sub_apply (f g : M →ₛₗ[σ₁₂] N₂) (x : M) : (f - g) x = f x - g x :=
  rfl

theorem sub_comp (f : M →ₛₗ[σ₁₂] M₂) (g h : M₂ →ₛₗ[σ₂₃] N₃) :
    (g - h).comp f = g.comp f - h.comp f :=
  rfl

theorem comp_sub (f g : M →ₛₗ[σ₁₂] N₂) (h : N₂ →ₛₗ[σ₂₃] N₃) :
    h.comp (g - f) = h.comp g - h.comp f :=
  ext fun _ ↦ h.map_sub _ _

/-- The type of linear maps is an additive group. -/
instance addCommGroup : AddCommGroup (M →ₛₗ[σ₁₂] N₂) :=
  DFunLike.coe_injective.addCommGroup _ rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) fun _ _ ↦ rfl

/-- Evaluation of a `σ₁₂`-linear map at a fixed `a`, as an `AddMonoidHom`. -/
@[simps]
def evalAddMonoidHom (a : M) : (M →ₛₗ[σ₁₂] M₂) →+ M₂ where
  toFun f := f a
  map_add' f g := LinearMap.add_apply f g a
  map_zero' := rfl

/-- `LinearMap.toAddMonoidHom` promoted to an `AddMonoidHom`. -/
@[simps]
def toAddMonoidHom' : (M →ₛₗ[σ₁₂] M₂) →+ M →+ M₂ where
  toFun := toAddMonoidHom
  map_zero' := by ext; rfl
  map_add' := by intros; ext; rfl

/-- If `M` is the zero module, then the identity map of `M` is the zero map. -/
@[simp]
theorem identityMapOfZeroModuleIsZero [Subsingleton M] : id (R := R₁) (M := M) = 0 :=
  Subsingleton.eq_zero id

end Arithmetic

section Actions

variable [Semiring R] [Semiring R₂] [Semiring R₃]
variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable [Module R M] [Module R₂ M₂] [Module R₃ M₃]
variable {σ₁₂ : R →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R →+* R₃} [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

section SMul

variable [Monoid S] [DistribMulAction S M₂] [SMulCommClass R₂ S M₂]
variable [Monoid S₃] [DistribMulAction S₃ M₃] [SMulCommClass R₃ S₃ M₃]

instance : DistribMulAction S (M →ₛₗ[σ₁₂] M₂) where
  one_smul _ := ext fun _ ↦ one_smul _ _
  mul_smul _ _ _ := ext fun _ ↦ mul_smul _ _ _
  smul_add _ _ _ := ext fun _ ↦ smul_add _ _ _
  smul_zero _ := ext fun _ ↦ smul_zero _

theorem smul_comp (a : S₃) (g : M₂ →ₛₗ[σ₂₃] M₃) (f : M →ₛₗ[σ₁₂] M₂) :
    (a • g).comp f = a • g.comp f :=
  rfl

-- TODO: generalize this to semilinear maps
theorem comp_smul [Module R M₂] [Module R M₃] [SMulCommClass R S M₂] [DistribMulAction S M₃]
    [SMulCommClass R S M₃] [CompatibleSMul M₃ M₂ S R] (g : M₃ →ₗ[R] M₂) (a : S) (f : M →ₗ[R] M₃) :
    g.comp (a • f) = a • g.comp f :=
  ext fun _ ↦ g.map_smul_of_tower _ _

end SMul

section Module

variable [Semiring S] [Module S M] [Module S M₂] [SMulCommClass R₂ S M₂]

instance module : Module S (M →ₛₗ[σ₁₂] M₂) where
  add_smul _ _ _ := ext fun _ ↦ add_smul _ _ _
  zero_smul _ := ext fun _ ↦ zero_smul _ _

end Module

end Actions

section RestrictScalarsAsLinearMap

variable {R S M N P : Type*} [Semiring R] [Semiring S] [AddCommMonoid M] [AddCommMonoid N]
  [Module R M] [Module R N] [Module S M] [Module S N] [CompatibleSMul M N R S]

variable (R S M N) in
@[simp]
lemma restrictScalars_zero : (0 : M →ₗ[S] N).restrictScalars R = 0 :=
  rfl

@[simp]
theorem restrictScalars_add (f g : M →ₗ[S] N) :
    (f + g).restrictScalars R = f.restrictScalars R + g.restrictScalars R :=
  rfl

@[simp]
theorem restrictScalars_neg {M N : Type*} [AddCommMonoid M] [AddCommGroup N]
    [Module R M] [Module R N] [Module S M] [Module S N] [CompatibleSMul M N R S]
    (f : M →ₗ[S] N) : (-f).restrictScalars R = -f.restrictScalars R :=
  rfl

variable {R₁ : Type*} [Semiring R₁] [Module R₁ N] [SMulCommClass S R₁ N] [SMulCommClass R R₁ N]

@[simp]
theorem restrictScalars_smul (c : R₁) (f : M →ₗ[S] N) :
    (c • f).restrictScalars R = c • f.restrictScalars R :=
  rfl

@[simp]
lemma restrictScalars_comp [AddCommMonoid P] [Module S P] [Module R P]
    [CompatibleSMul N P R S] [CompatibleSMul M P R S] (f : N →ₗ[S] P) (g : M →ₗ[S] N) :
    (f ∘ₗ g).restrictScalars R = f.restrictScalars R ∘ₗ g.restrictScalars R :=
  rfl

@[simp]
lemma restrictScalars_trans {T : Type*} [Semiring T] [Module T M] [Module T N]
    [CompatibleSMul M N S T] [CompatibleSMul M N R T] (f : M →ₗ[T] N) :
    (f.restrictScalars S).restrictScalars R = f.restrictScalars R :=
  rfl

variable (S M N R R₁)

/-- `LinearMap.restrictScalars` as a `LinearMap`. -/
@[simps apply]
def restrictScalarsₗ : (M →ₗ[S] N) →ₗ[R₁] M →ₗ[R] N where
  toFun := restrictScalars R
  map_add' := restrictScalars_add
  map_smul' := restrictScalars_smul

end RestrictScalarsAsLinearMap

section mulLeftRight
variable {R A : Type*} [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A]

section left
variable (R) [SMulCommClass R A A]

/-- The multiplication on the left in an algebra is a linear map.

Note that this only assumes `SMulCommClass R A A`, so that it also works for `R := Aᵐᵒᵖ`.

When `A` is unital and associative, this is the same as `DistribSMul.toLinearMap R A a` -/
def mulLeft (a : A) : A →ₗ[R] A where
  __ := AddMonoidHom.mulLeft a
  map_smul' _ := mul_smul_comm _ _

@[simp]
theorem mulLeft_apply (a b : A) : mulLeft R a b = a * b := rfl

@[simp]
theorem toAddMonoidHom_mulLeft (a : A) : (mulLeft R a : A →+ A) = AddMonoidHom.mulLeft a := rfl

@[deprecated (since := "2025-12-30")] alias mulLeft_toAddMonoidHom := toAddMonoidHom_mulLeft

variable (A) in
@[simp]
theorem mulLeft_zero_eq_zero : mulLeft R (0 : A) = 0 := ext zero_mul

end left

section right
variable (R) [IsScalarTower R A A]

/-- The multiplication on the right in an algebra is a linear map.

Note that this only assumes `IsScalarTower R A A`, so that it also works for `R := A`.

When `A` is unital and associative, this is the same as
`DistribSMul.toLinearMap R A (MulOpposite.op b)`. -/
def mulRight (b : A) : A →ₗ[R] A where
  __ := AddMonoidHom.mulRight b
  map_smul' _ _ := smul_mul_assoc _ _ _

@[simp]
theorem mulRight_apply (a b : A) : mulRight R a b = b * a := rfl

@[simp]
theorem toAddMonoidHom_mulRight (a : A) : (mulRight R a : A →+ A) = AddMonoidHom.mulRight a := rfl

@[deprecated (since := "2025-12-30")] alias mulRight_toAddMonoidHom := toAddMonoidHom_mulRight

variable (A) in
@[simp]
theorem mulRight_zero_eq_zero : mulRight R (0 : A) = 0 := ext mul_zero

end right

variable [SMulCommClass R A A] [IsScalarTower R A A]

variable (R) in
/-- Simultaneous multiplication on the left and right is a linear map. -/
def mulLeftRight (ab : A × A) : A →ₗ[R] A :=
  (mulRight R ab.snd).comp (mulLeft R ab.fst)

@[simp]
theorem mulLeftRight_apply (a b x : A) : mulLeftRight R (a, b) x = a * x * b :=
  rfl

end mulLeftRight

end LinearMap
