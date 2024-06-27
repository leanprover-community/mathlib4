/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.BigOperators.Finsupp

#align_import algebra.algebra.hom from "leanprover-community/mathlib"@"e97cf15cd1aec9bd5c193b2ffac5a6dc9118912b"

/-!
# Homomorphisms of `R`-algebras

This file defines bundled homomorphisms of `R`-algebras.

## Main definitions

* `AlgHom R A B`: the type of `R`-algebra morphisms from `A` to `B`.
* `Algebra.ofId R A : R →ₐ[R] A`: the canonical map from `R` to `A`, as an `AlgHom`.

## Notations

* `A →ₐ[R] B` : `R`-algebra homomorphism from `A` to `B`.
-/

universe u v w u₁ v₁

/-- Defining the homomorphism in the category R-Alg. -/
-- @[nolint has_nonempty_instance] -- Porting note(#5171): linter not ported yet
structure AlgHom (R : Type u) (A : Type v) (B : Type w) [CommSemiring R] [Semiring A] [Semiring B]
  [Algebra R A] [Algebra R B] extends RingHom A B where
  commutes' : ∀ r : R, toFun (algebraMap R A r) = algebraMap R B r
#align alg_hom AlgHom

/-- Reinterpret an `AlgHom` as a `RingHom` -/
add_decl_doc AlgHom.toRingHom

@[inherit_doc AlgHom]
infixr:25 " →ₐ " => AlgHom _

@[inherit_doc]
notation:25 A " →ₐ[" R "] " B => AlgHom R A B

/-- `AlgHomClass F R A B` asserts `F` is a type of bundled algebra homomorphisms
from `A` to `B`.  -/
class AlgHomClass (F : Type*) (R A B : outParam Type*)
  [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
  [FunLike F A B] extends RingHomClass F A B : Prop where
  commutes : ∀ (f : F) (r : R), f (algebraMap R A r) = algebraMap R B r
#align alg_hom_class AlgHomClass

-- Porting note: `dangerousInstance` linter has become smarter about `outParam`s
-- attribute [nolint dangerousInstance] AlgHomClass.toRingHomClass

-- Porting note (#10618): simp can prove this
-- attribute [simp] AlgHomClass.commutes

namespace AlgHomClass

variable {R A B F : Type*} [CommSemiring R] [Semiring A] [Semiring B]
  [Algebra R A] [Algebra R B] [FunLike F A B]

-- see Note [lower instance priority]
instance (priority := 100) linearMapClass [AlgHomClass F R A B] : LinearMapClass F R A B :=
  { ‹AlgHomClass F R A B› with
    map_smulₛₗ := fun f r x => by
      simp only [Algebra.smul_def, map_mul, commutes, RingHom.id_apply] }
#align alg_hom_class.linear_map_class AlgHomClass.linearMapClass

-- Porting note (#11445): A new definition underlying a coercion `↑`.
/-- Turn an element of a type `F` satisfying `AlgHomClass F α β` into an actual
`AlgHom`. This is declared as the default coercion from `F` to `α →+* β`. -/
@[coe]
def toAlgHom {F : Type*} [FunLike F A B] [AlgHomClass F R A B] (f : F) : A →ₐ[R] B where
  __ := (f : A →+* B)
  toFun := f
  commutes' := AlgHomClass.commutes f

instance coeTC {F : Type*} [FunLike F A B] [AlgHomClass F R A B] : CoeTC F (A →ₐ[R] B) :=
  ⟨AlgHomClass.toAlgHom⟩
#align alg_hom_class.alg_hom.has_coe_t AlgHomClass.coeTC

end AlgHomClass

namespace AlgHom

variable {R : Type u} {A : Type v} {B : Type w} {C : Type u₁} {D : Type v₁}

section Semiring

variable [CommSemiring R] [Semiring A] [Semiring B] [Semiring C] [Semiring D]
variable [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]

-- Porting note: we don't port specialized `CoeFun` instances if there is `DFunLike` instead
#noalign alg_hom.has_coe_to_fun

instance funLike : FunLike (A →ₐ[R] B) A B where
  coe f := f.toFun
  coe_injective' f g h := by
    rcases f with ⟨⟨⟨⟨_, _⟩, _⟩, _, _⟩, _⟩
    rcases g with ⟨⟨⟨⟨_, _⟩, _⟩, _, _⟩, _⟩
    congr

-- Porting note: This instance is moved.
instance algHomClass : AlgHomClass (A →ₐ[R] B) R A B where
  map_add f := f.map_add'
  map_zero f := f.map_zero'
  map_mul f := f.map_mul'
  map_one f := f.map_one'
  commutes f := f.commutes'
#align alg_hom.alg_hom_class AlgHom.algHomClass

/-- See Note [custom simps projection] -/
def Simps.apply {R : Type u} {α : Type v} {β : Type w} [CommSemiring R]
    [Semiring α] [Semiring β] [Algebra R α] [Algebra R β] (f : α →ₐ[R] β) : α → β := f

initialize_simps_projections AlgHom (toFun → apply)

@[simp]
protected theorem coe_coe {F : Type*} [FunLike F A B] [AlgHomClass F R A B] (f : F) :
    ⇑(f : A →ₐ[R] B) = f :=
  rfl
#align alg_hom.coe_coe AlgHom.coe_coe

@[simp]
theorem toFun_eq_coe (f : A →ₐ[R] B) : f.toFun = f :=
  rfl
#align alg_hom.to_fun_eq_coe AlgHom.toFun_eq_coe

#noalign alg_hom.coe_ring_hom

-- Porting note (#11445): A new definition underlying a coercion `↑`.
@[coe]
def toMonoidHom' (f : A →ₐ[R] B) : A →* B := (f : A →+* B)

instance coeOutMonoidHom : CoeOut (A →ₐ[R] B) (A →* B) :=
  ⟨AlgHom.toMonoidHom'⟩
#align alg_hom.coe_monoid_hom AlgHom.coeOutMonoidHom

-- Porting note (#11445): A new definition underlying a coercion `↑`.
@[coe]
def toAddMonoidHom' (f : A →ₐ[R] B) : A →+ B := (f : A →+* B)

instance coeOutAddMonoidHom : CoeOut (A →ₐ[R] B) (A →+ B) :=
  ⟨AlgHom.toAddMonoidHom'⟩
#align alg_hom.coe_add_monoid_hom AlgHom.coeOutAddMonoidHom

-- Porting note: Lean 3: `@[simp, norm_cast] coe_mk`
--               Lean 4: `@[simp] coe_mk` & `@[norm_cast] coe_mks`
@[simp]
theorem coe_mk {f : A →+* B} (h) : ((⟨f, h⟩ : A →ₐ[R] B) : A → B) = f :=
  rfl

@[norm_cast]
theorem coe_mks {f : A → B} (h₁ h₂ h₃ h₄ h₅) : ⇑(⟨⟨⟨⟨f, h₁⟩, h₂⟩, h₃, h₄⟩, h₅⟩ : A →ₐ[R] B) = f :=
  rfl
#align alg_hom.coe_mk AlgHom.coe_mks

-- Porting note: This theorem is new.
@[simp, norm_cast]
theorem coe_ringHom_mk {f : A →+* B} (h) : ((⟨f, h⟩ : A →ₐ[R] B) : A →+* B) = f :=
  rfl

-- make the coercion the simp-normal form
@[simp]
theorem toRingHom_eq_coe (f : A →ₐ[R] B) : f.toRingHom = f :=
  rfl
#align alg_hom.to_ring_hom_eq_coe AlgHom.toRingHom_eq_coe

@[simp, norm_cast]
theorem coe_toRingHom (f : A →ₐ[R] B) : ⇑(f : A →+* B) = f :=
  rfl
#align alg_hom.coe_to_ring_hom AlgHom.coe_toRingHom

@[simp, norm_cast]
theorem coe_toMonoidHom (f : A →ₐ[R] B) : ⇑(f : A →* B) = f :=
  rfl
#align alg_hom.coe_to_monoid_hom AlgHom.coe_toMonoidHom

@[simp, norm_cast]
theorem coe_toAddMonoidHom (f : A →ₐ[R] B) : ⇑(f : A →+ B) = f :=
  rfl
#align alg_hom.coe_to_add_monoid_hom AlgHom.coe_toAddMonoidHom

variable (φ : A →ₐ[R] B)

theorem coe_fn_injective : @Function.Injective (A →ₐ[R] B) (A → B) (↑) :=
  DFunLike.coe_injective
#align alg_hom.coe_fn_injective AlgHom.coe_fn_injective

theorem coe_fn_inj {φ₁ φ₂ : A →ₐ[R] B} : (φ₁ : A → B) = φ₂ ↔ φ₁ = φ₂ :=
  DFunLike.coe_fn_eq
#align alg_hom.coe_fn_inj AlgHom.coe_fn_inj

theorem coe_ringHom_injective : Function.Injective ((↑) : (A →ₐ[R] B) → A →+* B) := fun φ₁ φ₂ H =>
  coe_fn_injective <| show ((φ₁ : A →+* B) : A → B) = ((φ₂ : A →+* B) : A → B) from congr_arg _ H
#align alg_hom.coe_ring_hom_injective AlgHom.coe_ringHom_injective

theorem coe_monoidHom_injective : Function.Injective ((↑) : (A →ₐ[R] B) → A →* B) :=
  RingHom.coe_monoidHom_injective.comp coe_ringHom_injective
#align alg_hom.coe_monoid_hom_injective AlgHom.coe_monoidHom_injective

theorem coe_addMonoidHom_injective : Function.Injective ((↑) : (A →ₐ[R] B) → A →+ B) :=
  RingHom.coe_addMonoidHom_injective.comp coe_ringHom_injective
#align alg_hom.coe_add_monoid_hom_injective AlgHom.coe_addMonoidHom_injective

protected theorem congr_fun {φ₁ φ₂ : A →ₐ[R] B} (H : φ₁ = φ₂) (x : A) : φ₁ x = φ₂ x :=
  DFunLike.congr_fun H x
#align alg_hom.congr_fun AlgHom.congr_fun

protected theorem congr_arg (φ : A →ₐ[R] B) {x y : A} (h : x = y) : φ x = φ y :=
  DFunLike.congr_arg φ h
#align alg_hom.congr_arg AlgHom.congr_arg

@[ext]
theorem ext {φ₁ φ₂ : A →ₐ[R] B} (H : ∀ x, φ₁ x = φ₂ x) : φ₁ = φ₂ :=
  DFunLike.ext _ _ H
#align alg_hom.ext AlgHom.ext

theorem ext_iff {φ₁ φ₂ : A →ₐ[R] B} : φ₁ = φ₂ ↔ ∀ x, φ₁ x = φ₂ x :=
  DFunLike.ext_iff
#align alg_hom.ext_iff AlgHom.ext_iff

@[simp]
theorem mk_coe {f : A →ₐ[R] B} (h₁ h₂ h₃ h₄ h₅) : (⟨⟨⟨⟨f, h₁⟩, h₂⟩, h₃, h₄⟩, h₅⟩ : A →ₐ[R] B) = f :=
  ext fun _ => rfl
#align alg_hom.mk_coe AlgHom.mk_coe

@[simp]
theorem commutes (r : R) : φ (algebraMap R A r) = algebraMap R B r :=
  φ.commutes' r
#align alg_hom.commutes AlgHom.commutes

theorem comp_algebraMap : (φ : A →+* B).comp (algebraMap R A) = algebraMap R B :=
  RingHom.ext <| φ.commutes
#align alg_hom.comp_algebra_map AlgHom.comp_algebraMap

protected theorem map_add (r s : A) : φ (r + s) = φ r + φ s :=
  map_add _ _ _
#align alg_hom.map_add AlgHom.map_add

protected theorem map_zero : φ 0 = 0 :=
  map_zero _
#align alg_hom.map_zero AlgHom.map_zero

protected theorem map_mul (x y) : φ (x * y) = φ x * φ y :=
  map_mul _ _ _
#align alg_hom.map_mul AlgHom.map_mul

protected theorem map_one : φ 1 = 1 :=
  map_one _
#align alg_hom.map_one AlgHom.map_one

protected theorem map_pow (x : A) (n : ℕ) : φ (x ^ n) = φ x ^ n :=
  map_pow _ _ _
#align alg_hom.map_pow AlgHom.map_pow

-- @[simp] -- Porting note (#10618): simp can prove this
protected theorem map_smul (r : R) (x : A) : φ (r • x) = r • φ x :=
  map_smul _ _ _
#align alg_hom.map_smul AlgHom.map_smul

protected theorem map_sum {ι : Type*} (f : ι → A) (s : Finset ι) :
    φ (∑ x ∈ s, f x) = ∑ x ∈ s, φ (f x) :=
  map_sum _ _ _
#align alg_hom.map_sum AlgHom.map_sum

protected theorem map_finsupp_sum {α : Type*} [Zero α] {ι : Type*} (f : ι →₀ α) (g : ι → α → A) :
    φ (f.sum g) = f.sum fun i a => φ (g i a) :=
  map_finsupp_sum _ _ _
#align alg_hom.map_finsupp_sum AlgHom.map_finsupp_sum

#noalign alg_hom.map_bit0
#noalign alg_hom.map_bit1

/-- If a `RingHom` is `R`-linear, then it is an `AlgHom`. -/
def mk' (f : A →+* B) (h : ∀ (c : R) (x), f (c • x) = c • f x) : A →ₐ[R] B :=
  { f with
    toFun := f
    commutes' := fun c => by simp only [Algebra.algebraMap_eq_smul_one, h, f.map_one] }
#align alg_hom.mk' AlgHom.mk'

@[simp]
theorem coe_mk' (f : A →+* B) (h : ∀ (c : R) (x), f (c • x) = c • f x) : ⇑(mk' f h) = f :=
  rfl
#align alg_hom.coe_mk' AlgHom.coe_mk'

section

variable (R A)

/-- Identity map as an `AlgHom`. -/
protected def id : A →ₐ[R] A :=
  { RingHom.id A with commutes' := fun _ => rfl }
#align alg_hom.id AlgHom.id

@[simp]
theorem coe_id : ⇑(AlgHom.id R A) = id :=
  rfl
#align alg_hom.coe_id AlgHom.coe_id

@[simp]
theorem id_toRingHom : (AlgHom.id R A : A →+* A) = RingHom.id _ :=
  rfl
#align alg_hom.id_to_ring_hom AlgHom.id_toRingHom

end

theorem id_apply (p : A) : AlgHom.id R A p = p :=
  rfl
#align alg_hom.id_apply AlgHom.id_apply

/-- Composition of algebra homeomorphisms. -/
def comp (φ₁ : B →ₐ[R] C) (φ₂ : A →ₐ[R] B) : A →ₐ[R] C :=
  { φ₁.toRingHom.comp ↑φ₂ with
    commutes' := fun r : R => by rw [← φ₁.commutes, ← φ₂.commutes]; rfl }
#align alg_hom.comp AlgHom.comp

@[simp]
theorem coe_comp (φ₁ : B →ₐ[R] C) (φ₂ : A →ₐ[R] B) : ⇑(φ₁.comp φ₂) = φ₁ ∘ φ₂ :=
  rfl
#align alg_hom.coe_comp AlgHom.coe_comp

theorem comp_apply (φ₁ : B →ₐ[R] C) (φ₂ : A →ₐ[R] B) (p : A) : φ₁.comp φ₂ p = φ₁ (φ₂ p) :=
  rfl
#align alg_hom.comp_apply AlgHom.comp_apply

theorem comp_toRingHom (φ₁ : B →ₐ[R] C) (φ₂ : A →ₐ[R] B) :
    (φ₁.comp φ₂ : A →+* C) = (φ₁ : B →+* C).comp ↑φ₂ :=
  rfl
#align alg_hom.comp_to_ring_hom AlgHom.comp_toRingHom

@[simp]
theorem comp_id : φ.comp (AlgHom.id R A) = φ :=
  ext fun _x => rfl
#align alg_hom.comp_id AlgHom.comp_id

@[simp]
theorem id_comp : (AlgHom.id R B).comp φ = φ :=
  ext fun _x => rfl
#align alg_hom.id_comp AlgHom.id_comp

theorem comp_assoc (φ₁ : C →ₐ[R] D) (φ₂ : B →ₐ[R] C) (φ₃ : A →ₐ[R] B) :
    (φ₁.comp φ₂).comp φ₃ = φ₁.comp (φ₂.comp φ₃) :=
  ext fun _x => rfl
#align alg_hom.comp_assoc AlgHom.comp_assoc

/-- R-Alg ⥤ R-Mod -/
def toLinearMap : A →ₗ[R] B where
  toFun := φ
  map_add' := map_add _
  map_smul' := map_smul _
#align alg_hom.to_linear_map AlgHom.toLinearMap

@[simp]
theorem toLinearMap_apply (p : A) : φ.toLinearMap p = φ p :=
  rfl
#align alg_hom.to_linear_map_apply AlgHom.toLinearMap_apply

theorem toLinearMap_injective :
    Function.Injective (toLinearMap : _ → A →ₗ[R] B) := fun _φ₁ _φ₂ h =>
  ext <| LinearMap.congr_fun h
#align alg_hom.to_linear_map_injective AlgHom.toLinearMap_injective

@[simp]
theorem comp_toLinearMap (f : A →ₐ[R] B) (g : B →ₐ[R] C) :
    (g.comp f).toLinearMap = g.toLinearMap.comp f.toLinearMap :=
  rfl
#align alg_hom.comp_to_linear_map AlgHom.comp_toLinearMap

@[simp]
theorem toLinearMap_id : toLinearMap (AlgHom.id R A) = LinearMap.id :=
  LinearMap.ext fun _ => rfl
#align alg_hom.to_linear_map_id AlgHom.toLinearMap_id

/-- Promote a `LinearMap` to an `AlgHom` by supplying proofs about the behavior on `1` and `*`. -/
@[simps]
def ofLinearMap (f : A →ₗ[R] B) (map_one : f 1 = 1) (map_mul : ∀ x y, f (x * y) = f x * f y) :
    A →ₐ[R] B :=
  { f.toAddMonoidHom with
    toFun := f
    map_one' := map_one
    map_mul' := map_mul
    commutes' := fun c => by simp only [Algebra.algebraMap_eq_smul_one, f.map_smul, map_one] }
#align alg_hom.of_linear_map AlgHom.ofLinearMap

@[simp]
theorem ofLinearMap_toLinearMap (map_one) (map_mul) :
    ofLinearMap φ.toLinearMap map_one map_mul = φ := by
  ext
  rfl
#align alg_hom.of_linear_map_to_linear_map AlgHom.ofLinearMap_toLinearMap

@[simp]
theorem toLinearMap_ofLinearMap (f : A →ₗ[R] B) (map_one) (map_mul) :
    toLinearMap (ofLinearMap f map_one map_mul) = f := by
  ext
  rfl
#align alg_hom.to_linear_map_of_linear_map AlgHom.toLinearMap_ofLinearMap

@[simp]
theorem ofLinearMap_id (map_one) (map_mul) :
    ofLinearMap LinearMap.id map_one map_mul = AlgHom.id R A :=
  ext fun _ => rfl
#align alg_hom.of_linear_map_id AlgHom.ofLinearMap_id

theorem map_smul_of_tower {R'} [SMul R' A] [SMul R' B] [LinearMap.CompatibleSMul A B R' R] (r : R')
    (x : A) : φ (r • x) = r • φ x :=
  φ.toLinearMap.map_smul_of_tower r x
#align alg_hom.map_smul_of_tower AlgHom.map_smul_of_tower

nonrec theorem map_list_prod (s : List A) : φ s.prod = (s.map φ).prod :=
  map_list_prod φ s
#align alg_hom.map_list_prod AlgHom.map_list_prod

@[simps (config := .lemmasOnly) toSemigroup_toMul_mul toOne_one]
instance End : Monoid (A →ₐ[R] A) where
  mul := comp
  mul_assoc ϕ ψ χ := rfl
  one := AlgHom.id R A
  one_mul ϕ := ext fun x => rfl
  mul_one ϕ := ext fun x => rfl
#align alg_hom.End AlgHom.End

@[simp]
theorem one_apply (x : A) : (1 : A →ₐ[R] A) x = x :=
  rfl
#align alg_hom.one_apply AlgHom.one_apply

@[simp]
theorem mul_apply (φ ψ : A →ₐ[R] A) (x : A) : (φ * ψ) x = φ (ψ x) :=
  rfl
#align alg_hom.mul_apply AlgHom.mul_apply

theorem algebraMap_eq_apply (f : A →ₐ[R] B) {y : R} {x : A} (h : algebraMap R A y = x) :
    algebraMap R B y = f x :=
  h ▸ (f.commutes _).symm
#align alg_hom.algebra_map_eq_apply AlgHom.algebraMap_eq_apply

end Semiring

section CommSemiring

variable [CommSemiring R] [CommSemiring A] [CommSemiring B]
variable [Algebra R A] [Algebra R B] (φ : A →ₐ[R] B)

protected theorem map_multiset_prod (s : Multiset A) : φ s.prod = (s.map φ).prod :=
  map_multiset_prod _ _
#align alg_hom.map_multiset_prod AlgHom.map_multiset_prod

protected theorem map_prod {ι : Type*} (f : ι → A) (s : Finset ι) :
    φ (∏ x ∈ s, f x) = ∏ x ∈ s, φ (f x) :=
  map_prod _ _ _
#align alg_hom.map_prod AlgHom.map_prod

protected theorem map_finsupp_prod {α : Type*} [Zero α] {ι : Type*} (f : ι →₀ α) (g : ι → α → A) :
    φ (f.prod g) = f.prod fun i a => φ (g i a) :=
  map_finsupp_prod _ _ _
#align alg_hom.map_finsupp_prod AlgHom.map_finsupp_prod

end CommSemiring

section Ring

variable [CommSemiring R] [Ring A] [Ring B]
variable [Algebra R A] [Algebra R B] (φ : A →ₐ[R] B)

protected theorem map_neg (x) : φ (-x) = -φ x :=
  map_neg _ _
#align alg_hom.map_neg AlgHom.map_neg

protected theorem map_sub (x y) : φ (x - y) = φ x - φ y :=
  map_sub _ _ _
#align alg_hom.map_sub AlgHom.map_sub

end Ring

end AlgHom

namespace RingHom

variable {R S : Type*}

/-- Reinterpret a `RingHom` as an `ℕ`-algebra homomorphism. -/
def toNatAlgHom [Semiring R] [Semiring S] (f : R →+* S) : R →ₐ[ℕ] S :=
  { f with
    toFun := f
    commutes' := fun n => by simp }
#align ring_hom.to_nat_alg_hom RingHom.toNatAlgHom

/-- Reinterpret a `RingHom` as a `ℤ`-algebra homomorphism. -/
def toIntAlgHom [Ring R] [Ring S] [Algebra ℤ R] [Algebra ℤ S] (f : R →+* S) : R →ₐ[ℤ] S :=
  { f with commutes' := fun n => by simp }
#align ring_hom.to_int_alg_hom RingHom.toIntAlgHom

lemma toIntAlgHom_injective [Ring R] [Ring S] [Algebra ℤ R] [Algebra ℤ S] :
    Function.Injective (RingHom.toIntAlgHom : (R →+* S) → _) :=
  fun _ _ e ↦ DFunLike.ext _ _ (fun x ↦ DFunLike.congr_fun e x)

/-- Reinterpret a `RingHom` as a `ℚ`-algebra homomorphism. This actually yields an equivalence,
see `RingHom.equivRatAlgHom`. -/
def toRatAlgHom [Ring R] [Ring S] [Algebra ℚ R] [Algebra ℚ S] (f : R →+* S) : R →ₐ[ℚ] S :=
  { f with commutes' := f.map_rat_algebraMap }
#align ring_hom.to_rat_alg_hom RingHom.toRatAlgHom

@[simp]
theorem toRatAlgHom_toRingHom [Ring R] [Ring S] [Algebra ℚ R] [Algebra ℚ S] (f : R →+* S) :
    ↑f.toRatAlgHom = f :=
  RingHom.ext fun _x => rfl
#align ring_hom.to_rat_alg_hom_to_ring_hom RingHom.toRatAlgHom_toRingHom

end RingHom

section

variable {R S : Type*}

@[simp]
theorem AlgHom.toRingHom_toRatAlgHom [Ring R] [Ring S] [Algebra ℚ R] [Algebra ℚ S]
    (f : R →ₐ[ℚ] S) : (f : R →+* S).toRatAlgHom = f :=
  AlgHom.ext fun _x => rfl
#align alg_hom.to_ring_hom_to_rat_alg_hom AlgHom.toRingHom_toRatAlgHom

/-- The equivalence between `RingHom` and `ℚ`-algebra homomorphisms. -/
@[simps]
def RingHom.equivRatAlgHom [Ring R] [Ring S] [Algebra ℚ R] [Algebra ℚ S] :
    (R →+* S) ≃ (R →ₐ[ℚ] S) where
  toFun := RingHom.toRatAlgHom
  invFun := AlgHom.toRingHom
  left_inv f := RingHom.toRatAlgHom_toRingHom f
  right_inv f := AlgHom.toRingHom_toRatAlgHom f
#align ring_hom.equiv_rat_alg_hom RingHom.equivRatAlgHom

end

namespace Algebra

variable (R : Type u) (A : Type v)
variable [CommSemiring R] [Semiring A] [Algebra R A]

/-- `AlgebraMap` as an `AlgHom`. -/
def ofId : R →ₐ[R] A :=
  { algebraMap R A with commutes' := fun _ => rfl }
#align algebra.of_id Algebra.ofId

variable {R}

theorem ofId_apply (r) : ofId R A r = algebraMap R A r :=
  rfl
#align algebra.of_id_apply Algebra.ofId_apply

/-- This is a special case of a more general instance that we define in a later file. -/
instance subsingleton_id : Subsingleton (R →ₐ[R] A) :=
  ⟨fun f g => AlgHom.ext fun _ => (f.commutes _).trans (g.commutes _).symm⟩

/-- This ext lemma closes trivial subgoals create when chaining heterobasic ext lemmas. -/
@[ext high]
theorem ext_id (f g : R →ₐ[R] A) : f = g := Subsingleton.elim _ _

section MulDistribMulAction

instance : MulDistribMulAction (A →ₐ[R] A) Aˣ where
  smul := fun f => Units.map f
  one_smul := fun x => by ext; rfl
  mul_smul := fun x y z => by ext; rfl
  smul_mul := fun x y z => by ext; exact x.map_mul _ _
  smul_one := fun x => by ext; exact x.map_one

@[simp]
theorem smul_units_def (f : A →ₐ[R] A) (x : Aˣ) :
    f • x = Units.map (f : A →* A) x := rfl

end MulDistribMulAction
end Algebra

namespace MulSemiringAction

variable {M G : Type*} (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]
variable [Monoid M] [MulSemiringAction M A] [SMulCommClass M R A]

/-- Each element of the monoid defines an algebra homomorphism.

This is a stronger version of `MulSemiringAction.toRingHom` and
`DistribMulAction.toLinearMap`. -/
@[simps]
def toAlgHom (m : M) : A →ₐ[R] A :=
  { MulSemiringAction.toRingHom _ _ m with
    toFun := fun a => m • a
    commutes' := smul_algebraMap _ }
#align mul_semiring_action.to_alg_hom MulSemiringAction.toAlgHom

theorem toAlgHom_injective [FaithfulSMul M A] :
    Function.Injective (MulSemiringAction.toAlgHom R A : M → A →ₐ[R] A) := fun _m₁ _m₂ h =>
  eq_of_smul_eq_smul fun r => AlgHom.ext_iff.1 h r
#align mul_semiring_action.to_alg_hom_injective MulSemiringAction.toAlgHom_injective

end MulSemiringAction
