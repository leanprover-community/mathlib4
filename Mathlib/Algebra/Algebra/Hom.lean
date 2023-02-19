/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov

! This file was ported from Lean 3 source module algebra.algebra.hom
! leanprover-community/mathlib commit e97cf15cd1aec9bd5c193b2ffac5a6dc9118912b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Algebra.Basic

/-!
# Homomorphisms of `R`-algebras

This file defines bundled homomorphisms of `R`-algebras.

## Main definitions

* `alg_hom R A B`: the type of `R`-algebra morphisms from `A` to `B`.
* `algebra.of_id R A : R →ₐ[R] A`: the canonical map from `R` to `A`, as an `alg_hom`.

## Notations

* `A →ₐ[R] B` : `R`-algebra homomorphism from `A` to `B`.
-/


open BigOperators

universe u v w u₁ v₁

/-- Defining the homomorphism in the category R-Alg. -/
@[nolint has_nonempty_instance]
structure AlgHom (R : Type u) (A : Type v) (B : Type w) [CommSemiring R] [Semiring A] [Semiring B]
  [Algebra R A] [Algebra R B] extends RingHom A B where
  commutes' : ∀ r : R, to_fun (algebraMap R A r) = algebraMap R B r
#align alg_hom AlgHom

run_cmd
  tactic.add_doc_string `alg_hom.to_ring_hom "Reinterpret an `alg_hom` as a `ring_hom`"

-- mathport name: «expr →ₐ »
infixr:25 " →ₐ " => AlgHom _

-- mathport name: «expr →ₐ[ ] »
notation:25 A " →ₐ[" R "] " B => AlgHom R A B

/-- `alg_hom_class F R A B` asserts `F` is a type of bundled algebra homomorphisms
from `A` to `B`.  -/
class AlgHomClass (F : Type _) (R : outParam (Type _)) (A : outParam (Type _))
  (B : outParam (Type _)) [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A]
  [Algebra R B] extends RingHomClass F A B where
  commutes : ∀ (f : F) (r : R), f (algebraMap R A r) = algebraMap R B r
#align alg_hom_class AlgHomClass

-- `R` becomes a metavariable but that's fine because it's an `out_param`
attribute [nolint dangerous_instance] AlgHomClass.toRingHomClass

attribute [simp] AlgHomClass.commutes

namespace AlgHomClass

variable {R : Type _} {A : Type _} {B : Type _} [CommSemiring R] [Semiring A] [Semiring B]
  [Algebra R A] [Algebra R B]

-- see Note [lower instance priority]
instance (priority := 100) {F : Type _} [AlgHomClass F R A B] : LinearMapClass F R A B :=
  { ‹AlgHomClass F R A B› with
    map_smulₛₗ := fun f r x => by
      simp only [Algebra.smul_def, map_mul, commutes, RingHom.id_apply] }

instance {F : Type _} [AlgHomClass F R A B] : CoeTC F (A →ₐ[R] B)
    where coe f :=
    { (f : A →+* B) with
      toFun := f
      commutes' := AlgHomClass.commutes f }

end AlgHomClass

namespace AlgHom

variable {R : Type u} {A : Type v} {B : Type w} {C : Type u₁} {D : Type v₁}

section Semiring

variable [CommSemiring R] [Semiring A] [Semiring B] [Semiring C] [Semiring D]

variable [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]

instance : CoeFun (A →ₐ[R] B) fun _ => A → B :=
  ⟨AlgHom.toFun⟩

initialize_simps_projections AlgHom (toFun → apply)

@[simp, protected]
theorem coe_coe {F : Type _} [AlgHomClass F R A B] (f : F) : ⇑(f : A →ₐ[R] B) = f :=
  rfl
#align alg_hom.coe_coe AlgHom.coe_coe

@[simp]
theorem toFun_eq_coe (f : A →ₐ[R] B) : f.toFun = f :=
  rfl
#align alg_hom.to_fun_eq_coe AlgHom.toFun_eq_coe

instance : AlgHomClass (A →ₐ[R] B) R A B
    where
  coe := toFun
  coe_injective' f g h := by
    cases f
    cases g
    congr
  map_add := map_add'
  map_zero := map_zero'
  map_mul := map_mul'
  map_one := map_one'
  commutes f := f.commutes'

instance coeRingHom : Coe (A →ₐ[R] B) (A →+* B) :=
  ⟨AlgHom.toRingHom⟩
#align alg_hom.coe_ring_hom AlgHom.coeRingHom

instance coeMonoidHom : Coe (A →ₐ[R] B) (A →* B) :=
  ⟨fun f => ↑(f : A →+* B)⟩
#align alg_hom.coe_monoid_hom AlgHom.coeMonoidHom

instance coeAddMonoidHom : Coe (A →ₐ[R] B) (A →+ B) :=
  ⟨fun f => ↑(f : A →+* B)⟩
#align alg_hom.coe_add_monoid_hom AlgHom.coeAddMonoidHom

@[simp, norm_cast]
theorem coe_mk {f : A → B} (h₁ h₂ h₃ h₄ h₅) : ⇑(⟨f, h₁, h₂, h₃, h₄, h₅⟩ : A →ₐ[R] B) = f :=
  rfl
#align alg_hom.coe_mk AlgHom.coe_mk

-- make the coercion the simp-normal form
@[simp]
theorem toRingHom_eq_coe (f : A →ₐ[R] B) : f.toRingHom = f :=
  rfl
#align alg_hom.to_ring_hom_eq_coe AlgHom.toRingHom_eq_coe

@[simp, norm_cast]
theorem coe_to_ringHom (f : A →ₐ[R] B) : ⇑(f : A →+* B) = f :=
  rfl
#align alg_hom.coe_to_ring_hom AlgHom.coe_to_ringHom

@[simp, norm_cast]
theorem coe_to_monoidHom (f : A →ₐ[R] B) : ⇑(f : A →* B) = f :=
  rfl
#align alg_hom.coe_to_monoid_hom AlgHom.coe_to_monoidHom

@[simp, norm_cast]
theorem coe_toAddMonoid_hom (f : A →ₐ[R] B) : ⇑(f : A →+ B) = f :=
  rfl
#align alg_hom.coe_to_add_monoid_hom AlgHom.coe_toAddMonoid_hom

variable (φ : A →ₐ[R] B)

theorem coeFn_injective : @Function.Injective (A →ₐ[R] B) (A → B) coeFn :=
  FunLike.coe_injective
#align alg_hom.coe_fn_injective AlgHom.coeFn_injective

theorem coeFn_inj {φ₁ φ₂ : A →ₐ[R] B} : (φ₁ : A → B) = φ₂ ↔ φ₁ = φ₂ :=
  FunLike.coe_fn_eq
#align alg_hom.coe_fn_inj AlgHom.coeFn_inj

theorem coe_ringHom_injective : Function.Injective (coe : (A →ₐ[R] B) → A →+* B) := fun φ₁ φ₂ H =>
  coeFn_injective <| show ((φ₁ : A →+* B) : A → B) = ((φ₂ : A →+* B) : A → B) from congr_arg _ H
#align alg_hom.coe_ring_hom_injective AlgHom.coe_ringHom_injective

theorem coe_monoidHom_injective : Function.Injective (coe : (A →ₐ[R] B) → A →* B) :=
  RingHom.coe_monoidHom_injective.comp coe_ringHom_injective
#align alg_hom.coe_monoid_hom_injective AlgHom.coe_monoidHom_injective

theorem coe_addMonoidHom_injective : Function.Injective (coe : (A →ₐ[R] B) → A →+ B) :=
  RingHom.coe_addMonoidHom_injective.comp coe_ringHom_injective
#align alg_hom.coe_add_monoid_hom_injective AlgHom.coe_addMonoidHom_injective

protected theorem congr_fun {φ₁ φ₂ : A →ₐ[R] B} (H : φ₁ = φ₂) (x : A) : φ₁ x = φ₂ x :=
  FunLike.congr_fun H x
#align alg_hom.congr_fun AlgHom.congr_fun

protected theorem congr_arg (φ : A →ₐ[R] B) {x y : A} (h : x = y) : φ x = φ y :=
  FunLike.congr_arg φ h
#align alg_hom.congr_arg AlgHom.congr_arg

@[ext]
theorem ext {φ₁ φ₂ : A →ₐ[R] B} (H : ∀ x, φ₁ x = φ₂ x) : φ₁ = φ₂ :=
  FunLike.ext _ _ H
#align alg_hom.ext AlgHom.ext

theorem ext_iff {φ₁ φ₂ : A →ₐ[R] B} : φ₁ = φ₂ ↔ ∀ x, φ₁ x = φ₂ x :=
  FunLike.ext_iff
#align alg_hom.ext_iff AlgHom.ext_iff

@[simp]
theorem mk_coe {f : A →ₐ[R] B} (h₁ h₂ h₃ h₄ h₅) : (⟨f, h₁, h₂, h₃, h₄, h₅⟩ : A →ₐ[R] B) = f :=
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

@[simp]
protected theorem map_smul (r : R) (x : A) : φ (r • x) = r • φ x :=
  map_smul _ _ _
#align alg_hom.map_smul AlgHom.map_smul

protected theorem map_sum {ι : Type _} (f : ι → A) (s : Finset ι) :
    φ (∑ x in s, f x) = ∑ x in s, φ (f x) :=
  map_sum _ _ _
#align alg_hom.map_sum AlgHom.map_sum

protected theorem map_finsupp_sum {α : Type _} [Zero α] {ι : Type _} (f : ι →₀ α) (g : ι → α → A) :
    φ (f.Sum g) = f.Sum fun i a => φ (g i a) :=
  map_finsupp_sum _ _ _
#align alg_hom.map_finsupp_sum AlgHom.map_finsupp_sum

protected theorem map_bit0 (x) : φ (bit0 x) = bit0 (φ x) :=
  map_bit0 _ _
#align alg_hom.map_bit0 AlgHom.map_bit0

protected theorem map_bit1 (x) : φ (bit1 x) = bit1 (φ x) :=
  map_bit1 _ _
#align alg_hom.map_bit1 AlgHom.map_bit1

/-- If a `ring_hom` is `R`-linear, then it is an `alg_hom`. -/
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

/-- Identity map as an `alg_hom`. -/
protected def id : A →ₐ[R] A :=
  { RingHom.id A with commutes' := fun _ => rfl }
#align alg_hom.id AlgHom.id

@[simp]
theorem coe_id : ⇑(AlgHom.id R A) = id :=
  rfl
#align alg_hom.coe_id AlgHom.coe_id

@[simp]
theorem id_to_ringHom : (AlgHom.id R A : A →+* A) = RingHom.id _ :=
  rfl
#align alg_hom.id_to_ring_hom AlgHom.id_to_ringHom

end

theorem id_apply (p : A) : AlgHom.id R A p = p :=
  rfl
#align alg_hom.id_apply AlgHom.id_apply

/-- Composition of algebra homeomorphisms. -/
def comp (φ₁ : B →ₐ[R] C) (φ₂ : A →ₐ[R] B) : A →ₐ[R] C :=
  { φ₁.toRingHom.comp ↑φ₂ with
    commutes' := fun r : R => by rw [← φ₁.commutes, ← φ₂.commutes] <;> rfl }
#align alg_hom.comp AlgHom.comp

@[simp]
theorem coe_comp (φ₁ : B →ₐ[R] C) (φ₂ : A →ₐ[R] B) : ⇑(φ₁.comp φ₂) = φ₁ ∘ φ₂ :=
  rfl
#align alg_hom.coe_comp AlgHom.coe_comp

theorem comp_apply (φ₁ : B →ₐ[R] C) (φ₂ : A →ₐ[R] B) (p : A) : φ₁.comp φ₂ p = φ₁ (φ₂ p) :=
  rfl
#align alg_hom.comp_apply AlgHom.comp_apply

theorem comp_to_ringHom (φ₁ : B →ₐ[R] C) (φ₂ : A →ₐ[R] B) :
    (φ₁.comp φ₂ : A →+* C) = (φ₁ : B →+* C).comp ↑φ₂ :=
  rfl
#align alg_hom.comp_to_ring_hom AlgHom.comp_to_ringHom

@[simp]
theorem comp_id : φ.comp (AlgHom.id R A) = φ :=
  ext fun x => rfl
#align alg_hom.comp_id AlgHom.comp_id

@[simp]
theorem id_comp : (AlgHom.id R B).comp φ = φ :=
  ext fun x => rfl
#align alg_hom.id_comp AlgHom.id_comp

theorem comp_assoc (φ₁ : C →ₐ[R] D) (φ₂ : B →ₐ[R] C) (φ₃ : A →ₐ[R] B) :
    (φ₁.comp φ₂).comp φ₃ = φ₁.comp (φ₂.comp φ₃) :=
  ext fun x => rfl
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

theorem toLinearMap_injective : Function.Injective (toLinearMap : _ → A →ₗ[R] B) := fun φ₁ φ₂ h =>
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

/-- Promote a `linear_map` to an `alg_hom` by supplying proofs about the behavior on `1` and `*`. -/
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
    ofLinearMap φ.toLinearMap map_one map_mul = φ :=
  by
  ext
  rfl
#align alg_hom.of_linear_map_to_linear_map AlgHom.ofLinearMap_toLinearMap

@[simp]
theorem toLinearMap_ofLinearMap (f : A →ₗ[R] B) (map_one) (map_mul) :
    toLinearMap (ofLinearMap f map_one map_mul) = f :=
  by
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

theorem map_list_prod (s : List A) : φ s.Prod = (s.map φ).Prod :=
  φ.toRingHom.map_list_prod s
#align alg_hom.map_list_prod AlgHom.map_list_prod

@[simps (config := { attrs := [] }) mul one]
instance end : Monoid (A →ₐ[R] A) where
  mul := comp
  mul_assoc ϕ ψ χ := rfl
  one := AlgHom.id R A
  one_mul ϕ := ext fun x => rfl
  mul_one ϕ := ext fun x => rfl
#align alg_hom.End AlgHom.end

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

protected theorem map_multiset_prod (s : Multiset A) : φ s.Prod = (s.map φ).Prod :=
  map_multiset_prod _ _
#align alg_hom.map_multiset_prod AlgHom.map_multiset_prod

protected theorem map_prod {ι : Type _} (f : ι → A) (s : Finset ι) :
    φ (∏ x in s, f x) = ∏ x in s, φ (f x) :=
  map_prod _ _ _
#align alg_hom.map_prod AlgHom.map_prod

protected theorem map_finsupp_prod {α : Type _} [Zero α] {ι : Type _} (f : ι →₀ α) (g : ι → α → A) :
    φ (f.Prod g) = f.Prod fun i a => φ (g i a) :=
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

variable {R S : Type _}

/-- Reinterpret a `ring_hom` as an `ℕ`-algebra homomorphism. -/
def toNatAlgHom [Semiring R] [Semiring S] (f : R →+* S) : R →ₐ[ℕ] S :=
  { f with
    toFun := f
    commutes' := fun n => by simp }
#align ring_hom.to_nat_alg_hom RingHom.toNatAlgHom

/-- Reinterpret a `ring_hom` as a `ℤ`-algebra homomorphism. -/
def toIntAlgHom [Ring R] [Ring S] [Algebra ℤ R] [Algebra ℤ S] (f : R →+* S) : R →ₐ[ℤ] S :=
  { f with commutes' := fun n => by simp }
#align ring_hom.to_int_alg_hom RingHom.toIntAlgHom

/-- Reinterpret a `ring_hom` as a `ℚ`-algebra homomorphism. This actually yields an equivalence,
see `ring_hom.equiv_rat_alg_hom`. -/
def toRatAlgHom [Ring R] [Ring S] [Algebra ℚ R] [Algebra ℚ S] (f : R →+* S) : R →ₐ[ℚ] S :=
  { f with commutes' := f.map_rat_algebraMap }
#align ring_hom.to_rat_alg_hom RingHom.toRatAlgHom

@[simp]
theorem toRatAlgHom_to_ringHom [Ring R] [Ring S] [Algebra ℚ R] [Algebra ℚ S] (f : R →+* S) :
    ↑f.toRatAlgHom = f :=
  RingHom.ext fun x => rfl
#align ring_hom.to_rat_alg_hom_to_ring_hom RingHom.toRatAlgHom_to_ringHom

end RingHom

section

variable {R S : Type _}

@[simp]
theorem AlgHom.to_ringHom_toRatAlgHom [Ring R] [Ring S] [Algebra ℚ R] [Algebra ℚ S]
    (f : R →ₐ[ℚ] S) : (f : R →+* S).toRatAlgHom = f :=
  AlgHom.ext fun x => rfl
#align alg_hom.to_ring_hom_to_rat_alg_hom AlgHom.to_ringHom_toRatAlgHom

/-- The equivalence between `ring_hom` and `ℚ`-algebra homomorphisms. -/
@[simps]
def RingHom.equivRatAlgHom [Ring R] [Ring S] [Algebra ℚ R] [Algebra ℚ S] : (R →+* S) ≃ (R →ₐ[ℚ] S)
    where
  toFun := RingHom.toRatAlgHom
  invFun := AlgHom.toRingHom
  left_inv := RingHom.toRatAlgHom_to_ringHom
  right_inv := AlgHom.to_ringHom_toRatAlgHom
#align ring_hom.equiv_rat_alg_hom RingHom.equivRatAlgHom

end

namespace Algebra

variable (R : Type u) (A : Type v)

variable [CommSemiring R] [Semiring A] [Algebra R A]

/-- `algebra_map` as an `alg_hom`. -/
def ofId : R →ₐ[R] A :=
  { algebraMap R A with commutes' := fun _ => rfl }
#align algebra.of_id Algebra.ofId

variable {R}

theorem ofId_apply (r) : ofId R A r = algebraMap R A r :=
  rfl
#align algebra.of_id_apply Algebra.ofId_apply

end Algebra

namespace MulSemiringAction

variable {M G : Type _} (R A : Type _) [CommSemiring R] [Semiring A] [Algebra R A]

variable [Monoid M] [MulSemiringAction M A] [SMulCommClass M R A]

/-- Each element of the monoid defines a algebra homomorphism.

This is a stronger version of `mul_semiring_action.to_ring_hom` and
`distrib_mul_action.to_linear_map`. -/
@[simps]
def toAlgHom (m : M) : A →ₐ[R] A :=
  {
    MulSemiringAction.toRingHom _ _
      m with
    toFun := fun a => m • a
    commutes' := smul_algebraMap _ }
#align mul_semiring_action.to_alg_hom MulSemiringAction.toAlgHom

theorem toAlgHom_injective [FaithfulSMul M A] :
    Function.Injective (MulSemiringAction.toAlgHom R A : M → A →ₐ[R] A) := fun m₁ m₂ h =>
  eq_of_smul_eq_smul fun r => AlgHom.ext_iff.1 h r
#align mul_semiring_action.to_alg_hom_injective MulSemiringAction.toAlgHom_injective

end MulSemiringAction

