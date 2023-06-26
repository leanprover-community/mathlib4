/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov

! This file was ported from Lean 3 source module subalgebra
-/
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.RingTheory.NonUnitalSubsemiring.Basic
import Mathlib.RingTheory.NonUnitalSubring.Basic
import Mathlib.Algebra.Hom.NonUnitalAlg
import Mathlib.Data.Set.UnionLift
import Mathlib.LinearAlgebra.Finsupp
import Mathlib.RingTheory.Ideal.Operations

/-!
# Non-unital Subalgebras over Commutative Semirings

In this file we define `non_unital_subalgebra`s and the usual operations on them (`map`, `comap`).

## TODO

* once we have scalar actions by semigroups (as opposed to monoids), implement the action of a
  non-unital subalgebra on the larger algebra.
-/


/-- The identity map as a `non_unital_alg_hom`. -/
protected def NonUnitalAlgHom.id (R A : Type _) [Monoid R] [NonUnitalNonAssocSemiring A]
    [DistribMulAction R A] : A →ₙₐ[R] A :=
  { NonUnitalRingHom.id A with
    toFun := id
    map_smul' := fun _ _ => rfl }
#align non_unital_alg_hom.id NonUnitalAlgHom.id

universe u u' v v' w w'

open scoped BigOperators

section NonUnitalSubalgebraClass

/-
/-- `non_unital_subalgebra_class S R` states that `S` is a type of subsets `s ⊆ R` that
are both a subsemiring and a submodule. -/
class non_unital_subalgebra_class (S : Type*) (R : out_param (Type*)) (A : Type*) [comm_semiring R]
  [non_unital_semiring A] [has_smul R A] [set_like S A] extends
  non_unital_subsemiring_class S A, smul_mem_class S R A : Prop

@[priority 100] -- See note [lower instance priority]
instance non_unital_subalgebra_class.to_submodule_class (S : Type*) (R : Type*) (A : Type*)
  [comm_ring R] [non_unital_ring A] [module R A] [set_like S A]
  [non_unital_subsemiring_class S A] [h : non_unital_subalgebra_class S R A] :
  submodule_class S R A :=
{ .. non_unital_subalgebra_class.to_smul_mem_class S R A }

-- not a problem because `R` is marked as an `out_param`
attribute [nolint dangerous_instance] non_unital_subalgebra_class.to_non_unital_subring_class
-/
-- not a problem because `R` is marked as an `out_param` in `smul_mem_class`
--attribute [nolint dangerous_instance] non_unital_subalgebra_class.to_non_unital_subring_class
variable {S R A : Type _} [CommSemiring R] [NonUnitalSemiring A] [Module R A]

variable [SetLike S A] [NonUnitalSubsemiringClass S A] [hSR : SMulMemClass S R A] (s : S)

namespace NonUnitalSubalgebraClass

/-- Embedding of a non-unital subalgebra into the non-unital algebra. -/
def subtype (s : S) : s →ₙₐ[R] A :=
  { NonUnitalSubsemiringClass.subtype s, SMulMemClass.subtype s with toFun := (↑) }
#align non_unital_subalgebra_class.subtype NonUnitalSubalgebraClass.subtype

@[simp]
theorem coeSubtype : (subtype s (R := R) : s → A) = ((↑) : s → A) :=
  rfl
#align non_unital_subalgebra_class.coe_subtype NonUnitalSubalgebraClass.coeSubtype

end NonUnitalSubalgebraClass

end NonUnitalSubalgebraClass

/-- A non-unital subalgebra is a sub(semi)ring that is also a submodule. -/
structure NonUnitalSubalgebra (R : Type u) (A : Type v) [CommSemiring R] [NonUnitalSemiring A]
    [Module R A] extends NonUnitalSubsemiring A, Submodule R A : Type v
#align non_unital_subalgebra NonUnitalSubalgebra

/-- Reinterpret a `non_unital_subalgebra` as a `non_unital_subsemiring`. -/
add_decl_doc NonUnitalSubalgebra.toNonUnitalSubsemiring

/-- Reinterpret a `non_unital_subalgebra` as a `submodule`. -/
add_decl_doc NonUnitalSubalgebra.toSubmodule

namespace NonUnitalSubalgebra

variable {F : Type v'} {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [NonUnitalSemiring A] [Module R A] [NonUnitalSemiring B] [Module R B]

variable [NonUnitalSemiring C] [Module R C] [NonUnitalAlgHomClass F R A B]

instance : SetLike (NonUnitalSubalgebra R A) A
    where
  coe s := s.carrier
  coe_injective' p q h := by cases p; cases q; congr; exact SetLike.coe_injective h

instance instNonUnitalSubsemiringClass : NonUnitalSubsemiringClass (NonUnitalSubalgebra R A) A
    where
  add_mem {s} := s.add_mem'
  mul_mem {s} := s.mul_mem'
  zero_mem {s} := s.zero_mem'

instance : SMulMemClass (NonUnitalSubalgebra R A) R A where smul_mem := @fun s => s.smul_mem'

instance {R : Type u} {A : Type v} [CommRing R] [NonUnitalRing A] [Module R A] :
    NonUnitalSubringClass (NonUnitalSubalgebra R A) A :=
  { NonUnitalSubalgebra.instNonUnitalSubsemiringClass with
    neg_mem := @fun _ x hx => neg_one_smul R x ▸ SMulMemClass.smul_mem _ hx }

theorem mem_carrier {s : NonUnitalSubalgebra R A} {x : A} : x ∈ s.carrier ↔ x ∈ s :=
  Iff.rfl
#align non_unital_subalgebra.mem_carrier NonUnitalSubalgebra.mem_carrier

@[ext]
theorem ext {S T : NonUnitalSubalgebra R A} (h : ∀ x : A, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h
#align non_unital_subalgebra.ext NonUnitalSubalgebra.ext

@[simp]
theorem mem_toNonUnitalSubsemiring {S : NonUnitalSubalgebra R A} {x} :
    x ∈ S.toNonUnitalSubsemiring ↔ x ∈ S :=
  Iff.rfl
#align non_unital_subalgebra.mem_to_non_unital_subsemiring NonUnitalSubalgebra.mem_toNonUnitalSubsemiring

@[simp]
theorem coe_toNonUnitalSubsemiring (S : NonUnitalSubalgebra R A) :
    (↑S.toNonUnitalSubsemiring : Set A) = S :=
  rfl
#align non_unital_subalgebra.coe_to_non_unital_subsemiring NonUnitalSubalgebra.coe_toNonUnitalSubsemiring

theorem toNonUnitalSubsemiring_injective :
    Function.Injective
      (toNonUnitalSubsemiring : NonUnitalSubalgebra R A → NonUnitalSubsemiring A) :=
  fun S T h =>
  ext fun x => by rw [← mem_toNonUnitalSubsemiring, ← mem_toNonUnitalSubsemiring, h]
#align non_unital_subalgebra.to_non_unital_subsemiring_injective NonUnitalSubalgebra.toNonUnitalSubsemiring_injective

theorem toNonUnitalSubsemiring_inj {S U : NonUnitalSubalgebra R A} :
    S.toNonUnitalSubsemiring = U.toNonUnitalSubsemiring ↔ S = U :=
  toNonUnitalSubsemiring_injective.eq_iff
#align non_unital_subalgebra.to_non_unital_subsemiring_inj NonUnitalSubalgebra.toNonUnitalSubsemiring_inj

theorem mem_toSubmodule (S : NonUnitalSubalgebra R A) {x} : x ∈ S.toSubmodule ↔ x ∈ S :=
  Iff.rfl
#align non_unital_subalgebra.mem_to_submodule NonUnitalSubalgebra.mem_toSubmodule

@[simp]
theorem coe_toSubmodule (S : NonUnitalSubalgebra R A) : (↑S.toSubmodule : Set A) = S :=
  rfl
#align non_unital_subalgebra.coe_to_submodule NonUnitalSubalgebra.coe_toSubmodule

theorem toSubmodule_injective :
    Function.Injective (toSubmodule : NonUnitalSubalgebra R A → Submodule R A) := fun S T h =>
  ext fun x => by rw [← mem_toSubmodule, ← mem_toSubmodule, h]
#align non_unital_subalgebra.to_submodule_injective NonUnitalSubalgebra.toSubmodule_injective

theorem toSubmodule_inj {S U : NonUnitalSubalgebra R A} : S.toSubmodule = U.toSubmodule ↔ S = U :=
  toSubmodule_injective.eq_iff
#align non_unital_subalgebra.to_submodule_inj NonUnitalSubalgebra.toSubmodule_inj

/-- Copy of a non-unital subalgebra with a new `carrier` equal to the old one.
Useful to fix definitional equalities. -/
protected def copy (S : NonUnitalSubalgebra R A) (s : Set A) (hs : s = ↑S) :
    NonUnitalSubalgebra R A :=
  { S.toNonUnitalSubsemiring.copy s hs with
    smul_mem' := fun r a (ha : a ∈ s) => by
      show r • a ∈ s
      rw [hs] at ha ⊢
      exact S.smul_mem' r ha }
#align non_unital_subalgebra.copy NonUnitalSubalgebra.copy

@[simp]
theorem coe_copy (S : NonUnitalSubalgebra R A) (s : Set A) (hs : s = ↑S) :
    (S.copy s hs : Set A) = s :=
  rfl
#align non_unital_subalgebra.coe_copy NonUnitalSubalgebra.coe_copy

theorem copy_eq (S : NonUnitalSubalgebra R A) (s : Set A) (hs : s = ↑S) : S.copy s hs = S :=
  SetLike.coe_injective hs
#align non_unital_subalgebra.copy_eq NonUnitalSubalgebra.copy_eq

variable (S : NonUnitalSubalgebra R A)

protected theorem smul_mem {x : A} (hx : x ∈ S) (r : R) : r • x ∈ S :=
  S.smul_mem' r hx
#align non_unital_subalgebra.smul_mem NonUnitalSubalgebra.smul_mem

protected theorem mul_mem {x y : A} (hx : x ∈ S) (hy : y ∈ S) : x * y ∈ S :=
  mul_mem hx hy
#align non_unital_subalgebra.mul_mem NonUnitalSubalgebra.mul_mem

protected theorem zero_mem : (0 : A) ∈ S :=
  zero_mem S
#align non_unital_subalgebra.zero_mem NonUnitalSubalgebra.zero_mem

protected theorem add_mem {x y : A} (hx : x ∈ S) (hy : y ∈ S) : x + y ∈ S :=
  add_mem hx hy
#align non_unital_subalgebra.add_mem NonUnitalSubalgebra.add_mem

protected theorem nsmul_mem {x : A} (hx : x ∈ S) (n : ℕ) : n • x ∈ S :=
  nsmul_mem hx n
#align non_unital_subalgebra.nsmul_mem NonUnitalSubalgebra.nsmul_mem

protected theorem list_sum_mem {L : List A} (h : ∀ x ∈ L, x ∈ S) : L.sum ∈ S :=
  list_sum_mem h
#align non_unital_subalgebra.list_sum_mem NonUnitalSubalgebra.list_sum_mem

protected theorem multiset_sum_mem {m : Multiset A} (h : ∀ x ∈ m, x ∈ S) : m.sum ∈ S :=
  multiset_sum_mem m h
#align non_unital_subalgebra.multiset_sum_mem NonUnitalSubalgebra.multiset_sum_mem

protected theorem sum_mem {ι : Type w} {t : Finset ι} {f : ι → A} (h : ∀ x ∈ t, f x ∈ S) :
    ∑ x in t, f x ∈ S :=
  sum_mem h
#align non_unital_subalgebra.sum_mem NonUnitalSubalgebra.sum_mem

protected theorem neg_mem {R : Type u} {A : Type v} [CommRing R] [NonUnitalRing A] [Module R A]
    (S : NonUnitalSubalgebra R A) {x : A} (hx : x ∈ S) : -x ∈ S :=
  neg_mem hx
#align non_unital_subalgebra.neg_mem NonUnitalSubalgebra.neg_mem

protected theorem sub_mem {R : Type u} {A : Type v} [CommRing R] [NonUnitalRing A] [Module R A]
    (S : NonUnitalSubalgebra R A) {x y : A} (hx : x ∈ S) (hy : y ∈ S) : x - y ∈ S :=
  sub_mem hx hy
#align non_unital_subalgebra.sub_mem NonUnitalSubalgebra.sub_mem

protected theorem zsmul_mem {R : Type u} {A : Type v} [CommRing R] [NonUnitalRing A] [Module R A]
    (S : NonUnitalSubalgebra R A) {x : A} (hx : x ∈ S) (n : ℤ) : n • x ∈ S :=
  zsmul_mem hx n
#align non_unital_subalgebra.zsmul_mem NonUnitalSubalgebra.zsmul_mem

/-- A non-unital subalgebra over a ring is also a `subring`. -/
def toNonUnitalSubring {R : Type u} {A : Type v} [CommRing R] [NonUnitalRing A] [Module R A]
    (S : NonUnitalSubalgebra R A) : NonUnitalSubring A where
  toNonUnitalSubsemiring := S.toNonUnitalSubsemiring
  neg_mem' := S.neg_mem
#align non_unital_subalgebra.to_non_unital_subring NonUnitalSubalgebra.toNonUnitalSubring

@[simp]
theorem mem_toNonUnitalSubring {R : Type u} {A : Type v} [CommRing R] [NonUnitalRing A] [Module R A]
    {S : NonUnitalSubalgebra R A} {x} : x ∈ S.toNonUnitalSubring ↔ x ∈ S :=
  Iff.rfl
#align non_unital_subalgebra.mem_to_non_unital_subring NonUnitalSubalgebra.mem_toNonUnitalSubring

@[simp]
theorem coe_toNonUnitalSubring {R : Type u} {A : Type v} [CommRing R] [NonUnitalRing A] [Module R A]
    (S : NonUnitalSubalgebra R A) : (↑S.toNonUnitalSubring : Set A) = S :=
  rfl
#align non_unital_subalgebra.coe_to_non_unital_subring NonUnitalSubalgebra.coe_toNonUnitalSubring

theorem toNonUnitalSubring_injective {R : Type u} {A : Type v} [CommRing R] [NonUnitalRing A]
    [Module R A] :
    Function.Injective (toNonUnitalSubring : NonUnitalSubalgebra R A → NonUnitalSubring A) :=
  fun S T h => ext fun x => by rw [← mem_toNonUnitalSubring, ← mem_toNonUnitalSubring, h]
#align non_unital_subalgebra.to_non_unital_subring_injective NonUnitalSubalgebra.toNonUnitalSubring_injective

theorem toNonUnitalSubring_inj {R : Type u} {A : Type v} [CommRing R] [NonUnitalRing A] [Module R A]
    {S U : NonUnitalSubalgebra R A} : S.toNonUnitalSubring = U.toNonUnitalSubring ↔ S = U :=
  toNonUnitalSubring_injective.eq_iff
#align non_unital_subalgebra.to_non_unital_subring_inj NonUnitalSubalgebra.toNonUnitalSubring_inj

instance : Inhabited S :=
  ⟨(0 : S.toNonUnitalSubsemiring)⟩

section

/-! `non_unital_subalgebra`s inherit structure from their `non_unital_subsemiring` / `semiring` coercions. -/


instance toNonUnitalSemiring {R A} [CommSemiring R] [NonUnitalSemiring A] [Module R A]
    (S : NonUnitalSubalgebra R A) : NonUnitalSemiring S :=
  inferInstance
#align non_unital_subalgebra.to_non_unital_semiring NonUnitalSubalgebra.toNonUnitalSemiring

instance toNonUnitalCommSemiring {R A} [CommSemiring R] [NonUnitalCommSemiring A] [Module R A]
    (S : NonUnitalSubalgebra R A) : NonUnitalCommSemiring S :=
  inferInstance
#align non_unital_subalgebra.to_non_unital_comm_semiring NonUnitalSubalgebra.toNonUnitalCommSemiring

instance toNonUnitalRing {R A} [CommRing R] [NonUnitalRing A] [Module R A]
    (S : NonUnitalSubalgebra R A) : NonUnitalRing S :=
  inferInstance
#align non_unital_subalgebra.to_non_unital_ring NonUnitalSubalgebra.toNonUnitalRing

instance toNonUnitalCommRing {R A} [CommRing R] [NonUnitalCommRing A] [Module R A]
    (S : NonUnitalSubalgebra R A) : NonUnitalCommRing S :=
  inferInstance
#align non_unital_subalgebra.to_non_unital_comm_ring NonUnitalSubalgebra.toNonUnitalCommRing

end

/-- The forgetful map from `non_unital_subalgebra` to `submodule` as an `order_embedding` -/
def toSubmodule' : NonUnitalSubalgebra R A ↪o Submodule R A
    where
  toEmbedding :=
    { toFun := fun S => S.toSubmodule
      inj' := fun S T h => ext <| by apply SetLike.ext_iff.1 h }
  map_rel_iff' := SetLike.coe_subset_coe.symm.trans SetLike.coe_subset_coe
#align non_unital_subalgebra.to_submodule' NonUnitalSubalgebra.toSubmodule'

/-- The forgetful map from `non_unital_subalgebra` to `non_unital_subsemiring` as an
`order_embedding` -/
def toNonUnitalSubsemiring' : NonUnitalSubalgebra R A ↪o NonUnitalSubsemiring A
    where
  toEmbedding :=
    { toFun := fun S => S.toNonUnitalSubsemiring
      inj' := fun S T h => ext <| by apply SetLike.ext_iff.1 h }
  map_rel_iff' := SetLike.coe_subset_coe.symm.trans SetLike.coe_subset_coe
#align non_unital_subalgebra.to_non_unital_subsemiring' NonUnitalSubalgebra.toNonUnitalSubsemiring'

/-- The forgetful map from `non_unital_subalgebra` to `non_unital_subsemiring` as an
`order_embedding` -/
def toNonUnitalSubring' {R : Type u} {A : Type v} [CommRing R] [NonUnitalRing A] [Module R A] :
    NonUnitalSubalgebra R A ↪o NonUnitalSubring A
    where
  toEmbedding :=
    { toFun := fun S => S.toNonUnitalSubring
      inj' := fun S T h => ext <| by apply SetLike.ext_iff.1 h }
  map_rel_iff' := SetLike.coe_subset_coe.symm.trans SetLike.coe_subset_coe
#align non_unital_subalgebra.to_non_unital_subring' NonUnitalSubalgebra.toNonUnitalSubring'

section

/-! `non_unital_subalgebra`s inherit structure from their `submodule` coercions. -/


-- TODO: generalize to `non_unital_subalgebra_class` or `submodule_class`
/- is there any reason we don't want this?
instance smul_mem_class.of_is_scalar_tower {S M N α : Type*} [set_like S α] [has_smul M N] [has_smul M α] [monoid N] [mul_action N α]
  [smul_mem_class S N α] [is_scalar_tower M N α] :
  smul_mem_class S M α :=
{ smul_mem := λ s m a ha, smul_one_smul N m a ▸ smul_mem_class.smul_mem _ ha }
-/
/- instance wtf_why {S A : Type*} [add_comm_monoid A]
  [set_like S A] [add_submonoid_class S A] (s : S) :
  add_comm_monoid s :=
add_submonoid_class.to_add_comm_monoid s -/
/- needs the `smul_mem_class.of_is_scalar_tower` above
instance foo {S R A : Type*} [comm_semiring R] [non_unital_semiring A] [module R A]
  [semiring R'] [has_smul R' R] [module R' A] [is_scalar_tower R' R A]
  [set_like S A] [non_unital_subsemiring_class S A] [smul_mem_class S R A] (s : S) :
  module R' s :=
infer_instance
-/
instance module' [Semiring R'] [SMul R' R] [Module R' A] [IsScalarTower R' R A] : Module R' S :=
  S.toSubmodule.module'
#align non_unital_subalgebra.module' NonUnitalSubalgebra.module'

instance : Module R S :=
  S.module'

instance is_scalar_tower' [Semiring R'] [SMul R' R] [Module R' A] [IsScalarTower R' R A] :
    IsScalarTower R' R S :=
  S.toSubmodule.isScalarTower
#align non_unital_subalgebra.is_scalar_tower' NonUnitalSubalgebra.is_scalar_tower'

instance [IsScalarTower R A A] : IsScalarTower R S S
    where smul_assoc r x y := Subtype.ext <| smul_assoc r (x : A) (y : A)

instance smul_comm_class' [Semiring R'] [SMul R' R] [Module R' A] [IsScalarTower R' R A]
    [SMulCommClass R' R A] : SMulCommClass R' R S
    where smul_comm r' r s := Subtype.ext <| smul_comm r' r (s : A)
#align non_unital_subalgebra.smul_comm_class' NonUnitalSubalgebra.smul_comm_class'

instance [SMulCommClass R A A] : SMulCommClass R S S
    where smul_comm r x y := Subtype.ext <| smul_comm r (x : A) (y : A)

end

instance noZeroSMulDivisors_bot [NoZeroSMulDivisors R A] : NoZeroSMulDivisors R S :=
  ⟨fun {c x} h =>
    have : c = 0 ∨ (x : A) = 0 := eq_zero_or_eq_zero_of_smul_eq_zero (congr_arg ((↑) : S → A) h)
    this.imp_right (@Subtype.ext_iff _ _ x 0).mpr⟩
#align non_unital_subalgebra.no_zero_smul_divisors_bot NonUnitalSubalgebra.noZeroSMulDivisors_bot

protected theorem coe_add (x y : S) : (↑(x + y) : A) = ↑x + ↑y :=
  rfl
#align non_unital_subalgebra.coe_add NonUnitalSubalgebra.coe_add

protected theorem coe_mul (x y : S) : (↑(x * y) : A) = ↑x * ↑y :=
  rfl
#align non_unital_subalgebra.coe_mul NonUnitalSubalgebra.coe_mul

protected theorem coe_zero : ((0 : S) : A) = 0 :=
  rfl
#align non_unital_subalgebra.coe_zero NonUnitalSubalgebra.coe_zero

protected theorem coe_neg {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    {S : NonUnitalSubalgebra R A} (x : S) : (↑(-x) : A) = -↑x :=
  rfl
#align non_unital_subalgebra.coe_neg NonUnitalSubalgebra.coe_neg

protected theorem coe_sub {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    {S : NonUnitalSubalgebra R A} (x y : S) : (↑(x - y) : A) = ↑x - ↑y :=
  rfl
#align non_unital_subalgebra.coe_sub NonUnitalSubalgebra.coe_sub

@[simp, norm_cast]
theorem coe_smul [Semiring R'] [SMul R' R] [Module R' A] [IsScalarTower R' R A] (r : R') (x : S) :
    (r • x : A) = r • (x : A) :=
  rfl
#align non_unital_subalgebra.coe_smul NonUnitalSubalgebra.coe_smul

protected theorem coe_eq_zero {x : S} : (x : A) = 0 ↔ x = 0 :=
  ZeroMemClass.coe_eq_zero
#align non_unital_subalgebra.coe_eq_zero NonUnitalSubalgebra.coe_eq_zero

-- todo: standardize on the names these morphisms
-- compare with submodule.subtype
@[simp]
theorem to_non_unital_subsemiring_subtype :
    NonUnitalSubsemiringClass.subtype S = NonUnitalSubalgebraClass.subtype (R := R) S :=
  rfl
#align non_unital_subalgebra.to_non_unital_subsemiring_subtype NonUnitalSubalgebra.to_non_unital_subsemiring_subtype

@[simp]
theorem to_subring_subtype {R A : Type _} [CommRing R] [Ring A] [Algebra R A]
    (S : NonUnitalSubalgebra R A) :
    NonUnitalSubringClass.subtype S = NonUnitalSubalgebraClass.subtype (R := R) S :=
  rfl
#align non_unital_subalgebra.to_subring_subtype NonUnitalSubalgebra.to_subring_subtype

/-- Linear equivalence between `S : submodule R A` and `S`. Though these types are equal,
we define it as a `linear_equiv` to avoid type equalities. -/
def toSubmoduleEquiv (S : NonUnitalSubalgebra R A) : S.toSubmodule ≃ₗ[R] S :=
  LinearEquiv.ofEq _ _ rfl
#align non_unital_subalgebra.to_submodule_equiv NonUnitalSubalgebra.toSubmoduleEquiv

/-- Transport a non_unital_subalgebra via an algebra homomorphism. -/
def map (f : F) (S : NonUnitalSubalgebra R A) : NonUnitalSubalgebra R B :=
  { S.toNonUnitalSubsemiring.map (f : A →ₙ+* B) with
    smul_mem' := fun r b hb => by
      rcases hb with ⟨a, ha, rfl⟩
      exact map_smul f r a ▸ Set.mem_image_of_mem f (S.smul_mem' r ha) }
#align non_unital_subalgebra.map NonUnitalSubalgebra.map

theorem map_mono {S₁ S₂ : NonUnitalSubalgebra R A} {f : F} :
    S₁ ≤ S₂ → (map f S₁ : NonUnitalSubalgebra R B) ≤ map f S₂ :=
  Set.image_subset f
#align non_unital_subalgebra.map_mono NonUnitalSubalgebra.map_mono

--- keep fixing from here `(f : F)`
theorem map_injective {f : F} (hf : Function.Injective f) :
    Function.Injective (map f : NonUnitalSubalgebra R A → NonUnitalSubalgebra R B) :=
  fun _S₁ _S₂ ih =>
  ext <| Set.ext_iff.1 <| Set.image_injective.2 hf <| Set.ext <| SetLike.ext_iff.mp ih
#align non_unital_subalgebra.map_injective NonUnitalSubalgebra.map_injective

@[simp]
theorem map_id (S : NonUnitalSubalgebra R A) : map (NonUnitalAlgHom.id R A) S = S :=
  SetLike.coe_injective <| Set.image_id _
#align non_unital_subalgebra.map_id NonUnitalSubalgebra.map_id

theorem map_map (S : NonUnitalSubalgebra R A) (g : B →ₙₐ[R] C) (f : A →ₙₐ[R] B) :
    (S.map f).map g = S.map (g.comp f) :=
  SetLike.coe_injective <| Set.image_image _ _ _
#align non_unital_subalgebra.map_map NonUnitalSubalgebra.map_map

theorem mem_map {S : NonUnitalSubalgebra R A} {f : F} {y : B} : y ∈ map f S ↔ ∃ x ∈ S, f x = y :=
  NonUnitalSubsemiring.mem_map
#align non_unital_subalgebra.mem_map NonUnitalSubalgebra.mem_map

-- we don't have the coercion for linear maps?
theorem map_toSubmodule {S : NonUnitalSubalgebra R A} {f : A →ₙₐ[R] B} :
    (map f S).toSubmodule = Submodule.map (f : A →ₗ[R] B) S.toSubmodule :=
  SetLike.coe_injective rfl
#align non_unital_subalgebra.map_to_submodule NonUnitalSubalgebra.map_toSubmodule

theorem map_toNonUnitalSubsemiring {S : NonUnitalSubalgebra R A} {f : F} :
    (map f S).toNonUnitalSubsemiring = S.toNonUnitalSubsemiring.map (f : A →ₙ+* B) :=
  SetLike.coe_injective rfl
#align non_unital_subalgebra.map_to_non_unital_subsemiring NonUnitalSubalgebra.map_toNonUnitalSubsemiring

@[simp]
theorem coe_map (S : NonUnitalSubalgebra R A) (f : F) : (map f S : Set B) = f '' S :=
  rfl
#align non_unital_subalgebra.coe_map NonUnitalSubalgebra.coe_map

/-- Preimage of a non_unital_subalgebra under an algebra homomorphism. -/
def comap (f : F) (S : NonUnitalSubalgebra R B) : NonUnitalSubalgebra R A :=
  { S.toNonUnitalSubsemiring.comap (f : A →ₙ+* B) with
    smul_mem' := fun r a (ha : f a ∈ S) =>
      show f (r • a) ∈ S from (map_smul f r a).symm ▸ S.smul_mem ha r }
#align non_unital_subalgebra.comap NonUnitalSubalgebra.comap

theorem map_le {S : NonUnitalSubalgebra R A} {f : F} {U : NonUnitalSubalgebra R B} :
    map f S ≤ U ↔ S ≤ comap f U :=
  Set.image_subset_iff
#align non_unital_subalgebra.map_le NonUnitalSubalgebra.map_le

theorem gc_map_comap (f : F) :
    GaloisConnection (map f : NonUnitalSubalgebra R A → NonUnitalSubalgebra R B) (comap f) :=
  fun _ _ => map_le
#align non_unital_subalgebra.gc_map_comap NonUnitalSubalgebra.gc_map_comap

@[simp]
theorem mem_comap (S : NonUnitalSubalgebra R B) (f : F) (x : A) : x ∈ comap f S ↔ f x ∈ S :=
  Iff.rfl
#align non_unital_subalgebra.mem_comap NonUnitalSubalgebra.mem_comap

@[simp, norm_cast]
theorem coe_comap (S : NonUnitalSubalgebra R B) (f : F) : (comap f S : Set A) = f ⁻¹' (S : Set B) :=
  rfl
#align non_unital_subalgebra.coe_comap NonUnitalSubalgebra.coe_comap

instance noZeroDivisors {R A : Type _} [CommSemiring R] [NonUnitalSemiring A] [NoZeroDivisors A]
    [Module R A] (S : NonUnitalSubalgebra R A) : NoZeroDivisors S :=
  NonUnitalSubsemiringClass.noZeroDivisors S
#align non_unital_subalgebra.no_zero_divisors NonUnitalSubalgebra.noZeroDivisors

end NonUnitalSubalgebra

namespace Submodule

variable {R A : Type _} [CommSemiring R] [Semiring A] [Algebra R A]

variable (p : Submodule R A)

/-- A submodule closed under multiplication is a non-unital subalgebra. -/
def toNonUnitalSubalgebra (p : Submodule R A) (h_mul : ∀ x y, x ∈ p → y ∈ p → x * y ∈ p) :
    NonUnitalSubalgebra R A :=
  { p with
    mul_mem' := h_mul _ _ }
#align submodule.to_non_unital_subalgebra Submodule.toNonUnitalSubalgebra

@[simp]
theorem mem_toNonUnitalSubalgebra {p : Submodule R A} {h_mul} {x} :
    x ∈ p.toNonUnitalSubalgebra h_mul ↔ x ∈ p :=
  Iff.rfl
#align submodule.mem_to_non_unital_subalgebra Submodule.mem_toNonUnitalSubalgebra

@[simp]
theorem coe_toNonUnitalSubalgebra (p : Submodule R A) (h_mul) :
    (p.toNonUnitalSubalgebra h_mul : Set A) = p :=
  rfl
#align submodule.coe_to_non_unital_subalgebra Submodule.coe_toNonUnitalSubalgebra

theorem toNonUnitalSubalgebra_mk (p : Submodule R A) hmul :
    p.toNonUnitalSubalgebra hmul =
      NonUnitalSubalgebra.mk ⟨⟨⟨p, p.add_mem⟩, p.zero_mem⟩, hmul _ _⟩ p.smul_mem' :=
  rfl
#align submodule.to_non_unital_subalgebra_mk Submodule.toNonUnitalSubalgebra_mk

@[simp]
theorem toNonUnitalSubalgebra_toSubmodule (p : Submodule R A) (h_mul) :
    (p.toNonUnitalSubalgebra h_mul).toSubmodule = p :=
  SetLike.coe_injective rfl
#align submodule.to_non_unital_subalgebra_to_submodule Submodule.toNonUnitalSubalgebra_toSubmodule

@[simp]
theorem _root_.NonUnitalSubalgebra.toSubmodule_toNonUnitalSubalgebra (S : NonUnitalSubalgebra R A) :
    (S.toSubmodule.toNonUnitalSubalgebra fun _ _ => S.mul_mem) = S :=
  SetLike.coe_injective rfl
#align non_unital_subalgebra.to_submodule_to_non_unital_subalgebra NonUnitalSubalgebra.toSubmodule_toNonUnitalSubalgebra

end Submodule

namespace NonUnitalAlgHom

variable {F : Type v'} {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [NonUnitalSemiring A] [Module R A] [NonUnitalSemiring B] [Module R B]

variable [NonUnitalSemiring C] [Module R C] [NonUnitalAlgHomClass F R A B]

/-- Range of an `non_unital_alg_hom` as a non_unital_subalgebra. -/
protected def range (φ : F) : NonUnitalSubalgebra R B where
  toNonUnitalSubsemiring := NonUnitalRingHom.srange (φ : A →ₙ+* B)
  smul_mem' := fun r a => by rintro ⟨a, rfl⟩; exact ⟨r • a, map_smul φ r a⟩
#align non_unital_alg_hom.range NonUnitalAlgHom.range

@[simp]
theorem mem_range (φ : F) {y : B} :
    y ∈ (NonUnitalAlgHom.range φ : NonUnitalSubalgebra R B) ↔ ∃ x : A, φ x = y :=
  NonUnitalRingHom.mem_srange
#align non_unital_alg_hom.mem_range NonUnitalAlgHom.mem_range

theorem mem_range_self (φ : F) (x : A) :
    φ x ∈ (NonUnitalAlgHom.range φ : NonUnitalSubalgebra R B) :=
  (NonUnitalAlgHom.mem_range φ).2 ⟨x, rfl⟩
#align non_unital_alg_hom.mem_range_self NonUnitalAlgHom.mem_range_self

@[simp]
theorem coe_range (φ : F) :
    ((NonUnitalAlgHom.range φ : NonUnitalSubalgebra R B) : Set B) = Set.range (φ : A → B) := by
  ext
  rw [SetLike.mem_coe, mem_range]
  rfl
#align non_unital_alg_hom.coe_range NonUnitalAlgHom.coe_range

theorem range_comp (f : A →ₙₐ[R] B) (g : B →ₙₐ[R] C) :
    NonUnitalAlgHom.range (g.comp f) = (NonUnitalAlgHom.range f).map g :=
  SetLike.coe_injective (Set.range_comp g f)
#align non_unital_alg_hom.range_comp NonUnitalAlgHom.range_comp

theorem range_comp_le_range (f : A →ₙₐ[R] B) (g : B →ₙₐ[R] C) :
    NonUnitalAlgHom.range (g.comp f) ≤ NonUnitalAlgHom.range g :=
  SetLike.coe_mono (Set.range_comp_subset_range f g)
#align non_unital_alg_hom.range_comp_le_range NonUnitalAlgHom.range_comp_le_range

/-- Restrict the codomain of an algebra homomorphism. -/
def codRestrict (f : F) (S : NonUnitalSubalgebra R B) (hf : ∀ x, f x ∈ S) : A →ₙₐ[R] S :=
  { NonUnitalRingHom.codRestrict (f : A →ₙ+* B) S.toNonUnitalSubsemiring hf with
    map_smul' := fun r a => Subtype.ext <| map_smul f r a }
#align non_unital_alg_hom.cod_restrict NonUnitalAlgHom.codRestrict

@[simp]
theorem subtype_comp_codRestrict (f : F) (S : NonUnitalSubalgebra R B) (hf : ∀ x : A, f x ∈ S) :
    (NonUnitalSubalgebraClass.subtype S).comp (NonUnitalAlgHom.codRestrict f S hf) = f :=
  NonUnitalAlgHom.ext fun _ => rfl
#align non_unital_alg_hom.subtype_comp_cod_restrict NonUnitalAlgHom.subtype_comp_codRestrict

@[simp]
theorem coe_codRestrict (f : F) (S : NonUnitalSubalgebra R B) (hf : ∀ x, f x ∈ S) (x : A) :
    ↑(NonUnitalAlgHom.codRestrict f S hf x) = f x :=
  rfl
#align non_unital_alg_hom.coe_cod_restrict NonUnitalAlgHom.coe_codRestrict

theorem injective_codRestrict (f : F) (S : NonUnitalSubalgebra R B) (hf : ∀ x : A, f x ∈ S) :
    Function.Injective (NonUnitalAlgHom.codRestrict f S hf) ↔ Function.Injective f :=
  ⟨fun H _x _y hxy => H <| Subtype.eq hxy, fun H _x _y hxy => H (congr_arg Subtype.val hxy : _)⟩
#align non_unital_alg_hom.injective_cod_restrict NonUnitalAlgHom.injective_codRestrict

/-- Restrict the codomain of a alg_hom `f` to `f.range`.

This is the bundled version of `set.range_factorization`. -/
@[reducible]
def rangeRestrict (f : F) : A →ₙₐ[R] (NonUnitalAlgHom.range f : NonUnitalSubalgebra R B) :=
  NonUnitalAlgHom.codRestrict f (NonUnitalAlgHom.range f) (NonUnitalAlgHom.mem_range_self f)
#align non_unital_alg_hom.range_restrict NonUnitalAlgHom.rangeRestrict

/-- The equalizer of two R-algebra homomorphisms -/
def equalizer (ϕ ψ : F) : NonUnitalSubalgebra R A
    where
  carrier := {a | (ϕ a : B) = ψ a}
  zero_mem' := by rw [Set.mem_setOf_eq, map_zero, map_zero]
  add_mem' {x y} (hx : ϕ x = ψ x) (hy : ϕ y = ψ y) := by
    rw [Set.mem_setOf_eq, map_add, map_add, hx, hy]
  mul_mem' {x y} (hx : ϕ x = ψ x) (hy : ϕ y = ψ y) := by
    rw [Set.mem_setOf_eq, map_mul, map_mul, hx, hy]
  smul_mem' r x (hx : ϕ x = ψ x) := by rw [Set.mem_setOf_eq, map_smul, map_smul, hx]
#align non_unital_alg_hom.equalizer NonUnitalAlgHom.equalizer

@[simp]
theorem mem_equalizer (φ ψ : F) (x : A) :
    x ∈ @NonUnitalAlgHom.equalizer F R A B _ _ _ _ _ _ φ ψ ↔ φ x = ψ x :=
  Iff.rfl
#align non_unital_alg_hom.mem_equalizer NonUnitalAlgHom.mem_equalizer

/-- The range of a morphism of algebras is a fintype, if the domain is a fintype.

Note that this instance can cause a diamond with `subtype.fintype` if `B` is also a fintype. -/
instance fintypeRange [Fintype A] [DecidableEq B] (φ : F) :
    Fintype (@NonUnitalAlgHom.range F R A B _ _ _ _ _ _ φ) :=
  Set.fintypeRange φ
#align non_unital_alg_hom.fintype_range NonUnitalAlgHom.fintypeRange

end NonUnitalAlgHom

/- This needs a refactor of `alg_equiv` to replace `commutes` with `map_smul`.
namespace alg_equiv

variables {R : Type u} {A : Type v} {B : Type w}
variables [comm_semiring R] [semiring A] [semiring B] [algebra R A] [algebra R B]

/-- Restrict an algebra homomorphism with a left inverse to an algebra isomorphism to its range.

This is a computable alternative to `alg_equiv.of_injective`. -/
def of_left_inverse
  {g : B → A} {f : A →ₙₐ[R] B} (h : function.left_inverse g f) :
  A ≃ₐ[R] f.range :=
{ to_fun := f.range_restrict,
  inv_fun := g ∘ f.range.val,
  left_inv := h,
  right_inv := λ x, subtype.ext $
    let ⟨x', hx'⟩ := f.mem_range.mp x.prop in
    show f (g x) = x, by rw [←hx', h x'],
  ..f.range_restrict }

@[simp] lemma of_left_inverse_apply
  {g : B → A} {f : A →ₙₐ[R] B} (h : function.left_inverse g f) (x : A) :
  ↑(of_left_inverse h x) = f x := rfl

@[simp] lemma of_left_inverse_symm_apply
  {g : B → A} {f : A →ₙₐ[R] B} (h : function.left_inverse g f) (x : f.range) :
  (of_left_inverse h).symm x = g x := rfl

/-- Restrict an injective algebra homomorphism to an algebra isomorphism -/
noncomputable def of_injective (f : A →ₙₐ[R] B) (hf : function.injective f) :
  A ≃ₐ[R] f.range :=
of_left_inverse (classical.some_spec hf.has_left_inverse)

@[simp] lemma of_injective_apply (f : A →ₙₐ[R] B) (hf : function.injective f) (x : A) :
  ↑(of_injective f hf x) = f x := rfl

/-- Restrict an algebra homomorphism between fields to an algebra isomorphism -/
noncomputable def of_injective_field {E F : Type*} [division_ring E] [semiring F]
  [nontrivial F] [algebra R E] [algebra R F] (f : E →ₙₐ[R] F) : E ≃ₐ[R] f.range :=
of_injective f f.to_ring_hom.injective

/-- Given an equivalence `e : A ≃ₐ[R] B` of `R`-algebras and a non_unital_subalgebra `S` of `A`,
`non_unital_subalgebra_map` is the induced equivalence between `S` and `S.map e` -/
@[simps] def non_unital_subalgebra_map (e : A ≃ₐ[R] B) (S : non_unital_subalgebra R A) :
  S ≃ₐ[R] (S.map e.to_alg_hom) :=
{ commutes' := λ r, by { ext, simp },
  ..e.to_ring_equiv.non_unital_subsemiring_map S.to_non_unital_subsemiring }

end alg_equiv
-/
namespace NonUnitalAlgebra

variable {F : Type _} (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R]

variable [NonUnitalSemiring A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]

variable [NonUnitalSemiring B] [Module R B] [IsScalarTower R B B] [SMulCommClass R B B]

variable [NonUnitalAlgHomClass F R A B]

/-- The minimal non-unital subalgebra that includes `s`. -/
def adjoin (s : Set A) : NonUnitalSubalgebra R A :=
  { Submodule.span R (NonUnitalSubsemiring.closure s : Set A) with
    mul_mem' :=
      @fun a b (ha : a ∈ Submodule.span R (NonUnitalSubsemiring.closure s : Set A))
        (hb : b ∈ Submodule.span R (NonUnitalSubsemiring.closure s : Set A)) =>
      show a * b ∈ Submodule.span R (NonUnitalSubsemiring.closure s : Set A)
        by
        refine' Submodule.span_induction ha _ _ _ _
        · refine' Submodule.span_induction hb _ _ _ _
          ·
            exact
              fun x (hx : x ∈ NonUnitalSubsemiring.closure s) y
                (hy : y ∈ NonUnitalSubsemiring.closure s) =>
              Submodule.subset_span (mul_mem hy hx)
          · exact fun x _hx => (MulZeroClass.mul_zero x).symm ▸ Submodule.zero_mem _
          · exact fun x y hx hy z hz => (mul_add z x y).symm ▸ add_mem (hx z hz) (hy z hz)
          · exact fun r x hx y hy => (mul_smul_comm r y x).symm ▸ SMulMemClass.smul_mem r (hx y hy)
        · exact (MulZeroClass.zero_mul b).symm ▸ Submodule.zero_mem _
        · exact fun x y => (add_mul x y b).symm ▸ add_mem
        · exact fun r x hx => (smul_mul_assoc r x b).symm ▸ SMulMemClass.smul_mem r hx }
#align non_unital_algebra.adjoin NonUnitalAlgebra.adjoin

theorem adjoin_toSubmodule (s : Set A) :
    (adjoin R s).toSubmodule = Submodule.span R (NonUnitalSubsemiring.closure s : Set A) :=
  rfl
#align non_unital_algebra.adjoin_to_submodule NonUnitalAlgebra.adjoin_toSubmodule

theorem subset_adjoin {s : Set A} : s ⊆ adjoin R s :=
  NonUnitalSubsemiring.subset_closure.trans Submodule.subset_span
#align non_unital_algebra.subset_adjoin NonUnitalAlgebra.subset_adjoin

theorem self_mem_adjoin_singleton (x : A) : x ∈ adjoin R ({x} : Set A) :=
  NonUnitalAlgebra.subset_adjoin R (Set.mem_singleton x)
#align non_unital_algebra.self_mem_adjoin_singleton NonUnitalAlgebra.self_mem_adjoin_singleton

variable {R}

/-- If some predicate holds for all `x ∈ (s : set A)` and this predicate is closed under the
`algebra_map`, addition, multiplication and star operations, then it holds for `a ∈ adjoin R s`. -/
theorem adjoin_induction {s : Set A} {p : A → Prop} {a : A} (h : a ∈ adjoin R s)
    (Hs : ∀ x : A, x ∈ s → p x) (Hadd : ∀ x y : A, p x → p y → p (x + y)) (H0 : p 0)
    (Hmul : ∀ x y : A, p x → p y → p (x * y)) (Hsmul : ∀ (r : R) {x : A}, p x → p (r • x)) : p a :=
  Submodule.span_induction h
    (fun _a ha => NonUnitalSubsemiring.closure_induction ha Hs H0 Hadd Hmul) H0 Hadd Hsmul
#align non_unital_algebra.adjoin_induction NonUnitalAlgebra.adjoin_induction

-- needs to go with submodules
theorem _root_.Submodule.span_induction₂ {R M : Type _} [Semiring R] [AddCommMonoid M] [Module R M]
    {a b : M} {s : Set M} {p : M → M → Prop} (ha : a ∈ Submodule.span R s)
    (hb : b ∈ Submodule.span R s) (Hs : ∀ x : M, x ∈ s → ∀ {y : M}, y ∈ s → p x y)
    (H0_left : ∀ y : M, p 0 y) (H0_right : ∀ x : M, p x 0)
    (Hadd_left : ∀ x₁ x₂ y : M, p x₁ y → p x₂ y → p (x₁ + x₂) y)
    (Hadd_right : ∀ x y₁ y₂ : M, p x y₁ → p x y₂ → p x (y₁ + y₂))
    (Hsmul_left : ∀ (r : R) (x y : M), p x y → p (r • x) y)
    (Hsmul_right : ∀ (r : R) (x y : M), p x y → p x (r • y)) : p a b :=
  Submodule.span_induction ha
    (fun x hx =>
      Submodule.span_induction hb (fun _y => Hs x hx) (H0_right x) (Hadd_right x) fun r =>
        Hsmul_right r x)
    (H0_left b) (fun x₁ x₂ => Hadd_left x₁ x₂ b) fun r x => Hsmul_left r x b
#align submodule.span_induction₂ Submodule.span_induction₂

theorem adjoin_induction₂ {s : Set A} {p : A → A → Prop} {a b : A} (ha : a ∈ adjoin R s)
    (hb : b ∈ adjoin R s) (Hs : ∀ x : A, x ∈ s → ∀ y : A, y ∈ s → p x y) (H0_left : ∀ y : A, p 0 y)
    (H0_right : ∀ x : A, p x 0) (Hadd_left : ∀ x₁ x₂ y : A, p x₁ y → p x₂ y → p (x₁ + x₂) y)
    (Hadd_right : ∀ x y₁ y₂ : A, p x y₁ → p x y₂ → p x (y₁ + y₂))
    (Hmul_left : ∀ x₁ x₂ y : A, p x₁ y → p x₂ y → p (x₁ * x₂) y)
    (Hmul_right : ∀ x y₁ y₂ : A, p x y₁ → p x y₂ → p x (y₁ * y₂))
    (Hsmul_left : ∀ (r : R) (x y : A), p x y → p (r • x) y)
    (Hsmul_right : ∀ (r : R) (x y : A), p x y → p x (r • y)) : p a b :=
  Submodule.span_induction₂ ha hb
    (fun _x hx _y hy =>
      NonUnitalSubsemiring.closure_induction₂ hx hy Hs H0_left H0_right Hadd_left Hadd_right
        Hmul_left Hmul_right)
    H0_left H0_right Hadd_left Hadd_right Hsmul_left Hsmul_right
#align non_unital_algebra.adjoin_induction₂ NonUnitalAlgebra.adjoin_induction₂

/-
/-- The difference with `star_subalgebra.adjoin_induction` is that this acts on the subtype. -/
lemma adjoin_induction' {s : set A} {p : adjoin R s → Prop} (a : adjoin R s)
  (Hs : ∀ x (h : x ∈ s), p ⟨x, subset_adjoin R s h⟩)
  (Halg : ∀ r, p (algebra_map R _ r)) (Hadd : ∀ x y, p x → p y → p (x + y))
  (Hmul : ∀ x y, p x → p y → p (x * y)) (Hstar : ∀ x, p x → p (star x)) : p a :=
subtype.rec_on a $ λ b hb,
begin
  refine exists.elim _ (λ (hb : b ∈ adjoin R s) (hc : p ⟨b, hb⟩), hc),
  apply adjoin_induction hb,
  exacts [λ x hx, ⟨subset_adjoin R s hx, Hs x hx⟩,
    λ r, ⟨star_subalgebra.algebra_map_mem _ r, Halg r⟩,
    (λ x y hx hy, exists.elim hx $ λ hx' hx,
      exists.elim hy $ λ hy' hy, ⟨add_mem hx' hy', Hadd _ _ hx hy⟩),
    (λ x y hx hy, exists.elim hx $ λ hx' hx,
      exists.elim hy $ λ hy' hy, ⟨mul_mem hx' hy', Hmul _ _ hx hy⟩),
    λ x hx, exists.elim hx (λ hx' hx, ⟨star_mem hx', Hstar _ hx⟩)]
end
-/
protected theorem gc : GaloisConnection (adjoin R : Set A → NonUnitalSubalgebra R A) (↑) :=
  fun s S =>
  ⟨fun H => (NonUnitalSubsemiring.subset_closure.trans Submodule.subset_span).trans H,
    fun H => show Submodule.span R _ ≤ S.toSubmodule from Submodule.span_le.mpr <|
      show NonUnitalSubsemiring.closure s ≤ S.toNonUnitalSubsemiring from
        NonUnitalSubsemiring.closure_le.2 H⟩
#align non_unital_algebra.gc NonUnitalAlgebra.gc

/-- Galois insertion between `adjoin` and `coe`. -/
protected def gi : GaloisInsertion (adjoin R : Set A → NonUnitalSubalgebra R A) (↑)
    where
  choice s hs := (adjoin R s).copy s <| le_antisymm (NonUnitalAlgebra.gc.le_u_l s) hs
  gc := NonUnitalAlgebra.gc
  le_l_u S := (NonUnitalAlgebra.gc (S : Set A) (adjoin R S)).1 <| le_rfl
  choice_eq _ _ := NonUnitalSubalgebra.copy_eq _ _ _
#align non_unital_algebra.gi NonUnitalAlgebra.gi

instance : CompleteLattice (NonUnitalSubalgebra R A) :=
  GaloisInsertion.liftCompleteLattice NonUnitalAlgebra.gi

theorem adjoin_le {S : NonUnitalSubalgebra R A} {s : Set A} (hs : s ⊆ S) : adjoin R s ≤ S :=
  NonUnitalAlgebra.gc.l_le hs
#align non_unital_algebra.adjoin_le NonUnitalAlgebra.adjoin_le

theorem adjoin_le_iff {S : NonUnitalSubalgebra R A} {s : Set A} : adjoin R s ≤ S ↔ s ⊆ S :=
  NonUnitalAlgebra.gc _ _
#align non_unital_algebra.adjoin_le_iff NonUnitalAlgebra.adjoin_le_iff

theorem adjoin_union (s t : Set A) : adjoin R (s ∪ t) = adjoin R s ⊔ adjoin R t :=
  (NonUnitalAlgebra.gc : GaloisConnection _ ((↑) : NonUnitalSubalgebra R A → Set A)).l_sup
#align non_unital_algebra.adjoin_union NonUnitalAlgebra.adjoin_union

variable (R A)

@[simp]
theorem adjoin_empty : adjoin R (∅ : Set A) = ⊥ :=
  show adjoin R ⊥ = ⊥ by apply GaloisConnection.l_bot; exact NonUnitalAlgebra.gc
#align non_unital_algebra.adjoin_empty NonUnitalAlgebra.adjoin_empty

@[simp]
theorem adjoin_univ : adjoin R (Set.univ : Set A) = ⊤ :=
  eq_top_iff.2 fun _x hx => subset_adjoin R hx
#align non_unital_algebra.adjoin_univ NonUnitalAlgebra.adjoin_univ

variable {R A}

@[simp]
theorem coe_top : (↑(⊤ : NonUnitalSubalgebra R A) : Set A) = Set.univ :=
  rfl
#align non_unital_algebra.coe_top NonUnitalAlgebra.coe_top

@[simp]
theorem mem_top {x : A} : x ∈ (⊤ : NonUnitalSubalgebra R A) :=
  Set.mem_univ x
#align non_unital_algebra.mem_top NonUnitalAlgebra.mem_top

@[simp]
theorem top_toSubmodule : (⊤ : NonUnitalSubalgebra R A).toSubmodule = ⊤ :=
  rfl
#align non_unital_algebra.top_to_submodule NonUnitalAlgebra.top_toSubmodule

@[simp]
theorem top_toNonUnitalSubsemiring : (⊤ : NonUnitalSubalgebra R A).toNonUnitalSubsemiring = ⊤ :=
  rfl
#align non_unital_algebra.top_to_non_unital_subsemiring NonUnitalAlgebra.top_toNonUnitalSubsemiring

@[simp]
theorem top_to_subring {R A : Type _} [CommRing R] [NonUnitalRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] :
    (⊤ : NonUnitalSubalgebra R A).toNonUnitalSubring = ⊤ :=
  rfl
#align non_unital_algebra.top_to_subring NonUnitalAlgebra.top_to_subring

@[simp]
theorem toSubmodule_eq_top {S : NonUnitalSubalgebra R A} : S.toSubmodule = ⊤ ↔ S = ⊤ :=
  NonUnitalSubalgebra.toSubmodule'.injective.eq_iff' top_toSubmodule
#align non_unital_algebra.to_submodule_eq_top NonUnitalAlgebra.toSubmodule_eq_top

@[simp]
theorem toNonUnitalSubsemiring_eq_top {S : NonUnitalSubalgebra R A} :
    S.toNonUnitalSubsemiring = ⊤ ↔ S = ⊤ :=
  NonUnitalSubalgebra.toNonUnitalSubsemiring_injective.eq_iff' top_toNonUnitalSubsemiring
#align non_unital_algebra.to_non_unital_subsemiring_eq_top NonUnitalAlgebra.toNonUnitalSubsemiring_eq_top

@[simp]
theorem to_subring_eq_top {R A : Type _} [CommRing R] [Ring A] [Algebra R A]
    {S : NonUnitalSubalgebra R A} : S.toNonUnitalSubring = ⊤ ↔ S = ⊤ :=
  NonUnitalSubalgebra.toNonUnitalSubring_injective.eq_iff' top_to_subring
#align non_unital_algebra.to_subring_eq_top NonUnitalAlgebra.to_subring_eq_top

theorem mem_sup_left {S T : NonUnitalSubalgebra R A} : ∀ {x : A}, x ∈ S → x ∈ S ⊔ T := by
  rw [←SetLike.le_def]
  exact le_sup_left
#align non_unital_algebra.mem_sup_left NonUnitalAlgebra.mem_sup_left

theorem mem_sup_right {S T : NonUnitalSubalgebra R A} : ∀ {x : A}, x ∈ T → x ∈ S ⊔ T := by
  rw [←SetLike.le_def]
  exact le_sup_right
#align non_unital_algebra.mem_sup_right NonUnitalAlgebra.mem_sup_right

theorem mul_mem_sup {S T : NonUnitalSubalgebra R A} {x y : A} (hx : x ∈ S) (hy : y ∈ T) :
    x * y ∈ S ⊔ T :=
  (S ⊔ T).mul_mem (mem_sup_left hx) (mem_sup_right hy)
#align non_unital_algebra.mul_mem_sup NonUnitalAlgebra.mul_mem_sup

theorem map_sup (f : F) (S T : NonUnitalSubalgebra R A) :
    ((S ⊔ T).map f : NonUnitalSubalgebra R B) = S.map f ⊔ T.map f :=
  (@NonUnitalSubalgebra.gc_map_comap F R A B _ _ _ _ _ _ f).l_sup
#align non_unital_algebra.map_sup NonUnitalAlgebra.map_sup

@[simp, norm_cast]
theorem coe_inf (S T : NonUnitalSubalgebra R A) : (↑(S ⊓ T) : Set A) = (S : Set A) ∩ T :=
  rfl
#align non_unital_algebra.coe_inf NonUnitalAlgebra.coe_inf

@[simp]
theorem mem_inf {S T : NonUnitalSubalgebra R A} {x : A} : x ∈ S ⊓ T ↔ x ∈ S ∧ x ∈ T :=
  Iff.rfl
#align non_unital_algebra.mem_inf NonUnitalAlgebra.mem_inf

@[simp]
theorem inf_toSubmodule (S T : NonUnitalSubalgebra R A) :
    (S ⊓ T).toSubmodule = S.toSubmodule ⊓ T.toSubmodule :=
  rfl
#align non_unital_algebra.inf_to_submodule NonUnitalAlgebra.inf_toSubmodule

@[simp]
theorem inf_toNonUnitalSubsemiring (S T : NonUnitalSubalgebra R A) :
    (S ⊓ T).toNonUnitalSubsemiring = S.toNonUnitalSubsemiring ⊓ T.toNonUnitalSubsemiring :=
  rfl
#align non_unital_algebra.inf_to_non_unital_subsemiring NonUnitalAlgebra.inf_toNonUnitalSubsemiring

@[simp, norm_cast]
theorem coe_sInf (S : Set (NonUnitalSubalgebra R A)) : (↑(sInf S) : Set A) = ⋂ s ∈ S, ↑s :=
  sInf_image
#align non_unital_algebra.coe_Inf NonUnitalAlgebra.coe_sInf

theorem mem_sInf {S : Set (NonUnitalSubalgebra R A)} {x : A} : x ∈ sInf S ↔ ∀ p ∈ S, x ∈ p := by
  simp only [← SetLike.mem_coe, coe_sInf, Set.mem_iInter₂]
#align non_unital_algebra.mem_Inf NonUnitalAlgebra.mem_sInf

@[simp]
theorem sInf_toSubmodule (S : Set (NonUnitalSubalgebra R A)) :
    (sInf S).toSubmodule = sInf (NonUnitalSubalgebra.toSubmodule '' S) :=
  SetLike.coe_injective <| by simp
#align non_unital_algebra.Inf_to_submodule NonUnitalAlgebra.sInf_toSubmodule

@[simp]
theorem sInf_toNonUnitalSubsemiring (S : Set (NonUnitalSubalgebra R A)) :
    (sInf S).toNonUnitalSubsemiring = sInf (NonUnitalSubalgebra.toNonUnitalSubsemiring '' S) :=
  SetLike.coe_injective <| by simp
#align non_unital_algebra.Inf_to_non_unital_subsemiring NonUnitalAlgebra.sInf_toNonUnitalSubsemiring

@[simp, norm_cast]
theorem coe_iInf {ι : Sort _} {S : ι → NonUnitalSubalgebra R A} :
    (↑(⨅ i, S i) : Set A) = ⋂ i, S i := by simp [iInf]
#align non_unital_algebra.coe_infi NonUnitalAlgebra.coe_iInf

theorem mem_iInf {ι : Sort _} {S : ι → NonUnitalSubalgebra R A} {x : A} :
    (x ∈ ⨅ i, S i) ↔ ∀ i, x ∈ S i := by simp only [iInf, mem_sInf, Set.forall_range_iff]
#align non_unital_algebra.mem_infi NonUnitalAlgebra.mem_iInf

@[simp]
theorem iInf_toSubmodule {ι : Sort _} (S : ι → NonUnitalSubalgebra R A) :
    (⨅ i, S i).toSubmodule = ⨅ i, (S i).toSubmodule :=
  SetLike.coe_injective <| by simp
#align non_unital_algebra.infi_to_submodule NonUnitalAlgebra.iInf_toSubmodule

instance : Inhabited (NonUnitalSubalgebra R A) :=
  ⟨⊥⟩

theorem mem_bot {x : A} : x ∈ (⊥ : NonUnitalSubalgebra R A) ↔ x = 0 :=
  show x ∈ Submodule.span R (NonUnitalSubsemiring.closure (∅ : Set A) : Set A) ↔ x = 0 by
    rw [NonUnitalSubsemiring.closure_empty, NonUnitalSubsemiring.coe_bot,
      Submodule.span_zero_singleton, Submodule.mem_bot]
#align non_unital_algebra.mem_bot NonUnitalAlgebra.mem_bot

theorem toSubmodule_bot : (⊥ : NonUnitalSubalgebra R A).toSubmodule = ⊥ := by
  ext
  simp only [mem_bot, NonUnitalSubalgebra.mem_toSubmodule, Submodule.mem_bot]
#align non_unital_algebra.to_submodule_bot NonUnitalAlgebra.toSubmodule_bot

@[simp]
theorem coe_bot : ((⊥ : NonUnitalSubalgebra R A) : Set A) = {0} := by
  simp [Set.ext_iff, NonUnitalAlgebra.mem_bot]
#align non_unital_algebra.coe_bot NonUnitalAlgebra.coe_bot

theorem eq_top_iff {S : NonUnitalSubalgebra R A} : S = ⊤ ↔ ∀ x : A, x ∈ S :=
  ⟨fun h x => by rw [h]; exact mem_top, fun h => by ext x; exact ⟨fun _ => mem_top, fun _ => h x⟩⟩
#align non_unital_algebra.eq_top_iff NonUnitalAlgebra.eq_top_iff

theorem range_top_iff_surjective (f : A →ₙₐ[R] B) :
    NonUnitalAlgHom.range f = (⊤ : NonUnitalSubalgebra R B) ↔ Function.Surjective f :=
  NonUnitalAlgebra.eq_top_iff
#align non_unital_algebra.range_top_iff_surjective NonUnitalAlgebra.range_top_iff_surjective

@[simp]
theorem range_id : NonUnitalAlgHom.range (NonUnitalAlgHom.id R A) = ⊤ :=
  SetLike.coe_injective Set.range_id
#align non_unital_algebra.range_id NonUnitalAlgebra.range_id

@[simp]
theorem map_top (f : A →ₙₐ[R] B) : (⊤ : NonUnitalSubalgebra R A).map f = NonUnitalAlgHom.range f :=
  SetLike.coe_injective Set.image_univ
#align non_unital_algebra.map_top NonUnitalAlgebra.map_top

@[simp]
theorem map_bot (f : A →ₙₐ[R] B) : (⊥ : NonUnitalSubalgebra R A).map f = ⊥ :=
  SetLike.coe_injective <| by simp [NonUnitalAlgebra.coe_bot, NonUnitalSubalgebra.coe_map]
#align non_unital_algebra.map_bot NonUnitalAlgebra.map_bot

@[simp]
theorem comap_top (f : A →ₙₐ[R] B) : (⊤ : NonUnitalSubalgebra R B).comap f = ⊤ :=
  eq_top_iff.2 fun _ => mem_top
#align non_unital_algebra.comap_top NonUnitalAlgebra.comap_top

/-- `non_unital_alg_hom` to `⊤ : non_unital_subalgebra R A`. -/
def toTop : A →ₙₐ[R] (⊤ : NonUnitalSubalgebra R A) :=
  NonUnitalAlgHom.codRestrict (NonUnitalAlgHom.id R A) ⊤ fun _ => mem_top
#align non_unital_algebra.to_top NonUnitalAlgebra.toTop

end NonUnitalAlgebra

namespace NonUnitalSubalgebra

open NonUnitalAlgebra

variable {F : Type _} {R : Type u} {A : Type v} {B : Type w}

variable [CommSemiring R]

variable [NonUnitalSemiring A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]

variable [NonUnitalSemiring B] [Module R B] [IsScalarTower R B B] [SMulCommClass R B B]

variable [NonUnitalAlgHomClass F R A B] (S : NonUnitalSubalgebra R A)

/- can't have this until we refactor `alg_equiv`.
/-- The top non_unital_subalgebra is isomorphic to the algebra.

This is the algebra version of `submodule.top_equiv`. -/
@[simps] def top_equiv : (⊤ : non_unital_subalgebra R A) ≃ₐ[R] A :=
alg_equiv.of_alg_hom (non_unital_subalgebra_class.subtype ⊤) to_top rfl $
  non_unital_alg_hom.ext $ λ _, subtype.ext rfl
  -/
instance subsingleton_of_subsingleton [Subsingleton A] : Subsingleton (NonUnitalSubalgebra R A) :=
  ⟨fun B C => ext fun x => by simp only [Subsingleton.elim x 0, zero_mem B, zero_mem C]⟩
#align non_unital_subalgebra.subsingleton_of_subsingleton NonUnitalSubalgebra.subsingleton_of_subsingleton

instance _root_.NonUnitalAlgHom.subsingleton [Subsingleton (NonUnitalSubalgebra R A)] :
    Subsingleton (A →ₙₐ[R] B) :=
  ⟨fun f g =>
    NonUnitalAlgHom.ext fun a =>
      have : a ∈ (⊥ : NonUnitalSubalgebra R A) :=
        Subsingleton.elim (⊤ : NonUnitalSubalgebra R A) ⊥ ▸ mem_top
      (mem_bot.mp this).symm ▸ (map_zero f).trans (map_zero g).symm⟩
#align non_unital_alg_hom.subsingleton NonUnitalAlgHom.subsingleton

/- need to refactor `alg_equiv` first
instance _root_.non_unital_alg_equiv.subsingleton_left [subsingleton (non_unital_subalgebra R A)] :
  subsingleton (A ≃ₐ[R] B) :=
⟨λ f g, alg_equiv.ext (λ x, alg_hom.ext_iff.mp (subsingleton.elim f.to_alg_hom g.to_alg_hom) x)⟩

instance _root_.alg_equiv.subsingleton_right [subsingleton (non_unital_subalgebra R B)] :
  subsingleton (A ≃ₐ[R] B) :=
⟨λ f g, by rw [← f.symm_symm, subsingleton.elim f.symm g.symm, g.symm_symm]⟩
-/
theorem range_val : NonUnitalAlgHom.range (NonUnitalSubalgebraClass.subtype S) = S :=
  ext <| Set.ext_iff.1 <| (NonUnitalSubalgebraClass.subtype S).coe_range.trans Subtype.range_val
#align non_unital_subalgebra.range_val NonUnitalSubalgebra.range_val

/-- The map `S → T` when `S` is a non_unital_subalgebra contained in the non_unital_subalgebra `T`.

This is the non_unital_subalgebra version of `submodule.of_le`, or `subring.inclusion`  -/
def inclusion {S T : NonUnitalSubalgebra R A} (h : S ≤ T) : S →ₙₐ[R] T
    where
  toFun := Set.inclusion h
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_smul' _ _ := rfl
#align non_unital_subalgebra.inclusion NonUnitalSubalgebra.inclusion

theorem inclusion_injective {S T : NonUnitalSubalgebra R A} (h : S ≤ T) :
    Function.Injective (inclusion h) := fun _ _ => Subtype.ext ∘ Subtype.mk.inj
#align non_unital_subalgebra.inclusion_injective NonUnitalSubalgebra.inclusion_injective

@[simp]
theorem inclusion_self {S : NonUnitalSubalgebra R A} :
    inclusion (le_refl S) = NonUnitalAlgHom.id R S :=
  NonUnitalAlgHom.ext fun _ => Subtype.ext rfl
#align non_unital_subalgebra.inclusion_self NonUnitalSubalgebra.inclusion_self

@[simp]
theorem inclusion_mk {S T : NonUnitalSubalgebra R A} (h : S ≤ T) (x : A) (hx : x ∈ S) :
    inclusion h ⟨x, hx⟩ = ⟨x, h hx⟩ :=
  rfl
#align non_unital_subalgebra.inclusion_mk NonUnitalSubalgebra.inclusion_mk

theorem inclusion_right {S T : NonUnitalSubalgebra R A} (h : S ≤ T) (x : T) (m : (x : A) ∈ S) :
    inclusion h ⟨x, m⟩ = x :=
  Subtype.ext rfl
#align non_unital_subalgebra.inclusion_right NonUnitalSubalgebra.inclusion_right

@[simp]
theorem inclusion_inclusion {S T U : NonUnitalSubalgebra R A} (hst : S ≤ T) (htu : T ≤ U) (x : S) :
    inclusion htu (inclusion hst x) = inclusion (le_trans hst htu) x :=
  Subtype.ext rfl
#align non_unital_subalgebra.inclusion_inclusion NonUnitalSubalgebra.inclusion_inclusion

@[simp]
theorem coe_inclusion {S T : NonUnitalSubalgebra R A} (h : S ≤ T) (s : S) :
    (inclusion h s : A) = s :=
  rfl
#align non_unital_subalgebra.coe_inclusion NonUnitalSubalgebra.coe_inclusion

/- need to refactor `alg_equiv`
/-- Two non_unital_subalgebras that are equal are also equivalent as algebras.

This is the `non_unital_subalgebra` version of `linear_equiv.of_eq` and `equiv.set.of_eq`. -/
@[simps apply]
def equiv_of_eq (S T : non_unital_subalgebra R A) (h : S = T) : S ≃ₐ[R] T :=
{ to_fun := λ x, ⟨x, h ▸ x.2⟩,
  inv_fun := λ x, ⟨x, h.symm ▸ x.2⟩,
  map_mul' := λ _ _, rfl,
  commutes' := λ _, rfl,
  .. linear_equiv.of_eq _ _ (congr_arg to_submodule h) }

@[simp] lemma equiv_of_eq_symm (S T : non_unital_subalgebra R A) (h : S = T) :
  (equiv_of_eq S T h).symm = equiv_of_eq T S h.symm :=
rfl

@[simp] lemma equiv_of_eq_rfl (S : non_unital_subalgebra R A) :
  equiv_of_eq S S rfl = alg_equiv.refl :=
by { ext, refl }

@[simp] lemma equiv_of_eq_trans (S T U : non_unital_subalgebra R A) (hST : S = T) (hTU : T = U) :
  (equiv_of_eq S T hST).trans (equiv_of_eq T U hTU) = equiv_of_eq S U (trans hST hTU) :=
rfl
  -/
section Prod

variable (S₁ : NonUnitalSubalgebra R B)

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- The product of two non_unital_subalgebras is a non_unital_subalgebra. -/
def prod : NonUnitalSubalgebra R (A × B) :=
  {
    S.toNonUnitalSubsemiring.prod
      S₁.toNonUnitalSubsemiring with
    carrier := S ×ˢ S₁
    smul_mem' := fun r _x hx => ⟨S.smul_mem hx.1 r, S₁.smul_mem hx.2 r⟩ }
#align non_unital_subalgebra.prod NonUnitalSubalgebra.prod

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem coe_prod : (prod S S₁ : Set (A × B)) = (S : Set A) ×ˢ S₁ :=
  rfl
#align non_unital_subalgebra.coe_prod NonUnitalSubalgebra.coe_prod

theorem prod_toSubmodule : (S.prod S₁).toSubmodule = S.toSubmodule.prod S₁.toSubmodule :=
  rfl
#align non_unital_subalgebra.prod_to_submodule NonUnitalSubalgebra.prod_toSubmodule

@[simp]
theorem mem_prod {S : NonUnitalSubalgebra R A} {S₁ : NonUnitalSubalgebra R B} {x : A × B} :
    x ∈ prod S S₁ ↔ x.1 ∈ S ∧ x.2 ∈ S₁ :=
  Set.mem_prod
#align non_unital_subalgebra.mem_prod NonUnitalSubalgebra.mem_prod

@[simp]
theorem prod_top : (prod ⊤ ⊤ : NonUnitalSubalgebra R (A × B)) = ⊤ := by ext; simp
#align non_unital_subalgebra.prod_top NonUnitalSubalgebra.prod_top

theorem prod_mono {S T : NonUnitalSubalgebra R A} {S₁ T₁ : NonUnitalSubalgebra R B} :
    S ≤ T → S₁ ≤ T₁ → prod S S₁ ≤ prod T T₁ :=
  Set.prod_mono
#align non_unital_subalgebra.prod_mono NonUnitalSubalgebra.prod_mono

@[simp]
theorem prod_inf_prod {S T : NonUnitalSubalgebra R A} {S₁ T₁ : NonUnitalSubalgebra R B} :
    S.prod S₁ ⊓ T.prod T₁ = (S ⊓ T).prod (S₁ ⊓ T₁) :=
  SetLike.coe_injective Set.prod_inter_prod
#align non_unital_subalgebra.prod_inf_prod NonUnitalSubalgebra.prod_inf_prod

end Prod

section SuprLift

variable {ι : Type _}

theorem coe_iSup_of_directed [Nonempty ι] {S : ι → NonUnitalSubalgebra R A}
    (dir : Directed (· ≤ ·) S) : ↑(iSup S) = ⋃ i, (S i : Set A) :=
  let K : NonUnitalSubalgebra R A :=
    { carrier := ⋃ i, S i
      zero_mem' :=
        let i := @Nonempty.some ι inferInstance
        Set.mem_iUnion.2 ⟨i, zero_mem (S i)⟩
      mul_mem' := @fun _x _y hx hy =>
        let ⟨i, hi⟩ := Set.mem_iUnion.1 hx
        let ⟨j, hj⟩ := Set.mem_iUnion.1 hy
        let ⟨k, hik, hjk⟩ := dir i j
        Set.mem_iUnion.2 ⟨k, NonUnitalSubalgebra.mul_mem (S k) (hik hi) (hjk hj)⟩
      add_mem' := @fun _x _y hx hy =>
        let ⟨i, hi⟩ := Set.mem_iUnion.1 hx
        let ⟨j, hj⟩ := Set.mem_iUnion.1 hy
        let ⟨k, hik, hjk⟩ := dir i j
        Set.mem_iUnion.2 ⟨k, NonUnitalSubalgebra.add_mem (S k) (hik hi) (hjk hj)⟩
      smul_mem' := fun r _x hx =>
        let ⟨i, hi⟩ := Set.mem_iUnion.1 hx
        Set.mem_iUnion.2 ⟨i, (S i).smul_mem hi r⟩ }
  have : iSup S = K :=
    le_antisymm (iSup_le fun i => Set.subset_iUnion (fun i => (S i : Set A)) i)
      (SetLike.coe_subset_coe.1 (Set.iUnion_subset fun _i => SetLike.coe_subset_coe.2 (le_iSup _ _)))
  this.symm ▸ rfl
#align non_unital_subalgebra.coe_supr_of_directed NonUnitalSubalgebra.coe_iSup_of_directed

/-- Define an algebra homomorphism on a directed supremum of non-unital subalgebras by defining
it on each non-unital subalgebra, and proving that it agrees on the intersection of
non-unital subalgebras. -/
noncomputable def iSupLift [Nonempty ι] (K : ι → NonUnitalSubalgebra R A) (dir : Directed (· ≤ ·) K)
    (f : ∀ i, K i →ₙₐ[R] B) (hf : ∀ (i j : ι) (h : K i ≤ K j), f i = (f j).comp (inclusion h))
    (T : NonUnitalSubalgebra R A) (hT : T = iSup K) : ↥T →ₙₐ[R] B := by
  subst hT
  exact
      { toFun :=
          Set.iUnionLift (fun i => ↑(K i)) (fun i x => f i x)
            (fun i j x hxi hxj => by
              let ⟨k, hik, hjk⟩ := dir i j
              simp only
              rw [hf i k hik, hf j k hjk]
              rfl)
            (↑(iSup K)) (by rw [coe_iSup_of_directed dir])
        map_zero' := by
          dsimp
          exact Set.iUnionLift_const _ (fun i : ι => (0 : K i)) (fun _ => rfl)  _ (by simp)
        map_mul' := by
          dsimp
          apply Set.iUnionLift_binary (coe_iSup_of_directed dir) dir _ (fun _ => (· * ·))
          on_goal 3 => rw [coe_iSup_of_directed dir]
          all_goals simp
        map_add' := by
          dsimp
          apply Set.iUnionLift_binary (coe_iSup_of_directed dir) dir _ (fun _ => (· + ·))
          on_goal 3 => rw [coe_iSup_of_directed dir]
          all_goals simp
        map_smul' := fun r => by
          dsimp
          apply Set.iUnionLift_unary (coe_iSup_of_directed dir) _ (fun _ x => r • x)
            (fun _ _ => rfl)
          on_goal 2 => rw [coe_iSup_of_directed dir]
          all_goals simp }
#align non_unital_subalgebra.supr_lift NonUnitalSubalgebra.iSupLift

variable [Nonempty ι] {K : ι → NonUnitalSubalgebra R A} {dir : Directed (· ≤ ·) K}
  {f : ∀ i, K i →ₙₐ[R] B} {hf : ∀ (i j : ι) (h : K i ≤ K j), f i = (f j).comp (inclusion h)}
  {T : NonUnitalSubalgebra R A} {hT : T = iSup K}

@[simp]
theorem iSupLift_inclusion {i : ι} (x : K i) (h : K i ≤ T) :
    iSupLift K dir f hf T hT (inclusion h x) = f i x := by
  subst T
  dsimp [iSupLift]
  apply Set.iUnionLift_inclusion
  exact h
#align non_unital_subalgebra.supr_lift_inclusion NonUnitalSubalgebra.iSupLift_inclusion

@[simp]
theorem iSupLift_comp_inclusion {i : ι} (h : K i ≤ T) :
    (iSupLift K dir f hf T hT).comp (inclusion h) = f i := by ext; simp
#align non_unital_subalgebra.supr_lift_comp_inclusion NonUnitalSubalgebra.iSupLift_comp_inclusion

@[simp]
theorem iSupLift_mk {i : ι} (x : K i) (hx : (x : A) ∈ T) :
    iSupLift K dir f hf T hT ⟨x, hx⟩ = f i x := by
  subst hT
  dsimp [iSupLift]
  apply Set.iUnionLift_mk
#align non_unital_subalgebra.supr_lift_mk NonUnitalSubalgebra.iSupLift_mk

theorem iSupLift_of_mem {i : ι} (x : T) (hx : (x : A) ∈ K i) :
    iSupLift K dir f hf T hT x = f i ⟨x, hx⟩ := by
  subst hT
  dsimp [iSupLift]
  apply Set.iUnionLift_of_mem
#align non_unital_subalgebra.supr_lift_of_mem NonUnitalSubalgebra.iSupLift_of_mem

end SuprLift

section Center

theorem _root_.Set.smul_mem_center (r : R) {a : A} (ha : a ∈ Set.center A) : r • a ∈ Set.center A := by
  simp [Set.mem_center_iff, mul_smul_comm, smul_mul_assoc, (Set.mem_center_iff A).mp ha]
#align set.smul_mem_center Set.smul_mem_center

variable (R A)

/-- The center of an algebra is the set of elements which commute with every element. They form a
non-unital subalgebra. -/
def center : NonUnitalSubalgebra R A :=
  { NonUnitalSubsemiring.center A with smul_mem' := Set.smul_mem_center }
#align non_unital_subalgebra.center NonUnitalSubalgebra.center

theorem coe_center : (center R A : Set A) = Set.center A :=
  rfl
#align non_unital_subalgebra.coe_center NonUnitalSubalgebra.coe_center

@[simp]
theorem center_toNonUnitalSubsemiring :
    (center R A).toNonUnitalSubsemiring = NonUnitalSubsemiring.center A :=
  rfl
#align non_unital_subalgebra.center_to_non_unital_subsemiring NonUnitalSubalgebra.center_toNonUnitalSubsemiring

/-  we don't have `non_unital_subring.center`?
@[simp] lemma center_to_non_unital_subring (R A : Type*) [comm_ring R] [non_unital_ring A]
  [module R A] [is_scalar_tower R A A] [smul_comm_class R A A] :
  (center R A).to_non_unital_subring = non_unital_subring.center A :=
rfl
-/
@[simp]
theorem center_eq_top (A : Type _) [NonUnitalCommSemiring A] [Module R A] [IsScalarTower R A A]
    [SMulCommClass R A A] : center R A = ⊤ :=
  SetLike.coe_injective (Set.center_eq_univ A)
#align non_unital_subalgebra.center_eq_top NonUnitalSubalgebra.center_eq_top

variable {R A}

instance center.instNonUnitalCommSemiring : NonUnitalCommSemiring (center R A) :=
  NonUnitalSubsemiring.center.instNonUnitalCommSemiring

instance center.instNonUnitalCommRing {A : Type _} [NonUnitalRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] : NonUnitalCommRing (center R A) :=
  NonUnitalSubring.center.instNonUnitalCommRing

theorem mem_center_iff {a : A} : a ∈ center R A ↔ ∀ b : A, b * a = a * b :=
  Iff.rfl
#align non_unital_subalgebra.mem_center_iff NonUnitalSubalgebra.mem_center_iff

end Center

section Centralizer

@[simp]
theorem _root_.Set.smul_mem_centralizer {s : Set A} (r : R) {a : A} (ha : a ∈ s.centralizer) :
    r • a ∈ s.centralizer := fun x hx => by rw [mul_smul_comm, smul_mul_assoc, ha x hx]
#align set.smul_mem_centralizer Set.smul_mem_centralizer

variable (R)

/-- The centralizer of a set as a non_unital_subalgebra. -/
def centralizer (s : Set A) : NonUnitalSubalgebra R A :=
  { NonUnitalSubsemiring.centralizer s with smul_mem' := Set.smul_mem_centralizer }
#align non_unital_subalgebra.centralizer NonUnitalSubalgebra.centralizer

@[simp, norm_cast]
theorem coe_centralizer (s : Set A) : (centralizer R s : Set A) = s.centralizer :=
  rfl
#align non_unital_subalgebra.coe_centralizer NonUnitalSubalgebra.coe_centralizer

theorem mem_centralizer_iff {s : Set A} {z : A} : z ∈ centralizer R s ↔ ∀ g ∈ s, g * z = z * g :=
  Iff.rfl
#align non_unital_subalgebra.mem_centralizer_iff NonUnitalSubalgebra.mem_centralizer_iff

theorem centralizer_le (s t : Set A) (h : s ⊆ t) : centralizer R t ≤ centralizer R s :=
  Set.centralizer_subset h
#align non_unital_subalgebra.centralizer_le NonUnitalSubalgebra.centralizer_le

@[simp]
theorem centralizer_univ : centralizer R Set.univ = center R A :=
  SetLike.ext' (Set.centralizer_univ A)
#align non_unital_subalgebra.centralizer_univ NonUnitalSubalgebra.centralizer_univ

end Centralizer

end NonUnitalSubalgebra

section Nat

variable {R : Type _} [NonUnitalSemiring R]

-- this belongs in the `non_unital_subsemiring` file
instance NonUnitalSubsemiringClass.nsmulMemClass {S R : Type _} [NonUnitalSemiring R] [SetLike S R]
    [NonUnitalSubsemiringClass S R] : SMulMemClass S ℕ R where
  smul_mem {s} n x hx := Nat.recOn n ((zero_smul ℕ x).symm ▸ zero_mem s) fun k hk =>
    (succ_nsmul x k).symm ▸ add_mem hx hk
#align non_unital_subsemiring_class.nsmul_mem_class NonUnitalSubsemiringClass.nsmulMemClass

-- this belongs in the `non_unital_subsemiring` file
protected theorem NonUnitalSubsemiring.nsmul_mem (S : NonUnitalSubsemiring R) (n : ℕ) {x : R}
    (hx : x ∈ S) : n • x ∈ S :=
  SMulMemClass.smul_mem n hx
#align non_unital_subsemiring.nsmul_mem NonUnitalSubsemiring.nsmul_mem

/-- A non-unital subsemiring is a `ℕ`-non-unital subalgebra. -/
def nonUnitalSubalgebraOfNonUnitalSubsemiring (S : NonUnitalSubsemiring R) :
    NonUnitalSubalgebra ℕ R :=
  {--algebra_map_mem' := λ i, coe_nat_mem S i,
    S with
    smul_mem' := S.nsmul_mem }
#align non_unital_subalgebra_of_non_unital_subsemiring nonUnitalSubalgebraOfNonUnitalSubsemiring

@[simp]
theorem mem_nonUnitalSubalgebraOfNonUnitalSubsemiring {x : R} {S : NonUnitalSubsemiring R} :
    x ∈ nonUnitalSubalgebraOfNonUnitalSubsemiring S ↔ x ∈ S :=
  Iff.rfl
#align mem_non_unital_subalgebra_of_non_unital_subsemiring mem_nonUnitalSubalgebraOfNonUnitalSubsemiring

end Nat

section Int

variable {R : Type _} [NonUnitalRing R]

-- this belongs in the `non_unital_subring` file
protected theorem NonUnitalSubring.nsmul_mem (S : NonUnitalSubring R) (n : ℕ) {x : R} (hx : x ∈ S) :
    n • x ∈ S :=
  SMulMemClass.smul_mem n hx
#align non_unital_subring.nsmul_mem NonUnitalSubring.nsmul_mem

-- there's a problem with this instance and the `NonUnitalSubsemiringClass.nsmulMemClass` instance
-- The issue is that in `SMulMemClass S R M`, the `R` is an `outParam`, and so it should be unique.
-- But `NonUnitalSubring R` has both a `NonUnitalSubsemiringClass` and a `NonUnitalSubringClass`
-- instnace, and so it can't fill in `R` with both `ℕ` and `ℤ`. Maybe this needs to be a
-- `semiOutParam`?
instance NonUnitalSubringClass.zsmulMemClass {S R : Type _} [NonUnitalRing R] [SetLike S R]
    [NonUnitalSubringClass S R] : SMulMemClass S ℤ R where
  smul_mem {s} n x hx := by
    cases n <;>
      simpa only [Int.ofNat_eq_coe, coe_nat_zsmul, negSucc_zsmul, neg_mem_iff] using
        SMulMemClass.smul_mem _ hx
#align non_unital_subring_class.zsmul_mem_class NonUnitalSubringClass.zsmulMemClass

variable {S R : Type _} [NonUnitalRing R] [SetLike S R] [NonUnitalSubringClass S R]
#synth SMulMemClass S ℕ R
#check NonUnitalSubsemiringClass.nsmulMemClass
/-- A non-unital subring is a `ℤ`-non_unital_subalgebra. -/
def nonUnitalSubalgebraOfNonUnitalSubring (S : NonUnitalSubring R) : NonUnitalSubalgebra ℤ R :=
  { S with
    smul_mem' := SMulMemClass.smul_mem (s := S) }
#align non_unital_subalgebra_of_non_unital_subring nonUnitalSubalgebraOfNonUnitalSubring

@[simp]
theorem mem_nonUnitalSubalgebraOfNonUnitalSubring {x : R} {S : NonUnitalSubring R} :
    x ∈ nonUnitalSubalgebraOfNonUnitalSubring S ↔ x ∈ S :=
  Iff.rfl
#align mem_non_unital_subalgebra_of_non_unital_subring mem_nonUnitalSubalgebraOfNonUnitalSubring

end Int
