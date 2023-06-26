/-
Copyright (c) 2023 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
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

variable {S R A : Type _} [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]

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
structure NonUnitalSubalgebra (R : Type u) (A : Type v) [CommSemiring R]
    [NonUnitalNonAssocSemiring A] [Module R A]
    extends NonUnitalSubsemiring A, Submodule R A : Type v
#align non_unital_subalgebra NonUnitalSubalgebra

/-- Reinterpret a `non_unital_subalgebra` as a `non_unital_subsemiring`. -/
add_decl_doc NonUnitalSubalgebra.toNonUnitalSubsemiring

/-- Reinterpret a `non_unital_subalgebra` as a `submodule`. -/
add_decl_doc NonUnitalSubalgebra.toSubmodule

namespace NonUnitalSubalgebra

variable {F : Type v'} {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [NonUnitalNonAssocSemiring A] [Module R A] [NonUnitalNonAssocSemiring B] [Module R B]

variable [NonUnitalNonAssocSemiring C] [Module R C] [NonUnitalAlgHomClass F R A B]

instance : SetLike (NonUnitalSubalgebra R A) A
    where
  coe s := s.carrier
  coe_injective' p q h := by cases p; cases q; congr; exact SetLike.coe_injective h

instance instNonUnitalSubsemiringClass : NonUnitalSubsemiringClass (NonUnitalSubalgebra R A) A
    where
  add_mem {s} := s.add_mem'
  mul_mem {s} := s.mul_mem'
  zero_mem {s} := s.zero_mem'

instance instSMulMemClass : SMulMemClass (NonUnitalSubalgebra R A) R A where
  smul_mem := @fun s => s.smul_mem'

instance instNonUnitalSubringClass {R : Type u} {A : Type v} [CommRing R] [NonUnitalRing A]
    [Module R A] : NonUnitalSubringClass (NonUnitalSubalgebra R A) A :=
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

/-- A non-unital subalgebra over a ring is also a `subring`. -/
def toNonUnitalSubring {R : Type u} {A : Type v} [CommRing R] [NonUnitalRing A] [Module R A]
    (S : NonUnitalSubalgebra R A) : NonUnitalSubring A where
  toNonUnitalSubsemiring := S.toNonUnitalSubsemiring
  neg_mem' := neg_mem (s := S)
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

/-! `non_unital_subalgebra`s inherit structure from their `non_unital_subsemiring` / `semiring`
coercions. -/


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

/-! ### `non_unital_subalgebra`s inherit structure from their `submodule` coercions. -/

-- maybe these next two declarations should be moved?
-- the first to `SubMulAction`? and the second to `Submodule.Basic`?
/-- This can't be an instance because Lean wouldn't know how to find `N`, but we can still use
this to manually derive `SMulMemClass` on specific types. -/
def SMulMemClass.ofIsScalarTower (S M N α : Type _) [SetLike S α] [SMul M N]
  [SMul M α] [Monoid N] [MulAction N α] [SMulMemClass S N α] [IsScalarTower M N α] :
  SMulMemClass S M α :=
{ smul_mem := fun m a ha => smul_one_smul N m a ▸ SMulMemClass.smul_mem _ ha }

/-- This can't be an instance because Lean wouldn't know how to find `R`, but we can still use
this to manually derive `Module` on specific types. -/
def SMulMemClass.toModule' (S R' R A : Type _) [Semiring R] [NonUnitalNonAssocSemiring A]
    [Module R A] [Semiring R'] [SMul R' R] [Module R' A] [IsScalarTower R' R A]
    [SetLike S A] [AddSubmonoidClass S A] [SMulMemClass S R A] (s : S) :
    Module R' s :=
  haveI : SMulMemClass S R' A := SMulMemClass.ofIsScalarTower S R' R  A
  SMulMemClass.toModule s

instance instModule' [Semiring R'] [SMul R' R] [Module R' A] [IsScalarTower R' R A] : Module R' S :=
  SMulMemClass.toModule' _ R' R A S
#align non_unital_subalgebra.module' NonUnitalSubalgebra.instModule'

instance instModule : Module R S :=
  S.instModule'

instance instIsScalarTower' [Semiring R'] [SMul R' R] [Module R' A] [IsScalarTower R' R A] :
    IsScalarTower R' R S :=
  S.toSubmodule.isScalarTower
#align non_unital_subalgebra.is_scalar_tower' NonUnitalSubalgebra.instIsScalarTower'

instance [IsScalarTower R A A] : IsScalarTower R S S
    where smul_assoc r x y := Subtype.ext <| smul_assoc r (x : A) (y : A)

instance instSMulCommClass' [Semiring R'] [SMul R' R] [Module R' A] [IsScalarTower R' R A]
    [SMulCommClass R' R A] : SMulCommClass R' R S
    where smul_comm r' r s := Subtype.ext <| smul_comm r' r (s : A)
#align non_unital_subalgebra.smul_comm_class' NonUnitalSubalgebra.instSMulCommClass'

instance instSMulCommClass [SMulCommClass R A A] : SMulCommClass R S S
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

@[simp]
theorem toNonUnitalSubsemiring_subtype :
    NonUnitalSubsemiringClass.subtype S = NonUnitalSubalgebraClass.subtype (R := R) S :=
  rfl
#align non_unital_subalgebra.to_non_unital_subsemiring_subtype NonUnitalSubalgebra.toNonUnitalSubsemiring_subtype

@[simp]
theorem toSubring_subtype {R A : Type _} [CommRing R] [Ring A] [Algebra R A]
    (S : NonUnitalSubalgebra R A) :
    NonUnitalSubringClass.subtype S = NonUnitalSubalgebraClass.subtype (R := R) S :=
  rfl
#align non_unital_subalgebra.to_subring_subtype NonUnitalSubalgebra.toSubring_subtype

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

theorem map_toSubmodule {S : NonUnitalSubalgebra R A} {f : F} :
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
      show f (r • a) ∈ S from (map_smul f r a).symm ▸ SMulMemClass.smul_mem r ha }
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

variable {R A : Type _} [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]
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
    (S.toSubmodule.toNonUnitalSubalgebra fun _ _ => mul_mem (s := S)) = S :=
  SetLike.coe_injective rfl
#align non_unital_subalgebra.to_submodule_to_non_unital_subalgebra NonUnitalSubalgebra.toSubmodule_toNonUnitalSubalgebra

end Submodule

namespace NonUnitalAlgHom

variable {F : Type v'} {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}
variable [CommSemiring R]
variable [NonUnitalNonAssocSemiring A] [Module R A] [NonUnitalNonAssocSemiring B] [Module R B]
variable [NonUnitalNonAssocSemiring C] [Module R C] [NonUnitalAlgHomClass F R A B]

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

namespace NonUnitalAlgebra

variable {F : Type _} (R : Type u) {A : Type v} {B : Type w}
variable [CommSemiring R]
variable [NonUnitalNonAssocSemiring A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
variable [NonUnitalNonAssocSemiring B] [Module R B] [IsScalarTower R B B] [SMulCommClass R B B]
variable [NonUnitalAlgHomClass F R A B]

/-- The minimal non-unital subalgebra that includes `s`. -/
def adjoin (s : Set A) : NonUnitalSubalgebra R A :=
  { Submodule.span R (NonUnitalSubsemiring.closure s : Set A) with
    mul_mem' :=
      @fun a b (ha : a ∈ Submodule.span R (NonUnitalSubsemiring.closure s : Set A))
        (hb : b ∈ Submodule.span R (NonUnitalSubsemiring.closure s : Set A)) =>
      show a * b ∈ Submodule.span R (NonUnitalSubsemiring.closure s : Set A) by
        refine' Submodule.span_induction ha _ _ _ _
        · refine' Submodule.span_induction hb _ _ _ _
          · exact fun x (hx : x ∈ NonUnitalSubsemiring.closure s) y
              (hy : y ∈ NonUnitalSubsemiring.closure s) => Submodule.subset_span (mul_mem hy hx)
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

/-- The difference with `non_unital_algebra.adjoin_induction` is that this acts on the subtype. -/
lemma adjoin_induction' {s : Set A} {p : adjoin R s → Prop} (a : adjoin R s)
  (Hs : ∀ x (h : x ∈ s), p ⟨x, subset_adjoin R h⟩)
  (Hadd : ∀ x y, p x → p y → p (x + y)) (H0 : p 0)
  (Hmul : ∀ x y, p x → p y → p (x * y)) (Hsmul : ∀ (r : R) x, p x → p (r • x)) : p a :=
Subtype.recOn a <| fun b hb => by
  refine Exists.elim ?_ (fun (hb : b ∈ adjoin R s) (hc : p ⟨b, hb⟩) => hc)
  apply adjoin_induction hb
  · exact fun x hx => ⟨subset_adjoin R hx, Hs x hx⟩
  · exact fun x y hx hy => Exists.elim hx <| fun hx' hx => Exists.elim hy <| fun hy' hy =>
      ⟨add_mem hx' hy', Hadd _ _ hx hy⟩
  · exact ⟨_, H0⟩
  · exact fun x y hx hy => Exists.elim hx <| fun hx' hx => Exists.elim hy <| fun hy' hy =>
      ⟨mul_mem hx' hy', Hmul _ _ hx hy⟩
  · exact fun r x hx => Exists.elim hx <| fun hx' hx => ⟨SMulMemClass.smul_mem r hx', Hsmul r _ hx⟩
#align non_unital_algebra.adjoin_induction' NonUnitalAlgebra.adjoin_induction'

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
  mul_mem (mem_sup_left hx) (mem_sup_right hy)
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

section NonAssoc

variable {F : Type _} {R : Type u} {A : Type v} {B : Type w}

variable [CommSemiring R]

variable [NonUnitalNonAssocSemiring A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]

variable [NonUnitalNonAssocSemiring B] [Module R B] [IsScalarTower R B B] [SMulCommClass R B B]

variable [NonUnitalAlgHomClass F R A B] (S : NonUnitalSubalgebra R A)

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

section Prod

variable (S₁ : NonUnitalSubalgebra R B)

/-- The product of two non_unital_subalgebras is a non_unital_subalgebra. -/
def prod : NonUnitalSubalgebra R (A × B) :=
  { S.toNonUnitalSubsemiring.prod S₁.toNonUnitalSubsemiring with
    carrier := S ×ˢ S₁
    smul_mem' := fun r _x hx => ⟨SMulMemClass.smul_mem r hx.1, SMulMemClass.smul_mem r hx.2⟩ }
#align non_unital_subalgebra.prod NonUnitalSubalgebra.prod

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
        Set.mem_iUnion.2 ⟨k, mul_mem (hik hi) (hjk hj)⟩
      add_mem' := @fun _x _y hx hy =>
        let ⟨i, hi⟩ := Set.mem_iUnion.1 hx
        let ⟨j, hj⟩ := Set.mem_iUnion.1 hy
        let ⟨k, hik, hjk⟩ := dir i j
        Set.mem_iUnion.2 ⟨k, add_mem (hik hi) (hjk hj)⟩
      smul_mem' := fun r _x hx =>
        let ⟨i, hi⟩ := Set.mem_iUnion.1 hx
        Set.mem_iUnion.2 ⟨i, SMulMemClass.smul_mem r hi⟩ }
  have : iSup S = K :=
    le_antisymm (iSup_le fun i => Set.subset_iUnion (fun i => (S i : Set A)) i) <|
      SetLike.coe_subset_coe.1 (Set.iUnion_subset fun _i => SetLike.coe_subset_coe.2 (le_iSup _ _))
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

end NonAssoc

section Center

theorem _root_.Set.smul_mem_center {R A : Type _} [CommSemiring R] [NonUnitalNonAssocSemiring A]
  [Module R A] [IsScalarTower R A A] [SMulCommClass R A A](r : R) {a : A} (ha : a ∈ Set.center A) :
    r • a ∈ Set.center A := by
  simp [Set.mem_center_iff, mul_smul_comm, smul_mul_assoc, (Set.mem_center_iff A).mp ha]
#align set.smul_mem_center Set.smul_mem_center

variable (R A : Type _) [CommSemiring R] [NonUnitalSemiring A] [Module R A] [IsScalarTower R A A]
  [SMulCommClass R A A]

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

@[simp] lemma center_toNonUnitalSubring (R A : Type _) [CommRing R] [NonUnitalRing A]
    [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] :
    (center R A).toNonUnitalSubring = NonUnitalSubring.center A :=
  rfl

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

variable {R A : Type _} [CommSemiring R] [NonUnitalSemiring A] [Module R A] [IsScalarTower R A A]
  [SMulCommClass R A A]

@[simp]
theorem _root_.Set.smul_mem_centralizer {s : Set A} (r : R) {a : A} (ha : a ∈ s.centralizer) :
    r • a ∈ s.centralizer :=
  fun x hx => by rw [mul_smul_comm, smul_mul_assoc, ha x hx]
#align set.smul_mem_centralizer Set.smul_mem_centralizer

variable (R)

/-- The centralizer of a set as a non_unital_subalgebra. -/
def centralizer (s : Set A) : NonUnitalSubalgebra R A where
  toNonUnitalSubsemiring := NonUnitalSubsemiring.centralizer s
  smul_mem' := Set.smul_mem_centralizer
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

/-- A non-unital subsemiring is a `ℕ`-non-unital subalgebra. -/
def nonUnitalSubalgebraOfNonUnitalSubsemiring (S : NonUnitalSubsemiring R) :
    NonUnitalSubalgebra ℕ R where
  toNonUnitalSubsemiring := S
  smul_mem' n _x hx := nsmul_mem (S := S) hx n
#align non_unital_subalgebra_of_non_unital_subsemiring nonUnitalSubalgebraOfNonUnitalSubsemiring

@[simp]
theorem mem_nonUnitalSubalgebraOfNonUnitalSubsemiring {x : R} {S : NonUnitalSubsemiring R} :
    x ∈ nonUnitalSubalgebraOfNonUnitalSubsemiring S ↔ x ∈ S :=
  Iff.rfl
#align mem_non_unital_subalgebra_of_non_unital_subsemiring mem_nonUnitalSubalgebraOfNonUnitalSubsemiring

end Nat

section Int

variable {R : Type _} [NonUnitalRing R]

/-- A non-unital subring is a `ℤ`-non_unital_subalgebra. -/
def nonUnitalSubalgebraOfNonUnitalSubring (S : NonUnitalSubring R) : NonUnitalSubalgebra ℤ R where
  toNonUnitalSubsemiring := S.toNonUnitalSubsemiring
  smul_mem' n _x hx := zsmul_mem (K := S) hx n
#align non_unital_subalgebra_of_non_unital_subring nonUnitalSubalgebraOfNonUnitalSubring

@[simp]
theorem mem_nonUnitalSubalgebraOfNonUnitalSubring {x : R} {S : NonUnitalSubring R} :
    x ∈ nonUnitalSubalgebraOfNonUnitalSubring S ↔ x ∈ S :=
  Iff.rfl
#align mem_non_unital_subalgebra_of_non_unital_subring mem_nonUnitalSubalgebraOfNonUnitalSubring

end Int
