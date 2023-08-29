/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Data.Set.UnionLift
import Mathlib.LinearAlgebra.Finsupp
import Mathlib.RingTheory.Ideal.Operations

#align_import algebra.algebra.subalgebra.basic from "leanprover-community/mathlib"@"b915e9392ecb2a861e1e766f0e1df6ac481188ca"

/-!
# Subalgebras over Commutative Semiring

In this file we define `Subalgebra`s and the usual operations on them (`map`, `comap`).

More lemmas about `adjoin` can be found in `RingTheory.Adjoin`.
-/


universe u u' v w w'

open BigOperators

/-- A subalgebra is a sub(semi)ring that includes the range of `algebraMap`. -/
structure Subalgebra (R : Type u) (A : Type v) [CommSemiring R] [Semiring A] [Algebra R A] extends
  Subsemiring A : Type v where
  /-- The image of `algebraMap` is contained in the underlying set of the subalgebra -/
  algebraMap_mem' : ∀ r, algebraMap R A r ∈ carrier
  zero_mem' := (algebraMap R A).map_zero ▸ algebraMap_mem' 0
  one_mem' := (algebraMap R A).map_one ▸ algebraMap_mem' 1
#align subalgebra Subalgebra

/-- Reinterpret a `Subalgebra` as a `Subsemiring`. -/
add_decl_doc Subalgebra.toSubsemiring

namespace Subalgebra

variable {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]

instance : SetLike (Subalgebra R A) A where
  coe s := s.carrier
  coe_injective' p q h := by cases p; cases q; congr; exact SetLike.coe_injective' h
                             -- ⊢ { toSubsemiring := toSubsemiring✝, algebraMap_mem' := algebraMap_mem'✝ } = q
                                      -- ⊢ { toSubsemiring := toSubsemiring✝¹, algebraMap_mem' := algebraMap_mem'✝¹ } = …
                                               -- ⊢ toSubsemiring✝¹ = toSubsemiring✝
                                                      -- 🎉 no goals

instance SubsemiringClass : SubsemiringClass (Subalgebra R A) A where
  add_mem {s} := add_mem (s := s.toSubsemiring)
  mul_mem {s} := mul_mem (s := s.toSubsemiring)
  one_mem {s} := one_mem s.toSubsemiring
  zero_mem {s} := zero_mem s.toSubsemiring

@[simp]
theorem mem_toSubsemiring {S : Subalgebra R A} {x} : x ∈ S.toSubsemiring ↔ x ∈ S :=
  Iff.rfl
#align subalgebra.mem_to_subsemiring Subalgebra.mem_toSubsemiring

-- @[simp] -- Porting note: simp can prove this
theorem mem_carrier {s : Subalgebra R A} {x : A} : x ∈ s.carrier ↔ x ∈ s :=
  Iff.rfl
#align subalgebra.mem_carrier Subalgebra.mem_carrier

@[ext]
theorem ext {S T : Subalgebra R A} (h : ∀ x : A, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h
#align subalgebra.ext Subalgebra.ext

@[simp]
theorem coe_toSubsemiring (S : Subalgebra R A) : (↑S.toSubsemiring : Set A) = S :=
  rfl
#align subalgebra.coe_to_subsemiring Subalgebra.coe_toSubsemiring

theorem toSubsemiring_injective :
    Function.Injective (toSubsemiring : Subalgebra R A → Subsemiring A) := fun S T h =>
  ext fun x => by rw [← mem_toSubsemiring, ← mem_toSubsemiring, h]
                  -- 🎉 no goals
#align subalgebra.to_subsemiring_injective Subalgebra.toSubsemiring_injective

theorem toSubsemiring_inj {S U : Subalgebra R A} : S.toSubsemiring = U.toSubsemiring ↔ S = U :=
  toSubsemiring_injective.eq_iff
#align subalgebra.to_subsemiring_inj Subalgebra.toSubsemiring_inj

/-- Copy of a subalgebra with a new `carrier` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (S : Subalgebra R A) (s : Set A) (hs : s = ↑S) : Subalgebra R A :=
  { S.toSubsemiring.copy s hs with
    carrier := s
    algebraMap_mem' := hs.symm ▸ S.algebraMap_mem' }
#align subalgebra.copy Subalgebra.copy

@[simp]
theorem coe_copy (S : Subalgebra R A) (s : Set A) (hs : s = ↑S) : (S.copy s hs : Set A) = s :=
  rfl
#align subalgebra.coe_copy Subalgebra.coe_copy

theorem copy_eq (S : Subalgebra R A) (s : Set A) (hs : s = ↑S) : S.copy s hs = S :=
  SetLike.coe_injective hs
#align subalgebra.copy_eq Subalgebra.copy_eq

variable (S : Subalgebra R A)

instance instSMulMemClass : SMulMemClass (Subalgebra R A) R A where
  smul_mem {S} r x hx := (Algebra.smul_def r x).symm ▸ mul_mem (S.algebraMap_mem' r) hx

theorem _root_.algebraMap_mem {S R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    [SetLike S A] [OneMemClass S A] [SMulMemClass S R A] (s : S) (r : R) :
    algebraMap R A r ∈ s :=
  Algebra.algebraMap_eq_smul_one (A := A) r ▸ SMulMemClass.smul_mem r (one_mem s)

protected theorem algebraMap_mem (r : R) : algebraMap R A r ∈ S :=
  algebraMap_mem S r
#align subalgebra.algebra_map_mem Subalgebra.algebraMap_mem

theorem rangeS_le : (algebraMap R A).rangeS ≤ S.toSubsemiring := fun _x ⟨r, hr⟩ =>
  hr ▸ S.algebraMap_mem r
#align subalgebra.srange_le Subalgebra.rangeS_le

theorem range_subset : Set.range (algebraMap R A) ⊆ S := fun _x ⟨r, hr⟩ => hr ▸ S.algebraMap_mem r
#align subalgebra.range_subset Subalgebra.range_subset

theorem range_le : Set.range (algebraMap R A) ≤ S :=
  S.range_subset
#align subalgebra.range_le Subalgebra.range_le

theorem smul_mem {x : A} (hx : x ∈ S) (r : R) : r • x ∈ S :=
  SMulMemClass.smul_mem r hx
#align subalgebra.smul_mem Subalgebra.smul_mem

protected theorem one_mem : (1 : A) ∈ S :=
  one_mem S
#align subalgebra.one_mem Subalgebra.one_mem

protected theorem mul_mem {x y : A} (hx : x ∈ S) (hy : y ∈ S) : x * y ∈ S :=
  mul_mem hx hy
#align subalgebra.mul_mem Subalgebra.mul_mem

protected theorem pow_mem {x : A} (hx : x ∈ S) (n : ℕ) : x ^ n ∈ S :=
  pow_mem hx n
#align subalgebra.pow_mem Subalgebra.pow_mem

protected theorem zero_mem : (0 : A) ∈ S :=
  zero_mem S
#align subalgebra.zero_mem Subalgebra.zero_mem

protected theorem add_mem {x y : A} (hx : x ∈ S) (hy : y ∈ S) : x + y ∈ S :=
  add_mem hx hy
#align subalgebra.add_mem Subalgebra.add_mem

protected theorem nsmul_mem {x : A} (hx : x ∈ S) (n : ℕ) : n • x ∈ S :=
  nsmul_mem hx n
#align subalgebra.nsmul_mem Subalgebra.nsmul_mem

protected theorem coe_nat_mem (n : ℕ) : (n : A) ∈ S :=
  coe_nat_mem S n
#align subalgebra.coe_nat_mem Subalgebra.coe_nat_mem

protected theorem list_prod_mem {L : List A} (h : ∀ x ∈ L, x ∈ S) : L.prod ∈ S :=
  list_prod_mem h
#align subalgebra.list_prod_mem Subalgebra.list_prod_mem

protected theorem list_sum_mem {L : List A} (h : ∀ x ∈ L, x ∈ S) : L.sum ∈ S :=
  list_sum_mem h
#align subalgebra.list_sum_mem Subalgebra.list_sum_mem

protected theorem multiset_sum_mem {m : Multiset A} (h : ∀ x ∈ m, x ∈ S) : m.sum ∈ S :=
  multiset_sum_mem m h
#align subalgebra.multiset_sum_mem Subalgebra.multiset_sum_mem

protected theorem sum_mem {ι : Type w} {t : Finset ι} {f : ι → A} (h : ∀ x ∈ t, f x ∈ S) :
    (∑ x in t, f x) ∈ S :=
  sum_mem h
#align subalgebra.sum_mem Subalgebra.sum_mem

protected theorem multiset_prod_mem {R : Type u} {A : Type v} [CommSemiring R] [CommSemiring A]
    [Algebra R A] (S : Subalgebra R A) {m : Multiset A} (h : ∀ x ∈ m, x ∈ S) : m.prod ∈ S :=
  multiset_prod_mem m h
#align subalgebra.multiset_prod_mem Subalgebra.multiset_prod_mem

protected theorem prod_mem {R : Type u} {A : Type v} [CommSemiring R] [CommSemiring A] [Algebra R A]
    (S : Subalgebra R A) {ι : Type w} {t : Finset ι} {f : ι → A} (h : ∀ x ∈ t, f x ∈ S) :
    (∏ x in t, f x) ∈ S :=
  prod_mem h
#align subalgebra.prod_mem Subalgebra.prod_mem

instance {R A : Type*} [CommRing R] [Ring A] [Algebra R A] : SubringClass (Subalgebra R A) A :=
  { Subalgebra.SubsemiringClass with
    neg_mem := fun {S x} hx => neg_one_smul R x ▸ S.smul_mem hx _ }

protected theorem neg_mem {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (S : Subalgebra R A) {x : A} (hx : x ∈ S) : -x ∈ S :=
  neg_mem hx
#align subalgebra.neg_mem Subalgebra.neg_mem

protected theorem sub_mem {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (S : Subalgebra R A) {x y : A} (hx : x ∈ S) (hy : y ∈ S) : x - y ∈ S :=
  sub_mem hx hy
#align subalgebra.sub_mem Subalgebra.sub_mem

protected theorem zsmul_mem {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (S : Subalgebra R A) {x : A} (hx : x ∈ S) (n : ℤ) : n • x ∈ S :=
  zsmul_mem hx n
#align subalgebra.zsmul_mem Subalgebra.zsmul_mem

protected theorem coe_int_mem {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (S : Subalgebra R A) (n : ℤ) : (n : A) ∈ S :=
  coe_int_mem S n
#align subalgebra.coe_int_mem Subalgebra.coe_int_mem

/-- The projection from a subalgebra of `A` to an additive submonoid of `A`. -/
def toAddSubmonoid {R : Type u} {A : Type v} [CommSemiring R] [Semiring A] [Algebra R A]
    (S : Subalgebra R A) : AddSubmonoid A :=
  S.toSubsemiring.toAddSubmonoid
#align subalgebra.to_add_submonoid Subalgebra.toAddSubmonoid

-- Porting note: this field already exists in Lean 4.
-- /-- The projection from a subalgebra of `A` to a submonoid of `A`. -/
-- def toSubmonoid {R : Type u} {A : Type v} [CommSemiring R] [Semiring A] [Algebra R A]
--     (S : Subalgebra R A) : Submonoid A :=
--   S.toSubsemiring.toSubmonoid
set_option align.precheck false in
#align subalgebra.to_submonoid Subalgebra.toSubmonoid

/-- A subalgebra over a ring is also a `Subring`. -/
def toSubring {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A] (S : Subalgebra R A) :
    Subring A :=
  { S.toSubsemiring with neg_mem' := S.neg_mem }
#align subalgebra.to_subring Subalgebra.toSubring

@[simp]
theorem mem_toSubring {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    {S : Subalgebra R A} {x} : x ∈ S.toSubring ↔ x ∈ S :=
  Iff.rfl
#align subalgebra.mem_to_subring Subalgebra.mem_toSubring

@[simp]
theorem coe_toSubring {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (S : Subalgebra R A) : (↑S.toSubring : Set A) = S :=
  rfl
#align subalgebra.coe_to_subring Subalgebra.coe_toSubring

theorem toSubring_injective {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A] :
    Function.Injective (toSubring : Subalgebra R A → Subring A) := fun S T h =>
  ext fun x => by rw [← mem_toSubring, ← mem_toSubring, h]
                  -- 🎉 no goals
#align subalgebra.to_subring_injective Subalgebra.toSubring_injective

theorem toSubring_inj {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    {S U : Subalgebra R A} : S.toSubring = U.toSubring ↔ S = U :=
  toSubring_injective.eq_iff
#align subalgebra.to_subring_inj Subalgebra.toSubring_inj

instance : Inhabited S :=
  ⟨(0 : S.toSubsemiring)⟩

section

/-! `Subalgebra`s inherit structure from their `Subsemiring` / `Semiring` coercions. -/


instance toSemiring {R A} [CommSemiring R] [Semiring A] [Algebra R A] (S : Subalgebra R A) :
    Semiring S :=
  S.toSubsemiring.toSemiring
#align subalgebra.to_semiring Subalgebra.toSemiring

instance toCommSemiring {R A} [CommSemiring R] [CommSemiring A] [Algebra R A] (S : Subalgebra R A) :
    CommSemiring S :=
  S.toSubsemiring.toCommSemiring
#align subalgebra.to_comm_semiring Subalgebra.toCommSemiring

instance toRing {R A} [CommRing R] [Ring A] [Algebra R A] (S : Subalgebra R A) : Ring S :=
  S.toSubring.toRing
#align subalgebra.to_ring Subalgebra.toRing

instance toCommRing {R A} [CommRing R] [CommRing A] [Algebra R A] (S : Subalgebra R A) :
    CommRing S :=
  S.toSubring.toCommRing
#align subalgebra.to_comm_ring Subalgebra.toCommRing

instance toOrderedSemiring {R A} [CommSemiring R] [OrderedSemiring A] [Algebra R A]
    (S : Subalgebra R A) : OrderedSemiring S :=
  S.toSubsemiring.toOrderedSemiring
#align subalgebra.to_ordered_semiring Subalgebra.toOrderedSemiring

instance toStrictOrderedSemiring {R A} [CommSemiring R] [StrictOrderedSemiring A] [Algebra R A]
    (S : Subalgebra R A) : StrictOrderedSemiring S :=
  S.toSubsemiring.toStrictOrderedSemiring
#align subalgebra.to_strict_ordered_semiring Subalgebra.toStrictOrderedSemiring

instance toOrderedCommSemiring {R A} [CommSemiring R] [OrderedCommSemiring A] [Algebra R A]
    (S : Subalgebra R A) : OrderedCommSemiring S :=
  S.toSubsemiring.toOrderedCommSemiring
#align subalgebra.to_ordered_comm_semiring Subalgebra.toOrderedCommSemiring

instance toStrictOrderedCommSemiring {R A} [CommSemiring R] [StrictOrderedCommSemiring A]
    [Algebra R A] (S : Subalgebra R A) : StrictOrderedCommSemiring S :=
  S.toSubsemiring.toStrictOrderedCommSemiring
#align subalgebra.to_strict_ordered_comm_semiring Subalgebra.toStrictOrderedCommSemiring

instance toOrderedRing {R A} [CommRing R] [OrderedRing A] [Algebra R A] (S : Subalgebra R A) :
    OrderedRing S :=
  S.toSubring.toOrderedRing
#align subalgebra.to_ordered_ring Subalgebra.toOrderedRing

instance toOrderedCommRing {R A} [CommRing R] [OrderedCommRing A] [Algebra R A]
    (S : Subalgebra R A) : OrderedCommRing S :=
  S.toSubring.toOrderedCommRing
#align subalgebra.to_ordered_comm_ring Subalgebra.toOrderedCommRing

instance toLinearOrderedSemiring {R A} [CommSemiring R] [LinearOrderedSemiring A] [Algebra R A]
    (S : Subalgebra R A) : LinearOrderedSemiring S :=
  S.toSubsemiring.toLinearOrderedSemiring
#align subalgebra.to_linear_ordered_semiring Subalgebra.toLinearOrderedSemiring

instance toLinearOrderedCommSemiring {R A} [CommSemiring R] [LinearOrderedCommSemiring A]
    [Algebra R A] (S : Subalgebra R A) : LinearOrderedCommSemiring S :=
  S.toSubsemiring.toLinearOrderedCommSemiring
#align subalgebra.to_linear_ordered_comm_semiring Subalgebra.toLinearOrderedCommSemiring

instance toLinearOrderedRing {R A} [CommRing R] [LinearOrderedRing A] [Algebra R A]
    (S : Subalgebra R A) : LinearOrderedRing S :=
  S.toSubring.toLinearOrderedRing
#align subalgebra.to_linear_ordered_ring Subalgebra.toLinearOrderedRing

instance toLinearOrderedCommRing {R A} [CommRing R] [LinearOrderedCommRing A] [Algebra R A]
    (S : Subalgebra R A) : LinearOrderedCommRing S :=
  S.toSubring.toLinearOrderedCommRing
#align subalgebra.to_linear_ordered_comm_ring Subalgebra.toLinearOrderedCommRing

end

/-- The forgetful map from `Subalgebra` to `Submodule` as an `OrderEmbedding` -/
def toSubmodule : Subalgebra R A ↪o Submodule R A where
  toEmbedding :=
    { toFun := fun S =>
        { S with
          carrier := S
          smul_mem' := fun c {x} hx ↦
            (Algebra.smul_def c x).symm ▸ mul_mem (S.range_le ⟨c, rfl⟩) hx }
      inj' := fun _ _ h ↦ ext <| fun x ↦ SetLike.ext_iff.mp h x }
  map_rel_iff' := SetLike.coe_subset_coe.symm.trans SetLike.coe_subset_coe
#align subalgebra.to_submodule Subalgebra.toSubmodule

/- TODO: bundle other forgetful maps between algebraic substructures, e.g.
  `to_subsemiring` and `to_subring` in this file. -/
@[simp]
theorem mem_toSubmodule {x} : x ∈ (toSubmodule S) ↔ x ∈ S := Iff.rfl
#align subalgebra.mem_to_submodule Subalgebra.mem_toSubmodule

@[simp]
theorem coe_toSubmodule (S : Subalgebra R A) : (toSubmodule S : Set A) = S := rfl
#align subalgebra.coe_to_submodule Subalgebra.coe_toSubmodule

section

/-! `Subalgebra`s inherit structure from their `Submodule` coercions. -/


instance module' [Semiring R'] [SMul R' R] [Module R' A] [IsScalarTower R' R A] : Module R' S :=
  S.toSubmodule.module'
#align subalgebra.module' Subalgebra.module'

instance : Module R S :=
  S.module'

instance [Semiring R'] [SMul R' R] [Module R' A] [IsScalarTower R' R A] : IsScalarTower R' R S :=
  inferInstanceAs (IsScalarTower R' R (toSubmodule S))

instance algebra' [CommSemiring R'] [SMul R' R] [Algebra R' A] [IsScalarTower R' R A] :
    Algebra R' S :=
  { (algebraMap R' A).codRestrict S fun x => by
      rw [Algebra.algebraMap_eq_smul_one, ← smul_one_smul R x (1 : A), ←
        Algebra.algebraMap_eq_smul_one]
      exact algebraMap_mem S
          _ with
    commutes' := fun c x => Subtype.eq <| Algebra.commutes _ _
    smul_def' := fun c x => Subtype.eq <| Algebra.smul_def _ _ }
#align subalgebra.algebra' Subalgebra.algebra'

instance algebra : Algebra R S := S.algebra'
#align subalgebra.algebra Subalgebra.algebra

end

instance noZeroSMulDivisors_bot [NoZeroSMulDivisors R A] : NoZeroSMulDivisors R S :=
  ⟨fun {c} {x : S} h =>
    have : c = 0 ∨ (x : A) = 0 := eq_zero_or_eq_zero_of_smul_eq_zero (congr_arg Subtype.val h)
    this.imp_right (@Subtype.ext_iff _ _ x 0).mpr⟩
#align subalgebra.no_zero_smul_divisors_bot Subalgebra.noZeroSMulDivisors_bot

protected theorem coe_add (x y : S) : (↑(x + y) : A) = ↑x + ↑y := rfl
#align subalgebra.coe_add Subalgebra.coe_add

protected theorem coe_mul (x y : S) : (↑(x * y) : A) = ↑x * ↑y := rfl
#align subalgebra.coe_mul Subalgebra.coe_mul

protected theorem coe_zero : ((0 : S) : A) = 0 := rfl
#align subalgebra.coe_zero Subalgebra.coe_zero

protected theorem coe_one : ((1 : S) : A) = 1 := rfl
#align subalgebra.coe_one Subalgebra.coe_one

protected theorem coe_neg {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    {S : Subalgebra R A} (x : S) : (↑(-x) : A) = -↑x := rfl
#align subalgebra.coe_neg Subalgebra.coe_neg

protected theorem coe_sub {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    {S : Subalgebra R A} (x y : S) : (↑(x - y) : A) = ↑x - ↑y := rfl
#align subalgebra.coe_sub Subalgebra.coe_sub

@[simp, norm_cast]
theorem coe_smul [Semiring R'] [SMul R' R] [Module R' A] [IsScalarTower R' R A] (r : R') (x : S) :
    (↑(r • x) : A) = r • (x : A) := rfl
#align subalgebra.coe_smul Subalgebra.coe_smul

@[simp, norm_cast]
theorem coe_algebraMap [CommSemiring R'] [SMul R' R] [Algebra R' A] [IsScalarTower R' R A]
    (r : R') : ↑(algebraMap R' S r) = algebraMap R' A r := rfl
#align subalgebra.coe_algebra_map Subalgebra.coe_algebraMap

protected theorem coe_pow (x : S) (n : ℕ) : (↑(x ^ n) : A) = (x : A) ^ n :=
  SubmonoidClass.coe_pow x n
#align subalgebra.coe_pow Subalgebra.coe_pow

protected theorem coe_eq_zero {x : S} : (x : A) = 0 ↔ x = 0 :=
  ZeroMemClass.coe_eq_zero
#align subalgebra.coe_eq_zero Subalgebra.coe_eq_zero

protected theorem coe_eq_one {x : S} : (x : A) = 1 ↔ x = 1 :=
  OneMemClass.coe_eq_one
#align subalgebra.coe_eq_one Subalgebra.coe_eq_one

-- todo: standardize on the names these morphisms
-- compare with submodule.subtype
/-- Embedding of a subalgebra into the algebra. -/
def val : S →ₐ[R] A :=
  { toFun := ((↑) : S → A)
    map_zero' := rfl
    map_one' := rfl
    map_add' := fun _ _ ↦ rfl
    map_mul' := fun _ _ ↦ rfl
    commutes' := fun _ ↦ rfl }
#align subalgebra.val Subalgebra.val

@[simp]
theorem coe_val : (S.val : S → A) = ((↑) : S → A) := rfl
#align subalgebra.coe_val Subalgebra.coe_val

theorem val_apply (x : S) : S.val x = (x : A) := rfl
#align subalgebra.val_apply Subalgebra.val_apply

@[simp]
theorem toSubsemiring_subtype : S.toSubsemiring.subtype = (S.val : S →+* A) := rfl
#align subalgebra.to_subsemiring_subtype Subalgebra.toSubsemiring_subtype

@[simp]
theorem toSubring_subtype {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (S : Subalgebra R A) :
    S.toSubring.subtype = (S.val : S →+* A) := rfl
#align subalgebra.to_subring_subtype Subalgebra.toSubring_subtype

/-- Linear equivalence between `S : Submodule R A` and `S`. Though these types are equal,
we define it as a `LinearEquiv` to avoid type equalities. -/
def toSubmoduleEquiv (S : Subalgebra R A) : toSubmodule S ≃ₗ[R] S :=
  LinearEquiv.ofEq _ _ rfl
#align subalgebra.to_submodule_equiv Subalgebra.toSubmoduleEquiv

/-- Transport a subalgebra via an algebra homomorphism. -/
def map (f : A →ₐ[R] B) (S : Subalgebra R A) : Subalgebra R B :=
  { S.toSubsemiring.map (f : A →+* B) with
    algebraMap_mem' := fun r => f.commutes r ▸ Set.mem_image_of_mem _ (S.algebraMap_mem r) }
#align subalgebra.map Subalgebra.map

theorem map_mono {S₁ S₂ : Subalgebra R A} {f : A →ₐ[R] B} : S₁ ≤ S₂ → S₁.map f ≤ S₂.map f :=
  Set.image_subset f
#align subalgebra.map_mono Subalgebra.map_mono

theorem map_injective {f : A →ₐ[R] B} (hf : Function.Injective f) : Function.Injective (map f) :=
  fun _S₁ _S₂ ih =>
  ext <| Set.ext_iff.1 <| Set.image_injective.2 hf <| Set.ext <| SetLike.ext_iff.mp ih
#align subalgebra.map_injective Subalgebra.map_injective

@[simp]
theorem map_id (S : Subalgebra R A) : S.map (AlgHom.id R A) = S :=
  SetLike.coe_injective <| Set.image_id _
#align subalgebra.map_id Subalgebra.map_id

theorem map_map (S : Subalgebra R A) (g : B →ₐ[R] C) (f : A →ₐ[R] B) :
    (S.map f).map g = S.map (g.comp f) :=
  SetLike.coe_injective <| Set.image_image _ _ _
#align subalgebra.map_map Subalgebra.map_map

@[simp]
theorem mem_map {S : Subalgebra R A} {f : A →ₐ[R] B} {y : B} : y ∈ map f S ↔ ∃ x ∈ S, f x = y :=
  Subsemiring.mem_map
#align subalgebra.mem_map Subalgebra.mem_map

theorem map_toSubmodule {S : Subalgebra R A} {f : A →ₐ[R] B} :
    (toSubmodule $ S.map f) = S.toSubmodule.map f.toLinearMap :=
  SetLike.coe_injective rfl
#align subalgebra.map_to_submodule Subalgebra.map_toSubmodule

theorem map_toSubsemiring {S : Subalgebra R A} {f : A →ₐ[R] B} :
    (S.map f).toSubsemiring = S.toSubsemiring.map f.toRingHom :=
  SetLike.coe_injective rfl
#align subalgebra.map_to_subsemiring Subalgebra.map_toSubsemiring

@[simp]
theorem coe_map (S : Subalgebra R A) (f : A →ₐ[R] B) : (S.map f : Set B) = f '' S := rfl
#align subalgebra.coe_map Subalgebra.coe_map

/-- Preimage of a subalgebra under an algebra homomorphism. -/
def comap (f : A →ₐ[R] B) (S : Subalgebra R B) : Subalgebra R A :=
  { S.toSubsemiring.comap (f : A →+* B) with
    algebraMap_mem' := fun r =>
      show f (algebraMap R A r) ∈ S from (f.commutes r).symm ▸ S.algebraMap_mem r }
#align subalgebra.comap Subalgebra.comap

theorem map_le {S : Subalgebra R A} {f : A →ₐ[R] B} {U : Subalgebra R B} :
    map f S ≤ U ↔ S ≤ comap f U :=
  Set.image_subset_iff
#align subalgebra.map_le Subalgebra.map_le

theorem gc_map_comap (f : A →ₐ[R] B) : GaloisConnection (map f) (comap f) := fun _S _U => map_le
#align subalgebra.gc_map_comap Subalgebra.gc_map_comap

@[simp]
theorem mem_comap (S : Subalgebra R B) (f : A →ₐ[R] B) (x : A) : x ∈ S.comap f ↔ f x ∈ S :=
  Iff.rfl
#align subalgebra.mem_comap Subalgebra.mem_comap

@[simp, norm_cast]
theorem coe_comap (S : Subalgebra R B) (f : A →ₐ[R] B) : (S.comap f : Set A) = f ⁻¹' (S : Set B) :=
  rfl
#align subalgebra.coe_comap Subalgebra.coe_comap

instance noZeroDivisors {R A : Type*} [CommSemiring R] [Semiring A] [NoZeroDivisors A]
    [Algebra R A] (S : Subalgebra R A) : NoZeroDivisors S :=
  inferInstanceAs (NoZeroDivisors S.toSubsemiring)
#align subalgebra.no_zero_divisors Subalgebra.noZeroDivisors

instance isDomain {R A : Type*} [CommRing R] [Ring A] [IsDomain A] [Algebra R A]
    (S : Subalgebra R A) : IsDomain S :=
  inferInstanceAs (IsDomain S.toSubring)
#align subalgebra.is_domain Subalgebra.isDomain

end Subalgebra

namespace Submodule

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

variable (p : Submodule R A)

/-- A submodule containing `1` and closed under multiplication is a subalgebra. -/
def toSubalgebra (p : Submodule R A) (h_one : (1 : A) ∈ p)
    (h_mul : ∀ x y, x ∈ p → y ∈ p → x * y ∈ p) : Subalgebra R A :=
  { p with
    mul_mem' := fun hx hy ↦ h_mul _ _ hx hy
    one_mem' := h_one
    algebraMap_mem' := fun r => by
      rw [Algebra.algebraMap_eq_smul_one]
      -- ⊢ r • 1 ∈ { toSubmonoid := { toSubsemigroup := { carrier := p.carrier, mul_mem …
      exact p.smul_mem _ h_one }
      -- 🎉 no goals
#align submodule.to_subalgebra Submodule.toSubalgebra

@[simp]
theorem mem_toSubalgebra {p : Submodule R A} {h_one h_mul} {x} :
    x ∈ p.toSubalgebra h_one h_mul ↔ x ∈ p := Iff.rfl
#align submodule.mem_to_subalgebra Submodule.mem_toSubalgebra

@[simp]
theorem coe_toSubalgebra (p : Submodule R A) (h_one h_mul) :
    (p.toSubalgebra h_one h_mul : Set A) = p := rfl
#align submodule.coe_to_subalgebra Submodule.coe_toSubalgebra

-- Porting note: changed statement to reflect new structures
-- @[simp] -- Porting note: as a result, it is no longer a great simp lemma
theorem toSubalgebra_mk (s : Submodule R A) (h1 hmul) :
    s.toSubalgebra h1 hmul =
      Subalgebra.mk ⟨⟨⟨s, @hmul⟩, h1⟩, s.add_mem, s.zero_mem⟩
        (by intro r; rw [Algebra.algebraMap_eq_smul_one]; apply s.smul_mem _ h1) :=
            -- ⊢ ↑(algebraMap R A) r ∈ { toSubmonoid := { toSubsemigroup := { carrier := ↑s,  …
                     -- ⊢ r • 1 ∈ { toSubmonoid := { toSubsemigroup := { carrier := ↑s, mul_mem' := hm …
                                                          -- 🎉 no goals
  rfl
#align submodule.to_subalgebra_mk Submodule.toSubalgebra_mk

@[simp]
theorem toSubalgebra_toSubmodule (p : Submodule R A) (h_one h_mul) :
    Subalgebra.toSubmodule (p.toSubalgebra h_one h_mul) = p :=
  SetLike.coe_injective rfl
#align submodule.to_subalgebra_to_submodule Submodule.toSubalgebra_toSubmodule

@[simp]
theorem _root_.Subalgebra.toSubmodule_toSubalgebra (S : Subalgebra R A) :
    (S.toSubmodule.toSubalgebra S.one_mem fun _ _ => S.mul_mem) = S :=
  SetLike.coe_injective rfl
#align subalgebra.to_submodule_to_subalgebra Subalgebra.toSubmodule_toSubalgebra

end Submodule

namespace AlgHom

variable {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]

variable (φ : A →ₐ[R] B)

/-- Range of an `AlgHom` as a subalgebra. -/
protected def range (φ : A →ₐ[R] B) : Subalgebra R B :=
  { φ.toRingHom.rangeS with algebraMap_mem' := fun r => ⟨algebraMap R A r, φ.commutes r⟩ }
#align alg_hom.range AlgHom.range

@[simp]
theorem mem_range (φ : A →ₐ[R] B) {y : B} : y ∈ φ.range ↔ ∃ x, φ x = y :=
  RingHom.mem_rangeS
#align alg_hom.mem_range AlgHom.mem_range

theorem mem_range_self (φ : A →ₐ[R] B) (x : A) : φ x ∈ φ.range :=
  φ.mem_range.2 ⟨x, rfl⟩
#align alg_hom.mem_range_self AlgHom.mem_range_self

@[simp]
theorem coe_range (φ : A →ₐ[R] B) : (φ.range : Set B) = Set.range φ := by
  ext
  -- ⊢ x✝ ∈ ↑(AlgHom.range φ) ↔ x✝ ∈ Set.range ↑φ
  rw [SetLike.mem_coe, mem_range]
  -- ⊢ (∃ x, ↑φ x = x✝) ↔ x✝ ∈ Set.range ↑φ
  rfl
  -- 🎉 no goals
#align alg_hom.coe_range AlgHom.coe_range

theorem range_comp (f : A →ₐ[R] B) (g : B →ₐ[R] C) : (g.comp f).range = f.range.map g :=
  SetLike.coe_injective (Set.range_comp g f)
#align alg_hom.range_comp AlgHom.range_comp

theorem range_comp_le_range (f : A →ₐ[R] B) (g : B →ₐ[R] C) : (g.comp f).range ≤ g.range :=
  SetLike.coe_mono (Set.range_comp_subset_range f g)
#align alg_hom.range_comp_le_range AlgHom.range_comp_le_range

/-- Restrict the codomain of an algebra homomorphism. -/
def codRestrict (f : A →ₐ[R] B) (S : Subalgebra R B) (hf : ∀ x, f x ∈ S) : A →ₐ[R] S :=
  { RingHom.codRestrict (f : A →+* B) S hf with commutes' := fun r => Subtype.eq <| f.commutes r }
#align alg_hom.cod_restrict AlgHom.codRestrict

@[simp]
theorem val_comp_codRestrict (f : A →ₐ[R] B) (S : Subalgebra R B) (hf : ∀ x, f x ∈ S) :
    S.val.comp (f.codRestrict S hf) = f :=
  AlgHom.ext fun _ => rfl
#align alg_hom.val_comp_cod_restrict AlgHom.val_comp_codRestrict

@[simp]
theorem coe_codRestrict (f : A →ₐ[R] B) (S : Subalgebra R B) (hf : ∀ x, f x ∈ S) (x : A) :
    ↑(f.codRestrict S hf x) = f x :=
  rfl
#align alg_hom.coe_cod_restrict AlgHom.coe_codRestrict

theorem injective_codRestrict (f : A →ₐ[R] B) (S : Subalgebra R B) (hf : ∀ x, f x ∈ S) :
    Function.Injective (f.codRestrict S hf) ↔ Function.Injective f :=
  ⟨fun H _x _y hxy => H <| Subtype.eq hxy, fun H _x _y hxy => H (congr_arg Subtype.val hxy : _)⟩
#align alg_hom.injective_cod_restrict AlgHom.injective_codRestrict

/-- Restrict the codomain of an `AlgHom` `f` to `f.range`.

This is the bundled version of `Set.rangeFactorization`. -/
@[reducible]
def rangeRestrict (f : A →ₐ[R] B) : A →ₐ[R] f.range :=
  f.codRestrict f.range f.mem_range_self
#align alg_hom.range_restrict AlgHom.rangeRestrict

/-- The equalizer of two R-algebra homomorphisms -/
def equalizer (ϕ ψ : A →ₐ[R] B) : Subalgebra R A where
  carrier := { a | ϕ a = ψ a }
  zero_mem' := by simp only [Set.mem_setOf_eq, map_zero]
                  -- 🎉 no goals
                 -- 🎉 no goals
  one_mem' := by simp only [Set.mem_setOf_eq, map_one]
  add_mem' {x y} (hx : ϕ x = ψ x) (hy : ϕ y = ψ y) := by
    -- 🎉 no goals
    -- 🎉 no goals
    rw [Set.mem_setOf_eq, ϕ.map_add, ψ.map_add, hx, hy]
  mul_mem' {x y} (hx : ϕ x = ψ x) (hy : ϕ y = ψ y) := by
    rw [Set.mem_setOf_eq, ϕ.map_mul, ψ.map_mul, hx, hy]
  algebraMap_mem' x := by rw [Set.mem_setOf_eq, AlgHom.commutes, AlgHom.commutes]
                          -- 🎉 no goals
#align alg_hom.equalizer AlgHom.equalizer

@[simp]
theorem mem_equalizer (ϕ ψ : A →ₐ[R] B) (x : A) : x ∈ ϕ.equalizer ψ ↔ ϕ x = ψ x :=
  Iff.rfl
#align alg_hom.mem_equalizer AlgHom.mem_equalizer

/-- The range of a morphism of algebras is a fintype, if the domain is a fintype.

Note that this instance can cause a diamond with `Subtype.fintype` if `B` is also a fintype. -/
instance fintypeRange [Fintype A] [DecidableEq B] (φ : A →ₐ[R] B) : Fintype φ.range :=
  Set.fintypeRange φ
#align alg_hom.fintype_range AlgHom.fintypeRange

end AlgHom

namespace AlgEquiv

variable {R : Type u} {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

/-- Restrict an algebra homomorphism with a left inverse to an algebra isomorphism to its range.

This is a computable alternative to `AlgEquiv.ofInjective`. -/
def ofLeftInverse {g : B → A} {f : A →ₐ[R] B} (h : Function.LeftInverse g f) : A ≃ₐ[R] f.range :=
  { f.rangeRestrict with
    toFun := f.rangeRestrict
    invFun := g ∘ f.range.val
    left_inv := h
    right_inv := fun x =>
      Subtype.ext <|
        let ⟨x', hx'⟩ := f.mem_range.mp x.prop
        show f (g x) = x by rw [← hx', h x'] }
                            -- 🎉 no goals
#align alg_equiv.of_left_inverse AlgEquiv.ofLeftInverse

@[simp]
theorem ofLeftInverse_apply {g : B → A} {f : A →ₐ[R] B} (h : Function.LeftInverse g f) (x : A) :
    ↑(ofLeftInverse h x) = f x :=
  rfl
#align alg_equiv.of_left_inverse_apply AlgEquiv.ofLeftInverse_apply

@[simp]
theorem ofLeftInverse_symm_apply {g : B → A} {f : A →ₐ[R] B} (h : Function.LeftInverse g f)
    (x : f.range) : (ofLeftInverse h).symm x = g x :=
  rfl
#align alg_equiv.of_left_inverse_symm_apply AlgEquiv.ofLeftInverse_symm_apply

/-- Restrict an injective algebra homomorphism to an algebra isomorphism -/
noncomputable def ofInjective (f : A →ₐ[R] B) (hf : Function.Injective f) : A ≃ₐ[R] f.range :=
  ofLeftInverse (Classical.choose_spec hf.hasLeftInverse)
#align alg_equiv.of_injective AlgEquiv.ofInjective

@[simp]
theorem ofInjective_apply (f : A →ₐ[R] B) (hf : Function.Injective f) (x : A) :
    ↑(ofInjective f hf x) = f x :=
  rfl
#align alg_equiv.of_injective_apply AlgEquiv.ofInjective_apply

/-- Restrict an algebra homomorphism between fields to an algebra isomorphism -/
noncomputable def ofInjectiveField {E F : Type*} [DivisionRing E] [Semiring F] [Nontrivial F]
    [Algebra R E] [Algebra R F] (f : E →ₐ[R] F) : E ≃ₐ[R] f.range :=
  ofInjective f f.toRingHom.injective
#align alg_equiv.of_injective_field AlgEquiv.ofInjectiveField

/-- Given an equivalence `e : A ≃ₐ[R] B` of `R`-algebras and a subalgebra `S` of `A`,
`subalgebra_map` is the induced equivalence between `S` and `S.map e` -/
@[simps!]
def subalgebraMap (e : A ≃ₐ[R] B) (S : Subalgebra R A) : S ≃ₐ[R] S.map e.toAlgHom :=
  { e.toRingEquiv.subsemiringMap S.toSubsemiring with
    commutes' := fun r => by
      ext; dsimp only; erw [RingEquiv.subsemiringMap_apply_coe]
      -- ⊢ ↑(Equiv.toFun src✝.toEquiv (↑(algebraMap R { x // x ∈ S }) r)) = ↑(↑(algebra …
           -- ⊢ ↑(Equiv.toFun (RingEquiv.subsemiringMap (toRingEquiv e) S.toSubsemiring).toE …
                       -- ⊢ ↑(toRingEquiv e) ↑(↑(algebraMap R { x // x ∈ S }) r) = ↑(↑(algebraMap R { x  …
      exact e.commutes _ }
      -- 🎉 no goals
#align alg_equiv.subalgebra_map AlgEquiv.subalgebraMap

end AlgEquiv

namespace Algebra

variable (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

/-- The minimal subalgebra that includes `s`. -/
def adjoin (s : Set A) : Subalgebra R A :=
  { Subsemiring.closure (Set.range (algebraMap R A) ∪ s) with
    algebraMap_mem' := fun r => Subsemiring.subset_closure <| Or.inl ⟨r, rfl⟩ }
#align algebra.adjoin Algebra.adjoin

variable {R}

protected theorem gc : GaloisConnection (adjoin R : Set A → Subalgebra R A) (↑) := fun s S =>
  ⟨fun H => le_trans (le_trans (Set.subset_union_right _ _) Subsemiring.subset_closure) H,
   fun H => show Subsemiring.closure (Set.range (algebraMap R A) ∪ s) ≤ S.toSubsemiring from
      Subsemiring.closure_le.2 <| Set.union_subset S.range_subset H⟩
#align algebra.gc Algebra.gc

/-- Galois insertion between `adjoin` and `coe`. -/
protected def gi : GaloisInsertion (adjoin R : Set A → Subalgebra R A) (↑) where
  choice s hs := (adjoin R s).copy s <| le_antisymm (Algebra.gc.le_u_l s) hs
  gc := Algebra.gc
  le_l_u S := (Algebra.gc (S : Set A) (adjoin R S)).1 <| le_rfl
  choice_eq _ _ := Subalgebra.copy_eq _ _ _
#align algebra.gi Algebra.gi

instance : CompleteLattice (Subalgebra R A) :=
  GaloisInsertion.liftCompleteLattice Algebra.gi

@[simp]
theorem coe_top : (↑(⊤ : Subalgebra R A) : Set A) = Set.univ := rfl
#align algebra.coe_top Algebra.coe_top

@[simp]
theorem mem_top {x : A} : x ∈ (⊤ : Subalgebra R A) := Set.mem_univ x
#align algebra.mem_top Algebra.mem_top

@[simp]
theorem top_toSubmodule : Subalgebra.toSubmodule (⊤ : Subalgebra R A) = ⊤ := rfl
#align algebra.top_to_submodule Algebra.top_toSubmodule

@[simp]
theorem top_toSubsemiring : (⊤ : Subalgebra R A).toSubsemiring = ⊤ := rfl
#align algebra.top_to_subsemiring Algebra.top_toSubsemiring

@[simp]
theorem top_toSubring {R A : Type*} [CommRing R] [Ring A] [Algebra R A] :
    (⊤ : Subalgebra R A).toSubring = ⊤ := rfl
#align algebra.top_to_subring Algebra.top_toSubring

@[simp]
theorem toSubmodule_eq_top {S : Subalgebra R A} : Subalgebra.toSubmodule S = ⊤ ↔ S = ⊤ :=
  Subalgebra.toSubmodule.injective.eq_iff' top_toSubmodule
#align algebra.to_submodule_eq_top Algebra.toSubmodule_eq_top

@[simp]
theorem toSubsemiring_eq_top {S : Subalgebra R A} : S.toSubsemiring = ⊤ ↔ S = ⊤ :=
  Subalgebra.toSubsemiring_injective.eq_iff' top_toSubsemiring
#align algebra.to_subsemiring_eq_top Algebra.toSubsemiring_eq_top

@[simp]
theorem toSubring_eq_top {R A : Type*} [CommRing R] [Ring A] [Algebra R A] {S : Subalgebra R A} :
    S.toSubring = ⊤ ↔ S = ⊤ :=
  Subalgebra.toSubring_injective.eq_iff' top_toSubring
#align algebra.to_subring_eq_top Algebra.toSubring_eq_top

theorem mem_sup_left {S T : Subalgebra R A} : ∀ {x : A}, x ∈ S → x ∈ S ⊔ T :=
  have : S ≤ S ⊔ T := le_sup_left; (this ·) -- Porting note: need `have` instead of `show`
#align algebra.mem_sup_left Algebra.mem_sup_left

theorem mem_sup_right {S T : Subalgebra R A} : ∀ {x : A}, x ∈ T → x ∈ S ⊔ T :=
  have : T ≤ S ⊔ T := le_sup_right; (this ·) -- Porting note: need `have` instead of `show`
#align algebra.mem_sup_right Algebra.mem_sup_right

theorem mul_mem_sup {S T : Subalgebra R A} {x y : A} (hx : x ∈ S) (hy : y ∈ T) : x * y ∈ S ⊔ T :=
  (S ⊔ T).mul_mem (mem_sup_left hx) (mem_sup_right hy)
#align algebra.mul_mem_sup Algebra.mul_mem_sup

theorem map_sup (f : A →ₐ[R] B) (S T : Subalgebra R A) : (S ⊔ T).map f = S.map f ⊔ T.map f :=
  (Subalgebra.gc_map_comap f).l_sup
#align algebra.map_sup Algebra.map_sup

@[simp, norm_cast]
theorem coe_inf (S T : Subalgebra R A) : (↑(S ⊓ T) : Set A) = (S ∩ T : Set A) := rfl
#align algebra.coe_inf Algebra.coe_inf

@[simp]
theorem mem_inf {S T : Subalgebra R A} {x : A} : x ∈ S ⊓ T ↔ x ∈ S ∧ x ∈ T := Iff.rfl
#align algebra.mem_inf Algebra.mem_inf

open Subalgebra in
@[simp]
theorem inf_toSubmodule (S T : Subalgebra R A) :
    toSubmodule (S ⊓ T) = toSubmodule S ⊓ toSubmodule T := rfl
#align algebra.inf_to_submodule Algebra.inf_toSubmodule

@[simp]
theorem inf_toSubsemiring (S T : Subalgebra R A) :
    (S ⊓ T).toSubsemiring = S.toSubsemiring ⊓ T.toSubsemiring :=
  rfl
#align algebra.inf_to_subsemiring Algebra.inf_toSubsemiring

@[simp, norm_cast]
theorem coe_sInf (S : Set (Subalgebra R A)) : (↑(sInf S) : Set A) = ⋂ s ∈ S, ↑s :=
  sInf_image
#align algebra.coe_Inf Algebra.coe_sInf

theorem mem_sInf {S : Set (Subalgebra R A)} {x : A} : x ∈ sInf S ↔ ∀ p ∈ S, x ∈ p := by
  simp only [← SetLike.mem_coe, coe_sInf, Set.mem_iInter₂]
  -- 🎉 no goals
#align algebra.mem_Inf Algebra.mem_sInf

@[simp]
theorem sInf_toSubmodule (S : Set (Subalgebra R A)) :
    Subalgebra.toSubmodule (sInf S) = sInf (Subalgebra.toSubmodule '' S) :=
  SetLike.coe_injective <| by simp
                              -- 🎉 no goals
#align algebra.Inf_to_submodule Algebra.sInf_toSubmodule

@[simp]
theorem sInf_toSubsemiring (S : Set (Subalgebra R A)) :
    (sInf S).toSubsemiring = sInf (Subalgebra.toSubsemiring '' S) :=
  SetLike.coe_injective <| by simp
                              -- 🎉 no goals
#align algebra.Inf_to_subsemiring Algebra.sInf_toSubsemiring

@[simp, norm_cast]
theorem coe_iInf {ι : Sort*} {S : ι → Subalgebra R A} : (↑(⨅ i, S i) : Set A) = ⋂ i, S i := by
  simp [iInf]
  -- 🎉 no goals
#align algebra.coe_infi Algebra.coe_iInf

theorem mem_iInf {ι : Sort*} {S : ι → Subalgebra R A} {x : A} : (x ∈ ⨅ i, S i) ↔ ∀ i, x ∈ S i := by
  simp only [iInf, mem_sInf, Set.forall_range_iff]
  -- 🎉 no goals
#align algebra.mem_infi Algebra.mem_iInf

open Subalgebra in
@[simp]
theorem iInf_toSubmodule {ι : Sort*} (S : ι → Subalgebra R A) :
    toSubmodule (⨅ i, S i) = ⨅ i, toSubmodule (S i) :=
  SetLike.coe_injective <| by simp
                              -- 🎉 no goals
#align algebra.infi_to_submodule Algebra.iInf_toSubmodule

instance : Inhabited (Subalgebra R A) := ⟨⊥⟩

theorem mem_bot {x : A} : x ∈ (⊥ : Subalgebra R A) ↔ x ∈ Set.range (algebraMap R A) :=
  suffices (ofId R A).range = (⊥ : Subalgebra R A) by
    rw [← this, ← SetLike.mem_coe, AlgHom.coe_range]
    -- ⊢ x ∈ Set.range ↑(ofId R A) ↔ x ∈ Set.range ↑(algebraMap R A)
    rfl
    -- 🎉 no goals
  le_bot_iff.mp fun x hx => Subalgebra.range_le _ ((ofId R A).coe_range ▸ hx)
#align algebra.mem_bot Algebra.mem_bot

theorem toSubmodule_bot : Subalgebra.toSubmodule (⊥ : Subalgebra R A) = R ∙ 1 := by
  ext x
  -- ⊢ x ∈ ↑Subalgebra.toSubmodule ⊥ ↔ x ∈ Submodule.span R {1}
  simp [mem_bot, Submodule.mem_span_singleton, Algebra.smul_def]
  -- 🎉 no goals
#align algebra.to_submodule_bot Algebra.toSubmodule_bot

@[simp]
theorem coe_bot : ((⊥ : Subalgebra R A) : Set A) = Set.range (algebraMap R A) := by
  simp [Set.ext_iff, Algebra.mem_bot]
  -- 🎉 no goals
#align algebra.coe_bot Algebra.coe_bot

theorem eq_top_iff {S : Subalgebra R A} : S = ⊤ ↔ ∀ x : A, x ∈ S :=
  ⟨fun h x => by rw [h]; exact mem_top, fun h => by
                 -- ⊢ x ∈ ⊤
                         -- 🎉 no goals
    ext x; exact ⟨fun _ => mem_top, fun _ => h x⟩⟩
    -- ⊢ x ∈ S ↔ x ∈ ⊤
           -- 🎉 no goals
#align algebra.eq_top_iff Algebra.eq_top_iff

theorem range_top_iff_surjective (f : A →ₐ[R] B) :
    f.range = (⊤ : Subalgebra R B) ↔ Function.Surjective f :=
  Algebra.eq_top_iff
#align algebra.range_top_iff_surjective Algebra.range_top_iff_surjective

@[simp]
theorem range_id : (AlgHom.id R A).range = ⊤ :=
  SetLike.coe_injective Set.range_id
#align algebra.range_id Algebra.range_id

@[simp]
theorem map_top (f : A →ₐ[R] B) : (⊤ : Subalgebra R A).map f = f.range :=
  SetLike.coe_injective Set.image_univ
#align algebra.map_top Algebra.map_top

@[simp]
theorem map_bot (f : A →ₐ[R] B) : (⊥ : Subalgebra R A).map f = ⊥ :=
  SetLike.coe_injective <| by
    simp only [← Set.range_comp, (· ∘ ·), Algebra.coe_bot, Subalgebra.coe_map, f.commutes]
    -- 🎉 no goals
#align algebra.map_bot Algebra.map_bot

@[simp]
theorem comap_top (f : A →ₐ[R] B) : (⊤ : Subalgebra R B).comap f = ⊤ :=
  eq_top_iff.2 fun _x => mem_top
#align algebra.comap_top Algebra.comap_top

/-- `AlgHom` to `⊤ : Subalgebra R A`. -/
def toTop : A →ₐ[R] (⊤ : Subalgebra R A) :=
  (AlgHom.id R A).codRestrict ⊤ fun _ => mem_top
#align algebra.to_top Algebra.toTop

theorem surjective_algebraMap_iff :
    Function.Surjective (algebraMap R A) ↔ (⊤ : Subalgebra R A) = ⊥ :=
  ⟨fun h =>
    eq_bot_iff.2 fun y _ =>
      let ⟨_x, hx⟩ := h y
      hx ▸ Subalgebra.algebraMap_mem _ _,
    fun h y => Algebra.mem_bot.1 <| eq_bot_iff.1 h (Algebra.mem_top : y ∈ _)⟩
#align algebra.surjective_algebra_map_iff Algebra.surjective_algebraMap_iff

theorem bijective_algebraMap_iff {R A : Type*} [Field R] [Semiring A] [Nontrivial A]
    [Algebra R A] : Function.Bijective (algebraMap R A) ↔ (⊤ : Subalgebra R A) = ⊥ :=
  ⟨fun h => surjective_algebraMap_iff.1 h.2, fun h =>
    ⟨(algebraMap R A).injective, surjective_algebraMap_iff.2 h⟩⟩
#align algebra.bijective_algebra_map_iff Algebra.bijective_algebraMap_iff

/-- The bottom subalgebra is isomorphic to the base ring. -/
noncomputable def botEquivOfInjective (h : Function.Injective (algebraMap R A)) :
    (⊥ : Subalgebra R A) ≃ₐ[R] R :=
  AlgEquiv.symm <|
    AlgEquiv.ofBijective (Algebra.ofId R _)
      ⟨fun _x _y hxy => h (congr_arg Subtype.val hxy : _), fun ⟨_y, hy⟩ =>
        let ⟨x, hx⟩ := Algebra.mem_bot.1 hy
        ⟨x, Subtype.eq hx⟩⟩
#align algebra.bot_equiv_of_injective Algebra.botEquivOfInjective

/-- The bottom subalgebra is isomorphic to the field. -/
@[simps! symm_apply]
noncomputable def botEquiv (F R : Type*) [Field F] [Semiring R] [Nontrivial R] [Algebra F R] :
    (⊥ : Subalgebra F R) ≃ₐ[F] F :=
  botEquivOfInjective (RingHom.injective _)
#align algebra.bot_equiv Algebra.botEquiv

end Algebra

namespace Subalgebra

open Algebra

variable {R : Type u} {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

variable (S : Subalgebra R A)

/-- The top subalgebra is isomorphic to the algebra.

This is the algebra version of `Submodule.topEquiv`. -/
@[simps!]
def topEquiv : (⊤ : Subalgebra R A) ≃ₐ[R] A :=
  AlgEquiv.ofAlgHom (Subalgebra.val ⊤) toTop rfl <| AlgHom.ext fun _ => Subtype.ext rfl
#align subalgebra.top_equiv Subalgebra.topEquiv

instance subsingleton_of_subsingleton [Subsingleton A] : Subsingleton (Subalgebra R A) :=
  ⟨fun B C => ext fun x => by simp only [Subsingleton.elim x 0, zero_mem B, zero_mem C]⟩
                              -- 🎉 no goals
#align subalgebra.subsingleton_of_subsingleton Subalgebra.subsingleton_of_subsingleton

instance _root_.AlgHom.subsingleton [Subsingleton (Subalgebra R A)] : Subsingleton (A →ₐ[R] B) :=
  ⟨fun f g =>
    AlgHom.ext fun a =>
      have : a ∈ (⊥ : Subalgebra R A) := Subsingleton.elim (⊤ : Subalgebra R A) ⊥ ▸ mem_top
      let ⟨_x, hx⟩ := Set.mem_range.mp (mem_bot.mp this)
      hx ▸ (f.commutes _).trans (g.commutes _).symm⟩
#align alg_hom.subsingleton AlgHom.subsingleton

instance _root_.AlgEquiv.subsingleton_left [Subsingleton (Subalgebra R A)] :
    Subsingleton (A ≃ₐ[R] B) :=
  ⟨fun f g => AlgEquiv.ext fun x => AlgHom.ext_iff.mp (Subsingleton.elim f.toAlgHom g.toAlgHom) x⟩
#align alg_equiv.subsingleton_left AlgEquiv.subsingleton_left

instance _root_.AlgEquiv.subsingleton_right [Subsingleton (Subalgebra R B)] :
    Subsingleton (A ≃ₐ[R] B) :=
  ⟨fun f g => by rw [← f.symm_symm, Subsingleton.elim f.symm g.symm, g.symm_symm]⟩
                 -- 🎉 no goals
#align alg_equiv.subsingleton_right AlgEquiv.subsingleton_right

theorem range_val : S.val.range = S :=
  ext <| Set.ext_iff.1 <| S.val.coe_range.trans Subtype.range_val
#align subalgebra.range_val Subalgebra.range_val

instance : Unique (Subalgebra R R) :=
  { inferInstanceAs (Inhabited (Subalgebra R R)) with
    uniq := by
      intro S
      -- ⊢ S = default
      refine' le_antisymm ?_ bot_le
      -- ⊢ S ≤ default
      intro _ _
      -- ⊢ x✝ ∈ default
      simp only [Set.mem_range, mem_bot, id.map_eq_self, exists_apply_eq_apply, default] }
      -- 🎉 no goals

/-- The map `S → T` when `S` is a subalgebra contained in the subalgebra `T`.

This is the subalgebra version of `Submodule.ofLe`, or `Subring.inclusion`  -/
def inclusion {S T : Subalgebra R A} (h : S ≤ T) : S →ₐ[R] T
    where
  toFun := Set.inclusion h
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  commutes' _ := rfl
#align subalgebra.inclusion Subalgebra.inclusion

theorem inclusion_injective {S T : Subalgebra R A} (h : S ≤ T) : Function.Injective (inclusion h) :=
  fun _ _ => Subtype.ext ∘ Subtype.mk.inj
#align subalgebra.inclusion_injective Subalgebra.inclusion_injective

@[simp]
theorem inclusion_self {S : Subalgebra R A} : inclusion (le_refl S) = AlgHom.id R S :=
  AlgHom.ext fun _x => Subtype.ext rfl
#align subalgebra.inclusion_self Subalgebra.inclusion_self

@[simp]
theorem inclusion_mk {S T : Subalgebra R A} (h : S ≤ T) (x : A) (hx : x ∈ S) :
    inclusion h ⟨x, hx⟩ = ⟨x, h hx⟩ :=
  rfl
#align subalgebra.inclusion_mk Subalgebra.inclusion_mk

theorem inclusion_right {S T : Subalgebra R A} (h : S ≤ T) (x : T) (m : (x : A) ∈ S) :
    inclusion h ⟨x, m⟩ = x :=
  Subtype.ext rfl
#align subalgebra.inclusion_right Subalgebra.inclusion_right

@[simp]
theorem inclusion_inclusion {S T U : Subalgebra R A} (hst : S ≤ T) (htu : T ≤ U) (x : S) :
    inclusion htu (inclusion hst x) = inclusion (le_trans hst htu) x :=
  Subtype.ext rfl
#align subalgebra.inclusion_inclusion Subalgebra.inclusion_inclusion

@[simp]
theorem coe_inclusion {S T : Subalgebra R A} (h : S ≤ T) (s : S) : (inclusion h s : A) = s :=
  rfl
#align subalgebra.coe_inclusion Subalgebra.coe_inclusion

/-- Two subalgebras that are equal are also equivalent as algebras.

This is the `Subalgebra` version of `LinearEquiv.ofEq` and `Equiv.Set.ofEq`. -/
@[simps apply]
def equivOfEq (S T : Subalgebra R A) (h : S = T) : S ≃ₐ[R] T :=
  { LinearEquiv.ofEq _ _ (congr_arg toSubmodule h) with
    toFun := fun x => ⟨x, h ▸ x.2⟩
    invFun := fun x => ⟨x, h.symm ▸ x.2⟩
    map_mul' := fun _ _ => rfl
    commutes' := fun _ => rfl }
#align subalgebra.equiv_of_eq Subalgebra.equivOfEq

@[simp]
theorem equivOfEq_symm (S T : Subalgebra R A) (h : S = T) :
    (equivOfEq S T h).symm = equivOfEq T S h.symm := rfl
#align subalgebra.equiv_of_eq_symm Subalgebra.equivOfEq_symm

@[simp]
theorem equivOfEq_rfl (S : Subalgebra R A) : equivOfEq S S rfl = AlgEquiv.refl := by ext; rfl
                                                                                     -- ⊢ ↑(↑(equivOfEq S S (_ : S = S)) a✝) = ↑(↑AlgEquiv.refl a✝)
                                                                                          -- 🎉 no goals
#align subalgebra.equiv_of_eq_rfl Subalgebra.equivOfEq_rfl

@[simp]
theorem equivOfEq_trans (S T U : Subalgebra R A) (hST : S = T) (hTU : T = U) :
    (equivOfEq S T hST).trans (equivOfEq T U hTU) = equivOfEq S U (hST.trans hTU) := rfl
#align subalgebra.equiv_of_eq_trans Subalgebra.equivOfEq_trans

section Prod

variable (S₁ : Subalgebra R B)

/-- The product of two subalgebras is a subalgebra. -/
def prod : Subalgebra R (A × B) :=
  { S.toSubsemiring.prod S₁.toSubsemiring with
    carrier := S ×ˢ S₁
    algebraMap_mem' := fun _ => ⟨algebraMap_mem _ _, algebraMap_mem _ _⟩ }
#align subalgebra.prod Subalgebra.prod

@[simp]
theorem coe_prod : (prod S S₁ : Set (A × B)) = (S : Set A) ×ˢ (S₁ : Set B) :=
  rfl
#align subalgebra.coe_prod Subalgebra.coe_prod

open Subalgebra in
theorem prod_toSubmodule : toSubmodule (S.prod S₁) = (toSubmodule S).prod (toSubmodule S₁) := rfl
#align subalgebra.prod_to_submodule Subalgebra.prod_toSubmodule

@[simp]
theorem mem_prod {S : Subalgebra R A} {S₁ : Subalgebra R B} {x : A × B} :
    x ∈ prod S S₁ ↔ x.1 ∈ S ∧ x.2 ∈ S₁ := Set.mem_prod
#align subalgebra.mem_prod Subalgebra.mem_prod

@[simp]
theorem prod_top : (prod ⊤ ⊤ : Subalgebra R (A × B)) = ⊤ := by ext; simp
                                                               -- ⊢ x✝ ∈ prod ⊤ ⊤ ↔ x✝ ∈ ⊤
                                                                    -- 🎉 no goals
#align subalgebra.prod_top Subalgebra.prod_top

theorem prod_mono {S T : Subalgebra R A} {S₁ T₁ : Subalgebra R B} :
    S ≤ T → S₁ ≤ T₁ → prod S S₁ ≤ prod T T₁ :=
  Set.prod_mono
#align subalgebra.prod_mono Subalgebra.prod_mono

@[simp]
theorem prod_inf_prod {S T : Subalgebra R A} {S₁ T₁ : Subalgebra R B} :
    S.prod S₁ ⊓ T.prod T₁ = (S ⊓ T).prod (S₁ ⊓ T₁) :=
  SetLike.coe_injective Set.prod_inter_prod
#align subalgebra.prod_inf_prod Subalgebra.prod_inf_prod

end Prod

section SuprLift

variable {ι : Type*}

theorem coe_iSup_of_directed [Nonempty ι] {S : ι → Subalgebra R A} (dir : Directed (· ≤ ·) S) :
    ↑(iSup S) = ⋃ i, (S i : Set A) :=
  -- Porting note: moved up the `let i` to use it in `zero_mem'` and `one_mem'`
  let i := @Nonempty.some ι inferInstance
  let K : Subalgebra R A :=
    { carrier := ⋃ i, S i
      -- Porting note: auto_params failing, need to provide these explicitly
      zero_mem' := by simp only [Set.mem_iUnion, SetLike.mem_coe]; exact ⟨i, zero_mem _⟩
                      -- ⊢ ∃ i, 0 ∈ S i
                     -- ⊢ ∃ i, 1 ∈ S i
                                                                  -- 🎉 no goals
                                                                   -- 🎉 no goals
      one_mem' := by simp only [Set.mem_iUnion, SetLike.mem_coe]; exact ⟨i, one_mem _⟩
      mul_mem' := fun hx hy =>
        let ⟨i, hi⟩ := Set.mem_iUnion.1 hx
        let ⟨j, hj⟩ := Set.mem_iUnion.1 hy
        let ⟨k, hik, hjk⟩ := dir i j
        Set.mem_iUnion.2 ⟨k, Subalgebra.mul_mem (S k) (hik hi) (hjk hj)⟩
      add_mem' := fun hx hy =>
        let ⟨i, hi⟩ := Set.mem_iUnion.1 hx
        let ⟨j, hj⟩ := Set.mem_iUnion.1 hy
        let ⟨k, hik, hjk⟩ := dir i j
        Set.mem_iUnion.2 ⟨k, Subalgebra.add_mem (S k) (hik hi) (hjk hj)⟩
      algebraMap_mem' := fun _ ↦
        Set.mem_iUnion.2 ⟨i, Subalgebra.algebraMap_mem _ _⟩ }
  have : iSup S = K :=
    le_antisymm (iSup_le fun i => Set.subset_iUnion (fun i => (↑(S i) : Set A)) i)
      (SetLike.coe_subset_coe.1 (Set.iUnion_subset fun i => SetLike.coe_subset_coe.2 (le_iSup _ _)))
  this.symm ▸ rfl
#align subalgebra.coe_supr_of_directed Subalgebra.coe_iSup_of_directed

-- Porting note: TODO: turn `hT` into an assumption `T ≤ iSup K`. That's what `Set.iUnionLift` needs
-- Porting note: the proofs of `map_{zero,one,add,mul}` got a bit uglier, probably unification trbls
/-- Define an algebra homomorphism on a directed supremum of subalgebras by defining
it on each subalgebra, and proving that it agrees on the intersection of subalgebras. -/
noncomputable def iSupLift [Nonempty ι] (K : ι → Subalgebra R A) (dir : Directed (· ≤ ·) K)
    (f : ∀ i, K i →ₐ[R] B) (hf : ∀ (i j : ι) (h : K i ≤ K j), f i = (f j).comp (inclusion h))
    (T : Subalgebra R A) (hT : T = iSup K) : ↥T →ₐ[R] B :=
  { toFun := Set.iUnionLift (fun i => ↑(K i)) (fun i x => f i x)
        (fun i j x hxi hxj => by
          let ⟨k, hik, hjk⟩ := dir i j
          -- ⊢ (fun i x => ↑(f i) x) i { val := x, property := hxi } = (fun i x => ↑(f i) x …
          dsimp
          -- ⊢ ↑(f i) { val := x, property := hxi } = ↑(f j) { val := x, property := hxj }
          rw [hf i k hik, hf j k hjk]
          -- ⊢ ↑(AlgHom.comp (f k) (inclusion hik)) { val := x, property := hxi } = ↑(AlgHo …
          rfl)
          -- 🎉 no goals
        T (by rw [hT, coe_iSup_of_directed dir])
              -- 🎉 no goals
    map_one' := by apply Set.iUnionLift_const _ (fun _ => 1) <;> simp
                   -- ⊢ ∀ (i : ι), ↑1 = ↑1
                                                                 -- 🎉 no goals
                                                                 -- 🎉 no goals
    map_zero' := by dsimp; apply Set.iUnionLift_const _ (fun _ => 0) <;> simp
                    -- ⊢ Set.iUnionLift (fun i => ↑(K i)) (fun i x => ↑(f i) x) (_ : ∀ (i j : ι) (x : …
                           -- ⊢ ∀ (i : ι), ↑0 = ↑0
      -- ⊢ ∀ (x y : { x // x ∈ iSup K }), OneHom.toFun { toFun := Set.iUnionLift (fun i …
                -- ⊢ ∀ (x y : { x // x ∈ iSup K }), Set.iUnionLift (fun i => ↑(K i)) (fun i x =>  …
                                                                         -- 🎉 no goals
                                                                         -- 🎉 no goals
      -- ⊢ ∀ (i : ι) (x y : ↑↑(K i)), Set.inclusion (_ : ↑(K i) ⊆ ↑(iSup K)) (x * y) =  …
      -- ⊢ ∀ (i : ι) (x y : ↑↑(K i)), Set.inclusion (_ : ↑(K i) ⊆ ↑(iSup K)) (x * y) =  …
    map_mul' := by
      -- 🎉 no goals
      subst hT; dsimp
      apply Set.iUnionLift_binary (coe_iSup_of_directed dir) dir _ (fun _ => (· * ·))
      on_goal 3 => rw [coe_iSup_of_directed dir]
      all_goals simp
    map_add' := by
      subst hT; dsimp
      -- ⊢ ∀ (x y : { x // x ∈ iSup K }), OneHom.toFun (↑{ toOneHom := { toFun := Set.i …
                -- ⊢ ∀ (x y : { x // x ∈ iSup K }), Set.iUnionLift (fun i => ↑(K i)) (fun i x =>  …
      apply Set.iUnionLift_binary (coe_iSup_of_directed dir) dir _ (fun _ => (· + ·))
      on_goal 3 => rw [coe_iSup_of_directed dir]
      -- ⊢ ∀ (i : ι) (x y : ↑↑(K i)), Set.inclusion (_ : ↑(K i) ⊆ ↑(iSup K)) (x + y) =  …
      -- ⊢ ∀ (i : ι) (x y : ↑↑(K i)), Set.inclusion (_ : ↑(K i) ⊆ ↑(iSup K)) (x + y) =  …
      all_goals simp
      -- 🎉 no goals
    commutes' := fun r => by
      dsimp
      -- ⊢ Set.iUnionLift (fun i => ↑(K i)) (fun i x => ↑(f i) x) (_ : ∀ (i j : ι) (x : …
      apply Set.iUnionLift_const _ (fun _ => algebraMap R _ r) <;> simp }
      -- ⊢ ∀ (i : ι), ↑(↑(algebraMap R ↑↑(K i)) r) = ↑(↑(algebraMap R { x // x ∈ T }) r)
                                                                   -- 🎉 no goals
                                                                   -- 🎉 no goals
#align subalgebra.supr_lift Subalgebra.iSupLift

variable [Nonempty ι] {K : ι → Subalgebra R A} {dir : Directed (· ≤ ·) K} {f : ∀ i, K i →ₐ[R] B}
  {hf : ∀ (i j : ι) (h : K i ≤ K j), f i = (f j).comp (inclusion h)} {T : Subalgebra R A}
  {hT : T = iSup K}

@[simp]
theorem iSupLift_inclusion {i : ι} (x : K i) (h : K i ≤ T) :
    iSupLift K dir f hf T hT (inclusion h x) = f i x := by
  dsimp [iSupLift, inclusion]
  -- ⊢ Set.iUnionLift (fun i => ↑(K i)) (fun i x => ↑(f i) x) (_ : ∀ (i j : ι) (x : …
  rw [Set.iUnionLift_inclusion]
  -- 🎉 no goals
#align subalgebra.supr_lift_inclusion Subalgebra.iSupLift_inclusion

@[simp]
theorem iSupLift_comp_inclusion {i : ι} (h : K i ≤ T) :
    (iSupLift K dir f hf T hT).comp (inclusion h) = f i := by ext; simp
                                                              -- ⊢ ↑(AlgHom.comp (iSupLift K dir f hf T hT) (inclusion h)) x✝ = ↑(f i) x✝
                                                                   -- 🎉 no goals
#align subalgebra.supr_lift_comp_inclusion Subalgebra.iSupLift_comp_inclusion

@[simp]
theorem iSupLift_mk {i : ι} (x : K i) (hx : (x : A) ∈ T) :
    iSupLift K dir f hf T hT ⟨x, hx⟩ = f i x := by
  dsimp [iSupLift, inclusion]
  -- ⊢ Set.iUnionLift (fun i => ↑(K i)) (fun i x => ↑(f i) x) (_ : ∀ (i j : ι) (x : …
  rw [Set.iUnionLift_mk]
  -- 🎉 no goals
#align subalgebra.supr_lift_mk Subalgebra.iSupLift_mk

theorem iSupLift_of_mem {i : ι} (x : T) (hx : (x : A) ∈ K i) :
    iSupLift K dir f hf T hT x = f i ⟨x, hx⟩ := by
  dsimp [iSupLift, inclusion]
  -- ⊢ Set.iUnionLift (fun i => ↑(K i)) (fun i x => ↑(f i) x) (_ : ∀ (i j : ι) (x : …
  rw [Set.iUnionLift_of_mem]
  -- 🎉 no goals
#align subalgebra.supr_lift_of_mem Subalgebra.iSupLift_of_mem

end SuprLift

/-! ## Actions by `Subalgebra`s

These are just copies of the definitions about `Subsemiring` starting from
`Subring.mulAction`.
-/


section Actions

variable {α β : Type*}

/-- The action by a subalgebra is the action by the underlying algebra. -/
instance [SMul A α] (S : Subalgebra R A) : SMul S α :=
  inferInstanceAs (SMul S.toSubsemiring α)

theorem smul_def [SMul A α] {S : Subalgebra R A} (g : S) (m : α) : g • m = (g : A) • m := rfl
#align subalgebra.smul_def Subalgebra.smul_def

instance smulCommClass_left [SMul A β] [SMul α β] [SMulCommClass A α β] (S : Subalgebra R A) :
    SMulCommClass S α β :=
  S.toSubsemiring.smulCommClass_left
#align subalgebra.smul_comm_class_left Subalgebra.smulCommClass_left

instance smulCommClass_right [SMul α β] [SMul A β] [SMulCommClass α A β] (S : Subalgebra R A) :
    SMulCommClass α S β :=
  S.toSubsemiring.smulCommClass_right
#align subalgebra.smul_comm_class_right Subalgebra.smulCommClass_right

/-- Note that this provides `IsScalarTower S R R` which is needed by `smul_mul_assoc`. -/
instance isScalarTower_left [SMul α β] [SMul A α] [SMul A β] [IsScalarTower A α β]
    (S : Subalgebra R A) : IsScalarTower S α β :=
  inferInstanceAs (IsScalarTower S.toSubsemiring α β)
#align subalgebra.is_scalar_tower_left Subalgebra.isScalarTower_left

instance isScalarTower_mid {R S T : Type*} [CommSemiring R] [Semiring S] [AddCommMonoid T]
    [Algebra R S] [Module R T] [Module S T] [IsScalarTower R S T] (S' : Subalgebra R S) :
    IsScalarTower R S' T :=
  ⟨fun _x y _z => (smul_assoc _ (y : S) _ : _)⟩
#align subalgebra.is_scalar_tower_mid Subalgebra.isScalarTower_mid

instance [SMul A α] [FaithfulSMul A α] (S : Subalgebra R A) : FaithfulSMul S α :=
  inferInstanceAs (FaithfulSMul S.toSubsemiring α)

/-- The action by a subalgebra is the action by the underlying algebra. -/
instance [MulAction A α] (S : Subalgebra R A) : MulAction S α :=
  inferInstanceAs (MulAction S.toSubsemiring α)

/-- The action by a subalgebra is the action by the underlying algebra. -/
instance [AddMonoid α] [DistribMulAction A α] (S : Subalgebra R A) : DistribMulAction S α :=
  inferInstanceAs (DistribMulAction S.toSubsemiring α)

/-- The action by a subalgebra is the action by the underlying algebra. -/
instance [Zero α] [SMulWithZero A α] (S : Subalgebra R A) : SMulWithZero S α :=
  inferInstanceAs (SMulWithZero S.toSubsemiring α)

/-- The action by a subalgebra is the action by the underlying algebra. -/
instance [Zero α] [MulActionWithZero A α] (S : Subalgebra R A) : MulActionWithZero S α :=
  inferInstanceAs (MulActionWithZero S.toSubsemiring α)

/-- The action by a subalgebra is the action by the underlying algebra. -/
instance moduleLeft [AddCommMonoid α] [Module A α] (S : Subalgebra R A) : Module S α :=
  inferInstanceAs (Module S.toSubsemiring α)
#align subalgebra.module_left Subalgebra.moduleLeft

/-- The action by a subalgebra is the action by the underlying algebra. -/
instance toAlgebra {R A : Type*} [CommSemiring R] [CommSemiring A] [Semiring α] [Algebra R A]
    [Algebra A α] (S : Subalgebra R A) : Algebra S α :=
  Algebra.ofSubsemiring S.toSubsemiring
#align subalgebra.to_algebra Subalgebra.toAlgebra

theorem algebraMap_eq {R A : Type*} [CommSemiring R] [CommSemiring A] [Semiring α] [Algebra R A]
    [Algebra A α] (S : Subalgebra R A) : algebraMap S α = (algebraMap A α).comp S.val :=
  rfl
#align subalgebra.algebra_map_eq Subalgebra.algebraMap_eq

@[simp]
theorem rangeS_algebraMap {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
    (S : Subalgebra R A) : (algebraMap S A).rangeS = S.toSubsemiring := by
  rw [algebraMap_eq, Algebra.id.map_eq_id, RingHom.id_comp, ← toSubsemiring_subtype,
    Subsemiring.rangeS_subtype]
#align subalgebra.srange_algebra_map Subalgebra.rangeS_algebraMap

@[simp]
theorem range_algebraMap {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (S : Subalgebra R A) : (algebraMap S A).range = S.toSubring := by
  rw [algebraMap_eq, Algebra.id.map_eq_id, RingHom.id_comp, ← toSubring_subtype,
    Subring.range_subtype]
#align subalgebra.range_algebra_map Subalgebra.range_algebraMap

instance noZeroSMulDivisors_top [NoZeroDivisors A] (S : Subalgebra R A) : NoZeroSMulDivisors S A :=
  ⟨fun {c} x h =>
    have : (c : A) = 0 ∨ x = 0 := eq_zero_or_eq_zero_of_mul_eq_zero h
    this.imp_left (@Subtype.ext_iff _ _ c 0).mpr⟩
#align subalgebra.no_zero_smul_divisors_top Subalgebra.noZeroSMulDivisors_top

end Actions

section Center

theorem _root_.Set.algebraMap_mem_center (r : R) : algebraMap R A r ∈ Set.center A := by
  simp [Algebra.commutes, Set.mem_center_iff]
  -- 🎉 no goals
#align set.algebra_map_mem_center Set.algebraMap_mem_center

variable (R A)

/-- The center of an algebra is the set of elements which commute with every element. They form a
subalgebra. -/
def center : Subalgebra R A :=
  { Subsemiring.center A with algebraMap_mem' := Set.algebraMap_mem_center }
#align subalgebra.center Subalgebra.center

theorem coe_center : (center R A : Set A) = Set.center A :=
  rfl
#align subalgebra.coe_center Subalgebra.coe_center

@[simp]
theorem center_toSubsemiring : (center R A).toSubsemiring = Subsemiring.center A :=
  rfl
#align subalgebra.center_to_subsemiring Subalgebra.center_toSubsemiring

@[simp]
theorem center_toSubring (R A : Type*) [CommRing R] [Ring A] [Algebra R A] :
    (center R A).toSubring = Subring.center A :=
  rfl
#align subalgebra.center_to_subring Subalgebra.center_toSubring

@[simp]
theorem center_eq_top (A : Type*) [CommSemiring A] [Algebra R A] : center R A = ⊤ :=
  SetLike.coe_injective (Set.center_eq_univ A)
#align subalgebra.center_eq_top Subalgebra.center_eq_top

variable {R A}

instance : CommSemiring (center R A) :=
  inferInstanceAs (CommSemiring (Subsemiring.center A))

instance {A : Type*} [Ring A] [Algebra R A] : CommRing (center R A) :=
  inferInstanceAs (CommRing (Subring.center A))

theorem mem_center_iff {a : A} : a ∈ center R A ↔ ∀ b : A, b * a = a * b :=
  Iff.rfl
#align subalgebra.mem_center_iff Subalgebra.mem_center_iff

end Center

section Centralizer

@[simp]
theorem _root_.Set.algebraMap_mem_centralizer {s : Set A} (r : R) :
    algebraMap R A r ∈ s.centralizer :=
  fun _a _h => (Algebra.commutes _ _).symm
#align set.algebra_map_mem_centralizer Set.algebraMap_mem_centralizer

variable (R)

/-- The centralizer of a set as a subalgebra. -/
def centralizer (s : Set A) : Subalgebra R A :=
  { Subsemiring.centralizer s with algebraMap_mem' := Set.algebraMap_mem_centralizer }
#align subalgebra.centralizer Subalgebra.centralizer

@[simp, norm_cast]
theorem coe_centralizer (s : Set A) : (centralizer R s : Set A) = s.centralizer :=
  rfl
#align subalgebra.coe_centralizer Subalgebra.coe_centralizer

theorem mem_centralizer_iff {s : Set A} {z : A} : z ∈ centralizer R s ↔ ∀ g ∈ s, g * z = z * g :=
  Iff.rfl
#align subalgebra.mem_centralizer_iff Subalgebra.mem_centralizer_iff

theorem center_le_centralizer (s) : center R A ≤ centralizer R s :=
  s.center_subset_centralizer
#align subalgebra.center_le_centralizer Subalgebra.center_le_centralizer

theorem centralizer_le (s t : Set A) (h : s ⊆ t) : centralizer R t ≤ centralizer R s :=
  Set.centralizer_subset h
#align subalgebra.centralizer_le Subalgebra.centralizer_le

@[simp]
theorem centralizer_eq_top_iff_subset {s : Set A} : centralizer R s = ⊤ ↔ s ⊆ center R A :=
  SetLike.ext'_iff.trans Set.centralizer_eq_top_iff_subset
#align subalgebra.centralizer_eq_top_iff_subset Subalgebra.centralizer_eq_top_iff_subset

@[simp]
theorem centralizer_univ : centralizer R Set.univ = center R A :=
  SetLike.ext' (Set.centralizer_univ A)
#align subalgebra.centralizer_univ Subalgebra.centralizer_univ

end Centralizer

/-- Suppose we are given `∑ i, lᵢ * sᵢ = 1` in `S`, and `S'` a subalgebra of `S` that contains
`lᵢ` and `sᵢ`. To check that an `x : S` falls in `S'`, we only need to show that
`sᵢ ^ n • x ∈ S'` for some `n` for each `sᵢ`. -/
theorem mem_of_finset_sum_eq_one_of_pow_smul_mem {S : Type*} [CommRing S] [Algebra R S]
    (S' : Subalgebra R S) {ι : Type*} (ι' : Finset ι) (s : ι → S) (l : ι → S)
    (e : ∑ i in ι', l i * s i = 1) (hs : ∀ i, s i ∈ S') (hl : ∀ i, l i ∈ S') (x : S)
    (H : ∀ i, ∃ n : ℕ, (s i ^ n : S) • x ∈ S') : x ∈ S' := by
  -- Porting note: needed to add this instance
  let _i : Algebra { x // x ∈ S' } { x // x ∈ S' } := Algebra.id _
  -- ⊢ x ∈ S'
  suffices x ∈ Subalgebra.toSubmodule (Algebra.ofId S' S).range by
    obtain ⟨x, rfl⟩ := this
    exact x.2
  choose n hn using H
  -- ⊢ x ∈ ↑toSubmodule (AlgHom.range (ofId { x // x ∈ S' } S))
  let s' : ι → S' := fun x => ⟨s x, hs x⟩
  -- ⊢ x ∈ ↑toSubmodule (AlgHom.range (ofId { x // x ∈ S' } S))
  let l' : ι → S' := fun x => ⟨l x, hl x⟩
  -- ⊢ x ∈ ↑toSubmodule (AlgHom.range (ofId { x // x ∈ S' } S))
  have e' : ∑ i in ι', l' i * s' i = 1 := by
    ext
    show S'.subtype (∑ i in ι', l' i * s' i) = 1
    simpa only [map_sum, map_mul] using e
  have : Ideal.span (s' '' ι') = ⊤ := by
    rw [Ideal.eq_top_iff_one, ← e']
    apply sum_mem
    intros i hi
    exact Ideal.mul_mem_left _ _ <| Ideal.subset_span <| Set.mem_image_of_mem s' hi
  let N := ι'.sup n
  -- ⊢ x ∈ ↑toSubmodule (AlgHom.range (ofId { x // x ∈ S' } S))
  have hN := Ideal.span_pow_eq_top _ this N
  -- ⊢ x ∈ ↑toSubmodule (AlgHom.range (ofId { x // x ∈ S' } S))
  apply (Algebra.ofId S' S).range.toSubmodule.mem_of_span_top_of_smul_mem _ hN
  -- ⊢ ∀ (r : ↑((fun x => x ^ N) '' (s' '' ↑ι'))), ↑r • x ∈ ↑toSubmodule (AlgHom.ra …
  rintro ⟨_, _, ⟨i, hi, rfl⟩, rfl⟩
  -- ⊢ ↑{ val := (fun x => x ^ N) (s' i), property := (_ : ∃ a, a ∈ s' '' ↑ι' ∧ (fu …
  change s' i ^ N • x ∈ _
  -- ⊢ s' i ^ N • x ∈ ↑toSubmodule (AlgHom.range (ofId { x // x ∈ S' } S))
  rw [← tsub_add_cancel_of_le (show n i ≤ N from Finset.le_sup hi), pow_add, mul_smul]
  -- ⊢ s' i ^ (N - n i) • s' i ^ n i • x ∈ ↑toSubmodule (AlgHom.range (ofId { x //  …
  refine' Submodule.smul_mem _ (⟨_, pow_mem (hs i) _⟩ : S') _
  -- ⊢ s' i ^ n i • x ∈ ↑toSubmodule (AlgHom.range (ofId { x // x ∈ S' } S))
  exact ⟨⟨_, hn i⟩, rfl⟩
  -- 🎉 no goals
#align subalgebra.mem_of_finset_sum_eq_one_of_pow_smul_mem Subalgebra.mem_of_finset_sum_eq_one_of_pow_smul_mem

theorem mem_of_span_eq_top_of_smul_pow_mem {S : Type*} [CommRing S] [Algebra R S]
    (S' : Subalgebra R S) (s : Set S) (l : s →₀ S) (hs : Finsupp.total s S S (↑) l = 1)
    (hs' : s ⊆ S') (hl : ∀ i, l i ∈ S') (x : S) (H : ∀ r : s, ∃ n : ℕ, (r : S) ^ n • x ∈ S') :
    x ∈ S' :=
  mem_of_finset_sum_eq_one_of_pow_smul_mem S' l.support (↑) l hs (fun x => hs' x.2) hl x H
#align subalgebra.mem_of_span_eq_top_of_smul_pow_mem Subalgebra.mem_of_span_eq_top_of_smul_pow_mem

end Subalgebra

section Nat

variable {R : Type*} [Semiring R]

/-- A subsemiring is an `ℕ`-subalgebra. -/
def subalgebraOfSubsemiring (S : Subsemiring R) : Subalgebra ℕ R :=
  { S with algebraMap_mem' := fun i => coe_nat_mem S i }
#align subalgebra_of_subsemiring subalgebraOfSubsemiring

@[simp]
theorem mem_subalgebraOfSubsemiring {x : R} {S : Subsemiring R} :
    x ∈ subalgebraOfSubsemiring S ↔ x ∈ S :=
  Iff.rfl
#align mem_subalgebra_of_subsemiring mem_subalgebraOfSubsemiring

end Nat

section Int

variable {R : Type*} [Ring R]

/-- A subring is a `ℤ`-subalgebra. -/
def subalgebraOfSubring (S : Subring R) : Subalgebra ℤ R :=
  { S with
    algebraMap_mem' := fun i =>
      Int.induction_on i (by simpa using S.zero_mem)
                             -- 🎉 no goals
        (fun i ih => by simpa using S.add_mem ih S.one_mem) fun i ih =>
                        -- 🎉 no goals
        show ((-i - 1 : ℤ) : R) ∈ S by
          rw [Int.cast_sub, Int.cast_one]
          -- ⊢ ↑(-↑i) - 1 ∈ S
          exact S.sub_mem ih S.one_mem }
          -- 🎉 no goals
#align subalgebra_of_subring subalgebraOfSubring

variable {S : Type*} [Semiring S]

@[simp]
theorem mem_subalgebraOfSubring {x : R} {S : Subring R} : x ∈ subalgebraOfSubring S ↔ x ∈ S :=
  Iff.rfl
#align mem_subalgebra_of_subring mem_subalgebraOfSubring

end Int
