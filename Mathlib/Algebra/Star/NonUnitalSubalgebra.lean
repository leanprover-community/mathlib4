/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
import Mathlib.Algebra.Algebra.NonUnitalSubalgebra.Basic
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.Center

/-!
# Non-unital Star Subalgebras

In this file we define `non_unital_star_subalgebra`s and the usual operations on them
(`map`, `comap`).

## TODO

* once we have scalar actions by semigroups (as opposed to monoids), implement the action of a
  non-unital subalgebra on the larger algebra.
-/


namespace StarMemClass

instance instInvolutiveStar {S R : Type _} [InvolutiveStar R] [SetLike S R] [StarMemClass S R]
    (s : S) : InvolutiveStar s where
  star_involutive r := Subtype.ext <| star_star (r : R)

instance instStarSemigroup{S R : Type _} [Semigroup R] [StarSemigroup R] [SetLike S R]
    [MulMemClass S R] [StarMemClass S R] (s : S) : StarSemigroup s where
  star_mul _ _ := Subtype.ext <| star_mul _ _

instance instStarAddMonoid {S R : Type _} [AddMonoid R] [StarAddMonoid R] [SetLike S R]
    [AddSubmonoidClass S R] [StarMemClass S R] (s : S) : StarAddMonoid s where
  star_add _ _ := Subtype.ext <| star_add _ _

instance instStarRing {S R : Type _} [NonUnitalSemiring R] [StarRing R] [SetLike S R]
    [NonUnitalSubsemiringClass S R] [StarMemClass S R] (s : S) : StarRing s :=
  { StarMemClass.instStarSemigroup s, StarMemClass.instStarAddMonoid s with }

instance instStarModule {S : Type _} (R : Type _) {M : Type _} [Star R] [Star M] [SMul R M]
    [StarModule R M] [SetLike S M] [SMulMemClass S R M] [StarMemClass S M] (s : S) :
    StarModule R s where
  star_smul _ _ := Subtype.ext <| star_smul _ _

end StarMemClass

universe u u' v v' w w' w''

open scoped BigOperators

variable {F : Type v'} {R' : Type u'} {R : Type u}
variable {A : Type v} {B : Type w} {C : Type w'}

namespace NonUnitalStarSubalgebraClass

variable [CommSemiring R] [NonUnitalNonAssocSemiring A]
variable [Star A] [Module R A]
variable {S : Type w''} [SetLike S A] [NonUnitalSubsemiringClass S A]
variable [hSR : SMulMemClass S R A] [StarMemClass S A] (s : S)

/-- Embedding of a non-unital star subalgebra into the non-unital star algebra. -/
def subtype (s : S) : s →⋆ₙₐ[R] A :=
  { NonUnitalSubalgebraClass.subtype s with
    toFun := Subtype.val
    map_star' := fun _ => rfl }
#align non_unital_star_subalgebra_class.subtype NonUnitalStarSubalgebraClass.subtype

@[simp]
theorem coeSubtype : (subtype s : s → A) = Subtype.val :=
  rfl
#align non_unital_star_subalgebra_class.coe_subtype NonUnitalStarSubalgebraClass.coeSubtype

end NonUnitalStarSubalgebraClass

/-- A non-unital star subalgebra is a non-unital subalgebra which is closed under the `star`
operation. -/
structure NonUnitalStarSubalgebra (R : Type u) (A : Type v) [CommSemiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [Star A]
    extends NonUnitalSubalgebra R A : Type v where
  /-- The `carrier` of a `NonUnitalStarSubalgebra` is closed under the `star` operation. -/
  star_mem' : ∀ {a : A} (_ha : a ∈ carrier), star a ∈ carrier
#align non_unital_star_subalgebra NonUnitalStarSubalgebra

/-- Reinterpret a `non_unital_star_subalgebra` as a `non_unital_subalgebra`. -/
add_decl_doc NonUnitalStarSubalgebra.toNonUnitalSubalgebra

namespace NonUnitalStarSubalgebra

variable [CommSemiring R]
variable [NonUnitalNonAssocSemiring A] [Module R A] [Star A]
variable [NonUnitalNonAssocSemiring B] [Module R B] [Star B]
variable [NonUnitalNonAssocSemiring C] [Module R C] [Star C]
variable [NonUnitalStarAlgHomClass F R A B]

instance instSetLike : SetLike (NonUnitalStarSubalgebra R A) A where
  coe {s} := s.carrier
  coe_injective' p q h := by cases p; cases q; congr; exact SetLike.coe_injective h

instance instNonUnitalSubsemiringClass : NonUnitalSubsemiringClass (NonUnitalStarSubalgebra R A) A
    where
  add_mem {s} := s.add_mem'
  mul_mem {s} := s.mul_mem'
  zero_mem {s} := s.zero_mem'

instance instSMulMemClass : SMulMemClass (NonUnitalStarSubalgebra R A) R A where
  smul_mem {s} := s.smul_mem'

instance instStarMemClass : StarMemClass (NonUnitalStarSubalgebra R A) A where
  star_mem {s} := s.star_mem'

instance instNonUnitalSubringClass {R : Type u} {A : Type v} [CommRing R] [NonUnitalNonAssocRing A]
    [Module R A] [Star A] : NonUnitalSubringClass (NonUnitalStarSubalgebra R A) A :=
  { NonUnitalStarSubalgebra.instNonUnitalSubsemiringClass with
    neg_mem := fun _S {x} hx => neg_one_smul R x ▸ SMulMemClass.smul_mem _ hx }

theorem mem_carrier {s : NonUnitalStarSubalgebra R A} {x : A} : x ∈ s.carrier ↔ x ∈ s :=
  Iff.rfl
#align non_unital_star_subalgebra.mem_carrier NonUnitalStarSubalgebra.mem_carrier

@[ext]
theorem ext {S T : NonUnitalStarSubalgebra R A} (h : ∀ x : A, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h
#align non_unital_star_subalgebra.ext NonUnitalStarSubalgebra.ext

@[simp]
theorem mem_toNonUnitalSubalgebra {S : NonUnitalStarSubalgebra R A} {x} :
    x ∈ S.toNonUnitalSubalgebra ↔ x ∈ S :=
  Iff.rfl
#align non_unital_star_subalgebra.mem_to_non_unital_subalgebra NonUnitalStarSubalgebra.mem_toNonUnitalSubalgebra

@[simp]
theorem coe_toNonUnitalSubalgebra (S : NonUnitalStarSubalgebra R A) :
    (↑S.toNonUnitalSubalgebra : Set A) = S :=
  rfl
#align non_unital_star_subalgebra.coe_to_non_unital_subalgebra NonUnitalStarSubalgebra.coe_toNonUnitalSubalgebra

theorem toNonUnitalSubalgebra_injective :
    Function.Injective
      (toNonUnitalSubalgebra : NonUnitalStarSubalgebra R A → NonUnitalSubalgebra R A) :=
  fun S T h =>
  ext fun x => by rw [← mem_toNonUnitalSubalgebra, ← mem_toNonUnitalSubalgebra, h]
#align non_unital_star_subalgebra.to_non_unital_subalgebra_injective NonUnitalStarSubalgebra.toNonUnitalSubalgebra_injective

theorem toNonUnitalSubalgebra_inj {S U : NonUnitalStarSubalgebra R A} :
    S.toNonUnitalSubalgebra = U.toNonUnitalSubalgebra ↔ S = U :=
  toNonUnitalSubalgebra_injective.eq_iff
#align non_unital_star_subalgebra.to_non_unital_subalgebra_inj NonUnitalStarSubalgebra.toNonUnitalSubalgebra_inj

theorem toNonUnitalSubalgebra_le_iff {S₁ S₂ : NonUnitalStarSubalgebra R A} :
    S₁.toNonUnitalSubalgebra ≤ S₂.toNonUnitalSubalgebra ↔ S₁ ≤ S₂ :=
  Iff.rfl
#align non_unital_star_subalgebra.to_non_unital_subalgebra_le_iff NonUnitalStarSubalgebra.toNonUnitalSubalgebra_le_iff

/-- Copy of a non-unital star subalgebra with a new `carrier` equal to the old one.
Useful to fix definitional equalities. -/
protected def copy (S : NonUnitalStarSubalgebra R A) (s : Set A) (hs : s = ↑S) :
    NonUnitalStarSubalgebra R A :=
  { S.toNonUnitalSubalgebra.copy s hs with
    star_mem' := @fun x (hx : x ∈ s) => by
      show star x ∈ s
      rw [hs] at hx ⊢
      exact S.star_mem' hx }
#align non_unital_star_subalgebra.copy NonUnitalStarSubalgebra.copy

@[simp]
theorem coe_copy (S : NonUnitalStarSubalgebra R A) (s : Set A) (hs : s = ↑S) :
    (S.copy s hs : Set A) = s :=
  rfl
#align non_unital_star_subalgebra.coe_copy NonUnitalStarSubalgebra.coe_copy

theorem copy_eq (S : NonUnitalStarSubalgebra R A) (s : Set A) (hs : s = ↑S) : S.copy s hs = S :=
  SetLike.coe_injective hs
#align non_unital_star_subalgebra.copy_eq NonUnitalStarSubalgebra.copy_eq

variable (S : NonUnitalStarSubalgebra R A)

-- do we need to duplicate the `non_unital_subring` stuff given that we have the
-- `non_unital_subring_class` already?
/-- A non-unital subalgebra over a ring is also a `subring`. -/
def toNonUnitalSubring {R : Type u} {A : Type v} [CommRing R] [NonUnitalRing A] [Module R A]
    [Star A] (S : NonUnitalStarSubalgebra R A) : NonUnitalSubring A where
  toNonUnitalSubsemiring := S.toNonUnitalSubsemiring
  neg_mem' := neg_mem (s := S)
#align non_unital_star_subalgebra.to_non_unital_subring NonUnitalStarSubalgebra.toNonUnitalSubring

@[simp]
theorem mem_toNonUnitalSubring {R : Type u} {A : Type v} [CommRing R] [NonUnitalRing A] [Module R A]
    [Star A] {S : NonUnitalStarSubalgebra R A} {x} : x ∈ S.toNonUnitalSubring ↔ x ∈ S :=
  Iff.rfl
#align non_unital_star_subalgebra.mem_to_non_unital_subring NonUnitalStarSubalgebra.mem_toNonUnitalSubring

@[simp]
theorem coe_toNonUnitalSubring {R : Type u} {A : Type v} [CommRing R] [NonUnitalRing A] [Module R A]
    [Star A] (S : NonUnitalStarSubalgebra R A) : (↑S.toNonUnitalSubring : Set A) = S :=
  rfl
#align non_unital_star_subalgebra.coe_to_non_unital_subring NonUnitalStarSubalgebra.coe_toNonUnitalSubring

theorem toNonUnitalSubring_injective {R : Type u} {A : Type v} [CommRing R] [NonUnitalRing A]
    [Module R A] [Star A] :
    Function.Injective (toNonUnitalSubring : NonUnitalStarSubalgebra R A → NonUnitalSubring A) :=
  fun S T h => ext fun x => by rw [← mem_toNonUnitalSubring, ← mem_toNonUnitalSubring, h]
#align non_unital_star_subalgebra.to_non_unital_subring_injective NonUnitalStarSubalgebra.toNonUnitalSubring_injective

theorem toNonUnitalSubring_inj {R : Type u} {A : Type v} [CommRing R] [NonUnitalRing A] [Module R A]
    [Star A] {S U : NonUnitalStarSubalgebra R A} :
    S.toNonUnitalSubring = U.toNonUnitalSubring ↔ S = U :=
  toNonUnitalSubring_injective.eq_iff
#align non_unital_star_subalgebra.to_non_unital_subring_inj NonUnitalStarSubalgebra.toNonUnitalSubring_inj

instance instInhabited : Inhabited S :=
  ⟨(0 : S.toNonUnitalSubalgebra)⟩

section

/-! `non_unital_star_subalgebra`s inherit structure from their `non_unital_subalgebra` and
`semiring` coercions. -/

instance toNonUnitalSemiring {R A} [CommSemiring R] [NonUnitalSemiring A] [Module R A] [Star A]
    (S : NonUnitalStarSubalgebra R A) : NonUnitalSemiring S :=
  inferInstance
#align non_unital_star_subalgebra.to_non_unital_semiring NonUnitalStarSubalgebra.toNonUnitalSemiring

instance toNonUnitalCommSemiring {R A} [CommSemiring R] [NonUnitalCommSemiring A] [Module R A]
    [Star A] (S : NonUnitalStarSubalgebra R A) : NonUnitalCommSemiring S :=
  inferInstance
#align non_unital_star_subalgebra.to_non_unital_comm_semiring NonUnitalStarSubalgebra.toNonUnitalCommSemiring

instance toNonUnitalRing {R A} [CommRing R] [NonUnitalRing A] [Module R A] [Star A]
    (S : NonUnitalStarSubalgebra R A) : NonUnitalRing S :=
  inferInstance
#align non_unital_star_subalgebra.to_non_unital_ring NonUnitalStarSubalgebra.toNonUnitalRing

instance toNonUnitalCommRing {R A} [CommRing R] [NonUnitalCommRing A] [Module R A] [Star A]
    (S : NonUnitalStarSubalgebra R A) : NonUnitalCommRing S :=
  inferInstance
#align non_unital_star_subalgebra.to_non_unital_comm_ring NonUnitalStarSubalgebra.toNonUnitalCommRing

end

/-- The forgetful map from `non_unital_star_subalgebra` to `non_unital_subalgebra` as an
`order_embedding` -/
def toNonUnitalSubalgebra' : NonUnitalStarSubalgebra R A ↪o NonUnitalSubalgebra R A
    where
  toEmbedding :=
    { toFun := fun S => S.toNonUnitalSubalgebra
      inj' := fun S T h => ext <| by apply SetLike.ext_iff.1 h }
  map_rel_iff' := SetLike.coe_subset_coe.symm.trans SetLike.coe_subset_coe
#align non_unital_star_subalgebra.to_non_unital_subalgebra' NonUnitalStarSubalgebra.toNonUnitalSubalgebra'

section

/-! `non_unital_star_subalgebra`s inherit structure from their `submodule` coercions. -/


-- TODO: generalize to `smul_mem_class`
instance module' [Semiring R'] [SMul R' R] [Module R' A] [IsScalarTower R' R A] : Module R' S :=
  SMulMemClass.toModule' _ R' R A S
#align non_unital_star_subalgebra.module' NonUnitalStarSubalgebra.module'

instance instModule : Module R S :=
  S.module'

instance instIsScalarTower' [Semiring R'] [SMul R' R] [Module R' A] [IsScalarTower R' R A] :
    IsScalarTower R' R S :=
  S.toNonUnitalSubalgebra.instIsScalarTower'
#align non_unital_star_subalgebra.is_scalar_tower' NonUnitalStarSubalgebra.instIsScalarTower'

instance instIsScalarTower [IsScalarTower R A A] : IsScalarTower R S S where
  smul_assoc r x y := Subtype.ext <| smul_assoc r (x : A) (y : A)

instance instSMulCommClass' [Semiring R'] [SMul R' R] [Module R' A] [IsScalarTower R' R A]
    [SMulCommClass R' R A] : SMulCommClass R' R S where
  smul_comm r' r s := Subtype.ext <| smul_comm r' r (s : A)
#align non_unital_star_subalgebra.smul_comm_class' NonUnitalStarSubalgebra.instSMulCommClass'

instance instSMulCommClass [SMulCommClass R A A] : SMulCommClass R S S where
  smul_comm r x y := Subtype.ext <| smul_comm r (x : A) (y : A)

end

instance noZeroSMulDivisors_bot [NoZeroSMulDivisors R A] : NoZeroSMulDivisors R S :=
  ⟨fun {c x} h =>
    have : c = 0 ∨ (x : A) = 0 := eq_zero_or_eq_zero_of_smul_eq_zero (congr_arg ((↑) : S → A) h)
    this.imp_right (@Subtype.ext_iff _ _ x 0).mpr⟩
#align non_unital_star_subalgebra.no_zero_smul_divisors_bot NonUnitalStarSubalgebra.noZeroSMulDivisors_bot

protected theorem coe_add (x y : S) : (↑(x + y) : A) = ↑x + ↑y :=
  rfl
#align non_unital_star_subalgebra.coe_add NonUnitalStarSubalgebra.coe_add

protected theorem coe_mul (x y : S) : (↑(x * y) : A) = ↑x * ↑y :=
  rfl
#align non_unital_star_subalgebra.coe_mul NonUnitalStarSubalgebra.coe_mul

protected theorem coe_zero : ((0 : S) : A) = 0 :=
  rfl
#align non_unital_star_subalgebra.coe_zero NonUnitalStarSubalgebra.coe_zero

protected theorem coe_neg {R : Type u} {A : Type v} [CommRing R] [NonUnitalRing A] [Module R A]
    [Star A] {S : NonUnitalStarSubalgebra R A} (x : S) : (↑(-x) : A) = -↑x :=
  rfl
#align non_unital_star_subalgebra.coe_neg NonUnitalStarSubalgebra.coe_neg

protected theorem coe_sub {R : Type u} {A : Type v} [CommRing R] [NonUnitalRing A] [Module R A]
    [Star A] {S : NonUnitalStarSubalgebra R A} (x y : S) : (↑(x - y) : A) = ↑x - ↑y :=
  rfl
#align non_unital_star_subalgebra.coe_sub NonUnitalStarSubalgebra.coe_sub

@[simp, norm_cast]
theorem coe_smul [Semiring R'] [SMul R' R] [Module R' A] [IsScalarTower R' R A] (r : R') (x : S) :
    (r • x : A) = r • (x : A) :=
  rfl
#align non_unital_star_subalgebra.coe_smul NonUnitalStarSubalgebra.coe_smul

protected theorem coe_eq_zero {x : S} : (x : A) = 0 ↔ x = 0 :=
  ZeroMemClass.coe_eq_zero
#align non_unital_star_subalgebra.coe_eq_zero NonUnitalStarSubalgebra.coe_eq_zero

@[simp]
theorem toNonUnitalSubalgebra_subtype :
    NonUnitalSubalgebraClass.subtype S = NonUnitalStarSubalgebraClass.subtype S :=
  rfl
#align non_unital_star_subalgebra.to_non_unital_subalgebra_subtype NonUnitalStarSubalgebra.toNonUnitalSubalgebra_subtype

@[simp]
theorem toSubring_subtype {R A : Type _} [CommRing R] [NonUnitalRing A] [Module R A] [Star A]
    (S : NonUnitalStarSubalgebra R A) :
    NonUnitalSubringClass.subtype S = NonUnitalStarSubalgebraClass.subtype S :=
  rfl
#align non_unital_star_subalgebra.to_subring_subtype NonUnitalStarSubalgebra.toSubring_subtype

/-- Transport a non_unital_star_subalgebra via an algebra homomorphism. -/
def map (f : F) (S : NonUnitalStarSubalgebra R A) : NonUnitalStarSubalgebra R B :=
  { S.toNonUnitalSubalgebra.map (f : A →ₙₐ[R] B) with
    star_mem' := by rintro _ ⟨a, ha, rfl⟩; exact ⟨star a, star_mem (s := S) ha, map_star f a⟩ }
#align non_unital_star_subalgebra.map NonUnitalStarSubalgebra.map

theorem map_mono {S₁ S₂ : NonUnitalStarSubalgebra R A} {f : F} :
    S₁ ≤ S₂ → (map f S₁ : NonUnitalStarSubalgebra R B) ≤ map f S₂ :=
  Set.image_subset f
#align non_unital_star_subalgebra.map_mono NonUnitalStarSubalgebra.map_mono

theorem map_injective {f : F} (hf : Function.Injective f) :
    Function.Injective (map f : NonUnitalStarSubalgebra R A → NonUnitalStarSubalgebra R B) :=
  fun _S₁ _S₂ ih =>
  ext <| Set.ext_iff.1 <| Set.image_injective.2 hf <| Set.ext <| SetLike.ext_iff.mp ih
#align non_unital_star_subalgebra.map_injective NonUnitalStarSubalgebra.map_injective

@[simp]
theorem map_id (S : NonUnitalStarSubalgebra R A) : map (NonUnitalStarAlgHom.id R A) S = S :=
  SetLike.coe_injective <| Set.image_id _
#align non_unital_star_subalgebra.map_id NonUnitalStarSubalgebra.map_id

theorem map_map (S : NonUnitalStarSubalgebra R A) (g : B →⋆ₙₐ[R] C) (f : A →⋆ₙₐ[R] B) :
    (S.map f).map g = S.map (g.comp f) :=
  SetLike.coe_injective <| Set.image_image _ _ _
#align non_unital_star_subalgebra.map_map NonUnitalStarSubalgebra.map_map

theorem mem_map {S : NonUnitalStarSubalgebra R A} {f : F} {y : B} :
    y ∈ map f S ↔ ∃ x ∈ S, f x = y :=
  NonUnitalSubalgebra.mem_map
#align non_unital_star_subalgebra.mem_map NonUnitalStarSubalgebra.mem_map

theorem map_toNonUnitalSubalgebra {S : NonUnitalStarSubalgebra R A} {f : F} :
    (map f S : NonUnitalStarSubalgebra R B).toNonUnitalSubalgebra =
      NonUnitalSubalgebra.map f S.toNonUnitalSubalgebra :=
  SetLike.coe_injective rfl
#align non_unital_star_subalgebra.map_to_non_unital_subalgebra NonUnitalStarSubalgebra.map_toNonUnitalSubalgebra

@[simp]
theorem coe_map (S : NonUnitalStarSubalgebra R A) (f : F) : (map f S : Set B) = f '' S :=
  rfl
#align non_unital_star_subalgebra.coe_map NonUnitalStarSubalgebra.coe_map

/-- Preimage of a non_unital_star_subalgebra under an algebra homomorphism. -/
def comap (f : F) (S : NonUnitalStarSubalgebra R B) : NonUnitalStarSubalgebra R A :=
  { S.toNonUnitalSubalgebra.comap f with
    star_mem' := @fun a (ha : f a ∈ S) =>
      show f (star a) ∈ S from (map_star f a).symm ▸ star_mem (s := S) ha }
#align non_unital_star_subalgebra.comap NonUnitalStarSubalgebra.comap

theorem map_le {S : NonUnitalStarSubalgebra R A} {f : F} {U : NonUnitalStarSubalgebra R B} :
    map f S ≤ U ↔ S ≤ comap f U :=
  Set.image_subset_iff
#align non_unital_star_subalgebra.map_le NonUnitalStarSubalgebra.map_le

theorem gc_map_comap (f : F) :
    GaloisConnection (map f : NonUnitalStarSubalgebra R A → NonUnitalStarSubalgebra R B)
      (comap f) :=
  fun _S _U => map_le
#align non_unital_star_subalgebra.gc_map_comap NonUnitalStarSubalgebra.gc_map_comap

@[simp]
theorem mem_comap (S : NonUnitalStarSubalgebra R B) (f : F) (x : A) : x ∈ comap f S ↔ f x ∈ S :=
  Iff.rfl
#align non_unital_star_subalgebra.mem_comap NonUnitalStarSubalgebra.mem_comap

@[simp, norm_cast]
theorem coe_comap (S : NonUnitalStarSubalgebra R B) (f : F) :
    (comap f S : Set A) = f ⁻¹' (S : Set B) :=
  rfl
#align non_unital_star_subalgebra.coe_comap NonUnitalStarSubalgebra.coe_comap

instance instNoZeroDivisors {R A : Type _} [CommSemiring R] [NonUnitalSemiring A] [NoZeroDivisors A]
    [Module R A] [Star A] (S : NonUnitalStarSubalgebra R A) : NoZeroDivisors S :=
  NonUnitalSubsemiringClass.noZeroDivisors S
#align non_unital_star_subalgebra.no_zero_divisors NonUnitalStarSubalgebra.instNoZeroDivisors

end NonUnitalStarSubalgebra

namespace NonUnitalSubalgebra

variable [CommSemiring R] [NonUnitalSemiring A] [Module R A] [Star A]

variable (s : NonUnitalSubalgebra R A)

/-- A non-unital subalgebra closed under `star` is a non-unital star subalgebra. -/
def toNonUnitalStarSubalgebra (h_star : ∀ x, x ∈ s → star x ∈ s) : NonUnitalStarSubalgebra R A :=
  { s
    with star_mem' := @h_star }
#align non_unital_subalgebra.to_non_unital_star_subalgebra NonUnitalSubalgebra.toNonUnitalStarSubalgebra

@[simp]
theorem mem_toNonUnitalStarSubalgebra {s : NonUnitalSubalgebra R A} {h_star} {x} :
    x ∈ s.toNonUnitalStarSubalgebra h_star ↔ x ∈ s :=
  Iff.rfl
#align non_unital_subalgebra.mem_to_non_unital_star_subalgebra NonUnitalSubalgebra.mem_toNonUnitalStarSubalgebra

@[simp]
theorem coe_toNonUnitalStarSubalgebra (s : NonUnitalSubalgebra R A) (h_star) :
    (s.toNonUnitalStarSubalgebra h_star : Set A) = s :=
  rfl
#align non_unital_subalgebra.coe_to_non_unital_star_subalgebra NonUnitalSubalgebra.coe_toNonUnitalStarSubalgebra

@[simp]
theorem toNonUnitalStarSubalgebra_toNonUnitalSubalgebra (s : NonUnitalSubalgebra R A) (h_star) :
    (s.toNonUnitalStarSubalgebra h_star).toNonUnitalSubalgebra = s :=
  SetLike.coe_injective rfl
#align non_unital_subalgebra.to_non_unital_star_subalgebra_to_non_unital_subalgebra NonUnitalSubalgebra.toNonUnitalStarSubalgebra_toNonUnitalSubalgebra

@[simp]
theorem _root_.NonUnitalStarSubalgebra.toNonUnitalSubalgebra_toNonUnitalStarSubalgebra
    (S : NonUnitalStarSubalgebra R A) :
    (S.toNonUnitalSubalgebra.toNonUnitalStarSubalgebra fun _ => star_mem (s := S)) = S :=
  SetLike.coe_injective rfl
#align non_unital_star_subalgebra.to_non_unital_subalgebra_to_non_unital_star_subalgebra NonUnitalStarSubalgebra.toNonUnitalSubalgebra_toNonUnitalStarSubalgebra

end NonUnitalSubalgebra

---- INSERT MORE SUBALGEBRA STUFF HERE (E.G. `star_closure`)
namespace NonUnitalStarAlgHom

variable [CommSemiring R]
variable [NonUnitalNonAssocSemiring A] [Module R A] [Star A]
variable [NonUnitalNonAssocSemiring B] [Module R B] [Star B]
variable [NonUnitalNonAssocSemiring C] [Module R C] [Star C]
variable [NonUnitalStarAlgHomClass F R A B]

/-- Range of an `non_unital_alg_hom` as a non_unital_star_subalgebra. -/
protected def range (φ : F) : NonUnitalStarSubalgebra R B where
  toNonUnitalSubalgebra := NonUnitalAlgHom.range (φ : A →ₙₐ[R] B)
  star_mem' := by rintro _ ⟨a, rfl⟩; exact ⟨star a, map_star φ a⟩
#align non_unital_star_alg_hom.range NonUnitalStarAlgHom.range

@[simp]
theorem mem_range (φ : F) {y : B} :
    y ∈ (NonUnitalStarAlgHom.range φ : NonUnitalStarSubalgebra R B) ↔ ∃ x : A, φ x = y :=
  NonUnitalRingHom.mem_srange
#align non_unital_star_alg_hom.mem_range NonUnitalStarAlgHom.mem_range

theorem mem_range_self (φ : F) (x : A) :
    φ x ∈ (NonUnitalStarAlgHom.range φ : NonUnitalStarSubalgebra R B) :=
  (NonUnitalAlgHom.mem_range φ).2 ⟨x, rfl⟩
#align non_unital_star_alg_hom.mem_range_self NonUnitalStarAlgHom.mem_range_self

@[simp]
theorem coe_range (φ : F) :
    ((NonUnitalStarAlgHom.range φ : NonUnitalStarSubalgebra R B) : Set B) = Set.range (φ : A → B) :=
  by ext; rw [SetLike.mem_coe, mem_range]; rfl
#align non_unital_star_alg_hom.coe_range NonUnitalStarAlgHom.coe_range

theorem range_comp (f : A →⋆ₙₐ[R] B) (g : B →⋆ₙₐ[R] C) :
  NonUnitalStarAlgHom.range (g.comp f) = (NonUnitalStarAlgHom.range f).map g :=
  SetLike.coe_injective (Set.range_comp g f)
#align non_unital_star_alg_hom.range_comp NonUnitalStarAlgHom.range_comp

theorem range_comp_le_range (f : A →⋆ₙₐ[R] B) (g : B →⋆ₙₐ[R] C) :
  NonUnitalStarAlgHom.range (g.comp f) ≤ NonUnitalStarAlgHom.range g :=
  SetLike.coe_mono (Set.range_comp_subset_range f g)
#align non_unital_star_alg_hom.range_comp_le_range NonUnitalStarAlgHom.range_comp_le_range

/-- Restrict the codomain of an star algebra homomorphism. -/
def codRestrict (f : F) (S : NonUnitalStarSubalgebra R B) (hf : ∀ x, f x ∈ S) : A →⋆ₙₐ[R] S where
  toNonUnitalAlgHom := NonUnitalAlgHom.codRestrict f S.toNonUnitalSubalgebra hf
  map_star' := fun a => Subtype.ext <| map_star f a
#align non_unital_star_alg_hom.cod_restrict NonUnitalStarAlgHom.codRestrict

@[simp]
theorem subtype_comp_codRestrict (f : F) (S : NonUnitalStarSubalgebra R B) (hf : ∀ x : A, f x ∈ S) :
    (NonUnitalStarSubalgebraClass.subtype S).comp (NonUnitalStarAlgHom.codRestrict f S hf) = f :=
  NonUnitalStarAlgHom.ext fun _ => rfl
#align non_unital_star_alg_hom.subtype_comp_cod_restrict NonUnitalStarAlgHom.subtype_comp_codRestrict

@[simp]
theorem coe_codRestrict (f : F) (S : NonUnitalStarSubalgebra R B) (hf : ∀ x, f x ∈ S) (x : A) :
    ↑(NonUnitalStarAlgHom.codRestrict f S hf x) = f x :=
  rfl
#align non_unital_star_alg_hom.coe_cod_restrict NonUnitalStarAlgHom.coe_codRestrict

theorem injective_codRestrict (f : F) (S : NonUnitalStarSubalgebra R B) (hf : ∀ x : A, f x ∈ S) :
    Function.Injective (NonUnitalStarAlgHom.codRestrict f S hf) ↔ Function.Injective f :=
  ⟨fun H _x _y hxy => H <| Subtype.eq hxy, fun H _x _y hxy => H (congr_arg Subtype.val hxy : _)⟩
#align non_unital_star_alg_hom.injective_cod_restrict NonUnitalStarAlgHom.injective_codRestrict

/-- Restrict the codomain of a non-unital star algebra homomorphism `f` to `f.range`.

This is the bundled version of `set.range_factorization`. -/
@[reducible]
def rangeRestrict (f : F) : A →⋆ₙₐ[R] (NonUnitalStarAlgHom.range f : NonUnitalStarSubalgebra R B) :=
  NonUnitalStarAlgHom.codRestrict f (NonUnitalStarAlgHom.range f)
    (NonUnitalStarAlgHom.mem_range_self f)
#align non_unital_star_alg_hom.range_restrict NonUnitalStarAlgHom.rangeRestrict

/-- The equalizer of two R-algebra homomorphisms -/
def equalizer (ϕ ψ : F) : NonUnitalStarSubalgebra R A :=
  { NonUnitalAlgHom.equalizer ϕ ψ with
    carrier := {a | (ϕ a : B) = ψ a}
    star_mem' := @fun x (hx : ϕ x = ψ x) => by rw [Set.mem_setOf_eq, map_star, map_star, hx] }
#align non_unital_star_alg_hom.equalizer NonUnitalStarAlgHom.equalizer

@[simp]
theorem mem_equalizer (φ ψ : F) (x : A) :
    x ∈ NonUnitalStarAlgHom.equalizer φ ψ ↔ φ x = ψ x :=
  Iff.rfl
#align non_unital_star_alg_hom.mem_equalizer NonUnitalStarAlgHom.mem_equalizer

/-- The range of a morphism of algebras is a fintype, if the domain is a fintype.

Note that this instance can cause a diamond with `subtype.fintype` if `B` is also a fintype. -/
instance fintypeRange [Fintype A] [DecidableEq B] (φ : F) :
    Fintype (NonUnitalAlgHom.range φ) :=
  Set.fintypeRange φ
#align non_unital_star_alg_hom.fintype_range NonUnitalStarAlgHom.fintypeRange

end NonUnitalStarAlgHom

namespace StarAlgEquiv

variable [CommSemiring R]
variable [NonUnitalSemiring A] [Module R A] [Star A]
variable [NonUnitalSemiring B] [Module R B] [Star B]
variable [NonUnitalSemiring C] [Module R C] [Star C]
variable [hF : NonUnitalStarAlgHomClass F R A B]

/-- Restrict an algebra homomorphism with a left inverse to an algebra isomorphism to its range.

This is a computable alternative to `star_alg_equiv.of_injective`. -/
def ofLeftInverse {g : B → A} {f : F} (h : Function.LeftInverse g f) :
    A ≃⋆ₐ[R] NonUnitalStarAlgHom.range f :=
  { NonUnitalStarAlgHom.rangeRestrict f with
    toFun := NonUnitalStarAlgHom.rangeRestrict f
    invFun := g ∘ (NonUnitalStarSubalgebraClass.subtype <| NonUnitalStarAlgHom.range f)
    left_inv := h
    right_inv := fun x =>
      Subtype.ext <|
        let ⟨x', hx'⟩ := (NonUnitalStarAlgHom.mem_range f).mp x.prop
        show f (g x) = x by rw [← hx', h x'] }
#align star_alg_equiv.of_left_inverse StarAlgEquiv.ofLeftInverse

@[simp]
theorem ofLeftInverse_apply {g : B → A} {f : F} (h : Function.LeftInverse g f) (x : A) :
    ↑(ofLeftInverse h x) = f x :=
  rfl
#align star_alg_equiv.of_left_inverse_apply StarAlgEquiv.ofLeftInverse_apply

@[simp]
theorem ofLeftInverse_symm_apply {g : B → A} {f : F} (h : Function.LeftInverse g f)
    (x : NonUnitalStarAlgHom.range f) : (ofLeftInverse h).symm x = g x :=
  rfl
#align star_alg_equiv.of_left_inverse_symm_apply StarAlgEquiv.ofLeftInverse_symm_apply

/-- Restrict an injective algebra homomorphism to an algebra isomorphism -/
noncomputable def ofInjective (f : F) (hf : Function.Injective f) :
    A ≃⋆ₐ[R] NonUnitalStarAlgHom.range f :=
  ofLeftInverse (Classical.choose_spec hf.hasLeftInverse)
#align star_alg_equiv.of_injective StarAlgEquiv.ofInjective

@[simp]
theorem ofInjective_apply (f : F) (hf : Function.Injective f) (x : A) :
    ↑(ofInjective f hf x) = f x :=
  rfl
#align star_alg_equiv.of_injective_apply StarAlgEquiv.ofInjective_apply

end StarAlgEquiv

/-! ### The star closure of a subalgebra -/


namespace NonUnitalSubalgebra

open scoped Pointwise

variable [CommSemiring R] [StarRing R]
variable [NonUnitalSemiring A] [StarRing A] [Module R A]
variable [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A]
variable [NonUnitalSemiring B] [StarRing B] [Module R B]
variable [IsScalarTower R B B] [SMulCommClass R B B] [StarModule R B]

/-- The pointwise `star` of a non-unital subalgebra is a non-unital subalgebra. -/
instance : InvolutiveStar (NonUnitalSubalgebra R A)
    where
  star S :=
    { carrier := star S.carrier
      mul_mem' := @fun x y hx hy => by simpa only [Set.mem_star, NonUnitalSubalgebra.mem_carrier]
        using (star_mul x y).symm ▸ mul_mem hy hx
      add_mem' := @fun x y hx hy => by simpa only [Set.mem_star, NonUnitalSubalgebra.mem_carrier]
        using (star_add x y).symm ▸ add_mem hx hy
      zero_mem' := Set.mem_star.mp ((star_zero A).symm ▸ zero_mem S : star (0 : A) ∈ S)
      smul_mem' := fun r x hx => by simpa only [Set.mem_star, NonUnitalSubalgebra.mem_carrier]
        using (star_smul r x).symm ▸ SMulMemClass.smul_mem (star r) hx }
  star_involutive S := NonUnitalSubalgebra.ext fun x =>
      ⟨fun hx => star_star x ▸ hx, fun hx => ((star_star x).symm ▸ hx : star (star x) ∈ S)⟩

@[simp]
theorem mem_star_iff (S : NonUnitalSubalgebra R A) (x : A) : x ∈ star S ↔ star x ∈ S :=
  Iff.rfl
#align non_unital_subalgebra.mem_star_iff NonUnitalSubalgebra.mem_star_iff

theorem star_mem_star_iff (S : NonUnitalSubalgebra R A) (x : A) : star x ∈ star S ↔ x ∈ S := by
  simp
#align non_unital_subalgebra.star_mem_star_iff NonUnitalSubalgebra.star_mem_star_iff

@[simp]
theorem coe_star (S : NonUnitalSubalgebra R A) :
    star S = star (S : Set A) :=
  rfl
#align non_unital_subalgebra.coe_star NonUnitalSubalgebra.coe_star

theorem star_mono : Monotone (star : NonUnitalSubalgebra R A → NonUnitalSubalgebra R A) :=
  fun _ _ h _ hx => h hx
#align non_unital_subalgebra.star_mono NonUnitalSubalgebra.star_mono

variable (R)

/-- The star operation on `subalgebra` commutes with `algebra.adjoin`. -/
theorem star_adjoin_comm (s : Set A) :
    star (NonUnitalAlgebra.adjoin R s) = NonUnitalAlgebra.adjoin R (star s) :=
  have this :
    ∀ t : Set A, NonUnitalAlgebra.adjoin R (star t) ≤ star (NonUnitalAlgebra.adjoin R t) := fun t =>
    NonUnitalAlgebra.adjoin_le fun x hx => NonUnitalAlgebra.subset_adjoin R hx
  le_antisymm (by simpa only [star_star] using NonUnitalSubalgebra.star_mono (this (star s)))
    (this s)
#align non_unital_subalgebra.star_adjoin_comm NonUnitalSubalgebra.star_adjoin_comm

variable {R}

/-- The `non_unital_star_subalgebra` obtained from `S : non_unital_subalgebra R A` by taking the
smallest subalgebra containing both `S` and `star S`. -/
@[simps!]
def starClosure (S : NonUnitalSubalgebra R A) : NonUnitalStarSubalgebra R A where
  toNonUnitalSubalgebra := S ⊔ star S
  star_mem' := @fun a (ha : a ∈ S ⊔ star S) => show star a ∈ S ⊔ star S by
    simp only [← mem_star_iff _ a, ← (@NonUnitalAlgebra.gi R A _ _ _ _ _).l_sup_u _ _] at *
    convert ha using 2
    simp only [Set.sup_eq_union, star_adjoin_comm, Set.union_star, coe_star, star_star,
      Set.union_comm]
#align non_unital_subalgebra.star_closure NonUnitalSubalgebra.starClosure

theorem starClosure_le {S₁ : NonUnitalSubalgebra R A} {S₂ : NonUnitalStarSubalgebra R A}
    (h : S₁ ≤ S₂.toNonUnitalSubalgebra) : S₁.starClosure ≤ S₂ :=
  NonUnitalStarSubalgebra.toNonUnitalSubalgebra_le_iff.1 <|
    sup_le h fun x hx =>
      (star_star x ▸ star_mem (show star x ∈ S₂ from h <| (S₁.mem_star_iff _).1 hx) : x ∈ S₂)
#align non_unital_subalgebra.star_closure_le NonUnitalSubalgebra.starClosure_le

theorem starClosure_le_iff {S₁ : NonUnitalSubalgebra R A} {S₂ : NonUnitalStarSubalgebra R A} :
    S₁.starClosure ≤ S₂ ↔ S₁ ≤ S₂.toNonUnitalSubalgebra :=
  ⟨fun h => le_sup_left.trans h, starClosure_le⟩
#align non_unital_subalgebra.star_closure_le_iff NonUnitalSubalgebra.starClosure_le_iff

end NonUnitalSubalgebra

namespace NonUnitalStarAlgebra

variable [CommSemiring R] [StarRing R]
variable [NonUnitalSemiring A] [StarRing A]
variable [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A]
variable [NonUnitalSemiring B] [StarRing B]
variable [Module R B] [IsScalarTower R B B] [SMulCommClass R B B] [StarModule R B]
variable [hF : NonUnitalStarAlgHomClass F R A B]

open scoped Pointwise

open NonUnitalStarSubalgebra

variable (R)

/-- The minimal non-unital subalgebra that includes `s`. -/
def adjoin (s : Set A) : NonUnitalStarSubalgebra R A where
  toNonUnitalSubalgebra := NonUnitalAlgebra.adjoin R (s ∪ star s)
  star_mem' _ := by
    rwa [NonUnitalSubalgebra.mem_carrier, ← NonUnitalSubalgebra.mem_star_iff,
      NonUnitalSubalgebra.star_adjoin_comm, Set.union_star, star_star, Set.union_comm]
#align non_unital_star_algebra.adjoin NonUnitalStarAlgebra.adjoin

theorem adjoin_eq_starClosure_adjoin (s : Set A) :
    adjoin R s = (NonUnitalAlgebra.adjoin R s).starClosure :=
  toNonUnitalSubalgebra_injective <| show
    NonUnitalAlgebra.adjoin R (s ∪ star s) =
      NonUnitalAlgebra.adjoin R s ⊔ star (NonUnitalAlgebra.adjoin R s)
    from
      (NonUnitalSubalgebra.star_adjoin_comm R s).symm ▸ NonUnitalAlgebra.adjoin_union s (star s)
#align non_unital_star_algebra.adjoin_eq_star_closure_adjoin NonUnitalStarAlgebra.adjoin_eq_starClosure_adjoin

theorem adjoin_toNonUnitalSubalgebra (s : Set A) :
    (adjoin R s).toNonUnitalSubalgebra = NonUnitalAlgebra.adjoin R (s ∪ star s) :=
  rfl
#align non_unital_star_algebra.adjoin_to_non_unital_subalgebra NonUnitalStarAlgebra.adjoin_toNonUnitalSubalgebra

theorem subset_adjoin (s : Set A) : s ⊆ adjoin R s :=
  (Set.subset_union_left s (star s)).trans <| NonUnitalAlgebra.subset_adjoin R
#align non_unital_star_algebra.subset_adjoin NonUnitalStarAlgebra.subset_adjoin

theorem star_subset_adjoin (s : Set A) : star s ⊆ adjoin R s :=
  (Set.subset_union_right s (star s)).trans <| NonUnitalAlgebra.subset_adjoin R
#align non_unital_star_algebra.star_subset_adjoin NonUnitalStarAlgebra.star_subset_adjoin

theorem self_mem_adjoin_singleton (x : A) : x ∈ adjoin R ({x} : Set A) :=
  NonUnitalAlgebra.subset_adjoin R <| Set.mem_union_left _ (Set.mem_singleton x)
#align non_unital_star_algebra.self_mem_adjoin_singleton NonUnitalStarAlgebra.self_mem_adjoin_singleton

theorem star_self_mem_adjoin_singleton (x : A) : star x ∈ adjoin R ({x} : Set A) :=
  star_mem <| self_mem_adjoin_singleton R x
#align non_unital_star_algebra.star_self_mem_adjoin_singleton NonUnitalStarAlgebra.star_self_mem_adjoin_singleton

variable {R}

protected theorem gc : GaloisConnection (adjoin R : Set A → NonUnitalStarSubalgebra R A) (↑) :=
  by
  intro s S
  rw [← toNonUnitalSubalgebra_le_iff, adjoin_toNonUnitalSubalgebra,
    NonUnitalAlgebra.adjoin_le_iff, coe_toNonUnitalSubalgebra]
  exact
    ⟨fun h => (Set.subset_union_left s _).trans h, fun h =>
      Set.union_subset h fun x hx => star_star x ▸ star_mem (show star x ∈ S from h hx)⟩
#align non_unital_star_algebra.gc NonUnitalStarAlgebra.gc

/-- Galois insertion between `adjoin` and `coe`. -/
protected def gi : GaloisInsertion (adjoin R : Set A → NonUnitalStarSubalgebra R A) (↑)
    where
  choice s hs := (adjoin R s).copy s <| le_antisymm (NonUnitalStarAlgebra.gc.le_u_l s) hs
  gc := NonUnitalStarAlgebra.gc
  le_l_u S := (NonUnitalStarAlgebra.gc (S : Set A) (adjoin R S)).1 <| le_rfl
  choice_eq _ _ := NonUnitalStarSubalgebra.copy_eq _ _ _
#align non_unital_star_algebra.gi NonUnitalStarAlgebra.gi

theorem adjoin_le {S : NonUnitalStarSubalgebra R A} {s : Set A} (hs : s ⊆ S) : adjoin R s ≤ S :=
  NonUnitalStarAlgebra.gc.l_le hs
#align non_unital_star_algebra.adjoin_le NonUnitalStarAlgebra.adjoin_le

theorem adjoin_le_iff {S : NonUnitalStarSubalgebra R A} {s : Set A} : adjoin R s ≤ S ↔ s ⊆ S :=
  NonUnitalStarAlgebra.gc _ _
#align non_unital_star_algebra.adjoin_le_iff NonUnitalStarAlgebra.adjoin_le_iff

theorem _root_.NonUnitalSubalgebra.starClosure_eq_adjoin (S : NonUnitalSubalgebra R A) :
    S.starClosure = adjoin R (S : Set A) :=
  le_antisymm (NonUnitalSubalgebra.starClosure_le_iff.2 <| subset_adjoin R (S : Set A))
    (adjoin_le (le_sup_left : S ≤ S ⊔ star S))
#align non_unital_subalgebra.star_closure_eq_adjoin NonUnitalSubalgebra.starClosure_eq_adjoin

instance : CompleteLattice (NonUnitalStarSubalgebra R A) :=
  GaloisInsertion.liftCompleteLattice NonUnitalStarAlgebra.gi

@[simp]
theorem coe_top : (↑(⊤ : NonUnitalStarSubalgebra R A) : Set A) = Set.univ :=
  rfl
#align non_unital_star_algebra.coe_top NonUnitalStarAlgebra.coe_top

@[simp]
theorem mem_top {x : A} : x ∈ (⊤ : NonUnitalStarSubalgebra R A) :=
  Set.mem_univ x
#align non_unital_star_algebra.mem_top NonUnitalStarAlgebra.mem_top

@[simp]
theorem top_toNonUnitalSubalgebra :
    (⊤ : NonUnitalStarSubalgebra R A).toNonUnitalSubalgebra = ⊤ := by
  ext
  simp
/- note: it is reasonable that `rfl` doesn't work here, because Lean would need to see that
`Set.univ ∪ star Set.univ = Set.univ` by definition. -/
#align non_unital_star_algebra.top_to_non_unital_subalgebra NonUnitalStarAlgebra.top_toNonUnitalSubalgebra

@[simp]
theorem toNonUnitalSubalgebra_eq_top {S : NonUnitalStarSubalgebra R A} :
    S.toNonUnitalSubalgebra = ⊤ ↔ S = ⊤ :=
  NonUnitalStarSubalgebra.toNonUnitalSubalgebra_injective.eq_iff' top_toNonUnitalSubalgebra
#align non_unital_star_algebra.to_non_unital_subalgebra_eq_top NonUnitalStarAlgebra.toNonUnitalSubalgebra_eq_top

theorem mem_sup_left {S T : NonUnitalStarSubalgebra R A} : ∀ {x : A}, x ∈ S → x ∈ S ⊔ T := by
  rw [←SetLike.le_def]
  exact le_sup_left
#align non_unital_star_algebra.mem_sup_left NonUnitalStarAlgebra.mem_sup_left

theorem mem_sup_right {S T : NonUnitalStarSubalgebra R A} : ∀ {x : A}, x ∈ T → x ∈ S ⊔ T := by
  rw [←SetLike.le_def]
  exact le_sup_right
#align non_unital_star_algebra.mem_sup_right NonUnitalStarAlgebra.mem_sup_right

theorem mul_mem_sup {S T : NonUnitalStarSubalgebra R A} {x y : A} (hx : x ∈ S) (hy : y ∈ T) :
    x * y ∈ S ⊔ T :=
  mul_mem (mem_sup_left hx) (mem_sup_right hy)
#align non_unital_star_algebra.mul_mem_sup NonUnitalStarAlgebra.mul_mem_sup

theorem map_sup (f : F) (S T : NonUnitalStarSubalgebra R A) :
    ((S ⊔ T).map f : NonUnitalStarSubalgebra R B) = S.map f ⊔ T.map f :=
  (NonUnitalStarSubalgebra.gc_map_comap f).l_sup
#align non_unital_star_algebra.map_sup NonUnitalStarAlgebra.map_sup

@[simp, norm_cast]
theorem coe_inf (S T : NonUnitalStarSubalgebra R A) : (↑(S ⊓ T) : Set A) = (S : Set A) ∩ T :=
  rfl
#align non_unital_star_algebra.coe_inf NonUnitalStarAlgebra.coe_inf

@[simp]
theorem mem_inf {S T : NonUnitalStarSubalgebra R A} {x : A} : x ∈ S ⊓ T ↔ x ∈ S ∧ x ∈ T :=
  Iff.rfl
#align non_unital_star_algebra.mem_inf NonUnitalStarAlgebra.mem_inf

@[simp]
theorem inf_toNonUnitalSubalgebra (S T : NonUnitalStarSubalgebra R A) :
    (S ⊓ T).toNonUnitalSubalgebra = S.toNonUnitalSubalgebra ⊓ T.toNonUnitalSubalgebra :=
  SetLike.coe_injective <| coe_inf _ _
  -- it's a bit surprising `rfl` fails here.
#align non_unital_star_algebra.inf_to_non_unital_subalgebra NonUnitalStarAlgebra.inf_toNonUnitalSubalgebra

@[simp, norm_cast]
theorem coe_sInf (S : Set (NonUnitalStarSubalgebra R A)) : (↑(sInf S) : Set A) = ⋂ s ∈ S, ↑s :=
  sInf_image
#align non_unital_star_algebra.coe_Inf NonUnitalStarAlgebra.coe_sInf

theorem mem_sInf {S : Set (NonUnitalStarSubalgebra R A)} {x : A} : x ∈ sInf S ↔ ∀ p ∈ S, x ∈ p := by
  simp only [← SetLike.mem_coe, coe_sInf, Set.mem_iInter₂]
#align non_unital_star_algebra.mem_Inf NonUnitalStarAlgebra.mem_sInf

@[simp]
theorem sInf_toNonUnitalSubalgebra (S : Set (NonUnitalStarSubalgebra R A)) :
    (sInf S).toNonUnitalSubalgebra = sInf (NonUnitalStarSubalgebra.toNonUnitalSubalgebra '' S) :=
  SetLike.coe_injective <| by simp
#align non_unital_star_algebra.Inf_to_non_unital_subalgebra NonUnitalStarAlgebra.sInf_toNonUnitalSubalgebra

@[simp, norm_cast]
theorem coe_iInf {ι : Sort _} {S : ι → NonUnitalStarSubalgebra R A} :
    (↑(⨅ i, S i) : Set A) = ⋂ i, S i := by simp [iInf]
#align non_unital_star_algebra.coe_infi NonUnitalStarAlgebra.coe_iInf

theorem mem_iInf {ι : Sort _} {S : ι → NonUnitalStarSubalgebra R A} {x : A} :
    (x ∈ ⨅ i, S i) ↔ ∀ i, x ∈ S i := by simp only [iInf, mem_sInf, Set.forall_range_iff]
#align non_unital_star_algebra.mem_infi NonUnitalStarAlgebra.mem_iInf

@[simp]
theorem iInf_toNonUnitalSubalgebra {ι : Sort _} (S : ι → NonUnitalStarSubalgebra R A) :
    (⨅ i, S i).toNonUnitalSubalgebra = ⨅ i, (S i).toNonUnitalSubalgebra :=
  SetLike.coe_injective <| by simp
#align non_unital_star_algebra.infi_to_non_unital_subalgebra NonUnitalStarAlgebra.iInf_toNonUnitalSubalgebra

instance : Inhabited (NonUnitalStarSubalgebra R A) :=
  ⟨⊥⟩

theorem mem_bot {x : A} : x ∈ (⊥ : NonUnitalStarSubalgebra R A) ↔ x = 0 :=
  show x ∈ NonUnitalAlgebra.adjoin R (∅ ∪ star ∅ : Set A) ↔ x = 0 by
    rw [Set.star_empty, Set.union_empty, NonUnitalAlgebra.adjoin_empty, NonUnitalAlgebra.mem_bot]
#align non_unital_star_algebra.mem_bot NonUnitalStarAlgebra.mem_bot

theorem toNonUnitalSubalgebra_bot :
    (⊥ : NonUnitalStarSubalgebra R A).toNonUnitalSubalgebra = ⊥ := by
  ext x
  simp only [mem_bot, NonUnitalStarSubalgebra.mem_toNonUnitalSubalgebra, NonUnitalAlgebra.mem_bot]
#align non_unital_star_algebra.to_non_unital_subalgebra_bot NonUnitalStarAlgebra.toNonUnitalSubalgebra_bot

@[simp]
theorem coe_bot : ((⊥ : NonUnitalStarSubalgebra R A) : Set A) = {0} := by
  simp only [Set.ext_iff, NonUnitalStarAlgebra.mem_bot, SetLike.mem_coe, Set.mem_singleton_iff,
    iff_self_iff, forall_const]
#align non_unital_star_algebra.coe_bot NonUnitalStarAlgebra.coe_bot

theorem eq_top_iff {S : NonUnitalStarSubalgebra R A} : S = ⊤ ↔ ∀ x : A, x ∈ S :=
  ⟨fun h x => by rw [h]; exact mem_top,
    fun h => by ext x; exact ⟨fun _ => mem_top, fun _ => h x⟩⟩
#align non_unital_star_algebra.eq_top_iff NonUnitalStarAlgebra.eq_top_iff

theorem range_top_iff_surjective (f : F) :
    NonUnitalStarAlgHom.range f = (⊤ : NonUnitalStarSubalgebra R B) ↔ Function.Surjective f :=
  NonUnitalStarAlgebra.eq_top_iff
#align non_unital_star_algebra.range_top_iff_surjective NonUnitalStarAlgebra.range_top_iff_surjective

@[simp]
theorem range_id : NonUnitalStarAlgHom.range (NonUnitalStarAlgHom.id R A) = ⊤ :=
  SetLike.coe_injective Set.range_id
#align non_unital_star_algebra.range_id NonUnitalStarAlgebra.range_id

@[simp]
theorem map_top (f : F) : (⊤ : NonUnitalStarSubalgebra R A).map f = NonUnitalStarAlgHom.range f :=
  SetLike.coe_injective Set.image_univ
#align non_unital_star_algebra.map_top NonUnitalStarAlgebra.map_top

@[simp]
theorem map_bot (f : F) : (⊥ : NonUnitalStarSubalgebra R A).map f = ⊥ :=
  SetLike.coe_injective <| by simp [NonUnitalAlgebra.coe_bot, NonUnitalStarSubalgebra.coe_map]
#align non_unital_star_algebra.map_bot NonUnitalStarAlgebra.map_bot

@[simp]
theorem comap_top (f : F) : (⊤ : NonUnitalStarSubalgebra R B).comap f = ⊤ :=
  eq_top_iff.2 fun _x => mem_top
#align non_unital_star_algebra.comap_top NonUnitalStarAlgebra.comap_top

/-- `non_unital_alg_hom` to `⊤ : non_unital_star_subalgebra R A`. -/
def toTop : A →⋆ₙₐ[R] (⊤ : NonUnitalStarSubalgebra R A) :=
  NonUnitalStarAlgHom.codRestrict (NonUnitalStarAlgHom.id R A) ⊤ fun _ => mem_top
#align non_unital_star_algebra.to_top NonUnitalStarAlgebra.toTop

end NonUnitalStarAlgebra

namespace NonUnitalStarSubalgebra

open NonUnitalStarAlgebra

variable [CommSemiring R] [StarRing R]
variable [NonUnitalSemiring A] [StarRing A]
variable [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A]
variable [NonUnitalSemiring B] [StarRing B]
variable [Module R B] [IsScalarTower R B B] [SMulCommClass R B B] [StarModule R B]
variable [hF : NonUnitalStarAlgHomClass F R A B] (S : NonUnitalStarSubalgebra R A)

/- can't have this until we refactor `alg_equiv`.
/-- The top non_unital_star_subalgebra is isomorphic to the algebra.

This is the algebra version of `submodule.top_equiv`. -/
@[simps] def top_equiv : (⊤ : non_unital_star_subalgebra R A) ≃ₐ[R] A :=
alg_equiv.of_alg_hom (non_unital_star_subalgebra_class.subtype ⊤) to_top rfl $
  non_unital_alg_hom.ext $ λ _, subtype.ext rfl
  -/
instance subsingleton_of_subsingleton [Subsingleton A] :
    Subsingleton (NonUnitalStarSubalgebra R A) :=
  ⟨fun B C => ext fun x => by simp only [Subsingleton.elim x 0, zero_mem B, zero_mem C]⟩
#align non_unital_star_subalgebra.subsingleton_of_subsingleton NonUnitalStarSubalgebra.subsingleton_of_subsingleton

instance _root_.NonUnitalStarAlgHom.subsingleton [Subsingleton (NonUnitalStarSubalgebra R A)] :
    Subsingleton (A →⋆ₙₐ[R] B) :=
  ⟨fun f g =>
    NonUnitalStarAlgHom.ext fun a =>
      have : a ∈ (⊥ : NonUnitalStarSubalgebra R A) :=
        Subsingleton.elim (⊤ : NonUnitalStarSubalgebra R A) ⊥ ▸ mem_top
      (mem_bot.mp this).symm ▸ (map_zero f).trans (map_zero g).symm⟩
#align non_unital_star_alg_hom.subsingleton NonUnitalStarAlgHom.subsingleton

/- need to refactor `alg_equiv` first
instance _root_.non_unital_alg_equiv.subsingleton_left [subsingleton (non_unital_star_subalgebra R A)] :
  subsingleton (A ≃ₐ[R] B) :=
⟨λ f g, alg_equiv.ext (λ x, alg_hom.ext_iff.mp (subsingleton.elim f.to_alg_hom g.to_alg_hom) x)⟩

instance _root_.alg_equiv.subsingleton_right [subsingleton (non_unital_star_subalgebra R B)] :
  subsingleton (A ≃ₐ[R] B) :=
⟨λ f g, by rw [← f.symm_symm, subsingleton.elim f.symm g.symm, g.symm_symm]⟩
-/
theorem range_val : NonUnitalStarAlgHom.range (NonUnitalStarSubalgebraClass.subtype S) = S :=
  ext <| Set.ext_iff.1 <| (NonUnitalStarSubalgebraClass.subtype S).coe_range.trans Subtype.range_val
#align non_unital_star_subalgebra.range_val NonUnitalStarSubalgebra.range_val

/--
The map `S → T` when `S` is a non_unital_star_subalgebra contained in the non_unital_star_subalgebra `T`.

This is the non_unital_star_subalgebra version of `submodule.of_le`, or `subring.inclusion`  -/
def inclusion {S T : NonUnitalStarSubalgebra R A} (h : S ≤ T) : S →ₙₐ[R] T
    where
  toFun := Set.inclusion h
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_smul' _ _ := rfl
#align non_unital_star_subalgebra.inclusion NonUnitalStarSubalgebra.inclusion

theorem inclusion_injective {S T : NonUnitalStarSubalgebra R A} (h : S ≤ T) :
    Function.Injective (inclusion h) := fun _ _ => Subtype.ext ∘ Subtype.mk.inj
#align non_unital_star_subalgebra.inclusion_injective NonUnitalStarSubalgebra.inclusion_injective

@[simp]
theorem inclusion_self {S : NonUnitalStarSubalgebra R A} :
    inclusion (le_refl S) = NonUnitalAlgHom.id R S :=
  NonUnitalAlgHom.ext fun _x => Subtype.ext rfl
#align non_unital_star_subalgebra.inclusion_self NonUnitalStarSubalgebra.inclusion_self

@[simp]
theorem inclusion_mk {S T : NonUnitalStarSubalgebra R A} (h : S ≤ T) (x : A) (hx : x ∈ S) :
    inclusion h ⟨x, hx⟩ = ⟨x, h hx⟩ :=
  rfl
#align non_unital_star_subalgebra.inclusion_mk NonUnitalStarSubalgebra.inclusion_mk

theorem inclusion_right {S T : NonUnitalStarSubalgebra R A} (h : S ≤ T) (x : T) (m : (x : A) ∈ S) :
    inclusion h ⟨x, m⟩ = x :=
  Subtype.ext rfl
#align non_unital_star_subalgebra.inclusion_right NonUnitalStarSubalgebra.inclusion_right

@[simp]
theorem inclusion_inclusion {S T U : NonUnitalStarSubalgebra R A} (hst : S ≤ T) (htu : T ≤ U)
    (x : S) : inclusion htu (inclusion hst x) = inclusion (le_trans hst htu) x :=
  Subtype.ext rfl
#align non_unital_star_subalgebra.inclusion_inclusion NonUnitalStarSubalgebra.inclusion_inclusion

@[simp]
theorem coe_inclusion {S T : NonUnitalStarSubalgebra R A} (h : S ≤ T) (s : S) :
    (inclusion h s : A) = s :=
  rfl
#align non_unital_star_subalgebra.coe_inclusion NonUnitalStarSubalgebra.coe_inclusion

/- need to refactor `alg_equiv`
/-- Two non_unital_star_subalgebras that are equal are also equivalent as algebras.

This is the `non_unital_star_subalgebra` version of `linear_equiv.of_eq` and `equiv.set.of_eq`. -/
@[simps apply]
def equiv_of_eq (S T : non_unital_star_subalgebra R A) (h : S = T) : S ≃ₐ[R] T :=
{ to_fun := λ x, ⟨x, h ▸ x.2⟩,
  inv_fun := λ x, ⟨x, h.symm ▸ x.2⟩,
  map_mul' := λ _ _, rfl,
  commutes' := λ _, rfl,
  .. linear_equiv.of_eq _ _ (congr_arg to_submodule h) }

@[simp] lemma equiv_of_eq_symm (S T : non_unital_star_subalgebra R A) (h : S = T) :
  (equiv_of_eq S T h).symm = equiv_of_eq T S h.symm :=
rfl

@[simp] lemma equiv_of_eq_rfl (S : non_unital_star_subalgebra R A) :
  equiv_of_eq S S rfl = alg_equiv.refl :=
by { ext, refl }

@[simp] lemma equiv_of_eq_trans (S T U : non_unital_star_subalgebra R A) (hST : S = T) (hTU : T = U) :
  (equiv_of_eq S T hST).trans (equiv_of_eq T U hTU) = equiv_of_eq S U (trans hST hTU) :=
rfl
  -/
section Prod

variable (S₁ : NonUnitalStarSubalgebra R B)

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- The product of two non_unital_star_subalgebras is a non_unital_star_subalgebra. -/
def prod : NonUnitalStarSubalgebra R (A × B) :=
  { S.toNonUnitalSubalgebra.prod S₁.toNonUnitalSubalgebra with
    carrier := S ×ˢ S₁
    star_mem' := fun hx => ⟨star_mem hx.1, star_mem hx.2⟩ }
#align non_unital_star_subalgebra.prod NonUnitalStarSubalgebra.prod

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem coe_prod : (prod S S₁ : Set (A × B)) = (S : Set A) ×ˢ S₁ :=
  rfl
#align non_unital_star_subalgebra.coe_prod NonUnitalStarSubalgebra.coe_prod

theorem prod_toNonUnitalSubalgebra :
    (S.prod S₁).toNonUnitalSubalgebra = S.toNonUnitalSubalgebra.prod S₁.toNonUnitalSubalgebra :=
  rfl
#align non_unital_star_subalgebra.prod_to_non_unital_subalgebra NonUnitalStarSubalgebra.prod_toNonUnitalSubalgebra

@[simp]
theorem mem_prod {S : NonUnitalStarSubalgebra R A} {S₁ : NonUnitalStarSubalgebra R B} {x : A × B} :
    x ∈ prod S S₁ ↔ x.1 ∈ S ∧ x.2 ∈ S₁ :=
  Set.mem_prod
#align non_unital_star_subalgebra.mem_prod NonUnitalStarSubalgebra.mem_prod

@[simp]
theorem prod_top : (prod ⊤ ⊤ : NonUnitalStarSubalgebra R (A × B)) = ⊤ := by ext; simp
#align non_unital_star_subalgebra.prod_top NonUnitalStarSubalgebra.prod_top

theorem prod_mono {S T : NonUnitalStarSubalgebra R A} {S₁ T₁ : NonUnitalStarSubalgebra R B} :
    S ≤ T → S₁ ≤ T₁ → prod S S₁ ≤ prod T T₁ :=
  Set.prod_mono
#align non_unital_star_subalgebra.prod_mono NonUnitalStarSubalgebra.prod_mono

@[simp]
theorem prod_inf_prod {S T : NonUnitalStarSubalgebra R A} {S₁ T₁ : NonUnitalStarSubalgebra R B} :
    S.prod S₁ ⊓ T.prod T₁ = (S ⊓ T).prod (S₁ ⊓ T₁) :=
  SetLike.coe_injective Set.prod_inter_prod
#align non_unital_star_subalgebra.prod_inf_prod NonUnitalStarSubalgebra.prod_inf_prod

end Prod

section SuprLift

variable {ι : Type _}

theorem coe_iSup_of_directed [Nonempty ι] {S : ι → NonUnitalStarSubalgebra R A}
    (dir : Directed (· ≤ ·) S) : ↑(iSup S) = ⋃ i, (S i : Set A) :=
  let K : NonUnitalStarSubalgebra R A :=
    { carrier := ⋃ i, S i
      zero_mem' :=
        let i := @Nonempty.some ι inferInstance
        Set.mem_iUnion.2 ⟨i, zero_mem (S i)⟩
      mul_mem' := fun hx hy =>
        let ⟨i, hi⟩ := Set.mem_iUnion.1 hx
        let ⟨j, hj⟩ := Set.mem_iUnion.1 hy
        let ⟨k, hik, hjk⟩ := dir i j
        Set.mem_iUnion.2 ⟨k, mul_mem (s := S k) (hik hi) (hjk hj)⟩
      add_mem' := fun hx hy =>
        let ⟨i, hi⟩ := Set.mem_iUnion.1 hx
        let ⟨j, hj⟩ := Set.mem_iUnion.1 hy
        let ⟨k, hik, hjk⟩ := dir i j
        Set.mem_iUnion.2 ⟨k, add_mem (s := S k) (hik hi) (hjk hj)⟩
      smul_mem' := fun r _x hx =>
        let ⟨i, hi⟩ := Set.mem_iUnion.1 hx
        Set.mem_iUnion.2 ⟨i, SMulMemClass.smul_mem (s := (S i)) r hi⟩
      star_mem' := fun hx =>
        let ⟨i, hi⟩ := Set.mem_iUnion.1 hx
        Set.mem_iUnion.2 ⟨i, star_mem (s := (S i)) hi⟩ }
  have : iSup S = K := le_antisymm (iSup_le fun i => Set.subset_iUnion (fun i => (S i : Set A)) i)
    (SetLike.coe_subset_coe.1 (Set.iUnion_subset fun _i => SetLike.coe_subset_coe.2 (le_iSup _ _)))
  this.symm ▸ rfl
#align non_unital_star_subalgebra.coe_supr_of_directed NonUnitalStarSubalgebra.coe_iSup_of_directed

/-- Define an algebra homomorphism on a directed supremum of non-unital subalgebras by defining
it on each non-unital subalgebra, and proving that it agrees on the intersection of
non-unital subalgebras. -/
noncomputable def suprLift [Nonempty ι] (K : ι → NonUnitalStarSubalgebra R A)
    (dir : Directed (· ≤ ·) K) (f : ∀ i, K i →ₙₐ[R] B)
    (hf : ∀ (i j : ι) (h : K i ≤ K j), f i = (f j).comp (inclusion h))
    (T : NonUnitalStarSubalgebra R A) (hT : T = iSup K) : ↥T →ₙₐ[R] B := by
  subst hT <;>
    exact
      { toFun :=
          Set.iUnionLift (fun i => ↑(K i)) (fun i x => f i x)
            (fun i j x hxi hxj => by
              let ⟨k, hik, hjk⟩ := dir i j
              rw [hf i k hik, hf j k hjk]
              rfl)
            (↑(iSup K)) (by rw [coe_supr_of_directed dir] <;> rfl)
        map_zero' := Set.iUnionLift_const _ (fun _ => 0) (fun _ => rfl) _ (by simp)
        map_mul' :=
          Set.iUnionLift_binary (coe_supr_of_directed dir) dir _ (fun _ => (· * ·))
            (fun _ _ _ => rfl) _ (by simp)
        map_add' :=
          Set.iUnionLift_binary (coe_supr_of_directed dir) dir _ (fun _ => (· + ·))
            (fun _ _ _ => rfl) _ (by simp)
        map_smul' := fun r =>
          Set.iUnionLift_unary (coe_supr_of_directed dir) _ (fun _ x => r • x) (fun _ _ => rfl) _
            (by simp) }
#align non_unital_star_subalgebra.supr_lift NonUnitalStarSubalgebra.suprLift

variable [Nonempty ι] {K : ι → NonUnitalStarSubalgebra R A} {dir : Directed (· ≤ ·) K}
  {f : ∀ i, K i →ₙₐ[R] B} {hf : ∀ (i j : ι) (h : K i ≤ K j), f i = (f j).comp (inclusion h)}
  {T : NonUnitalStarSubalgebra R A} {hT : T = iSup K}

@[simp]
theorem suprLift_inclusion {i : ι} (x : K i) (h : K i ≤ T) :
    suprLift K dir f hf T hT (inclusion h x) = f i x := by
  subst T <;> exact Set.iUnionLift_inclusion _ _
#align non_unital_star_subalgebra.supr_lift_inclusion NonUnitalStarSubalgebra.suprLift_inclusion

@[simp]
theorem suprLift_comp_inclusion {i : ι} (h : K i ≤ T) :
    (suprLift K dir f hf T hT).comp (inclusion h) = f i := by ext <;> simp
#align non_unital_star_subalgebra.supr_lift_comp_inclusion NonUnitalStarSubalgebra.suprLift_comp_inclusion

@[simp]
theorem suprLift_mk {i : ι} (x : K i) (hx : (x : A) ∈ T) :
    suprLift K dir f hf T hT ⟨x, hx⟩ = f i x := by subst hT <;> exact Set.iUnionLift_mk x hx
#align non_unital_star_subalgebra.supr_lift_mk NonUnitalStarSubalgebra.suprLift_mk

theorem suprLift_of_mem {i : ι} (x : T) (hx : (x : A) ∈ K i) :
    suprLift K dir f hf T hT x = f i ⟨x, hx⟩ := by subst hT <;> exact Set.iUnionLift_of_mem x hx
#align non_unital_star_subalgebra.supr_lift_of_mem NonUnitalStarSubalgebra.suprLift_of_mem

end SuprLift

section Center

variable (R A)

/-- The center of an algebra is the set of elements which commute with every element. They form a
non-unital subalgebra. -/
def center : NonUnitalStarSubalgebra R A :=
  { NonUnitalSubalgebra.center R A with star_mem' := fun a => Set.star_mem_center' }
#align non_unital_star_subalgebra.center NonUnitalStarSubalgebra.center

theorem coe_center : (center R A : Set A) = Set.center A :=
  rfl
#align non_unital_star_subalgebra.coe_center NonUnitalStarSubalgebra.coe_center

@[simp]
theorem center_toNonUnitalSubalgebra :
    (center R A).toNonUnitalSubalgebra = NonUnitalSubalgebra.center R A :=
  rfl
#align non_unital_star_subalgebra.center_to_non_unital_subalgebra NonUnitalStarSubalgebra.center_toNonUnitalSubalgebra

@[simp]
theorem center_eq_top (A : Type _) [NonUnitalCommSemiring A] [StarRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A] : center R A = ⊤ :=
  SetLike.coe_injective (Set.center_eq_univ A)
#align non_unital_star_subalgebra.center_eq_top NonUnitalStarSubalgebra.center_eq_top

variable {R A}

/-
instance : comm_semiring (center R A) := non_unital_subalgebra.center.comm_semiring

instance {A : Type*} [non_unital_ring A] [star_ring A] [module R A] [is_scalar_tower R A A]
  [smul_comm_class R A A] [star_module R A] : comm_ring (center R A) :=
non_unital_subring.center.comm_ring
-/
theorem mem_center_iff {a : A} : a ∈ center R A ↔ ∀ b : A, b * a = a * b :=
  Iff.rfl
#align non_unital_star_subalgebra.mem_center_iff NonUnitalStarSubalgebra.mem_center_iff

end Center

section Centralizer

variable (R)

/-- The centralizer of the star-closure of a set as a non-unital star subalgebra. -/
def centralizer (s : Set A) : NonUnitalStarSubalgebra R A :=
  { NonUnitalSubalgebra.centralizer R (s ∪ star s) with
    star_mem' := fun a => Set.star_mem_centralizer' }
#align non_unital_star_subalgebra.centralizer NonUnitalStarSubalgebra.centralizer

@[simp, norm_cast]
theorem coe_centralizer (s : Set A) : (centralizer R s : Set A) = (s ∪ star s).centralizer :=
  rfl
#align non_unital_star_subalgebra.coe_centralizer NonUnitalStarSubalgebra.coe_centralizer

theorem mem_centralizer_iff {s : Set A} {z : A} :
    z ∈ centralizer R s ↔ ∀ g ∈ s, g * z = z * g ∧ star g * z = z * star g :=
  by
  show (∀ g ∈ s ∪ star s, g * z = z * g) ↔ ∀ g ∈ s, g * z = z * g ∧ star g * z = z * star g
  simp only [Set.mem_union, or_imp, forall_and, and_congr_right_iff]
  exact fun h =>
    ⟨fun hz a ha => hz _ (set.star_mem_star.mpr ha), fun hz a ha => star_star a ▸ hz _ ha⟩
#align non_unital_star_subalgebra.mem_centralizer_iff NonUnitalStarSubalgebra.mem_centralizer_iff

theorem centralizer_le (s t : Set A) (h : s ⊆ t) : centralizer R t ≤ centralizer R s :=
  Set.centralizer_subset (Set.union_subset_union h <| Set.preimage_mono h)
#align non_unital_star_subalgebra.centralizer_le NonUnitalStarSubalgebra.centralizer_le

@[simp]
theorem centralizer_univ : centralizer R Set.univ = center R A :=
  SetLike.ext' <| by rw [coe_centralizer, Set.univ_union, coe_center, Set.centralizer_univ]
#align non_unital_star_subalgebra.centralizer_univ NonUnitalStarSubalgebra.centralizer_univ

end Centralizer

end NonUnitalStarSubalgebra
