/-
Copyright (c) 2023 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Algebra.Algebra.NonUnitalSubalgebra
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.Center
import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.Algebra.Star.Prod

/-!
# Non-unital Star Subalgebras

In this file we define `NonUnitalStarSubalgebra`s and the usual operations on them
(`map`, `comap`).

## TODO

* once we have scalar actions by semigroups (as opposed to monoids), implement the action of a
  non-unital subalgebra on the larger algebra.
-/

namespace StarMemClass

/-- If a type carries an involutive star, then any star-closed subset does too. -/
instance instInvolutiveStar {S R : Type*} [InvolutiveStar R] [SetLike S R] [StarMemClass S R]
    (s : S) : InvolutiveStar s where
  star_involutive r := Subtype.ext <| star_star (r : R)

/-- In a star magma (i.e., a multiplication with an antimultiplicative involutive star
operation), any star-closed subset which is also closed under multiplication is itself a star
magma. -/
instance instStarMul {S R : Type*} [Mul R] [StarMul R] [SetLike S R]
    [MulMemClass S R] [StarMemClass S R] (s : S) : StarMul s where
  star_mul _ _ := Subtype.ext <| star_mul _ _

/-- In a `StarAddMonoid` (i.e., an additive monoid with an additive involutive star operation), any
star-closed subset which is also closed under addition and contains zero is itself a
`StarAddMonoid`. -/
instance instStarAddMonoid {S R : Type*} [AddMonoid R] [StarAddMonoid R] [SetLike S R]
    [AddSubmonoidClass S R] [StarMemClass S R] (s : S) : StarAddMonoid s where
  star_add _ _ := Subtype.ext <| star_add _ _

/-- In a star ring (i.e., a non-unital, non-associative, semiring with an additive,
antimultiplicative, involutive star operation), a star-closed non-unital subsemiring is itself a
star ring. -/
instance instStarRing {S R : Type*} [NonUnitalNonAssocSemiring R] [StarRing R] [SetLike S R]
    [NonUnitalSubsemiringClass S R] [StarMemClass S R] (s : S) : StarRing s :=
  { StarMemClass.instStarMul s, StarMemClass.instStarAddMonoid s with }

/-- In a star `R`-module (i.e., `star (r • m) = (star r) • m`) any star-closed subset which is also
closed under the scalar action by `R` is itself a star `R`-module. -/
instance instStarModule {S : Type*} (R : Type*) {M : Type*} [Star R] [Star M] [SMul R M]
    [StarModule R M] [SetLike S M] [SMulMemClass S R M] [StarMemClass S M] (s : S) :
    StarModule R s where
  star_smul _ _ := Subtype.ext <| star_smul _ _

end StarMemClass

universe u u' v v' w w' w''

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

variable {s} in
@[simp]
lemma subtype_apply (x : s) : subtype s x = x := rfl

lemma subtype_injective :
    Function.Injective (subtype s) :=
  Subtype.coe_injective

@[simp]
theorem coe_subtype : (subtype s : s → A) = Subtype.val :=
  rfl

end NonUnitalStarSubalgebraClass

/-- A non-unital star subalgebra is a non-unital subalgebra which is closed under the `star`
operation. -/
structure NonUnitalStarSubalgebra (R : Type u) (A : Type v) [CommSemiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [Star A] : Type v
    extends NonUnitalSubalgebra R A where
  /-- The `carrier` of a `NonUnitalStarSubalgebra` is closed under the `star` operation. -/
  star_mem' : ∀ {a : A} (_ha : a ∈ carrier), star a ∈ carrier

/-- Reinterpret a `NonUnitalStarSubalgebra` as a `NonUnitalSubalgebra`. -/
add_decl_doc NonUnitalStarSubalgebra.toNonUnitalSubalgebra

namespace NonUnitalStarSubalgebra

variable [CommSemiring R]
variable [NonUnitalNonAssocSemiring A] [Module R A] [Star A]
variable [NonUnitalNonAssocSemiring B] [Module R B] [Star B]
variable [NonUnitalNonAssocSemiring C] [Module R C] [Star C]
variable [FunLike F A B] [NonUnitalAlgHomClass F R A B] [StarHomClass F A B]

instance instSetLike : SetLike (NonUnitalStarSubalgebra R A) A where
  coe {s} := s.carrier
  coe_injective' p q h := by cases p; cases q; congr; exact SetLike.coe_injective h

/-- The actual `NonUnitalStarSubalgebra` obtained from an element of a type satisfying
`NonUnitalSubsemiringClass`, `SMulMemClass` and `StarMemClass`. -/
@[simps]
def ofClass {S R A : Type*} [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A] [Star A]
    [SetLike S A] [NonUnitalSubsemiringClass S A] [SMulMemClass S R A] [StarMemClass S A]
    (s : S) : NonUnitalStarSubalgebra R A where
  carrier := s
  add_mem' := add_mem
  zero_mem' := zero_mem _
  mul_mem' := mul_mem
  smul_mem' := SMulMemClass.smul_mem
  star_mem' := star_mem

instance (priority := 100) : CanLift (Set A) (NonUnitalStarSubalgebra R A) (↑)
    (fun s ↦ 0 ∈ s ∧ (∀ {x y}, x ∈ s → y ∈ s → x + y ∈ s) ∧ (∀ {x y}, x ∈ s → y ∈ s → x * y ∈ s) ∧
      (∀ (r : R) {x}, x ∈ s → r • x ∈ s) ∧ ∀ {x}, x ∈ s → star x ∈ s) where
  prf s h :=
    ⟨ { carrier := s
        zero_mem' := h.1
        add_mem' := h.2.1
        mul_mem' := h.2.2.1
        smul_mem' := h.2.2.2.1
        star_mem' := h.2.2.2.2 },
      rfl ⟩

instance instNonUnitalSubsemiringClass :
    NonUnitalSubsemiringClass (NonUnitalStarSubalgebra R A) A where
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

@[ext]
theorem ext {S T : NonUnitalStarSubalgebra R A} (h : ∀ x : A, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h

@[simp]
theorem mem_toNonUnitalSubalgebra {S : NonUnitalStarSubalgebra R A} {x} :
    x ∈ S.toNonUnitalSubalgebra ↔ x ∈ S :=
  Iff.rfl

@[simp]
theorem coe_toNonUnitalSubalgebra (S : NonUnitalStarSubalgebra R A) :
    (↑S.toNonUnitalSubalgebra : Set A) = S :=
  rfl

theorem toNonUnitalSubalgebra_injective :
    Function.Injective
      (toNonUnitalSubalgebra : NonUnitalStarSubalgebra R A → NonUnitalSubalgebra R A) :=
  fun S T h =>
  ext fun x => by rw [← mem_toNonUnitalSubalgebra, ← mem_toNonUnitalSubalgebra, h]

theorem toNonUnitalSubalgebra_inj {S U : NonUnitalStarSubalgebra R A} :
    S.toNonUnitalSubalgebra = U.toNonUnitalSubalgebra ↔ S = U :=
  toNonUnitalSubalgebra_injective.eq_iff

theorem toNonUnitalSubalgebra_le_iff {S₁ S₂ : NonUnitalStarSubalgebra R A} :
    S₁.toNonUnitalSubalgebra ≤ S₂.toNonUnitalSubalgebra ↔ S₁ ≤ S₂ :=
  Iff.rfl

/-- Copy of a non-unital star subalgebra with a new `carrier` equal to the old one.
Useful to fix definitional equalities. -/
protected def copy (S : NonUnitalStarSubalgebra R A) (s : Set A) (hs : s = ↑S) :
    NonUnitalStarSubalgebra R A :=
  { S.toNonUnitalSubalgebra.copy s hs with
    star_mem' := @fun x (hx : x ∈ s) => by
      change star x ∈ s
      rw [hs] at hx ⊢
      exact S.star_mem' hx }

@[simp]
theorem coe_copy (S : NonUnitalStarSubalgebra R A) (s : Set A) (hs : s = ↑S) :
    (S.copy s hs : Set A) = s :=
  rfl

theorem copy_eq (S : NonUnitalStarSubalgebra R A) (s : Set A) (hs : s = ↑S) : S.copy s hs = S :=
  SetLike.coe_injective hs

variable (S : NonUnitalStarSubalgebra R A)

/-- A non-unital star subalgebra over a ring is also a `Subring`. -/
def toNonUnitalSubring {R : Type u} {A : Type v} [CommRing R] [NonUnitalRing A] [Module R A]
    [Star A] (S : NonUnitalStarSubalgebra R A) : NonUnitalSubring A where
  toNonUnitalSubsemiring := S.toNonUnitalSubsemiring
  neg_mem' := neg_mem (s := S)

@[simp]
theorem mem_toNonUnitalSubring {R : Type u} {A : Type v} [CommRing R] [NonUnitalRing A] [Module R A]
    [Star A] {S : NonUnitalStarSubalgebra R A} {x} : x ∈ S.toNonUnitalSubring ↔ x ∈ S :=
  Iff.rfl

@[simp]
theorem coe_toNonUnitalSubring {R : Type u} {A : Type v} [CommRing R] [NonUnitalRing A] [Module R A]
    [Star A] (S : NonUnitalStarSubalgebra R A) : (↑S.toNonUnitalSubring : Set A) = S :=
  rfl

theorem toNonUnitalSubring_injective {R : Type u} {A : Type v} [CommRing R] [NonUnitalRing A]
    [Module R A] [Star A] :
    Function.Injective (toNonUnitalSubring : NonUnitalStarSubalgebra R A → NonUnitalSubring A) :=
  fun S T h => ext fun x => by rw [← mem_toNonUnitalSubring, ← mem_toNonUnitalSubring, h]

theorem toNonUnitalSubring_inj {R : Type u} {A : Type v} [CommRing R] [NonUnitalRing A] [Module R A]
    [Star A] {S U : NonUnitalStarSubalgebra R A} :
    S.toNonUnitalSubring = U.toNonUnitalSubring ↔ S = U :=
  toNonUnitalSubring_injective.eq_iff

instance instInhabited : Inhabited S :=
  ⟨(0 : S.toNonUnitalSubalgebra)⟩

section

/-! `NonUnitalStarSubalgebra`s inherit structure from their `NonUnitalSubsemiringClass` and
`NonUnitalSubringClass` instances. -/

instance toNonUnitalSemiring {R A} [CommSemiring R] [NonUnitalSemiring A] [Module R A] [Star A]
    (S : NonUnitalStarSubalgebra R A) : NonUnitalSemiring S :=
  inferInstance

instance toNonUnitalCommSemiring {R A} [CommSemiring R] [NonUnitalCommSemiring A] [Module R A]
    [Star A] (S : NonUnitalStarSubalgebra R A) : NonUnitalCommSemiring S :=
  inferInstance

instance toNonUnitalRing {R A} [CommRing R] [NonUnitalRing A] [Module R A] [Star A]
    (S : NonUnitalStarSubalgebra R A) : NonUnitalRing S :=
  inferInstance

instance toNonUnitalCommRing {R A} [CommRing R] [NonUnitalCommRing A] [Module R A] [Star A]
    (S : NonUnitalStarSubalgebra R A) : NonUnitalCommRing S :=
  inferInstance
end

/-- The forgetful map from `NonUnitalStarSubalgebra` to `NonUnitalSubalgebra` as an
`OrderEmbedding` -/
def toNonUnitalSubalgebra' : NonUnitalStarSubalgebra R A ↪o NonUnitalSubalgebra R A where
  toEmbedding :=
    { toFun := fun S => S.toNonUnitalSubalgebra
      inj' := fun S T h => ext <| by apply SetLike.ext_iff.1 h }
  map_rel_iff' := SetLike.coe_subset_coe.symm.trans SetLike.coe_subset_coe

section

/-! `NonUnitalStarSubalgebra`s inherit structure from their `Submodule` coercions. -/

instance module' [Semiring R'] [SMul R' R] [Module R' A] [IsScalarTower R' R A] : Module R' S :=
  SMulMemClass.toModule' _ R' R A S

instance instModule : Module R S :=
  S.module'

instance instIsScalarTower' [Semiring R'] [SMul R' R] [Module R' A] [IsScalarTower R' R A] :
    IsScalarTower R' R S :=
  S.toNonUnitalSubalgebra.instIsScalarTower'

instance instIsScalarTower [IsScalarTower R A A] : IsScalarTower R S S where
  smul_assoc r x y := Subtype.ext <| smul_assoc r (x : A) (y : A)

instance instSMulCommClass' [Semiring R'] [SMul R' R] [Module R' A] [IsScalarTower R' R A]
    [SMulCommClass R' R A] : SMulCommClass R' R S where
  smul_comm r' r s := Subtype.ext <| smul_comm r' r (s : A)

instance instSMulCommClass [SMulCommClass R A A] : SMulCommClass R S S where
  smul_comm r x y := Subtype.ext <| smul_comm r (x : A) (y : A)

end

instance noZeroSMulDivisors_bot [NoZeroSMulDivisors R A] : NoZeroSMulDivisors R S :=
  ⟨fun {c x} h =>
    have : c = 0 ∨ (x : A) = 0 := eq_zero_or_eq_zero_of_smul_eq_zero (congr_arg ((↑) : S → A) h)
    this.imp_right (@Subtype.ext_iff _ _ x 0).mpr⟩

protected theorem coe_add (x y : S) : (↑(x + y) : A) = ↑x + ↑y :=
  rfl

protected theorem coe_mul (x y : S) : (↑(x * y) : A) = ↑x * ↑y :=
  rfl

protected theorem coe_zero : ((0 : S) : A) = 0 :=
  rfl

protected theorem coe_neg {R : Type u} {A : Type v} [CommRing R] [NonUnitalNonAssocRing A]
    [Module R A] [Star A] {S : NonUnitalStarSubalgebra R A} (x : S) : (↑(-x) : A) = -↑x :=
  rfl

protected theorem coe_sub {R : Type u} {A : Type v} [CommRing R] [NonUnitalNonAssocRing A]
    [Module R A] [Star A] {S : NonUnitalStarSubalgebra R A} (x y : S) : (↑(x - y) : A) = ↑x - ↑y :=
  rfl

@[simp, norm_cast]
theorem coe_smul [SMul R' R] [SMul R' A] [IsScalarTower R' R A] (r : R') (x : S) :
    ↑(r • x) = r • (x : A) :=
  rfl

protected theorem coe_eq_zero {x : S} : (x : A) = 0 ↔ x = 0 :=
  ZeroMemClass.coe_eq_zero

@[simp]
theorem toNonUnitalSubalgebra_subtype :
    NonUnitalSubalgebraClass.subtype S = NonUnitalStarSubalgebraClass.subtype S :=
  rfl

@[simp]
theorem toSubring_subtype {R A : Type*} [CommRing R] [NonUnitalNonAssocRing A] [Module R A] [Star A]
    (S : NonUnitalStarSubalgebra R A) :
    NonUnitalSubringClass.subtype S = NonUnitalStarSubalgebraClass.subtype S :=
  rfl

/-- Transport a non-unital star subalgebra via a non-unital star algebra homomorphism. -/
def map (f : F) (S : NonUnitalStarSubalgebra R A) : NonUnitalStarSubalgebra R B where
  toNonUnitalSubalgebra := S.toNonUnitalSubalgebra.map (f : A →ₙₐ[R] B)
  star_mem' := by rintro _ ⟨a, ha, rfl⟩; exact ⟨star a, star_mem (s := S) ha, map_star f a⟩

theorem map_mono {S₁ S₂ : NonUnitalStarSubalgebra R A} {f : F} :
    S₁ ≤ S₂ → (map f S₁ : NonUnitalStarSubalgebra R B) ≤ map f S₂ :=
  Set.image_mono

theorem map_injective {f : F} (hf : Function.Injective f) :
    Function.Injective (map f : NonUnitalStarSubalgebra R A → NonUnitalStarSubalgebra R B) :=
  fun _S₁ _S₂ ih =>
  ext <| Set.ext_iff.1 <| Set.image_injective.2 hf <| Set.ext <| SetLike.ext_iff.mp ih

@[simp]
theorem map_id (S : NonUnitalStarSubalgebra R A) : map (NonUnitalStarAlgHom.id R A) S = S :=
  SetLike.coe_injective <| Set.image_id _

theorem map_map (S : NonUnitalStarSubalgebra R A) (g : B →⋆ₙₐ[R] C) (f : A →⋆ₙₐ[R] B) :
    (S.map f).map g = S.map (g.comp f) :=
  SetLike.coe_injective <| Set.image_image _ _ _

@[simp]
theorem mem_map {S : NonUnitalStarSubalgebra R A} {f : F} {y : B} :
    y ∈ map f S ↔ ∃ x ∈ S, f x = y :=
  NonUnitalSubalgebra.mem_map

theorem map_toNonUnitalSubalgebra {S : NonUnitalStarSubalgebra R A} {f : F} :
    (map f S : NonUnitalStarSubalgebra R B).toNonUnitalSubalgebra =
      NonUnitalSubalgebra.map f S.toNonUnitalSubalgebra :=
  SetLike.coe_injective rfl

@[simp]
theorem coe_map (S : NonUnitalStarSubalgebra R A) (f : F) : map f S = f '' S :=
  rfl

/-- Preimage of a non-unital star subalgebra under a non-unital star algebra homomorphism. -/
def comap (f : F) (S : NonUnitalStarSubalgebra R B) : NonUnitalStarSubalgebra R A where
  toNonUnitalSubalgebra := S.toNonUnitalSubalgebra.comap f
  star_mem' := @fun a (ha : f a ∈ S) =>
    show f (star a) ∈ S from (map_star f a).symm ▸ star_mem (s := S) ha

theorem map_le {S : NonUnitalStarSubalgebra R A} {f : F} {U : NonUnitalStarSubalgebra R B} :
    map f S ≤ U ↔ S ≤ comap f U :=
  Set.image_subset_iff

theorem gc_map_comap (f : F) : GaloisConnection (map f) (comap f) :=
  fun _S _U => map_le

@[simp]
theorem mem_comap (S : NonUnitalStarSubalgebra R B) (f : F) (x : A) : x ∈ comap f S ↔ f x ∈ S :=
  Iff.rfl

@[simp, norm_cast]
theorem coe_comap (S : NonUnitalStarSubalgebra R B) (f : F) : comap f S = f ⁻¹' (S : Set B) :=
  rfl

instance instNoZeroDivisors {R A : Type*} [CommSemiring R] [NonUnitalSemiring A] [NoZeroDivisors A]
    [Module R A] [Star A] (S : NonUnitalStarSubalgebra R A) : NoZeroDivisors S :=
  NonUnitalSubsemiringClass.noZeroDivisors S

end NonUnitalStarSubalgebra

namespace NonUnitalSubalgebra

variable [CommSemiring R] [NonUnitalSemiring A] [Module R A] [Star A]
variable (s : NonUnitalSubalgebra R A)

/-- A non-unital subalgebra closed under `star` is a non-unital star subalgebra. -/
def toNonUnitalStarSubalgebra (h_star : ∀ x, x ∈ s → star x ∈ s) : NonUnitalStarSubalgebra R A :=
  { s with
    star_mem' := @h_star }

@[simp]
theorem mem_toNonUnitalStarSubalgebra {s : NonUnitalSubalgebra R A} {h_star} {x} :
    x ∈ s.toNonUnitalStarSubalgebra h_star ↔ x ∈ s :=
  Iff.rfl

@[simp]
theorem coe_toNonUnitalStarSubalgebra (s : NonUnitalSubalgebra R A) (h_star) :
    (s.toNonUnitalStarSubalgebra h_star : Set A) = s :=
  rfl

@[simp]
theorem toNonUnitalStarSubalgebra_toNonUnitalSubalgebra (s : NonUnitalSubalgebra R A) (h_star) :
    (s.toNonUnitalStarSubalgebra h_star).toNonUnitalSubalgebra = s :=
  SetLike.coe_injective rfl

@[simp]
theorem _root_.NonUnitalStarSubalgebra.toNonUnitalSubalgebra_toNonUnitalStarSubalgebra
    (S : NonUnitalStarSubalgebra R A) :
    (S.toNonUnitalSubalgebra.toNonUnitalStarSubalgebra fun _ => star_mem (s := S)) = S :=
  SetLike.coe_injective rfl

end NonUnitalSubalgebra
namespace NonUnitalStarAlgHom

variable [CommSemiring R]
variable [NonUnitalNonAssocSemiring A] [Module R A] [Star A]
variable [NonUnitalNonAssocSemiring B] [Module R B] [Star B]
variable [NonUnitalNonAssocSemiring C] [Module R C] [Star C]
variable [FunLike F A B] [NonUnitalAlgHomClass F R A B] [StarHomClass F A B]

/-- Range of an `NonUnitalAlgHom` as a `NonUnitalStarSubalgebra`. -/
protected def range (φ : F) : NonUnitalStarSubalgebra R B where
  toNonUnitalSubalgebra := NonUnitalAlgHom.range (φ : A →ₙₐ[R] B)
  star_mem' := by rintro _ ⟨a, rfl⟩; exact ⟨star a, map_star φ a⟩

@[simp]
theorem mem_range (φ : F) {y : B} :
    y ∈ (NonUnitalStarAlgHom.range φ : NonUnitalStarSubalgebra R B) ↔ ∃ x : A, φ x = y :=
  NonUnitalRingHom.mem_srange

theorem mem_range_self (φ : F) (x : A) :
    φ x ∈ (NonUnitalStarAlgHom.range φ : NonUnitalStarSubalgebra R B) :=
  (NonUnitalAlgHom.mem_range φ).2 ⟨x, rfl⟩

@[simp]
theorem coe_range (φ : F) :
    ((NonUnitalStarAlgHom.range φ : NonUnitalStarSubalgebra R B) : Set B) = Set.range (φ : A → B) :=
  by ext; rw [SetLike.mem_coe, mem_range]; rfl

theorem range_comp (f : A →⋆ₙₐ[R] B) (g : B →⋆ₙₐ[R] C) :
    NonUnitalStarAlgHom.range (g.comp f) = (NonUnitalStarAlgHom.range f).map g :=
  SetLike.coe_injective (Set.range_comp g f)

theorem range_comp_le_range (f : A →⋆ₙₐ[R] B) (g : B →⋆ₙₐ[R] C) :
    NonUnitalStarAlgHom.range (g.comp f) ≤ NonUnitalStarAlgHom.range g :=
  SetLike.coe_mono (Set.range_comp_subset_range f g)

/-- Restrict the codomain of a non-unital star algebra homomorphism. -/
def codRestrict (f : F) (S : NonUnitalStarSubalgebra R B) (hf : ∀ x, f x ∈ S) : A →⋆ₙₐ[R] S where
  toNonUnitalAlgHom := NonUnitalAlgHom.codRestrict f S.toNonUnitalSubalgebra hf
  map_star' := fun a => Subtype.ext <| map_star f a

@[simp]
theorem subtype_comp_codRestrict (f : F) (S : NonUnitalStarSubalgebra R B) (hf : ∀ x : A, f x ∈ S) :
    (NonUnitalStarSubalgebraClass.subtype S).comp (NonUnitalStarAlgHom.codRestrict f S hf) = f :=
  NonUnitalStarAlgHom.ext fun _ => rfl

@[simp]
theorem coe_codRestrict (f : F) (S : NonUnitalStarSubalgebra R B) (hf : ∀ x, f x ∈ S) (x : A) :
    ↑(NonUnitalStarAlgHom.codRestrict f S hf x) = f x :=
  rfl

theorem injective_codRestrict (f : F) (S : NonUnitalStarSubalgebra R B) (hf : ∀ x : A, f x ∈ S) :
    Function.Injective (NonUnitalStarAlgHom.codRestrict f S hf) ↔ Function.Injective f :=
  ⟨fun H _x _y hxy => H <| Subtype.eq hxy, fun H _x _y hxy => H (congr_arg Subtype.val hxy :)⟩

/-- Restrict the codomain of a non-unital star algebra homomorphism `f` to `f.range`.

This is the bundled version of `Set.rangeFactorization`. -/
abbrev rangeRestrict (f : F) :
    A →⋆ₙₐ[R] (NonUnitalStarAlgHom.range f : NonUnitalStarSubalgebra R B) :=
  NonUnitalStarAlgHom.codRestrict f (NonUnitalStarAlgHom.range f)
    (NonUnitalStarAlgHom.mem_range_self f)

/-- The equalizer of two non-unital star `R`-algebra homomorphisms -/
def equalizer (ϕ ψ : F) : NonUnitalStarSubalgebra R A where
  toNonUnitalSubalgebra := NonUnitalAlgHom.equalizer ϕ ψ
  star_mem' := @fun x (hx : ϕ x = ψ x) => by simp [map_star, hx]

@[simp]
theorem mem_equalizer (φ ψ : F) (x : A) :
    x ∈ NonUnitalStarAlgHom.equalizer φ ψ ↔ φ x = ψ x :=
  Iff.rfl

end NonUnitalStarAlgHom

namespace StarAlgEquiv
variable [CommSemiring R]
variable [NonUnitalSemiring A] [Module R A] [Star A]
variable [NonUnitalSemiring B] [Module R B] [Star B]
variable [NonUnitalSemiring C] [Module R C] [Star C]
variable [FunLike F A B] [NonUnitalAlgHomClass F R A B] [StarHomClass F A B]

/-- Restrict a non-unital star algebra homomorphism with a left inverse to an algebra isomorphism
to its range.

This is a computable alternative to `StarAlgEquiv.ofInjective`. -/
def ofLeftInverse' {g : B → A} {f : F} (h : Function.LeftInverse g f) :
    A ≃⋆ₐ[R] NonUnitalStarAlgHom.range f :=
  { NonUnitalStarAlgHom.rangeRestrict f with
    toFun := NonUnitalStarAlgHom.rangeRestrict f
    invFun := g ∘ (NonUnitalStarSubalgebraClass.subtype <| NonUnitalStarAlgHom.range f)
    left_inv := h
    right_inv := fun x =>
      Subtype.ext <|
        let ⟨x', hx'⟩ := (NonUnitalStarAlgHom.mem_range f).mp x.prop
        show f (g x) = x by rw [← hx', h x'] }

@[simp]
theorem ofLeftInverse'_apply {g : B → A} {f : F} (h : Function.LeftInverse g f) (x : A) :
    ofLeftInverse' h x = f x :=
  rfl

@[simp]
theorem ofLeftInverse'_symm_apply {g : B → A} {f : F} (h : Function.LeftInverse g f)
    (x : NonUnitalStarAlgHom.range f) : (ofLeftInverse' h).symm x = g x :=
  rfl

/-- Restrict an injective non-unital star algebra homomorphism to a star algebra isomorphism -/
noncomputable def ofInjective' (f : F) (hf : Function.Injective f) :
    A ≃⋆ₐ[R] NonUnitalStarAlgHom.range f :=
  ofLeftInverse' (Classical.choose_spec hf.hasLeftInverse)

@[simp]
theorem ofInjective'_apply (f : F) (hf : Function.Injective f) (x : A) :
    ofInjective' f hf x = f x :=
  rfl

end StarAlgEquiv

/-! ### The star closure of a subalgebra -/


namespace NonUnitalSubalgebra

open scoped Pointwise

variable [CommSemiring R] [StarRing R]
variable [NonUnitalSemiring A] [StarRing A] [Module R A]
variable [StarModule R A]

/-- The pointwise `star` of a non-unital subalgebra is a non-unital subalgebra. -/
instance instInvolutiveStar : InvolutiveStar (NonUnitalSubalgebra R A) where
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

theorem star_mem_star_iff (S : NonUnitalSubalgebra R A) (x : A) : star x ∈ star S ↔ x ∈ S := by
  simp

@[simp]
theorem coe_star (S : NonUnitalSubalgebra R A) : star S = star (S : Set A) :=
  rfl

theorem star_mono : Monotone (star : NonUnitalSubalgebra R A → NonUnitalSubalgebra R A) :=
  fun _ _ h _ hx => h hx

variable (R)
variable [IsScalarTower R A A] [SMulCommClass R A A]

/-- The star operation on `NonUnitalSubalgebra` commutes with `NonUnitalAlgebra.adjoin`. -/
theorem star_adjoin_comm (s : Set A) :
    star (NonUnitalAlgebra.adjoin R s) = NonUnitalAlgebra.adjoin R (star s) :=
  have this :
    ∀ t : Set A, NonUnitalAlgebra.adjoin R (star t) ≤ star (NonUnitalAlgebra.adjoin R t) := fun _ =>
    NonUnitalAlgebra.adjoin_le fun _ hx => NonUnitalAlgebra.subset_adjoin R hx
  le_antisymm (by simpa only [star_star] using NonUnitalSubalgebra.star_mono (this (star s)))
    (this s)

variable {R}

/-- The `NonUnitalStarSubalgebra` obtained from `S : NonUnitalSubalgebra R A` by taking the
smallest non-unital subalgebra containing both `S` and `star S`. -/
def starClosure (S : NonUnitalSubalgebra R A) : NonUnitalStarSubalgebra R A where
  toNonUnitalSubalgebra := S ⊔ star S
  star_mem' {a} ha := by
    simpa [← mem_star_iff _ a, ← (@NonUnitalAlgebra.gi R A _ _ _ _ _).l_sup_u _ _, star_adjoin_comm,
      Set.union_comm] using ha

@[simp]
theorem coe_starClosure (S : NonUnitalSubalgebra R A) :
    (S.starClosure : Set A) = (S ⊔ star S : NonUnitalSubalgebra R A) := rfl

@[simp]
theorem mem_starClosure (S : NonUnitalSubalgebra R A) {x : A} :
    x ∈ S.starClosure ↔ x ∈ S ⊔ star S := Iff.rfl

@[simp]
theorem starClosure_toNonUnitalSubalgebra (S : NonUnitalSubalgebra R A) :
    S.starClosure.toNonUnitalSubalgebra = S ⊔ star S := rfl

@[deprecated (since := "2025-06-17")] alias
  starClosure_toNonunitalSubalgebra := starClosure_toNonUnitalSubalgebra

theorem starClosure_le {S₁ : NonUnitalSubalgebra R A} {S₂ : NonUnitalStarSubalgebra R A}
    (h : S₁ ≤ S₂.toNonUnitalSubalgebra) : S₁.starClosure ≤ S₂ :=
  NonUnitalStarSubalgebra.toNonUnitalSubalgebra_le_iff.1 <|
    sup_le h fun x hx =>
      (star_star x ▸ star_mem (show star x ∈ S₂ from h <| (S₁.mem_star_iff _).1 hx) : x ∈ S₂)

theorem starClosure_le_iff {S₁ : NonUnitalSubalgebra R A} {S₂ : NonUnitalStarSubalgebra R A} :
    S₁.starClosure ≤ S₂ ↔ S₁ ≤ S₂.toNonUnitalSubalgebra :=
  ⟨fun h => le_sup_left.trans h, starClosure_le⟩

@[mono]
theorem starClosure_mono : Monotone (starClosure (R := R) (A := A)) :=
  fun _ _ h => starClosure_le <| h.trans le_sup_left

end NonUnitalSubalgebra

namespace NonUnitalStarAlgebra

variable [CommSemiring R] [StarRing R]
variable [NonUnitalSemiring A] [StarRing A] [Module R A]
variable [NonUnitalSemiring B] [StarRing B] [Module R B]
variable [FunLike F A B] [NonUnitalAlgHomClass F R A B] [StarHomClass F A B]

section StarSubAlgebraA

variable [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A]

open scoped Pointwise

open NonUnitalStarSubalgebra

variable (R)

/-- The minimal non-unital subalgebra that includes `s`. -/
def adjoin (s : Set A) : NonUnitalStarSubalgebra R A where
  toNonUnitalSubalgebra := NonUnitalAlgebra.adjoin R (s ∪ star s)
  star_mem' _ := by
    rwa [NonUnitalSubalgebra.mem_carrier, ← NonUnitalSubalgebra.mem_star_iff,
      NonUnitalSubalgebra.star_adjoin_comm, Set.union_star, star_star, Set.union_comm]

theorem adjoin_eq_starClosure_adjoin (s : Set A) :
    adjoin R s = (NonUnitalAlgebra.adjoin R s).starClosure :=
  toNonUnitalSubalgebra_injective <| show
    NonUnitalAlgebra.adjoin R (s ∪ star s) =
      NonUnitalAlgebra.adjoin R s ⊔ star (NonUnitalAlgebra.adjoin R s)
    from
      (NonUnitalSubalgebra.star_adjoin_comm R s).symm ▸ NonUnitalAlgebra.adjoin_union s (star s)

theorem adjoin_toNonUnitalSubalgebra (s : Set A) :
    (adjoin R s).toNonUnitalSubalgebra = NonUnitalAlgebra.adjoin R (s ∪ star s) := rfl

@[simp, aesop safe 20 (rule_sets := [SetLike])]
theorem subset_adjoin (s : Set A) : s ⊆ adjoin R s :=
  Set.subset_union_left.trans <| NonUnitalAlgebra.subset_adjoin R

@[simp, aesop safe 20 (rule_sets := [SetLike])]
theorem star_subset_adjoin (s : Set A) : star s ⊆ adjoin R s :=
  Set.subset_union_right.trans <| NonUnitalAlgebra.subset_adjoin R

@[aesop 80% (rule_sets := [SetLike])]
theorem mem_adjoin_of_mem {s : Set A} {x : A} (hx : x ∈ s) : x ∈ adjoin R s := subset_adjoin R s hx

theorem self_mem_adjoin_singleton (x : A) : x ∈ adjoin R ({x} : Set A) :=
  NonUnitalAlgebra.subset_adjoin R <| Set.mem_union_left _ (Set.mem_singleton x)

theorem star_self_mem_adjoin_singleton (x : A) : star x ∈ adjoin R ({x} : Set A) :=
  star_mem <| self_mem_adjoin_singleton R x

@[elab_as_elim]
lemma adjoin_induction {s : Set A} {p : (x : A) → x ∈ adjoin R s → Prop}
    (mem : ∀ (x : A) (hx : x ∈ s), p x (subset_adjoin R s hx))
    (add : ∀ x y hx hy, p x hx → p y hy → p (x + y) (add_mem hx hy))
    (zero : p 0 (zero_mem _)) (mul : ∀ x y hx hy, p x hx → p y hy → p (x * y) (mul_mem hx hy))
    (smul : ∀ (r : R) x hx, p x hx → p (r • x) (SMulMemClass.smul_mem r hx))
    (star : ∀ x hx, p x hx → p (star x) (star_mem hx))
    {a : A} (ha : a ∈ adjoin R s) : p a ha := by
  refine NonUnitalAlgebra.adjoin_induction (fun x hx ↦ ?_) add zero mul smul ha
  simp only [Set.mem_union, Set.mem_star] at hx
  obtain (hx | hx) := hx
  · exact mem x hx
  · simpa using star _ (NonUnitalAlgebra.subset_adjoin R (by simpa using Or.inl hx)) (mem _ hx)

variable {R}

protected theorem gc : GaloisConnection (adjoin R : Set A → NonUnitalStarSubalgebra R A) (↑) := by
  intro s S
  rw [← toNonUnitalSubalgebra_le_iff, adjoin_toNonUnitalSubalgebra,
    NonUnitalAlgebra.adjoin_le_iff, coe_toNonUnitalSubalgebra]
  exact ⟨fun h => Set.subset_union_left.trans h,
    fun h => Set.union_subset h fun x hx => star_star x ▸ star_mem (show star x ∈ S from h hx)⟩

/-- Galois insertion between `adjoin` and `SetLike.coe`. -/
protected def gi : GaloisInsertion (adjoin R : Set A → NonUnitalStarSubalgebra R A) (↑) where
  choice s hs := (adjoin R s).copy s <| le_antisymm (NonUnitalStarAlgebra.gc.le_u_l s) hs
  gc := NonUnitalStarAlgebra.gc
  le_l_u S := (NonUnitalStarAlgebra.gc (S : Set A) (adjoin R S)).1 <| le_rfl
  choice_eq _ _ := NonUnitalStarSubalgebra.copy_eq _ _ _

theorem adjoin_le {S : NonUnitalStarSubalgebra R A} {s : Set A} (hs : s ⊆ S) : adjoin R s ≤ S :=
  NonUnitalStarAlgebra.gc.l_le hs

@[simp]
theorem adjoin_le_iff {S : NonUnitalStarSubalgebra R A} {s : Set A} : adjoin R s ≤ S ↔ s ⊆ S :=
  NonUnitalStarAlgebra.gc _ _

@[gcongr]
theorem adjoin_mono {s t : Set A} (H : s ⊆ t) : adjoin R s ≤ adjoin R t :=
  NonUnitalStarAlgebra.gc.monotone_l H

@[simp]
lemma adjoin_eq (s : NonUnitalStarSubalgebra R A) : adjoin R (s : Set A) = s :=
  le_antisymm (adjoin_le le_rfl) (subset_adjoin R (s : Set A))

lemma adjoin_eq_span (s : Set A) :
    (adjoin R s).toSubmodule = Submodule.span R (Subsemigroup.closure (s ∪ star s)) := by
  rw [adjoin_toNonUnitalSubalgebra, NonUnitalAlgebra.adjoin_eq_span]

@[simp]
lemma span_eq_toSubmodule {R} [CommSemiring R] [Module R A] (s : NonUnitalStarSubalgebra R A) :
    Submodule.span R (s : Set A) = s.toSubmodule := by
  simp [SetLike.ext'_iff, Submodule.coe_span_eq_self]

theorem _root_.NonUnitalSubalgebra.starClosure_eq_adjoin (S : NonUnitalSubalgebra R A) :
    S.starClosure = adjoin R (S : Set A) :=
  le_antisymm (NonUnitalSubalgebra.starClosure_le_iff.2 <| subset_adjoin R (S : Set A))
    (adjoin_le (le_sup_left : S ≤ S ⊔ star S))

instance : CompleteLattice (NonUnitalStarSubalgebra R A) :=
  GaloisInsertion.liftCompleteLattice NonUnitalStarAlgebra.gi

@[simp]
theorem coe_top : ((⊤ : NonUnitalStarSubalgebra R A) : Set A) = Set.univ :=
  rfl

@[simp]
theorem mem_top {x : A} : x ∈ (⊤ : NonUnitalStarSubalgebra R A) :=
  Set.mem_univ x

@[simp]
theorem top_toNonUnitalSubalgebra :
    (⊤ : NonUnitalStarSubalgebra R A).toNonUnitalSubalgebra = ⊤ := by ext; simp

@[simp]
theorem toNonUnitalSubalgebra_eq_top {S : NonUnitalStarSubalgebra R A} :
    S.toNonUnitalSubalgebra = ⊤ ↔ S = ⊤ :=
  NonUnitalStarSubalgebra.toNonUnitalSubalgebra_injective.eq_iff' top_toNonUnitalSubalgebra

theorem mem_sup_left {S T : NonUnitalStarSubalgebra R A} : ∀ {x : A}, x ∈ S → x ∈ S ⊔ T := by
  rw [← SetLike.le_def]
  exact le_sup_left

theorem mem_sup_right {S T : NonUnitalStarSubalgebra R A} : ∀ {x : A}, x ∈ T → x ∈ S ⊔ T := by
  rw [← SetLike.le_def]
  exact le_sup_right

theorem mul_mem_sup {S T : NonUnitalStarSubalgebra R A} {x y : A} (hx : x ∈ S) (hy : y ∈ T) :
    x * y ∈ S ⊔ T :=
  mul_mem (mem_sup_left hx) (mem_sup_right hy)

theorem map_sup [IsScalarTower R B B] [SMulCommClass R B B] [StarModule R B] (f : F)
    (S T : NonUnitalStarSubalgebra R A) :
    ((S ⊔ T).map f : NonUnitalStarSubalgebra R B) = S.map f ⊔ T.map f :=
  (NonUnitalStarSubalgebra.gc_map_comap f).l_sup

theorem map_inf [IsScalarTower R B B] [SMulCommClass R B B] [StarModule R B] (f : F)
    (hf : Function.Injective f) (S T : NonUnitalStarSubalgebra R A) :
    ((S ⊓ T).map f : NonUnitalStarSubalgebra R B) = S.map f ⊓ T.map f :=
  SetLike.coe_injective (Set.image_inter hf)

@[simp, norm_cast]
theorem coe_inf (S T : NonUnitalStarSubalgebra R A) : (↑(S ⊓ T) : Set A) = (S : Set A) ∩ T :=
  rfl

@[simp]
theorem mem_inf {S T : NonUnitalStarSubalgebra R A} {x : A} : x ∈ S ⊓ T ↔ x ∈ S ∧ x ∈ T :=
  Iff.rfl

@[simp]
theorem inf_toNonUnitalSubalgebra (S T : NonUnitalStarSubalgebra R A) :
    (S ⊓ T).toNonUnitalSubalgebra = S.toNonUnitalSubalgebra ⊓ T.toNonUnitalSubalgebra :=
  SetLike.coe_injective <| coe_inf _ _
  -- it's a bit surprising `rfl` fails here.

@[simp, norm_cast]
theorem coe_sInf (S : Set (NonUnitalStarSubalgebra R A)) : (↑(sInf S) : Set A) = ⋂ s ∈ S, ↑s :=
  sInf_image

theorem mem_sInf {S : Set (NonUnitalStarSubalgebra R A)} {x : A} : x ∈ sInf S ↔ ∀ p ∈ S, x ∈ p := by
  simp only [← SetLike.mem_coe, coe_sInf, Set.mem_iInter₂]

@[simp]
theorem sInf_toNonUnitalSubalgebra (S : Set (NonUnitalStarSubalgebra R A)) :
    (sInf S).toNonUnitalSubalgebra = sInf (NonUnitalStarSubalgebra.toNonUnitalSubalgebra '' S) :=
  SetLike.coe_injective <| by simp

@[simp, norm_cast]
theorem coe_iInf {ι : Sort*} {S : ι → NonUnitalStarSubalgebra R A} :
    (↑(⨅ i, S i) : Set A) = ⋂ i, S i := by simp [iInf]

theorem mem_iInf {ι : Sort*} {S : ι → NonUnitalStarSubalgebra R A} {x : A} :
    (x ∈ ⨅ i, S i) ↔ ∀ i, x ∈ S i := by simp only [iInf, mem_sInf, Set.forall_mem_range]

theorem map_iInf {ι : Sort*} [Nonempty ι]
    [IsScalarTower R B B] [SMulCommClass R B B] [StarModule R B] (f : F)
    (hf : Function.Injective f) (S : ι → NonUnitalStarSubalgebra R A) :
    ((⨅ i, S i).map f : NonUnitalStarSubalgebra R B) = ⨅ i, (S i).map f := by
  apply SetLike.coe_injective
  simpa using (Set.injOn_of_injective hf).image_iInter_eq (s := SetLike.coe ∘ S)

@[simp]
theorem iInf_toNonUnitalSubalgebra {ι : Sort*} (S : ι → NonUnitalStarSubalgebra R A) :
    (⨅ i, S i).toNonUnitalSubalgebra = ⨅ i, (S i).toNonUnitalSubalgebra :=
  SetLike.coe_injective <| by simp

instance : Inhabited (NonUnitalStarSubalgebra R A) :=
  ⟨⊥⟩

theorem mem_bot {x : A} : x ∈ (⊥ : NonUnitalStarSubalgebra R A) ↔ x = 0 :=
  show x ∈ NonUnitalAlgebra.adjoin R (∅ ∪ star ∅ : Set A) ↔ x = 0 by
    rw [Set.star_empty, Set.union_empty, NonUnitalAlgebra.adjoin_empty, NonUnitalAlgebra.mem_bot]

theorem toNonUnitalSubalgebra_bot :
    (⊥ : NonUnitalStarSubalgebra R A).toNonUnitalSubalgebra = ⊥ := by
  ext x
  simp only [mem_bot, NonUnitalStarSubalgebra.mem_toNonUnitalSubalgebra, NonUnitalAlgebra.mem_bot]

@[simp]
theorem coe_bot : ((⊥ : NonUnitalStarSubalgebra R A) : Set A) = {0} := by
  simp only [Set.ext_iff, NonUnitalStarAlgebra.mem_bot, SetLike.mem_coe, Set.mem_singleton_iff,
    forall_const]

theorem eq_top_iff {S : NonUnitalStarSubalgebra R A} : S = ⊤ ↔ ∀ x : A, x ∈ S :=
  ⟨fun h x => by rw [h]; exact mem_top,
    fun h => by ext x; exact ⟨fun _ => mem_top, fun _ => h x⟩⟩

@[simp]
theorem range_id : NonUnitalStarAlgHom.range (NonUnitalStarAlgHom.id R A) = ⊤ :=
  SetLike.coe_injective Set.range_id

@[simp]
theorem map_bot [IsScalarTower R B B] [SMulCommClass R B B] [StarModule R B] (f : F) :
    (⊥ : NonUnitalStarSubalgebra R A).map f = ⊥ :=
  SetLike.coe_injective <| by simp [NonUnitalStarSubalgebra.coe_map]

@[simp]
theorem comap_top [IsScalarTower R B B] [SMulCommClass R B B] [StarModule R B] (f : F) :
    (⊤ : NonUnitalStarSubalgebra R B).comap f = ⊤ :=
  eq_top_iff.2 fun _x => mem_top

/-- `NonUnitalStarAlgHom` to `⊤ : NonUnitalStarSubalgebra R A`. -/
def toTop : A →⋆ₙₐ[R] (⊤ : NonUnitalStarSubalgebra R A) :=
  NonUnitalStarAlgHom.codRestrict (NonUnitalStarAlgHom.id R A) ⊤ fun _ => mem_top

end StarSubAlgebraA

theorem range_eq_top [IsScalarTower R B B] [SMulCommClass R B B] [StarModule R B]
    (f : F) : NonUnitalStarAlgHom.range f = (⊤ : NonUnitalStarSubalgebra R B) ↔
      Function.Surjective f :=
  NonUnitalStarAlgebra.eq_top_iff

@[simp]
theorem map_top [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A] (f : F) :
    (⊤ : NonUnitalStarSubalgebra R A).map f = NonUnitalStarAlgHom.range f :=
  SetLike.coe_injective Set.image_univ

end NonUnitalStarAlgebra

namespace NonUnitalStarSubalgebra

open NonUnitalStarAlgebra

variable [CommSemiring R]
variable [NonUnitalSemiring A] [StarRing A] [Module R A]
variable [NonUnitalSemiring B] [StarRing B] [Module R B]
variable [FunLike F A B] [NonUnitalAlgHomClass F R A B] [StarHomClass F A B]
variable (S : NonUnitalStarSubalgebra R A)

section StarSubalgebra

variable [StarRing R]
variable [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A]
variable [IsScalarTower R B B] [SMulCommClass R B B] [StarModule R B]

lemma _root_.NonUnitalStarAlgHom.map_adjoin (f : F) (s : Set A) :
    map f (adjoin R s) = adjoin R (f '' s) :=
  Set.image_preimage.l_comm_of_u_comm (gc_map_comap f) NonUnitalStarAlgebra.gi.gc
    NonUnitalStarAlgebra.gi.gc fun _t => rfl

@[simp]
lemma _root_.NonUnitalStarAlgHom.map_adjoin_singleton (f : F) (x : A) :
    map f (adjoin R {x}) = adjoin R {f x} := by
  simp [NonUnitalStarAlgHom.map_adjoin]

instance subsingleton_of_subsingleton [Subsingleton A] :
    Subsingleton (NonUnitalStarSubalgebra R A) :=
  ⟨fun B C => ext fun x => by simp only [Subsingleton.elim x 0, zero_mem B, zero_mem C]⟩

instance _root_.NonUnitalStarAlgHom.subsingleton [Subsingleton (NonUnitalStarSubalgebra R A)] :
    Subsingleton (A →⋆ₙₐ[R] B) :=
  ⟨fun f g => NonUnitalStarAlgHom.ext fun a =>
    have : a ∈ (⊥ : NonUnitalStarSubalgebra R A) :=
      Subsingleton.elim (⊤ : NonUnitalStarSubalgebra R A) ⊥ ▸ mem_top
    (mem_bot.mp this).symm ▸ (map_zero f).trans (map_zero g).symm⟩

/--
The map `S → T` when `S` is a non-unital star subalgebra contained in the non-unital star
algebra `T`.

This is the non-unital star subalgebra version of `Submodule.inclusion`, or
`NonUnitalSubalgebra.inclusion` -/
def inclusion {S T : NonUnitalStarSubalgebra R A} (h : S ≤ T) : S →⋆ₙₐ[R] T where
  toNonUnitalAlgHom := NonUnitalSubalgebra.inclusion h
  map_star' _ := rfl

theorem inclusion_injective {S T : NonUnitalStarSubalgebra R A} (h : S ≤ T) :
    Function.Injective (inclusion h) :=
  fun _ _ => Subtype.ext ∘ Subtype.mk.inj

@[simp]
theorem inclusion_self {S : NonUnitalStarSubalgebra R A} :
    inclusion (le_refl S) = NonUnitalAlgHom.id R S :=
  NonUnitalAlgHom.ext fun _x => Subtype.ext rfl

@[simp]
theorem inclusion_mk {S T : NonUnitalStarSubalgebra R A} (h : S ≤ T) (x : A) (hx : x ∈ S) :
    inclusion h ⟨x, hx⟩ = ⟨x, h hx⟩ :=
  rfl

theorem inclusion_right {S T : NonUnitalStarSubalgebra R A} (h : S ≤ T) (x : T) (m : (x : A) ∈ S) :
    inclusion h ⟨x, m⟩ = x :=
  Subtype.ext rfl

@[simp]
theorem inclusion_inclusion {S T U : NonUnitalStarSubalgebra R A} (hst : S ≤ T) (htu : T ≤ U)
    (x : S) : inclusion htu (inclusion hst x) = inclusion (le_trans hst htu) x :=
  Subtype.ext rfl

@[simp]
theorem val_inclusion {S T : NonUnitalStarSubalgebra R A} (h : S ≤ T) (s : S) :
    (inclusion h s : A) = s :=
  rfl

end StarSubalgebra

theorem range_val : NonUnitalStarAlgHom.range (NonUnitalStarSubalgebraClass.subtype S) = S :=
  ext <| Set.ext_iff.1 <|
    (NonUnitalStarAlgHom.coe_range (NonUnitalStarSubalgebraClass.subtype S)).trans Subtype.range_val

section Prod

variable (S₁ : NonUnitalStarSubalgebra R B)

/-- The product of two non-unital star subalgebras is a non-unital star subalgebra. -/
def prod : NonUnitalStarSubalgebra R (A × B) :=
  { S.toNonUnitalSubalgebra.prod S₁.toNonUnitalSubalgebra with
    carrier := S ×ˢ S₁
    star_mem' := fun hx => ⟨star_mem hx.1, star_mem hx.2⟩ }

@[simp]
theorem coe_prod : (prod S S₁ : Set (A × B)) = (S : Set A) ×ˢ S₁ :=
  rfl

theorem prod_toNonUnitalSubalgebra :
    (S.prod S₁).toNonUnitalSubalgebra = S.toNonUnitalSubalgebra.prod S₁.toNonUnitalSubalgebra :=
  rfl

@[simp]
theorem mem_prod {S : NonUnitalStarSubalgebra R A} {S₁ : NonUnitalStarSubalgebra R B} {x : A × B} :
    x ∈ prod S S₁ ↔ x.1 ∈ S ∧ x.2 ∈ S₁ :=
  Set.mem_prod

variable [StarRing R]
variable [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A]
variable [IsScalarTower R B B] [SMulCommClass R B B] [StarModule R B]

@[simp]
theorem prod_top : (prod ⊤ ⊤ : NonUnitalStarSubalgebra R (A × B)) = ⊤ := by ext; simp

theorem prod_mono {S T : NonUnitalStarSubalgebra R A} {S₁ T₁ : NonUnitalStarSubalgebra R B} :
    S ≤ T → S₁ ≤ T₁ → prod S S₁ ≤ prod T T₁ :=
  Set.prod_mono

@[simp]
theorem prod_inf_prod {S T : NonUnitalStarSubalgebra R A} {S₁ T₁ : NonUnitalStarSubalgebra R B} :
    S.prod S₁ ⊓ T.prod T₁ = (S ⊓ T).prod (S₁ ⊓ T₁) :=
  SetLike.coe_injective Set.prod_inter_prod

end Prod

section iSupLift

variable {ι : Type*}
variable [StarRing R] [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A]

section StarSubalgebraB

variable [IsScalarTower R B B] [SMulCommClass R B B] [StarModule R B]

theorem coe_iSup_of_directed [Nonempty ι] {S : ι → NonUnitalStarSubalgebra R A}
    (dir : Directed (· ≤ ·) S) : ↑(iSup S) = ⋃ i, (S i : Set A) :=
  let K : NonUnitalStarSubalgebra R A :=
    { __ := NonUnitalSubalgebra.copy _ _ (NonUnitalSubalgebra.coe_iSup_of_directed dir).symm
      star_mem' := fun hx ↦
        let ⟨i, hi⟩ := Set.mem_iUnion.1 hx
        Set.mem_iUnion.2 ⟨i, star_mem (s := S i) hi⟩ }
  have : iSup S = K := le_antisymm (iSup_le fun i ↦ le_iSup (fun i ↦ (S i : Set A)) i)
    (Set.iUnion_subset fun _ ↦ le_iSup S _)
  this.symm ▸ rfl

/-- Define a non-unital star algebra homomorphism on a directed supremum of non-unital star
subalgebras by defining it on each non-unital star subalgebra, and proving that it agrees on the
intersection of non-unital star subalgebras. -/
noncomputable def iSupLift [Nonempty ι] (K : ι → NonUnitalStarSubalgebra R A)
    (dir : Directed (· ≤ ·) K) (f : ∀ i, K i →⋆ₙₐ[R] B)
    (hf : ∀ (i j : ι) (h : K i ≤ K j), f i = (f j).comp (inclusion h))
    (T : NonUnitalStarSubalgebra R A) (hT : T = iSup K) : ↥T →⋆ₙₐ[R] B := by
  subst hT
  exact
    { toFun :=
        Set.iUnionLift (fun i => ↑(K i)) (fun i x => f i x)
          (fun i j x hxi hxj => by
            let ⟨k, hik, hjk⟩ := dir i j
            simp only
            rw [hf i k hik, hf j k hjk]
            rfl)
          _ (by rw [coe_iSup_of_directed dir])
      map_zero' := by
        dsimp only [SetLike.coe_sort_coe, NonUnitalAlgHom.coe_comp, Function.comp_apply,
          inclusion_mk, Eq.ndrec, id_eq, eq_mpr_eq_cast]
        exact Set.iUnionLift_const _ (fun i : ι => (0 : K i)) (fun _ => rfl)  _ (by simp)
      map_mul' := by
        dsimp only [SetLike.coe_sort_coe, NonUnitalAlgHom.coe_comp, Function.comp_apply,
          inclusion_mk, Eq.ndrec, id_eq, eq_mpr_eq_cast, ZeroMemClass.coe_zero,
          AddSubmonoid.mk_add_mk, Set.inclusion_mk]
        apply Set.iUnionLift_binary (coe_iSup_of_directed dir) dir _ (fun _ => (· * ·))
        all_goals simp
      map_add' := by
        dsimp only [SetLike.coe_sort_coe, NonUnitalAlgHom.coe_comp, Function.comp_apply,
          inclusion_mk, Eq.ndrec, id_eq, eq_mpr_eq_cast]
        apply Set.iUnionLift_binary (coe_iSup_of_directed dir) dir _ (fun _ => (· + ·))
        all_goals simp
      map_smul' := fun r => by
        dsimp only [SetLike.coe_sort_coe, NonUnitalAlgHom.coe_comp, Function.comp_apply,
          inclusion_mk, Eq.ndrec, id_eq, eq_mpr_eq_cast]
        apply Set.iUnionLift_unary (coe_iSup_of_directed dir) _ (fun _ x => r • x)
          (fun _ _ => rfl)
        all_goals simp
      map_star' := by
        dsimp only [SetLike.coe_sort_coe, NonUnitalStarAlgHom.comp_apply, inclusion_mk, Eq.ndrec,
          id_eq, eq_mpr_eq_cast, ZeroMemClass.coe_zero, AddSubmonoid.mk_add_mk, Set.inclusion_mk,
          MulMemClass.mk_mul_mk, NonUnitalAlgHom.toDistribMulActionHom_eq_coe,
          DistribMulActionHom.toFun_eq_coe, NonUnitalAlgHom.coe_to_distribMulActionHom,
          NonUnitalAlgHom.coe_mk]
        apply Set.iUnionLift_unary (coe_iSup_of_directed dir) _ (fun _ x => star x)
          (fun _ _ => rfl)
        all_goals simp [map_star] }

end StarSubalgebraB

variable [Nonempty ι] {K : ι → NonUnitalStarSubalgebra R A} {dir : Directed (· ≤ ·) K}
  {f : ∀ i, K i →⋆ₙₐ[R] B} {hf : ∀ (i j : ι) (h : K i ≤ K j), f i = (f j).comp (inclusion h)}
  {T : NonUnitalStarSubalgebra R A} {hT : T = iSup K}

@[simp]
theorem iSupLift_inclusion {i : ι} (x : K i) (h : K i ≤ T) :
    iSupLift K dir f hf T hT (inclusion h x) = f i x := by
  subst T
  dsimp [iSupLift]
  apply Set.iUnionLift_inclusion
  exact h

@[simp]
theorem iSupLift_comp_inclusion {i : ι} (h : K i ≤ T) :
    (iSupLift K dir f hf T hT).comp (inclusion h) = f i := by ext; simp

@[simp]
theorem iSupLift_mk {i : ι} (x : K i) (hx : (x : A) ∈ T) :
    iSupLift K dir f hf T hT ⟨x, hx⟩ = f i x := by
  subst hT
  dsimp [iSupLift]
  apply Set.iUnionLift_mk

theorem iSupLift_of_mem {i : ι} (x : T) (hx : (x : A) ∈ K i) :
    iSupLift K dir f hf T hT x = f i ⟨x, hx⟩ := by
  subst hT
  dsimp [iSupLift]
  apply Set.iUnionLift_of_mem

end iSupLift

section Center

variable (R A)
variable [IsScalarTower R A A] [SMulCommClass R A A]

/-- The center of a non-unital star algebra is the set of elements which commute with every element.
They form a non-unital star subalgebra. -/
def center : NonUnitalStarSubalgebra R A where
  toNonUnitalSubalgebra := NonUnitalSubalgebra.center R A
  star_mem' := Set.star_mem_center

theorem coe_center : (center R A : Set A) = Set.center A :=
  rfl

@[simp]
theorem center_toNonUnitalSubalgebra :
    (center R A).toNonUnitalSubalgebra = NonUnitalSubalgebra.center R A :=
  rfl

@[simp]
theorem center_eq_top (A : Type*) [StarRing R] [NonUnitalCommSemiring A] [StarRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A] : center R A = ⊤ :=
  SetLike.coe_injective (Set.center_eq_univ A)

variable {R A}

instance instNonUnitalCommSemiring : NonUnitalCommSemiring (center R A) :=
  NonUnitalSubalgebra.center.instNonUnitalCommSemiring

instance instNonUnitalCommRing {A : Type*} [NonUnitalRing A] [StarRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] : NonUnitalCommRing (center R A) :=
  NonUnitalSubalgebra.center.instNonUnitalCommRing

theorem mem_center_iff {a : A} : a ∈ center R A ↔ ∀ b : A, b * a = a * b :=
  Subsemigroup.mem_center_iff

end Center

section Centralizer

variable (R)
variable [IsScalarTower R A A] [SMulCommClass R A A]

/-- The centralizer of the star-closure of a set as a non-unital star subalgebra. -/
def centralizer (s : Set A) : NonUnitalStarSubalgebra R A :=
  { NonUnitalSubalgebra.centralizer R (s ∪ star s) with
    star_mem' := Set.star_mem_centralizer }

@[simp, norm_cast]
theorem coe_centralizer (s : Set A) : (centralizer R s : Set A) = (s ∪ star s).centralizer :=
  rfl

theorem mem_centralizer_iff {s : Set A} {z : A} :
    z ∈ centralizer R s ↔ ∀ g ∈ s, g * z = z * g ∧ star g * z = z * star g := by
  change (∀ g ∈ s ∪ star s, g * z = z * g) ↔ ∀ g ∈ s, g * z = z * g ∧ star g * z = z * star g
  simp only [Set.mem_union, or_imp, forall_and, and_congr_right_iff]
  exact fun _ =>
    ⟨fun hz a ha => hz _ (Set.star_mem_star.mpr ha), fun hz a ha => star_star a ▸ hz _ ha⟩

theorem centralizer_le (s t : Set A) (h : s ⊆ t) : centralizer R t ≤ centralizer R s :=
  Set.centralizer_subset (Set.union_subset_union h <| Set.preimage_mono h)

@[simp]
theorem centralizer_univ : centralizer R Set.univ = center R A :=
  SetLike.ext' <| by rw [coe_centralizer, Set.univ_union, coe_center, Set.centralizer_univ]

theorem centralizer_toNonUnitalSubalgebra (s : Set A) :
    (centralizer R s).toNonUnitalSubalgebra = NonUnitalSubalgebra.centralizer R (s ∪ star s) :=
  rfl

theorem coe_centralizer_centralizer (s : Set A) :
    (centralizer R (centralizer R s : Set A)) = (s ∪ star s).centralizer.centralizer := by
  rw [coe_centralizer, StarMemClass.star_coe_eq, Set.union_self, coe_centralizer]

end Centralizer

end NonUnitalStarSubalgebra

namespace NonUnitalStarAlgebra

open NonUnitalStarSubalgebra

variable [CommSemiring R] [StarRing R]
variable [NonUnitalSemiring A] [StarRing A] [Module R A]
variable [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A]

variable (R) in
lemma adjoin_le_centralizer_centralizer (s : Set A) :
    adjoin R s ≤ centralizer R (centralizer R s) := by
  rw [← toNonUnitalSubalgebra_le_iff, centralizer_toNonUnitalSubalgebra,
    adjoin_toNonUnitalSubalgebra]
  convert NonUnitalAlgebra.adjoin_le_centralizer_centralizer R (s ∪ star s)
  rw [StarMemClass.star_coe_eq]
  simp

lemma commute_of_mem_adjoin_of_forall_mem_commute {a b : A} {s : Set A}
    (hb : b ∈ adjoin R s) (h : ∀ b ∈ s, Commute a b) (h_star : ∀ b ∈ s, Commute a (star b)) :
    Commute a b :=
  NonUnitalAlgebra.commute_of_mem_adjoin_of_forall_mem_commute hb fun b hb ↦
    hb.elim (h b) (by simpa using h_star (star b))

lemma commute_of_mem_adjoin_singleton_of_commute {a b c : A}
    (hc : c ∈ adjoin R {b}) (h : Commute a b) (h_star : Commute a (star b)) :
    Commute a c :=
  commute_of_mem_adjoin_of_forall_mem_commute hc (by simpa) (by simpa)

lemma commute_of_mem_adjoin_self {a b : A} [IsStarNormal a] (hb : b ∈ adjoin R {a}) :
    Commute a b :=
  commute_of_mem_adjoin_singleton_of_commute hb rfl (isStarNormal_iff a |>.mp inferInstance).symm

variable (R) in
/-- If all elements of `s : Set A` commute pairwise and with elements of `star s`, then `adjoin R s`
is a non-unital commutative semiring.

See note [reducible non-instances]. -/
abbrev adjoinNonUnitalCommSemiringOfComm {s : Set A} (hcomm : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a)
    (hcomm_star : ∀ a ∈ s, ∀ b ∈ s, a * star b = star b * a) :
    NonUnitalCommSemiring (adjoin R s) :=
  { (adjoin R s).toNonUnitalSemiring with
    mul_comm := fun ⟨_, h₁⟩ ⟨_, h₂⟩ ↦ by
      have hcomm : ∀ a ∈ s ∪ star s, ∀ b ∈ s ∪ star s, a * b = b * a := fun a ha b hb ↦
        Set.union_star_self_comm (fun _ ha _ hb ↦ hcomm _ hb _ ha)
          (fun _ ha _ hb ↦ hcomm_star _ hb _ ha) b hb a ha
      have := adjoin_le_centralizer_centralizer R s
      apply this at h₁
      apply this at h₂
      rw [← SetLike.mem_coe, coe_centralizer_centralizer] at h₁ h₂
      exact Subtype.ext <| Set.centralizer_centralizer_comm_of_comm hcomm _ h₁ _ h₂ }

/-- If all elements of `s : Set A` commute pairwise and with elements of `star s`, then `adjoin R s`
is a non-unital commutative ring.

See note [reducible non-instances]. -/
abbrev adjoinNonUnitalCommRingOfComm (R : Type*) {A : Type*} [CommRing R] [StarRing R]
    [NonUnitalRing A] [StarRing A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
    [StarModule R A] {s : Set A} (hcomm : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a)
    (hcomm_star : ∀ a ∈ s, ∀ b ∈ s, a * star b = star b * a) : NonUnitalCommRing (adjoin R s) :=
  { (adjoin R s).toNonUnitalRing, adjoinNonUnitalCommSemiringOfComm R hcomm hcomm_star with }

end NonUnitalStarAlgebra
