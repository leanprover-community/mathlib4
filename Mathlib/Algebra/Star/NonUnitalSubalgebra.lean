/-
Copyright (c) 2023 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Algebra.Algebra.NonUnitalSubalgebra
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.Center

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

/-- In a star semigroup (i.e., a semigroup with an antimultiplicative involutive star operation),
any star-closed subset which is also closed under multiplication is itself a star semigroup. -/
instance instStarSemigroup {S R : Type*} [Semigroup R] [StarSemigroup R] [SetLike S R]
    [MulMemClass S R] [StarMemClass S R] (s : S) : StarSemigroup s where
  star_mul _ _ := Subtype.ext <| star_mul _ _

/-- In a `StarAddMonoid` (i.e., an additive monoid with an additive involutive star operation), any
star-closed subset which is also closed under addition and contains zero is itself a
`StarAddMonoid`. -/
instance instStarAddMonoid {S R : Type*} [AddMonoid R] [StarAddMonoid R] [SetLike S R]
    [AddSubmonoidClass S R] [StarMemClass S R] (s : S) : StarAddMonoid s where
  star_add _ _ := Subtype.ext <| star_add _ _

/-- In a star ring (i.e., a non-unital semiring with an additive, antimultiplicative, involutive
star operation), an star-closed non-unital subsemiring is itself a star ring. -/
instance instStarRing {S R : Type*} [NonUnitalSemiring R] [StarRing R] [SetLike S R]
    [NonUnitalSubsemiringClass S R] [StarMemClass S R] (s : S) : StarRing s :=
  { StarMemClass.instStarSemigroup s, StarMemClass.instStarAddMonoid s with }

/-- In a star `R`-module (i.e., `star (r • m) = (star r) • m`) any star-closed subset which is also
closed under the scalar action by `R` is itself a star `R`-module. -/
instance instStarModule {S : Type*} (R : Type*) {M : Type*} [Star R] [Star M] [SMul R M]
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

@[simp]
theorem coeSubtype : (subtype s : s → A) = Subtype.val :=
  rfl

end NonUnitalStarSubalgebraClass

/-- A non-unital star subalgebra is a non-unital subalgebra which is closed under the `star`
operation. -/
structure NonUnitalStarSubalgebra (R : Type u) (A : Type v) [CommSemiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [Star A]
    extends NonUnitalSubalgebra R A : Type v where
  /-- The `carrier` of a `NonUnitalStarSubalgebra` is closed under the `star` operation. -/
  star_mem' : ∀ {a : A} (_ha : a ∈ carrier), star a ∈ carrier

/-- Reinterpret a `NonUnitalStarSubalgebra` as a `NonUnitalSubalgebra`. -/
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
                             -- ⊢ { toNonUnitalSubalgebra := toNonUnitalSubalgebra✝, star_mem' := star_mem'✝ } …
                                      -- ⊢ { toNonUnitalSubalgebra := toNonUnitalSubalgebra✝¹, star_mem' := star_mem'✝¹ …
                                               -- ⊢ toNonUnitalSubalgebra✝¹ = toNonUnitalSubalgebra✝
                                                      -- 🎉 no goals

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
                  -- 🎉 no goals

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
      show star x ∈ s
      -- ⊢ star x ∈ s
      rw [hs] at hx ⊢
      -- ⊢ star x ∈ ↑S
      exact S.star_mem' hx }
      -- 🎉 no goals

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
                               -- 🎉 no goals

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
                                     -- 🎉 no goals
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

protected theorem coe_neg {R : Type u} {A : Type v} [CommRing R] [NonUnitalRing A] [Module R A]
    [Star A] {S : NonUnitalStarSubalgebra R A} (x : S) : (↑(-x) : A) = -↑x :=
  rfl

protected theorem coe_sub {R : Type u} {A : Type v} [CommRing R] [NonUnitalRing A] [Module R A]
    [Star A] {S : NonUnitalStarSubalgebra R A} (x y : S) : (↑(x - y) : A) = ↑x - ↑y :=
  rfl

@[simp, norm_cast]
theorem coe_smul [Semiring R'] [SMul R' R] [Module R' A] [IsScalarTower R' R A] (r : R') (x : S) :
    (r • x : A) = r • (x : A) :=
  rfl

protected theorem coe_eq_zero {x : S} : (x : A) = 0 ↔ x = 0 :=
  ZeroMemClass.coe_eq_zero

@[simp]
theorem toNonUnitalSubalgebra_subtype :
    NonUnitalSubalgebraClass.subtype S = NonUnitalStarSubalgebraClass.subtype S :=
  rfl

@[simp]
theorem toSubring_subtype {R A : Type*} [CommRing R] [NonUnitalRing A] [Module R A] [Star A]
    (S : NonUnitalStarSubalgebra R A) :
    NonUnitalSubringClass.subtype S = NonUnitalStarSubalgebraClass.subtype S :=
  rfl

/-- Transport a non-unital star subalgebra via a non-unital star algebra homomorphism. -/
def map (f : F) (S : NonUnitalStarSubalgebra R A) : NonUnitalStarSubalgebra R B where
  toNonUnitalSubalgebra := S.toNonUnitalSubalgebra.map (f : A →ₙₐ[R] B)
  star_mem' := by rintro _ ⟨a, ha, rfl⟩; exact ⟨star a, star_mem (s := S) ha, map_star f a⟩
                  -- ⊢ star (↑↑↑f a) ∈ (NonUnitalSubalgebra.map (↑f) S.toNonUnitalSubalgebra).toNon …
                                         -- 🎉 no goals

theorem map_mono {S₁ S₂ : NonUnitalStarSubalgebra R A} {f : F} :
    S₁ ≤ S₂ → (map f S₁ : NonUnitalStarSubalgebra R B) ≤ map f S₂ :=
  Set.image_subset f

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
variable [NonUnitalStarAlgHomClass F R A B]

/-- Range of an `NonUnitalAlgHom` as a `NonUnitalStarSubalgebra`. -/
protected def range (φ : F) : NonUnitalStarSubalgebra R B where
  toNonUnitalSubalgebra := NonUnitalAlgHom.range (φ : A →ₙₐ[R] B)
  star_mem' := by rintro _ ⟨a, rfl⟩; exact ⟨star a, map_star φ a⟩
                  -- ⊢ star (↑↑↑φ a) ∈ (NonUnitalAlgHom.range ↑φ).toNonUnitalSubsemiring.toAddSubmo …
                                     -- 🎉 no goals

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
     -- ⊢ x✝ ∈ ↑(NonUnitalStarAlgHom.range φ) ↔ x✝ ∈ Set.range ↑φ
          -- ⊢ (∃ x, ↑φ x = x✝) ↔ x✝ ∈ Set.range ↑φ
                                           -- 🎉 no goals

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
  ⟨fun H _x _y hxy => H <| Subtype.eq hxy, fun H _x _y hxy => H (congr_arg Subtype.val hxy : _)⟩

/-- Restrict the codomain of a non-unital star algebra homomorphism `f` to `f.range`.

This is the bundled version of `Set.rangeFactorization`. -/
@[reducible]
def rangeRestrict (f : F) : A →⋆ₙₐ[R] (NonUnitalStarAlgHom.range f : NonUnitalStarSubalgebra R B) :=
  NonUnitalStarAlgHom.codRestrict f (NonUnitalStarAlgHom.range f)
    (NonUnitalStarAlgHom.mem_range_self f)

/-- The equalizer of two non-unital star `R`-algebra homomorphisms -/
def equalizer (ϕ ψ : F) : NonUnitalStarSubalgebra R A where
  toNonUnitalSubalgebra := NonUnitalAlgHom.equalizer ϕ ψ
  star_mem' := @fun x (hx : ϕ x = ψ x) => by simp [map_star, hx]
                                             -- 🎉 no goals

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
variable [hF : NonUnitalStarAlgHomClass F R A B]

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
                            -- 🎉 no goals

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
variable [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A]
variable [NonUnitalSemiring B] [StarRing B] [Module R B]
variable [IsScalarTower R B B] [SMulCommClass R B B] [StarModule R B]

/-- The pointwise `star` of a non-unital subalgebra is a non-unital subalgebra. -/
instance instInvolutiveStar : InvolutiveStar (NonUnitalSubalgebra R A)
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

theorem star_mem_star_iff (S : NonUnitalSubalgebra R A) (x : A) : star x ∈ star S ↔ x ∈ S := by
  simp
  -- 🎉 no goals

@[simp]
theorem coe_star (S : NonUnitalSubalgebra R A) : star S = star (S : Set A) :=
  rfl

theorem star_mono : Monotone (star : NonUnitalSubalgebra R A → NonUnitalSubalgebra R A) :=
  fun _ _ h _ hx => h hx

variable (R)

/-- The star operation on `NonUnitalSubalgebra` commutes with `NonUnitalAlgebra.adjoin`. -/
theorem star_adjoin_comm (s : Set A) :
    star (NonUnitalAlgebra.adjoin R s) = NonUnitalAlgebra.adjoin R (star s) :=
  have this :
    ∀ t : Set A, NonUnitalAlgebra.adjoin R (star t) ≤ star (NonUnitalAlgebra.adjoin R t) := fun t =>
    NonUnitalAlgebra.adjoin_le fun x hx => NonUnitalAlgebra.subset_adjoin R hx
  le_antisymm (by simpa only [star_star] using NonUnitalSubalgebra.star_mono (this (star s)))
                  -- 🎉 no goals
    (this s)

variable {R}

/-- The `NonUnitalStarSubalgebra` obtained from `S : NonUnitalSubalgebra R A` by taking the
smallest non-unital subalgebra containing both `S` and `star S`. -/
@[simps!]
def starClosure (S : NonUnitalSubalgebra R A) : NonUnitalStarSubalgebra R A where
  toNonUnitalSubalgebra := S ⊔ star S
  star_mem' := @fun a (ha : a ∈ S ⊔ star S) => show star a ∈ S ⊔ star S by
    simp only [← mem_star_iff _ a, ← (@NonUnitalAlgebra.gi R A _ _ _ _ _).l_sup_u _ _] at *
    -- ⊢ a ∈ star (NonUnitalAlgebra.adjoin R (↑S ⊔ ↑(star S)))
    convert ha using 2
    -- ⊢ star (NonUnitalAlgebra.adjoin R (↑S ⊔ ↑(star S))) = NonUnitalAlgebra.adjoin  …
    simp only [Set.sup_eq_union, star_adjoin_comm, Set.union_star, coe_star, star_star,
      Set.union_comm]

theorem starClosure_le {S₁ : NonUnitalSubalgebra R A} {S₂ : NonUnitalStarSubalgebra R A}
    (h : S₁ ≤ S₂.toNonUnitalSubalgebra) : S₁.starClosure ≤ S₂ :=
  NonUnitalStarSubalgebra.toNonUnitalSubalgebra_le_iff.1 <|
    sup_le h fun x hx =>
      (star_star x ▸ star_mem (show star x ∈ S₂ from h <| (S₁.mem_star_iff _).1 hx) : x ∈ S₂)

theorem starClosure_le_iff {S₁ : NonUnitalSubalgebra R A} {S₂ : NonUnitalStarSubalgebra R A} :
    S₁.starClosure ≤ S₂ ↔ S₁ ≤ S₂.toNonUnitalSubalgebra :=
  ⟨fun h => le_sup_left.trans h, starClosure_le⟩

@[simp]
theorem starClosure_toNonunitalSubalgebra {S : NonUnitalSubalgebra R A} :
    S.starClosure.toNonUnitalSubalgebra = S ⊔ star S :=
  rfl

@[mono]
theorem starClosure_mono : Monotone (starClosure (R := R) (A := A)) :=
  fun _ _ h => starClosure_le <| h.trans le_sup_left

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

theorem adjoin_eq_starClosure_adjoin (s : Set A) :
    adjoin R s = (NonUnitalAlgebra.adjoin R s).starClosure :=
  toNonUnitalSubalgebra_injective <| show
    NonUnitalAlgebra.adjoin R (s ∪ star s) =
      NonUnitalAlgebra.adjoin R s ⊔ star (NonUnitalAlgebra.adjoin R s)
    from
      (NonUnitalSubalgebra.star_adjoin_comm R s).symm ▸ NonUnitalAlgebra.adjoin_union s (star s)

theorem adjoin_toNonUnitalSubalgebra (s : Set A) :
    (adjoin R s).toNonUnitalSubalgebra = NonUnitalAlgebra.adjoin R (s ∪ star s) :=
  rfl

theorem subset_adjoin (s : Set A) : s ⊆ adjoin R s :=
  (Set.subset_union_left s (star s)).trans <| NonUnitalAlgebra.subset_adjoin R

theorem star_subset_adjoin (s : Set A) : star s ⊆ adjoin R s :=
  (Set.subset_union_right s (star s)).trans <| NonUnitalAlgebra.subset_adjoin R

theorem self_mem_adjoin_singleton (x : A) : x ∈ adjoin R ({x} : Set A) :=
  NonUnitalAlgebra.subset_adjoin R <| Set.mem_union_left _ (Set.mem_singleton x)

theorem star_self_mem_adjoin_singleton (x : A) : star x ∈ adjoin R ({x} : Set A) :=
  star_mem <| self_mem_adjoin_singleton R x

variable {R}

protected theorem gc : GaloisConnection (adjoin R : Set A → NonUnitalStarSubalgebra R A) (↑) := by
  intro s S
  -- ⊢ adjoin R s ≤ S ↔ s ≤ ↑S
  rw [← toNonUnitalSubalgebra_le_iff, adjoin_toNonUnitalSubalgebra,
    NonUnitalAlgebra.adjoin_le_iff, coe_toNonUnitalSubalgebra]
  exact ⟨fun h => (Set.subset_union_left s _).trans h,
    fun h => Set.union_subset h fun x hx => star_star x ▸ star_mem (show star x ∈ S from h hx)⟩

/-- Galois insertion between `adjoin` and `Subtype.val`. -/
protected def gi : GaloisInsertion (adjoin R : Set A → NonUnitalStarSubalgebra R A) (↑) where
  choice s hs := (adjoin R s).copy s <| le_antisymm (NonUnitalStarAlgebra.gc.le_u_l s) hs
  gc := NonUnitalStarAlgebra.gc
  le_l_u S := (NonUnitalStarAlgebra.gc (S : Set A) (adjoin R S)).1 <| le_rfl
  choice_eq _ _ := NonUnitalStarSubalgebra.copy_eq _ _ _

theorem adjoin_le {S : NonUnitalStarSubalgebra R A} {s : Set A} (hs : s ⊆ S) : adjoin R s ≤ S :=
  NonUnitalStarAlgebra.gc.l_le hs

theorem adjoin_le_iff {S : NonUnitalStarSubalgebra R A} {s : Set A} : adjoin R s ≤ S ↔ s ⊆ S :=
  NonUnitalStarAlgebra.gc _ _

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
                                                                      -- ⊢ x✝ ∈ ⊤.toNonUnitalSubalgebra ↔ x✝ ∈ ⊤
                                                                           -- 🎉 no goals

@[simp]
theorem toNonUnitalSubalgebra_eq_top {S : NonUnitalStarSubalgebra R A} :
    S.toNonUnitalSubalgebra = ⊤ ↔ S = ⊤ :=
  NonUnitalStarSubalgebra.toNonUnitalSubalgebra_injective.eq_iff' top_toNonUnitalSubalgebra

theorem mem_sup_left {S T : NonUnitalStarSubalgebra R A} : ∀ {x : A}, x ∈ S → x ∈ S ⊔ T := by
  rw [←SetLike.le_def]
  -- ⊢ S ≤ S ⊔ T
  exact le_sup_left
  -- 🎉 no goals

theorem mem_sup_right {S T : NonUnitalStarSubalgebra R A} : ∀ {x : A}, x ∈ T → x ∈ S ⊔ T := by
  rw [←SetLike.le_def]
  -- ⊢ T ≤ S ⊔ T
  exact le_sup_right
  -- 🎉 no goals

theorem mul_mem_sup {S T : NonUnitalStarSubalgebra R A} {x y : A} (hx : x ∈ S) (hy : y ∈ T) :
    x * y ∈ S ⊔ T :=
  mul_mem (mem_sup_left hx) (mem_sup_right hy)

theorem map_sup (f : F) (S T : NonUnitalStarSubalgebra R A) :
    ((S ⊔ T).map f : NonUnitalStarSubalgebra R B) = S.map f ⊔ T.map f :=
  (NonUnitalStarSubalgebra.gc_map_comap f).l_sup

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
  -- 🎉 no goals

@[simp]
theorem sInf_toNonUnitalSubalgebra (S : Set (NonUnitalStarSubalgebra R A)) :
    (sInf S).toNonUnitalSubalgebra = sInf (NonUnitalStarSubalgebra.toNonUnitalSubalgebra '' S) :=
  SetLike.coe_injective <| by simp
                              -- 🎉 no goals

@[simp, norm_cast]
theorem coe_iInf {ι : Sort*} {S : ι → NonUnitalStarSubalgebra R A} :
    (↑(⨅ i, S i) : Set A) = ⋂ i, S i := by simp [iInf]
                                           -- 🎉 no goals

theorem mem_iInf {ι : Sort*} {S : ι → NonUnitalStarSubalgebra R A} {x : A} :
    (x ∈ ⨅ i, S i) ↔ ∀ i, x ∈ S i := by simp only [iInf, mem_sInf, Set.forall_range_iff]
                                        -- 🎉 no goals

@[simp]
theorem iInf_toNonUnitalSubalgebra {ι : Sort*} (S : ι → NonUnitalStarSubalgebra R A) :
    (⨅ i, S i).toNonUnitalSubalgebra = ⨅ i, (S i).toNonUnitalSubalgebra :=
  SetLike.coe_injective <| by simp
                              -- 🎉 no goals

instance : Inhabited (NonUnitalStarSubalgebra R A) :=
  ⟨⊥⟩

theorem mem_bot {x : A} : x ∈ (⊥ : NonUnitalStarSubalgebra R A) ↔ x = 0 :=
  show x ∈ NonUnitalAlgebra.adjoin R (∅ ∪ star ∅ : Set A) ↔ x = 0 by
    rw [Set.star_empty, Set.union_empty, NonUnitalAlgebra.adjoin_empty, NonUnitalAlgebra.mem_bot]
    -- 🎉 no goals

theorem toNonUnitalSubalgebra_bot :
    (⊥ : NonUnitalStarSubalgebra R A).toNonUnitalSubalgebra = ⊥ := by
  ext x
  -- ⊢ x ∈ ⊥.toNonUnitalSubalgebra ↔ x ∈ ⊥
  simp only [mem_bot, NonUnitalStarSubalgebra.mem_toNonUnitalSubalgebra, NonUnitalAlgebra.mem_bot]
  -- 🎉 no goals

@[simp]
theorem coe_bot : ((⊥ : NonUnitalStarSubalgebra R A) : Set A) = {0} := by
  simp only [Set.ext_iff, NonUnitalStarAlgebra.mem_bot, SetLike.mem_coe, Set.mem_singleton_iff,
    iff_self_iff, forall_const]

theorem eq_top_iff {S : NonUnitalStarSubalgebra R A} : S = ⊤ ↔ ∀ x : A, x ∈ S :=
  ⟨fun h x => by rw [h]; exact mem_top,
                 -- ⊢ x ∈ ⊤
                         -- 🎉 no goals
    fun h => by ext x; exact ⟨fun _ => mem_top, fun _ => h x⟩⟩
                -- ⊢ x ∈ S ↔ x ∈ ⊤
                       -- 🎉 no goals

theorem range_top_iff_surjective (f : F) :
    NonUnitalStarAlgHom.range f = (⊤ : NonUnitalStarSubalgebra R B) ↔ Function.Surjective f :=
  NonUnitalStarAlgebra.eq_top_iff

@[simp]
theorem range_id : NonUnitalStarAlgHom.range (NonUnitalStarAlgHom.id R A) = ⊤ :=
  SetLike.coe_injective Set.range_id

@[simp]
theorem map_top (f : F) : (⊤ : NonUnitalStarSubalgebra R A).map f = NonUnitalStarAlgHom.range f :=
  SetLike.coe_injective Set.image_univ

@[simp]
theorem map_bot (f : F) : (⊥ : NonUnitalStarSubalgebra R A).map f = ⊥ :=
  SetLike.coe_injective <| by simp [NonUnitalAlgebra.coe_bot, NonUnitalStarSubalgebra.coe_map]
                              -- 🎉 no goals

@[simp]
theorem comap_top (f : F) : (⊤ : NonUnitalStarSubalgebra R B).comap f = ⊤ :=
  eq_top_iff.2 fun _x => mem_top

/-- `NonUnitalStarAlgHom` to `⊤ : NonUnitalStarSubalgebra R A`. -/
def toTop : A →⋆ₙₐ[R] (⊤ : NonUnitalStarSubalgebra R A) :=
  NonUnitalStarAlgHom.codRestrict (NonUnitalStarAlgHom.id R A) ⊤ fun _ => mem_top

end NonUnitalStarAlgebra

namespace NonUnitalStarSubalgebra

open NonUnitalStarAlgebra

variable [CommSemiring R] [StarRing R]
variable [NonUnitalSemiring A] [StarRing A]
variable [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A]
variable [NonUnitalSemiring B] [StarRing B]
variable [Module R B] [IsScalarTower R B B] [SMulCommClass R B B] [StarModule R B]
variable [hF : NonUnitalStarAlgHomClass F R A B] (S : NonUnitalStarSubalgebra R A)

instance subsingleton_of_subsingleton [Subsingleton A] :
    Subsingleton (NonUnitalStarSubalgebra R A) :=
  ⟨fun B C => ext fun x => by simp only [Subsingleton.elim x 0, zero_mem B, zero_mem C]⟩
                              -- 🎉 no goals

instance _root_.NonUnitalStarAlgHom.subsingleton [Subsingleton (NonUnitalStarSubalgebra R A)] :
    Subsingleton (A →⋆ₙₐ[R] B) :=
  ⟨fun f g => NonUnitalStarAlgHom.ext fun a =>
    have : a ∈ (⊥ : NonUnitalStarSubalgebra R A) :=
      Subsingleton.elim (⊤ : NonUnitalStarSubalgebra R A) ⊥ ▸ mem_top
    (mem_bot.mp this).symm ▸ (map_zero f).trans (map_zero g).symm⟩

theorem range_val : NonUnitalStarAlgHom.range (NonUnitalStarSubalgebraClass.subtype S) = S :=
  ext <| Set.ext_iff.1 <| (NonUnitalStarSubalgebraClass.subtype S).coe_range.trans Subtype.range_val

/--
The map `S → T` when `S` is a non-unital star subalgebra contained in the non-unital star
algebra `T`.

This is the non-unital star subalgebra version of `Submodule.ofLe`, or
`NonUnitalSubalgebra.inclusion`  -/
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

@[simp]
theorem prod_top : (prod ⊤ ⊤ : NonUnitalStarSubalgebra R (A × B)) = ⊤ := by ext; simp
                                                                            -- ⊢ x✝ ∈ prod ⊤ ⊤ ↔ x✝ ∈ ⊤
                                                                                 -- 🎉 no goals

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

/-- Define a non-unital star algebra homomorphism on a directed supremum of non-unital star
subalgebras by defining it on each non-unital star subalgebra, and proving that it agrees on the
intersection of non-unital star subalgebras. -/
noncomputable def iSupLift [Nonempty ι] (K : ι → NonUnitalStarSubalgebra R A)
    (dir : Directed (· ≤ ·) K) (f : ∀ i, K i →⋆ₙₐ[R] B)
    (hf : ∀ (i j : ι) (h : K i ≤ K j), f i = (f j).comp (inclusion h))
    (T : NonUnitalStarSubalgebra R A) (hT : T = iSup K) : ↥T →⋆ₙₐ[R] B := by
  subst hT
  -- ⊢ { x // x ∈ iSup K } →⋆ₙₐ[R] B
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
        dsimp only [SetLike.coe_sort_coe, NonUnitalAlgHom.coe_comp, Function.comp_apply,
          inclusion_mk, Eq.ndrec, id_eq, eq_mpr_eq_cast]
        exact Set.iUnionLift_const _ (fun i : ι => (0 : K i)) (fun _ => rfl)  _ (by simp)
      map_mul' := by
        dsimp only [SetLike.coe_sort_coe, NonUnitalAlgHom.coe_comp, Function.comp_apply,
          inclusion_mk, Eq.ndrec, id_eq, eq_mpr_eq_cast, ZeroMemClass.coe_zero,
          AddSubmonoid.mk_add_mk, Set.inclusion_mk]
        apply Set.iUnionLift_binary (coe_iSup_of_directed dir) dir _ (fun _ => (· * ·))
        on_goal 3 => rw [coe_iSup_of_directed dir]
        all_goals simp
      map_add' := by
        dsimp only [SetLike.coe_sort_coe, NonUnitalAlgHom.coe_comp, Function.comp_apply,
          inclusion_mk, Eq.ndrec, id_eq, eq_mpr_eq_cast]
        apply Set.iUnionLift_binary (coe_iSup_of_directed dir) dir _ (fun _ => (· + ·))
        on_goal 3 => rw [coe_iSup_of_directed dir]
        all_goals simp
      map_smul' := fun r => by
        dsimp only [SetLike.coe_sort_coe, NonUnitalAlgHom.coe_comp, Function.comp_apply,
          inclusion_mk, Eq.ndrec, id_eq, eq_mpr_eq_cast]
        apply Set.iUnionLift_unary (coe_iSup_of_directed dir) _ (fun _ x => r • x)
          (fun _ _ => rfl)
        on_goal 2 => rw [coe_iSup_of_directed dir]
        all_goals simp
      map_star' := by
        dsimp only [SetLike.coe_sort_coe, NonUnitalStarAlgHom.comp_apply, inclusion_mk, Eq.ndrec,
          id_eq, eq_mpr_eq_cast, ZeroMemClass.coe_zero, AddSubmonoid.mk_add_mk, Set.inclusion_mk,
          MulMemClass.mk_mul_mk, NonUnitalAlgHom.toDistribMulActionHom_eq_coe,
          DistribMulActionHom.toFun_eq_coe, NonUnitalAlgHom.coe_to_distribMulActionHom,
          NonUnitalAlgHom.coe_mk]
        apply Set.iUnionLift_unary (coe_iSup_of_directed dir) _ (fun _ x => star x)
          (fun _ _ => rfl)
        on_goal 2 => rw [coe_iSup_of_directed dir]
        all_goals simp [map_star] }

variable [Nonempty ι] {K : ι → NonUnitalStarSubalgebra R A} {dir : Directed (· ≤ ·) K}
  {f : ∀ i, K i →⋆ₙₐ[R] B} {hf : ∀ (i j : ι) (h : K i ≤ K j), f i = (f j).comp (inclusion h)}
  {T : NonUnitalStarSubalgebra R A} {hT : T = iSup K}

@[simp]
theorem iSupLift_inclusion {i : ι} (x : K i) (h : K i ≤ T) :
    iSupLift K dir f hf T hT (inclusion h x) = f i x := by
  subst T
  -- ⊢ ↑(iSupLift K dir f hf (iSup K) (_ : iSup K = iSup K)) (↑(inclusion h) x) = ↑ …
  dsimp [iSupLift]
  -- ⊢ Set.iUnionLift (fun i => ↑(K i)) (fun i x => ↑(f i) x) (_ : ∀ (i j : ι) (x : …
  apply Set.iUnionLift_inclusion
  -- ⊢ ↑(K i) ⊆ ↑(iSup K)
  exact h
  -- 🎉 no goals

@[simp]
theorem iSupLift_comp_inclusion {i : ι} (h : K i ≤ T) :
    (iSupLift K dir f hf T hT).comp (inclusion h) = f i := by ext; simp
                                                              -- ⊢ ↑(NonUnitalStarAlgHom.comp (iSupLift K dir f hf T hT) (inclusion h)) x✝ = ↑( …
                                                                   -- 🎉 no goals

@[simp]
theorem iSupLift_mk {i : ι} (x : K i) (hx : (x : A) ∈ T) :
    iSupLift K dir f hf T hT ⟨x, hx⟩ = f i x := by
  subst hT
  -- ⊢ ↑(iSupLift K dir f hf (iSup K) (_ : iSup K = iSup K)) { val := ↑x, property  …
  dsimp [iSupLift]
  -- ⊢ Set.iUnionLift (fun i => ↑(K i)) (fun i x => ↑(f i) x) (_ : ∀ (i j : ι) (x : …
  apply Set.iUnionLift_mk
  -- 🎉 no goals

theorem iSupLift_of_mem {i : ι} (x : T) (hx : (x : A) ∈ K i) :
    iSupLift K dir f hf T hT x = f i ⟨x, hx⟩ := by
  subst hT
  -- ⊢ ↑(iSupLift K dir f hf (iSup K) (_ : iSup K = iSup K)) x = ↑(f i) { val := ↑x …
  dsimp [iSupLift]
  -- ⊢ Set.iUnionLift (fun i => ↑(K i)) (fun i x => ↑(f i) x) (_ : ∀ (i j : ι) (x : …
  apply Set.iUnionLift_of_mem
  -- 🎉 no goals

end iSupLift

section Center

variable (R A)

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
theorem center_eq_top (A : Type*) [NonUnitalCommSemiring A] [StarRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A] : center R A = ⊤ :=
  SetLike.coe_injective (Set.center_eq_univ A)

variable {R A}

instance instNonUnitalCommSemiring : NonUnitalCommSemiring (center R A) :=
  NonUnitalSubalgebra.center.instNonUnitalCommSemiring

instance instNonUnitalCommRing {A : Type*} [NonUnitalRing A] [StarRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] : NonUnitalCommRing (center R A) :=
  NonUnitalSubalgebra.center.instNonUnitalCommRing

theorem mem_center_iff {a : A} : a ∈ center R A ↔ ∀ b : A, b * a = a * b :=
  Iff.rfl

end Center

section Centralizer

variable (R)

/-- The centralizer of the star-closure of a set as a non-unital star subalgebra. -/
def centralizer (s : Set A) : NonUnitalStarSubalgebra R A :=
  { NonUnitalSubalgebra.centralizer R (s ∪ star s) with
    star_mem' := Set.star_mem_centralizer }

@[simp, norm_cast]
theorem coe_centralizer (s : Set A) : (centralizer R s : Set A) = (s ∪ star s).centralizer :=
  rfl

theorem mem_centralizer_iff {s : Set A} {z : A} :
    z ∈ centralizer R s ↔ ∀ g ∈ s, g * z = z * g ∧ star g * z = z * star g := by
  show (∀ g ∈ s ∪ star s, g * z = z * g) ↔ ∀ g ∈ s, g * z = z * g ∧ star g * z = z * star g
  -- ⊢ (∀ (g : A), g ∈ s ∪ star s → g * z = z * g) ↔ ∀ (g : A), g ∈ s → g * z = z * …
  simp only [Set.mem_union, or_imp, forall_and, and_congr_right_iff]
  -- ⊢ (∀ (x : A), x ∈ s → x * z = z * x) → ((∀ (x : A), x ∈ star s → x * z = z * x …
  exact fun _ =>
    ⟨fun hz a ha => hz _ (Set.star_mem_star.mpr ha), fun hz a ha => star_star a ▸ hz _ ha⟩

theorem centralizer_le (s t : Set A) (h : s ⊆ t) : centralizer R t ≤ centralizer R s :=
  Set.centralizer_subset (Set.union_subset_union h <| Set.preimage_mono h)

@[simp]
theorem centralizer_univ : centralizer R Set.univ = center R A :=
  SetLike.ext' <| by rw [coe_centralizer, Set.univ_union, coe_center, Set.centralizer_univ]
                     -- 🎉 no goals

end Centralizer

end NonUnitalStarSubalgebra
