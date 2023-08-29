/-
Copyright (c) 2023 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.RingTheory.NonUnitalSubring.Basic
import Mathlib.Algebra.Hom.NonUnitalAlg
import Mathlib.Data.Set.UnionLift
import Mathlib.LinearAlgebra.Finsupp

/-!
# Non-unital Subalgebras over Commutative Semirings

In this file we define `NonUnitalSubalgebra`s and the usual operations on them (`map`, `comap`).

## TODO

* once we have scalar actions by semigroups (as opposed to monoids), implement the action of a
  non-unital subalgebra on the larger algebra.
-/

universe u u' v v' w w'

open scoped BigOperators

section NonUnitalSubalgebraClass

variable {S R A : Type*} [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]
variable [SetLike S A] [NonUnitalSubsemiringClass S A] [hSR : SMulMemClass S R A] (s : S)

namespace NonUnitalSubalgebraClass

/-- Embedding of a non-unital subalgebra into the non-unital algebra. -/
def subtype (s : S) : s →ₙₐ[R] A :=
  { NonUnitalSubsemiringClass.subtype s, SMulMemClass.subtype s with toFun := (↑) }

@[simp]
theorem coeSubtype : (subtype s : s → A) = ((↑) : s → A) :=
  rfl

end NonUnitalSubalgebraClass

end NonUnitalSubalgebraClass

/-- A non-unital subalgebra is a sub(semi)ring that is also a submodule. -/
structure NonUnitalSubalgebra (R : Type u) (A : Type v) [CommSemiring R]
    [NonUnitalNonAssocSemiring A] [Module R A]
    extends NonUnitalSubsemiring A, Submodule R A : Type v

/-- Reinterpret a `NonUnitalSubalgebra` as a `NonUnitalSubsemiring`. -/
add_decl_doc NonUnitalSubalgebra.toNonUnitalSubsemiring

/-- Reinterpret a `NonUnitalSubalgebra` as a `Submodule`. -/
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
                             -- ⊢ { toNonUnitalSubsemiring := toNonUnitalSubsemiring✝, smul_mem' := smul_mem'✝ …
                                      -- ⊢ { toNonUnitalSubsemiring := toNonUnitalSubsemiring✝¹, smul_mem' := smul_mem' …
                                               -- ⊢ toNonUnitalSubsemiring✝¹ = toNonUnitalSubsemiring✝
                                                      -- 🎉 no goals

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

@[ext]
theorem ext {S T : NonUnitalSubalgebra R A} (h : ∀ x : A, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h

@[simp]
theorem mem_toNonUnitalSubsemiring {S : NonUnitalSubalgebra R A} {x} :
    x ∈ S.toNonUnitalSubsemiring ↔ x ∈ S :=
  Iff.rfl

@[simp]
theorem coe_toNonUnitalSubsemiring (S : NonUnitalSubalgebra R A) :
    (↑S.toNonUnitalSubsemiring : Set A) = S :=
  rfl

theorem toNonUnitalSubsemiring_injective :
    Function.Injective
      (toNonUnitalSubsemiring : NonUnitalSubalgebra R A → NonUnitalSubsemiring A) :=
  fun S T h =>
  ext fun x => by rw [← mem_toNonUnitalSubsemiring, ← mem_toNonUnitalSubsemiring, h]
                  -- 🎉 no goals

theorem toNonUnitalSubsemiring_inj {S U : NonUnitalSubalgebra R A} :
    S.toNonUnitalSubsemiring = U.toNonUnitalSubsemiring ↔ S = U :=
  toNonUnitalSubsemiring_injective.eq_iff

theorem mem_toSubmodule (S : NonUnitalSubalgebra R A) {x} : x ∈ S.toSubmodule ↔ x ∈ S :=
  Iff.rfl

@[simp]
theorem coe_toSubmodule (S : NonUnitalSubalgebra R A) : (↑S.toSubmodule : Set A) = S :=
  rfl

theorem toSubmodule_injective :
    Function.Injective (toSubmodule : NonUnitalSubalgebra R A → Submodule R A) := fun S T h =>
  ext fun x => by rw [← mem_toSubmodule, ← mem_toSubmodule, h]
                  -- 🎉 no goals

theorem toSubmodule_inj {S U : NonUnitalSubalgebra R A} : S.toSubmodule = U.toSubmodule ↔ S = U :=
  toSubmodule_injective.eq_iff

/-- Copy of a non-unital subalgebra with a new `carrier` equal to the old one.
Useful to fix definitional equalities. -/
protected def copy (S : NonUnitalSubalgebra R A) (s : Set A) (hs : s = ↑S) :
    NonUnitalSubalgebra R A :=
  { S.toNonUnitalSubsemiring.copy s hs with
    smul_mem' := fun r a (ha : a ∈ s) => by
      show r • a ∈ s
      -- ⊢ r • a ∈ s
      rw [hs] at ha ⊢
      -- ⊢ r • a ∈ ↑S
      exact S.smul_mem' r ha }
      -- 🎉 no goals

@[simp]
theorem coe_copy (S : NonUnitalSubalgebra R A) (s : Set A) (hs : s = ↑S) :
    (S.copy s hs : Set A) = s :=
  rfl

theorem copy_eq (S : NonUnitalSubalgebra R A) (s : Set A) (hs : s = ↑S) : S.copy s hs = S :=
  SetLike.coe_injective hs

variable (S : NonUnitalSubalgebra R A)

/-- A non-unital subalgebra over a ring is also a `Subring`. -/
def toNonUnitalSubring {R : Type u} {A : Type v} [CommRing R] [NonUnitalRing A] [Module R A]
    (S : NonUnitalSubalgebra R A) : NonUnitalSubring A where
  toNonUnitalSubsemiring := S.toNonUnitalSubsemiring
  neg_mem' := neg_mem (s := S)

@[simp]
theorem mem_toNonUnitalSubring {R : Type u} {A : Type v} [CommRing R] [NonUnitalRing A] [Module R A]
    {S : NonUnitalSubalgebra R A} {x} : x ∈ S.toNonUnitalSubring ↔ x ∈ S :=
  Iff.rfl

@[simp]
theorem coe_toNonUnitalSubring {R : Type u} {A : Type v} [CommRing R] [NonUnitalRing A] [Module R A]
    (S : NonUnitalSubalgebra R A) : (↑S.toNonUnitalSubring : Set A) = S :=
  rfl

theorem toNonUnitalSubring_injective {R : Type u} {A : Type v} [CommRing R] [NonUnitalRing A]
    [Module R A] :
    Function.Injective (toNonUnitalSubring : NonUnitalSubalgebra R A → NonUnitalSubring A) :=
  fun S T h => ext fun x => by rw [← mem_toNonUnitalSubring, ← mem_toNonUnitalSubring, h]
                               -- 🎉 no goals

theorem toNonUnitalSubring_inj {R : Type u} {A : Type v} [CommRing R] [NonUnitalRing A] [Module R A]
    {S U : NonUnitalSubalgebra R A} : S.toNonUnitalSubring = U.toNonUnitalSubring ↔ S = U :=
  toNonUnitalSubring_injective.eq_iff

instance : Inhabited S :=
  ⟨(0 : S.toNonUnitalSubsemiring)⟩

section

/-! `NonUnitalSubalgebra`s inherit structure from their `NonUnitalSubsemiring` / `Semiring`
coercions. -/


instance toNonUnitalSemiring {R A} [CommSemiring R] [NonUnitalSemiring A] [Module R A]
    (S : NonUnitalSubalgebra R A) : NonUnitalSemiring S :=
  inferInstance

instance toNonUnitalCommSemiring {R A} [CommSemiring R] [NonUnitalCommSemiring A] [Module R A]
    (S : NonUnitalSubalgebra R A) : NonUnitalCommSemiring S :=
  inferInstance

instance toNonUnitalRing {R A} [CommRing R] [NonUnitalRing A] [Module R A]
    (S : NonUnitalSubalgebra R A) : NonUnitalRing S :=
  inferInstance

instance toNonUnitalCommRing {R A} [CommRing R] [NonUnitalCommRing A] [Module R A]
    (S : NonUnitalSubalgebra R A) : NonUnitalCommRing S :=
  inferInstance

end

/-- The forgetful map from `NonUnitalSubalgebra` to `Submodule` as an `OrderEmbedding` -/
def toSubmodule' : NonUnitalSubalgebra R A ↪o Submodule R A
    where
  toEmbedding :=
    { toFun := fun S => S.toSubmodule
      inj' := fun S T h => ext <| by apply SetLike.ext_iff.1 h }
                                     -- 🎉 no goals
  map_rel_iff' := SetLike.coe_subset_coe.symm.trans SetLike.coe_subset_coe

/-- The forgetful map from `NonUnitalSubalgebra` to `NonUnitalSubsemiring` as an
`OrderEmbedding` -/
def toNonUnitalSubsemiring' : NonUnitalSubalgebra R A ↪o NonUnitalSubsemiring A
    where
  toEmbedding :=
    { toFun := fun S => S.toNonUnitalSubsemiring
      inj' := fun S T h => ext <| by apply SetLike.ext_iff.1 h }
                                     -- 🎉 no goals
  map_rel_iff' := SetLike.coe_subset_coe.symm.trans SetLike.coe_subset_coe

/-- The forgetful map from `NonUnitalSubalgebra` to `NonUnitalSubsemiring` as an
`OrderEmbedding` -/
def toNonUnitalSubring' {R : Type u} {A : Type v} [CommRing R] [NonUnitalRing A] [Module R A] :
    NonUnitalSubalgebra R A ↪o NonUnitalSubring A
    where
  toEmbedding :=
    { toFun := fun S => S.toNonUnitalSubring
      inj' := fun S T h => ext <| by apply SetLike.ext_iff.1 h }
                                     -- 🎉 no goals
  map_rel_iff' := SetLike.coe_subset_coe.symm.trans SetLike.coe_subset_coe

section

/-! ### `NonUnitalSubalgebra`s inherit structure from their `Submodule` coercions. -/

instance instModule' [Semiring R'] [SMul R' R] [Module R' A] [IsScalarTower R' R A] : Module R' S :=
  SMulMemClass.toModule' _ R' R A S

instance instModule : Module R S :=
  S.instModule'

instance instIsScalarTower' [Semiring R'] [SMul R' R] [Module R' A] [IsScalarTower R' R A] :
    IsScalarTower R' R S :=
  S.toSubmodule.isScalarTower

instance [IsScalarTower R A A] : IsScalarTower R S S
    where smul_assoc r x y := Subtype.ext <| smul_assoc r (x : A) (y : A)

instance instSMulCommClass' [Semiring R'] [SMul R' R] [Module R' A] [IsScalarTower R' R A]
    [SMulCommClass R' R A] : SMulCommClass R' R S
    where smul_comm r' r s := Subtype.ext <| smul_comm r' r (s : A)

instance instSMulCommClass [SMulCommClass R A A] : SMulCommClass R S S
    where smul_comm r x y := Subtype.ext <| smul_comm r (x : A) (y : A)

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

protected theorem coe_neg {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    {S : NonUnitalSubalgebra R A} (x : S) : (↑(-x) : A) = -↑x :=
  rfl

protected theorem coe_sub {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    {S : NonUnitalSubalgebra R A} (x y : S) : (↑(x - y) : A) = ↑x - ↑y :=
  rfl

@[simp, norm_cast]
theorem coe_smul [Semiring R'] [SMul R' R] [Module R' A] [IsScalarTower R' R A] (r : R') (x : S) :
    (r • x : A) = r • (x : A) :=
  rfl

protected theorem coe_eq_zero {x : S} : (x : A) = 0 ↔ x = 0 :=
  ZeroMemClass.coe_eq_zero

@[simp]
theorem toNonUnitalSubsemiring_subtype :
    NonUnitalSubsemiringClass.subtype S = NonUnitalSubalgebraClass.subtype (R := R) S :=
  rfl

@[simp]
theorem toSubring_subtype {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (S : NonUnitalSubalgebra R A) :
    NonUnitalSubringClass.subtype S = NonUnitalSubalgebraClass.subtype (R := R) S :=
  rfl

/-- Linear equivalence between `S : Submodule R A` and `S`. Though these types are equal,
we define it as a `LinearEquiv` to avoid type equalities. -/
def toSubmoduleEquiv (S : NonUnitalSubalgebra R A) : S.toSubmodule ≃ₗ[R] S :=
  LinearEquiv.ofEq _ _ rfl

/-- Transport a non-unital subalgebra via an algebra homomorphism. -/
def map (f : F) (S : NonUnitalSubalgebra R A) : NonUnitalSubalgebra R B :=
  { S.toNonUnitalSubsemiring.map (f : A →ₙ+* B) with
    smul_mem' := fun r b hb => by
      rcases hb with ⟨a, ha, rfl⟩
      -- ⊢ r • ↑↑f a ∈ { toAddSubmonoid := src✝.toAddSubmonoid, mul_mem' := (_ : ∀ {a b …
      exact map_smul f r a ▸ Set.mem_image_of_mem f (S.smul_mem' r ha) }
      -- 🎉 no goals

theorem map_mono {S₁ S₂ : NonUnitalSubalgebra R A} {f : F} :
    S₁ ≤ S₂ → (map f S₁ : NonUnitalSubalgebra R B) ≤ map f S₂ :=
  Set.image_subset f

theorem map_injective {f : F} (hf : Function.Injective f) :
    Function.Injective (map f : NonUnitalSubalgebra R A → NonUnitalSubalgebra R B) :=
  fun _S₁ _S₂ ih =>
  ext <| Set.ext_iff.1 <| Set.image_injective.2 hf <| Set.ext <| SetLike.ext_iff.mp ih

@[simp]
theorem map_id (S : NonUnitalSubalgebra R A) : map (NonUnitalAlgHom.id R A) S = S :=
  SetLike.coe_injective <| Set.image_id _

theorem map_map (S : NonUnitalSubalgebra R A) (g : B →ₙₐ[R] C) (f : A →ₙₐ[R] B) :
    (S.map f).map g = S.map (g.comp f) :=
  SetLike.coe_injective <| Set.image_image _ _ _

@[simp]
theorem mem_map {S : NonUnitalSubalgebra R A} {f : F} {y : B} : y ∈ map f S ↔ ∃ x ∈ S, f x = y :=
  NonUnitalSubsemiring.mem_map

theorem map_toSubmodule {S : NonUnitalSubalgebra R A} {f : F} :
    (map f S).toSubmodule = Submodule.map (f : A →ₗ[R] B) S.toSubmodule :=
  SetLike.coe_injective rfl

theorem map_toNonUnitalSubsemiring {S : NonUnitalSubalgebra R A} {f : F} :
    (map f S).toNonUnitalSubsemiring = S.toNonUnitalSubsemiring.map (f : A →ₙ+* B) :=
  SetLike.coe_injective rfl

@[simp]
theorem coe_map (S : NonUnitalSubalgebra R A) (f : F) : (map f S : Set B) = f '' S :=
  rfl

/-- Preimage of a non-unital subalgebra under an algebra homomorphism. -/
def comap (f : F) (S : NonUnitalSubalgebra R B) : NonUnitalSubalgebra R A :=
  { S.toNonUnitalSubsemiring.comap (f : A →ₙ+* B) with
    smul_mem' := fun r a (ha : f a ∈ S) =>
      show f (r • a) ∈ S from (map_smul f r a).symm ▸ SMulMemClass.smul_mem r ha }

theorem map_le {S : NonUnitalSubalgebra R A} {f : F} {U : NonUnitalSubalgebra R B} :
    map f S ≤ U ↔ S ≤ comap f U :=
  Set.image_subset_iff

theorem gc_map_comap (f : F) :
    GaloisConnection (map f : NonUnitalSubalgebra R A → NonUnitalSubalgebra R B) (comap f) :=
  fun _ _ => map_le

@[simp]
theorem mem_comap (S : NonUnitalSubalgebra R B) (f : F) (x : A) : x ∈ comap f S ↔ f x ∈ S :=
  Iff.rfl

@[simp, norm_cast]
theorem coe_comap (S : NonUnitalSubalgebra R B) (f : F) : (comap f S : Set A) = f ⁻¹' (S : Set B) :=
  rfl

instance noZeroDivisors {R A : Type*} [CommSemiring R] [NonUnitalSemiring A] [NoZeroDivisors A]
    [Module R A] (S : NonUnitalSubalgebra R A) : NoZeroDivisors S :=
  NonUnitalSubsemiringClass.noZeroDivisors S

end NonUnitalSubalgebra

namespace Submodule

variable {R A : Type*} [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]

/-- A submodule closed under multiplication is a non-unital subalgebra. -/
def toNonUnitalSubalgebra (p : Submodule R A) (h_mul : ∀ x y, x ∈ p → y ∈ p → x * y ∈ p) :
    NonUnitalSubalgebra R A :=
  { p with
    mul_mem' := h_mul _ _ }

@[simp]
theorem mem_toNonUnitalSubalgebra {p : Submodule R A} {h_mul} {x} :
    x ∈ p.toNonUnitalSubalgebra h_mul ↔ x ∈ p :=
  Iff.rfl

@[simp]
theorem coe_toNonUnitalSubalgebra (p : Submodule R A) (h_mul) :
    (p.toNonUnitalSubalgebra h_mul : Set A) = p :=
  rfl

theorem toNonUnitalSubalgebra_mk (p : Submodule R A) hmul :
    p.toNonUnitalSubalgebra hmul =
      NonUnitalSubalgebra.mk ⟨⟨⟨p, p.add_mem⟩, p.zero_mem⟩, hmul _ _⟩ p.smul_mem' :=
  rfl

@[simp]
theorem toNonUnitalSubalgebra_toSubmodule (p : Submodule R A) (h_mul) :
    (p.toNonUnitalSubalgebra h_mul).toSubmodule = p :=
  SetLike.coe_injective rfl

@[simp]
theorem _root_.NonUnitalSubalgebra.toSubmodule_toNonUnitalSubalgebra (S : NonUnitalSubalgebra R A) :
    (S.toSubmodule.toNonUnitalSubalgebra fun _ _ => mul_mem (s := S)) = S :=
  SetLike.coe_injective rfl

end Submodule

namespace NonUnitalAlgHom

variable {F : Type v'} {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}
variable [CommSemiring R]
variable [NonUnitalNonAssocSemiring A] [Module R A] [NonUnitalNonAssocSemiring B] [Module R B]
variable [NonUnitalNonAssocSemiring C] [Module R C] [NonUnitalAlgHomClass F R A B]

/-- Range of an `NonUnitalAlgHom` as a non-unital subalgebra. -/
protected def range (φ : F) : NonUnitalSubalgebra R B where
  toNonUnitalSubsemiring := NonUnitalRingHom.srange (φ : A →ₙ+* B)
  smul_mem' := fun r a => by rintro ⟨a, rfl⟩; exact ⟨r • a, map_smul φ r a⟩
                             -- ⊢ r • ↑↑φ a ∈ (NonUnitalRingHom.srange ↑φ).toAddSubmonoid.toAddSubsemigroup.ca …
                                              -- 🎉 no goals

@[simp]
theorem mem_range (φ : F) {y : B} :
    y ∈ (NonUnitalAlgHom.range φ : NonUnitalSubalgebra R B) ↔ ∃ x : A, φ x = y :=
  NonUnitalRingHom.mem_srange

theorem mem_range_self (φ : F) (x : A) :
    φ x ∈ (NonUnitalAlgHom.range φ : NonUnitalSubalgebra R B) :=
  (NonUnitalAlgHom.mem_range φ).2 ⟨x, rfl⟩

@[simp]
theorem coe_range (φ : F) :
    ((NonUnitalAlgHom.range φ : NonUnitalSubalgebra R B) : Set B) = Set.range (φ : A → B) := by
  ext
  -- ⊢ x✝ ∈ ↑(NonUnitalAlgHom.range φ) ↔ x✝ ∈ Set.range ↑φ
  rw [SetLike.mem_coe, mem_range]
  -- ⊢ (∃ x, ↑φ x = x✝) ↔ x✝ ∈ Set.range ↑φ
  rfl
  -- 🎉 no goals

theorem range_comp (f : A →ₙₐ[R] B) (g : B →ₙₐ[R] C) :
    NonUnitalAlgHom.range (g.comp f) = (NonUnitalAlgHom.range f).map g :=
  SetLike.coe_injective (Set.range_comp g f)

theorem range_comp_le_range (f : A →ₙₐ[R] B) (g : B →ₙₐ[R] C) :
    NonUnitalAlgHom.range (g.comp f) ≤ NonUnitalAlgHom.range g :=
  SetLike.coe_mono (Set.range_comp_subset_range f g)

/-- Restrict the codomain of a non-unital algebra homomorphism. -/
def codRestrict (f : F) (S : NonUnitalSubalgebra R B) (hf : ∀ x, f x ∈ S) : A →ₙₐ[R] S :=
  { NonUnitalRingHom.codRestrict (f : A →ₙ+* B) S.toNonUnitalSubsemiring hf with
    map_smul' := fun r a => Subtype.ext <| map_smul f r a }

@[simp]
theorem subtype_comp_codRestrict (f : F) (S : NonUnitalSubalgebra R B) (hf : ∀ x : A, f x ∈ S) :
    (NonUnitalSubalgebraClass.subtype S).comp (NonUnitalAlgHom.codRestrict f S hf) = f :=
  NonUnitalAlgHom.ext fun _ => rfl

@[simp]
theorem coe_codRestrict (f : F) (S : NonUnitalSubalgebra R B) (hf : ∀ x, f x ∈ S) (x : A) :
    ↑(NonUnitalAlgHom.codRestrict f S hf x) = f x :=
  rfl

theorem injective_codRestrict (f : F) (S : NonUnitalSubalgebra R B) (hf : ∀ x : A, f x ∈ S) :
    Function.Injective (NonUnitalAlgHom.codRestrict f S hf) ↔ Function.Injective f :=
  ⟨fun H _x _y hxy => H <| Subtype.eq hxy, fun H _x _y hxy => H (congr_arg Subtype.val hxy : _)⟩

/-- Restrict the codomain of an alg_hom `f` to `f.range`.

This is the bundled version of `Set.rangeFactorization`. -/
@[reducible]
def rangeRestrict (f : F) : A →ₙₐ[R] (NonUnitalAlgHom.range f : NonUnitalSubalgebra R B) :=
  NonUnitalAlgHom.codRestrict f (NonUnitalAlgHom.range f) (NonUnitalAlgHom.mem_range_self f)

/-- The equalizer of two non-unital `R`-algebra homomorphisms -/
def equalizer (ϕ ψ : F) : NonUnitalSubalgebra R A
    where
  carrier := {a | (ϕ a : B) = ψ a}
  zero_mem' := by rw [Set.mem_setOf_eq, map_zero, map_zero]
                  -- 🎉 no goals
  add_mem' {x y} (hx : ϕ x = ψ x) (hy : ϕ y = ψ y) := by
    -- 🎉 no goals
    rw [Set.mem_setOf_eq, map_add, map_add, hx, hy]
  mul_mem' {x y} (hx : ϕ x = ψ x) (hy : ϕ y = ψ y) := by
    rw [Set.mem_setOf_eq, map_mul, map_mul, hx, hy]
    -- 🎉 no goals
  smul_mem' r x (hx : ϕ x = ψ x) := by rw [Set.mem_setOf_eq, map_smul, map_smul, hx]
                                       -- 🎉 no goals

@[simp]
theorem mem_equalizer (φ ψ : F) (x : A) :
    x ∈ @NonUnitalAlgHom.equalizer F R A B _ _ _ _ _ _ φ ψ ↔ φ x = ψ x :=
  Iff.rfl

/-- The range of a morphism of algebras is a fintype, if the domain is a fintype.

Note that this instance can cause a diamond with `Subtype.fintype` if `B` is also a fintype. -/
instance fintypeRange [Fintype A] [DecidableEq B] (φ : F) :
    Fintype (@NonUnitalAlgHom.range F R A B _ _ _ _ _ _ φ) :=
  Set.fintypeRange φ

end NonUnitalAlgHom

namespace NonUnitalAlgebra

variable {F : Type*} (R : Type u) {A : Type v} {B : Type w}
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
          · exact fun x _hx => (mul_zero x).symm ▸ Submodule.zero_mem _
            -- 🎉 no goals
          · exact fun x y hx hy z hz => (mul_add z x y).symm ▸ add_mem (hx z hz) (hy z hz)
            -- 🎉 no goals
          · exact fun r x hx y hy => (mul_smul_comm r y x).symm ▸ SMulMemClass.smul_mem r (hx y hy)
            -- 🎉 no goals
        · exact (zero_mul b).symm ▸ Submodule.zero_mem _
          -- 🎉 no goals
        · exact fun x y => (add_mul x y b).symm ▸ add_mem
          -- 🎉 no goals
        · exact fun r x hx => (smul_mul_assoc r x b).symm ▸ SMulMemClass.smul_mem r hx }
          -- 🎉 no goals

theorem adjoin_toSubmodule (s : Set A) :
    (adjoin R s).toSubmodule = Submodule.span R (NonUnitalSubsemiring.closure s : Set A) :=
  rfl

theorem subset_adjoin {s : Set A} : s ⊆ adjoin R s :=
  NonUnitalSubsemiring.subset_closure.trans Submodule.subset_span

theorem self_mem_adjoin_singleton (x : A) : x ∈ adjoin R ({x} : Set A) :=
  NonUnitalAlgebra.subset_adjoin R (Set.mem_singleton x)

variable {R}

/-- If some predicate holds for all `x ∈ (s : Set A)` and this predicate is closed under the
`algebraMap`, addition, multiplication and star operations, then it holds for `a ∈ adjoin R s`. -/
theorem adjoin_induction {s : Set A} {p : A → Prop} {a : A} (h : a ∈ adjoin R s)
    (Hs : ∀ x ∈ s, p x) (Hadd : ∀ x y, p x → p y → p (x + y)) (H0 : p 0)
    (Hmul : ∀ x y, p x → p y → p (x * y)) (Hsmul : ∀ (r : R) x, p x → p (r • x)) : p a :=
  Submodule.span_induction h
    (fun _a ha => NonUnitalSubsemiring.closure_induction ha Hs H0 Hadd Hmul) H0 Hadd Hsmul

theorem adjoin_induction₂ {s : Set A} {p : A → A → Prop} {a b : A} (ha : a ∈ adjoin R s)
    (hb : b ∈ adjoin R s) (Hs : ∀ x ∈ s, ∀ y ∈ s, p x y) (H0_left : ∀ y, p 0 y)
    (H0_right : ∀ x, p x 0) (Hadd_left : ∀ x₁ x₂ y, p x₁ y → p x₂ y → p (x₁ + x₂) y)
    (Hadd_right : ∀ x y₁ y₂, p x y₁ → p x y₂ → p x (y₁ + y₂))
    (Hmul_left : ∀ x₁ x₂ y, p x₁ y → p x₂ y → p (x₁ * x₂) y)
    (Hmul_right : ∀ x y₁ y₂, p x y₁ → p x y₂ → p x (y₁ * y₂))
    (Hsmul_left : ∀ (r : R) x y, p x y → p (r • x) y)
    (Hsmul_right : ∀ (r : R) x y, p x y → p x (r • y)) : p a b :=
  Submodule.span_induction₂ ha hb
    (fun _x hx _y hy =>
      NonUnitalSubsemiring.closure_induction₂ hx hy Hs H0_left H0_right Hadd_left Hadd_right
        Hmul_left Hmul_right)
    H0_left H0_right Hadd_left Hadd_right Hsmul_left Hsmul_right

/-- The difference with `NonUnitalAlgebra.adjoin_induction` is that this acts on the subtype. -/
lemma adjoin_induction' {s : Set A} {p : adjoin R s → Prop} (a : adjoin R s)
  (Hs : ∀ x (h : x ∈ s), p ⟨x, subset_adjoin R h⟩)
  (Hadd : ∀ x y, p x → p y → p (x + y)) (H0 : p 0)
  (Hmul : ∀ x y, p x → p y → p (x * y)) (Hsmul : ∀ (r : R) x, p x → p (r • x)) : p a :=
Subtype.recOn a <| fun b hb => by
  refine Exists.elim ?_ (fun (hb : b ∈ adjoin R s) (hc : p ⟨b, hb⟩) => hc)
  -- ⊢ ∃ x, p { val := b, property := x }
  apply adjoin_induction hb
  · exact fun x hx => ⟨subset_adjoin R hx, Hs x hx⟩
    -- 🎉 no goals
  · exact fun x y hx hy => Exists.elim hx <| fun hx' hx => Exists.elim hy <| fun hy' hy =>
      ⟨add_mem hx' hy', Hadd _ _ hx hy⟩
  · exact ⟨_, H0⟩
    -- 🎉 no goals
  · exact fun x y hx hy => Exists.elim hx <| fun hx' hx => Exists.elim hy <| fun hy' hy =>
      ⟨mul_mem hx' hy', Hmul _ _ hx hy⟩
  · exact fun r x hx => Exists.elim hx <| fun hx' hx => ⟨SMulMemClass.smul_mem r hx', Hsmul r _ hx⟩
    -- 🎉 no goals

protected theorem gc : GaloisConnection (adjoin R : Set A → NonUnitalSubalgebra R A) (↑) :=
  fun s S =>
  ⟨fun H => (NonUnitalSubsemiring.subset_closure.trans Submodule.subset_span).trans H,
    fun H => show Submodule.span R _ ≤ S.toSubmodule from Submodule.span_le.mpr <|
      show NonUnitalSubsemiring.closure s ≤ S.toNonUnitalSubsemiring from
        NonUnitalSubsemiring.closure_le.2 H⟩

/-- Galois insertion between `adjoin` and `Subtype.val`. -/
protected def gi : GaloisInsertion (adjoin R : Set A → NonUnitalSubalgebra R A) (↑)
    where
  choice s hs := (adjoin R s).copy s <| le_antisymm (NonUnitalAlgebra.gc.le_u_l s) hs
  gc := NonUnitalAlgebra.gc
  le_l_u S := (NonUnitalAlgebra.gc (S : Set A) (adjoin R S)).1 <| le_rfl
  choice_eq _ _ := NonUnitalSubalgebra.copy_eq _ _ _

instance : CompleteLattice (NonUnitalSubalgebra R A) :=
  GaloisInsertion.liftCompleteLattice NonUnitalAlgebra.gi

theorem adjoin_le {S : NonUnitalSubalgebra R A} {s : Set A} (hs : s ⊆ S) : adjoin R s ≤ S :=
  NonUnitalAlgebra.gc.l_le hs

theorem adjoin_le_iff {S : NonUnitalSubalgebra R A} {s : Set A} : adjoin R s ≤ S ↔ s ⊆ S :=
  NonUnitalAlgebra.gc _ _

theorem adjoin_union (s t : Set A) : adjoin R (s ∪ t) = adjoin R s ⊔ adjoin R t :=
  (NonUnitalAlgebra.gc : GaloisConnection _ ((↑) : NonUnitalSubalgebra R A → Set A)).l_sup

variable (R A)

@[simp]
theorem adjoin_empty : adjoin R (∅ : Set A) = ⊥ :=
  show adjoin R ⊥ = ⊥ by apply GaloisConnection.l_bot; exact NonUnitalAlgebra.gc
                         -- ⊢ GaloisConnection (adjoin R) ?u
                                                       -- 🎉 no goals

@[simp]
theorem adjoin_univ : adjoin R (Set.univ : Set A) = ⊤ :=
  eq_top_iff.2 fun _x hx => subset_adjoin R hx

variable {R A}

@[simp]
theorem coe_top : (↑(⊤ : NonUnitalSubalgebra R A) : Set A) = Set.univ :=
  rfl

@[simp]
theorem mem_top {x : A} : x ∈ (⊤ : NonUnitalSubalgebra R A) :=
  Set.mem_univ x

@[simp]
theorem top_toSubmodule : (⊤ : NonUnitalSubalgebra R A).toSubmodule = ⊤ :=
  rfl

@[simp]
theorem top_toNonUnitalSubsemiring : (⊤ : NonUnitalSubalgebra R A).toNonUnitalSubsemiring = ⊤ :=
  rfl

@[simp]
theorem top_toSubring {R A : Type*} [CommRing R] [NonUnitalRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] :
    (⊤ : NonUnitalSubalgebra R A).toNonUnitalSubring = ⊤ :=
  rfl

@[simp]
theorem toSubmodule_eq_top {S : NonUnitalSubalgebra R A} : S.toSubmodule = ⊤ ↔ S = ⊤ :=
  NonUnitalSubalgebra.toSubmodule'.injective.eq_iff' top_toSubmodule

@[simp]
theorem toNonUnitalSubsemiring_eq_top {S : NonUnitalSubalgebra R A} :
    S.toNonUnitalSubsemiring = ⊤ ↔ S = ⊤ :=
  NonUnitalSubalgebra.toNonUnitalSubsemiring_injective.eq_iff' top_toNonUnitalSubsemiring

@[simp]
theorem to_subring_eq_top {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    {S : NonUnitalSubalgebra R A} : S.toNonUnitalSubring = ⊤ ↔ S = ⊤ :=
  NonUnitalSubalgebra.toNonUnitalSubring_injective.eq_iff' top_toSubring

theorem mem_sup_left {S T : NonUnitalSubalgebra R A} : ∀ {x : A}, x ∈ S → x ∈ S ⊔ T := by
  rw [←SetLike.le_def]
  -- ⊢ S ≤ S ⊔ T
  exact le_sup_left
  -- 🎉 no goals

theorem mem_sup_right {S T : NonUnitalSubalgebra R A} : ∀ {x : A}, x ∈ T → x ∈ S ⊔ T := by
  rw [←SetLike.le_def]
  -- ⊢ T ≤ S ⊔ T
  exact le_sup_right
  -- 🎉 no goals

theorem mul_mem_sup {S T : NonUnitalSubalgebra R A} {x y : A} (hx : x ∈ S) (hy : y ∈ T) :
    x * y ∈ S ⊔ T :=
  mul_mem (mem_sup_left hx) (mem_sup_right hy)

theorem map_sup (f : F) (S T : NonUnitalSubalgebra R A) :
    ((S ⊔ T).map f : NonUnitalSubalgebra R B) = S.map f ⊔ T.map f :=
  (@NonUnitalSubalgebra.gc_map_comap F R A B _ _ _ _ _ _ f).l_sup

@[simp, norm_cast]
theorem coe_inf (S T : NonUnitalSubalgebra R A) : (↑(S ⊓ T) : Set A) = (S : Set A) ∩ T :=
  rfl

@[simp]
theorem mem_inf {S T : NonUnitalSubalgebra R A} {x : A} : x ∈ S ⊓ T ↔ x ∈ S ∧ x ∈ T :=
  Iff.rfl

@[simp]
theorem inf_toSubmodule (S T : NonUnitalSubalgebra R A) :
    (S ⊓ T).toSubmodule = S.toSubmodule ⊓ T.toSubmodule :=
  rfl

@[simp]
theorem inf_toNonUnitalSubsemiring (S T : NonUnitalSubalgebra R A) :
    (S ⊓ T).toNonUnitalSubsemiring = S.toNonUnitalSubsemiring ⊓ T.toNonUnitalSubsemiring :=
  rfl

@[simp, norm_cast]
theorem coe_sInf (S : Set (NonUnitalSubalgebra R A)) : (↑(sInf S) : Set A) = ⋂ s ∈ S, ↑s :=
  sInf_image

theorem mem_sInf {S : Set (NonUnitalSubalgebra R A)} {x : A} : x ∈ sInf S ↔ ∀ p ∈ S, x ∈ p := by
  simp only [← SetLike.mem_coe, coe_sInf, Set.mem_iInter₂]
  -- 🎉 no goals

@[simp]
theorem sInf_toSubmodule (S : Set (NonUnitalSubalgebra R A)) :
    (sInf S).toSubmodule = sInf (NonUnitalSubalgebra.toSubmodule '' S) :=
  SetLike.coe_injective <| by simp
                              -- 🎉 no goals

@[simp]
theorem sInf_toNonUnitalSubsemiring (S : Set (NonUnitalSubalgebra R A)) :
    (sInf S).toNonUnitalSubsemiring = sInf (NonUnitalSubalgebra.toNonUnitalSubsemiring '' S) :=
  SetLike.coe_injective <| by simp
                              -- 🎉 no goals

@[simp, norm_cast]
theorem coe_iInf {ι : Sort*} {S : ι → NonUnitalSubalgebra R A} :
    (↑(⨅ i, S i) : Set A) = ⋂ i, S i := by simp [iInf]
                                           -- 🎉 no goals

theorem mem_iInf {ι : Sort*} {S : ι → NonUnitalSubalgebra R A} {x : A} :
    (x ∈ ⨅ i, S i) ↔ ∀ i, x ∈ S i := by simp only [iInf, mem_sInf, Set.forall_range_iff]
                                        -- 🎉 no goals

@[simp]
theorem iInf_toSubmodule {ι : Sort*} (S : ι → NonUnitalSubalgebra R A) :
    (⨅ i, S i).toSubmodule = ⨅ i, (S i).toSubmodule :=
  SetLike.coe_injective <| by simp
                              -- 🎉 no goals

instance : Inhabited (NonUnitalSubalgebra R A) :=
  ⟨⊥⟩

theorem mem_bot {x : A} : x ∈ (⊥ : NonUnitalSubalgebra R A) ↔ x = 0 :=
  show x ∈ Submodule.span R (NonUnitalSubsemiring.closure (∅ : Set A) : Set A) ↔ x = 0 by
    rw [NonUnitalSubsemiring.closure_empty, NonUnitalSubsemiring.coe_bot,
      Submodule.span_zero_singleton, Submodule.mem_bot]

theorem toSubmodule_bot : (⊥ : NonUnitalSubalgebra R A).toSubmodule = ⊥ := by
  ext
  -- ⊢ x✝ ∈ NonUnitalSubalgebra.toSubmodule ⊥ ↔ x✝ ∈ ⊥
  simp only [mem_bot, NonUnitalSubalgebra.mem_toSubmodule, Submodule.mem_bot]
  -- 🎉 no goals

@[simp]
theorem coe_bot : ((⊥ : NonUnitalSubalgebra R A) : Set A) = {0} := by
  simp [Set.ext_iff, NonUnitalAlgebra.mem_bot]
  -- 🎉 no goals

theorem eq_top_iff {S : NonUnitalSubalgebra R A} : S = ⊤ ↔ ∀ x : A, x ∈ S :=
  ⟨fun h x => by rw [h]; exact mem_top, fun h => by ext x; exact ⟨fun _ => mem_top, fun _ => h x⟩⟩
                 -- ⊢ x ∈ ⊤
                         -- 🎉 no goals
                                                    -- ⊢ x ∈ S ↔ x ∈ ⊤
                                                           -- 🎉 no goals

theorem range_top_iff_surjective (f : A →ₙₐ[R] B) :
    NonUnitalAlgHom.range f = (⊤ : NonUnitalSubalgebra R B) ↔ Function.Surjective f :=
  NonUnitalAlgebra.eq_top_iff

@[simp]
theorem range_id : NonUnitalAlgHom.range (NonUnitalAlgHom.id R A) = ⊤ :=
  SetLike.coe_injective Set.range_id

@[simp]
theorem map_top (f : A →ₙₐ[R] B) : (⊤ : NonUnitalSubalgebra R A).map f = NonUnitalAlgHom.range f :=
  SetLike.coe_injective Set.image_univ

@[simp]
theorem map_bot (f : A →ₙₐ[R] B) : (⊥ : NonUnitalSubalgebra R A).map f = ⊥ :=
  SetLike.coe_injective <| by simp [NonUnitalAlgebra.coe_bot, NonUnitalSubalgebra.coe_map]
                              -- 🎉 no goals

@[simp]
theorem comap_top (f : A →ₙₐ[R] B) : (⊤ : NonUnitalSubalgebra R B).comap f = ⊤ :=
  eq_top_iff.2 fun _ => mem_top

/-- `NonUnitalAlgHom` to `⊤ : NonUnitalSubalgebra R A`. -/
def toTop : A →ₙₐ[R] (⊤ : NonUnitalSubalgebra R A) :=
  NonUnitalAlgHom.codRestrict (NonUnitalAlgHom.id R A) ⊤ fun _ => mem_top

end NonUnitalAlgebra

namespace NonUnitalSubalgebra

open NonUnitalAlgebra

section NonAssoc

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommSemiring R]
variable [NonUnitalNonAssocSemiring A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
variable [NonUnitalNonAssocSemiring B] [Module R B] [IsScalarTower R B B] [SMulCommClass R B B]
variable (S : NonUnitalSubalgebra R A)

instance subsingleton_of_subsingleton [Subsingleton A] : Subsingleton (NonUnitalSubalgebra R A) :=
  ⟨fun B C => ext fun x => by simp only [Subsingleton.elim x 0, zero_mem B, zero_mem C]⟩
                              -- 🎉 no goals

instance _root_.NonUnitalAlgHom.subsingleton [Subsingleton (NonUnitalSubalgebra R A)] :
    Subsingleton (A →ₙₐ[R] B) :=
  ⟨fun f g =>
    NonUnitalAlgHom.ext fun a =>
      have : a ∈ (⊥ : NonUnitalSubalgebra R A) :=
        Subsingleton.elim (⊤ : NonUnitalSubalgebra R A) ⊥ ▸ mem_top
      (mem_bot.mp this).symm ▸ (map_zero f).trans (map_zero g).symm⟩

theorem range_val : NonUnitalAlgHom.range (NonUnitalSubalgebraClass.subtype S) = S :=
  ext <| Set.ext_iff.1 <| (NonUnitalSubalgebraClass.subtype S).coe_range.trans Subtype.range_val

/-- The map `S → T` when `S` is a non-unital subalgebra contained in the non-unital subalgebra `T`.

This is the non-unital subalgebra version of `Submodule.ofLe`, or `Subring.inclusion`  -/
def inclusion {S T : NonUnitalSubalgebra R A} (h : S ≤ T) : S →ₙₐ[R] T
    where
  toFun := Set.inclusion h
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_smul' _ _ := rfl

theorem inclusion_injective {S T : NonUnitalSubalgebra R A} (h : S ≤ T) :
    Function.Injective (inclusion h) := fun _ _ => Subtype.ext ∘ Subtype.mk.inj

@[simp]
theorem inclusion_self {S : NonUnitalSubalgebra R A} :
    inclusion (le_refl S) = NonUnitalAlgHom.id R S :=
  NonUnitalAlgHom.ext fun _ => Subtype.ext rfl

@[simp]
theorem inclusion_mk {S T : NonUnitalSubalgebra R A} (h : S ≤ T) (x : A) (hx : x ∈ S) :
    inclusion h ⟨x, hx⟩ = ⟨x, h hx⟩ :=
  rfl

theorem inclusion_right {S T : NonUnitalSubalgebra R A} (h : S ≤ T) (x : T) (m : (x : A) ∈ S) :
    inclusion h ⟨x, m⟩ = x :=
  Subtype.ext rfl

@[simp]
theorem inclusion_inclusion {S T U : NonUnitalSubalgebra R A} (hst : S ≤ T) (htu : T ≤ U) (x : S) :
    inclusion htu (inclusion hst x) = inclusion (le_trans hst htu) x :=
  Subtype.ext rfl

@[simp]
theorem coe_inclusion {S T : NonUnitalSubalgebra R A} (h : S ≤ T) (s : S) :
    (inclusion h s : A) = s :=
  rfl

section Prod

variable (S₁ : NonUnitalSubalgebra R B)

/-- The product of two non-unital subalgebras is a non-unital subalgebra. -/
def prod : NonUnitalSubalgebra R (A × B) :=
  { S.toNonUnitalSubsemiring.prod S₁.toNonUnitalSubsemiring with
    carrier := S ×ˢ S₁
    smul_mem' := fun r _x hx => ⟨SMulMemClass.smul_mem r hx.1, SMulMemClass.smul_mem r hx.2⟩ }

@[simp]
theorem coe_prod : (prod S S₁ : Set (A × B)) = (S : Set A) ×ˢ S₁ :=
  rfl

theorem prod_toSubmodule : (S.prod S₁).toSubmodule = S.toSubmodule.prod S₁.toSubmodule :=
  rfl

@[simp]
theorem mem_prod {S : NonUnitalSubalgebra R A} {S₁ : NonUnitalSubalgebra R B} {x : A × B} :
    x ∈ prod S S₁ ↔ x.1 ∈ S ∧ x.2 ∈ S₁ :=
  Set.mem_prod

@[simp]
theorem prod_top : (prod ⊤ ⊤ : NonUnitalSubalgebra R (A × B)) = ⊤ := by ext; simp
                                                                        -- ⊢ x✝ ∈ prod ⊤ ⊤ ↔ x✝ ∈ ⊤
                                                                             -- 🎉 no goals

theorem prod_mono {S T : NonUnitalSubalgebra R A} {S₁ T₁ : NonUnitalSubalgebra R B} :
    S ≤ T → S₁ ≤ T₁ → prod S S₁ ≤ prod T T₁ :=
  Set.prod_mono

@[simp]
theorem prod_inf_prod {S T : NonUnitalSubalgebra R A} {S₁ T₁ : NonUnitalSubalgebra R B} :
    S.prod S₁ ⊓ T.prod T₁ = (S ⊓ T).prod (S₁ ⊓ T₁) :=
  SetLike.coe_injective Set.prod_inter_prod

end Prod

section SuprLift

variable {ι : Type*}

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

/-- Define an algebra homomorphism on a directed supremum of non-unital subalgebras by defining
it on each non-unital subalgebra, and proving that it agrees on the intersection of
non-unital subalgebras. -/
noncomputable def iSupLift [Nonempty ι] (K : ι → NonUnitalSubalgebra R A) (dir : Directed (· ≤ ·) K)
    (f : ∀ i, K i →ₙₐ[R] B) (hf : ∀ (i j : ι) (h : K i ≤ K j), f i = (f j).comp (inclusion h))
    (T : NonUnitalSubalgebra R A) (hT : T = iSup K) : ↥T →ₙₐ[R] B := by
  subst hT
  -- ⊢ { x // x ∈ iSup K } →ₙₐ[R] B
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
          exact Set.iUnionLift_const _ (fun i : ι => (0 : K i)) (fun _ => rfl) _ (by simp)
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

variable [Nonempty ι] {K : ι → NonUnitalSubalgebra R A} {dir : Directed (· ≤ ·) K}
  {f : ∀ i, K i →ₙₐ[R] B} {hf : ∀ (i j : ι) (h : K i ≤ K j), f i = (f j).comp (inclusion h)}
  {T : NonUnitalSubalgebra R A} {hT : T = iSup K}

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
                                                              -- ⊢ ↑(NonUnitalAlgHom.comp (iSupLift K dir f hf T hT) (inclusion h)) x✝ = ↑(f i) …
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

end SuprLift

end NonAssoc

section Center

theorem _root_.Set.smul_mem_center {R A : Type*} [CommSemiring R] [NonUnitalNonAssocSemiring A]
  [Module R A] [IsScalarTower R A A] [SMulCommClass R A A](r : R) {a : A} (ha : a ∈ Set.center A) :
    r • a ∈ Set.center A := by
  simp [Set.mem_center_iff, mul_smul_comm, smul_mul_assoc, (Set.mem_center_iff A).mp ha]
  -- 🎉 no goals

variable (R A : Type*) [CommSemiring R] [NonUnitalSemiring A] [Module R A] [IsScalarTower R A A]
  [SMulCommClass R A A]

/-- The center of a non-unital algebra is the set of elements which commute with every element.
They form a non-unital subalgebra. -/
def center : NonUnitalSubalgebra R A :=
  { NonUnitalSubsemiring.center A with smul_mem' := Set.smul_mem_center }

theorem coe_center : (center R A : Set A) = Set.center A :=
  rfl

@[simp]
theorem center_toNonUnitalSubsemiring :
    (center R A).toNonUnitalSubsemiring = NonUnitalSubsemiring.center A :=
  rfl

@[simp] lemma center_toNonUnitalSubring (R A : Type*) [CommRing R] [NonUnitalRing A]
    [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] :
    (center R A).toNonUnitalSubring = NonUnitalSubring.center A :=
  rfl

@[simp]
theorem center_eq_top (A : Type*) [NonUnitalCommSemiring A] [Module R A] [IsScalarTower R A A]
    [SMulCommClass R A A] : center R A = ⊤ :=
  SetLike.coe_injective (Set.center_eq_univ A)

variable {R A}

instance center.instNonUnitalCommSemiring : NonUnitalCommSemiring (center R A) :=
  NonUnitalSubsemiring.center.instNonUnitalCommSemiring

instance center.instNonUnitalCommRing {A : Type*} [NonUnitalRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] : NonUnitalCommRing (center R A) :=
  NonUnitalSubring.center.instNonUnitalCommRing

theorem mem_center_iff {a : A} : a ∈ center R A ↔ ∀ b : A, b * a = a * b :=
  Iff.rfl

end Center

section Centralizer

variable {R A : Type*} [CommSemiring R] [NonUnitalSemiring A] [Module R A] [IsScalarTower R A A]
  [SMulCommClass R A A]

@[simp]
theorem _root_.Set.smul_mem_centralizer {s : Set A} (r : R) {a : A} (ha : a ∈ s.centralizer) :
    r • a ∈ s.centralizer :=
  fun x hx => by rw [mul_smul_comm, smul_mul_assoc, ha x hx]
                 -- 🎉 no goals

variable (R)

/-- The centralizer of a set as a non-unital subalgebra. -/
def centralizer (s : Set A) : NonUnitalSubalgebra R A where
  toNonUnitalSubsemiring := NonUnitalSubsemiring.centralizer s
  smul_mem' := Set.smul_mem_centralizer

@[simp, norm_cast]
theorem coe_centralizer (s : Set A) : (centralizer R s : Set A) = s.centralizer :=
  rfl

theorem mem_centralizer_iff {s : Set A} {z : A} : z ∈ centralizer R s ↔ ∀ g ∈ s, g * z = z * g :=
  Iff.rfl

theorem centralizer_le (s t : Set A) (h : s ⊆ t) : centralizer R t ≤ centralizer R s :=
  Set.centralizer_subset h

@[simp]
theorem centralizer_univ : centralizer R Set.univ = center R A :=
  SetLike.ext' (Set.centralizer_univ A)

end Centralizer

end NonUnitalSubalgebra

section Nat

variable {R : Type*} [NonUnitalSemiring R]

/-- A non-unital subsemiring is a non-unital `ℕ`-subalgebra. -/
def nonUnitalSubalgebraOfNonUnitalSubsemiring (S : NonUnitalSubsemiring R) :
    NonUnitalSubalgebra ℕ R where
  toNonUnitalSubsemiring := S
  smul_mem' n _x hx := nsmul_mem (S := S) hx n

@[simp]
theorem mem_nonUnitalSubalgebraOfNonUnitalSubsemiring {x : R} {S : NonUnitalSubsemiring R} :
    x ∈ nonUnitalSubalgebraOfNonUnitalSubsemiring S ↔ x ∈ S :=
  Iff.rfl

end Nat

section Int

variable {R : Type*} [NonUnitalRing R]

/-- A non-unital subring is a non-unitalsubalgebra. -/
def nonUnitalSubalgebraOfNonUnitalSubring (S : NonUnitalSubring R) : NonUnitalSubalgebra ℤ R where
  toNonUnitalSubsemiring := S.toNonUnitalSubsemiring
  smul_mem' n _x hx := zsmul_mem (K := S) hx n

@[simp]
theorem mem_nonUnitalSubalgebraOfNonUnitalSubring {x : R} {S : NonUnitalSubring R} :
    x ∈ nonUnitalSubalgebraOfNonUnitalSubring S ↔ x ∈ S :=
  Iff.rfl

end Int
