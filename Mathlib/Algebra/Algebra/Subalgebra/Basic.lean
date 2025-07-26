/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Algebra.NonUnitalSubalgebra
import Mathlib.RingTheory.SimpleRing.Basic

/-!
# Subalgebras over Commutative Semiring

In this file we define `Subalgebra`s and the usual operations on them (`map`, `comap`).

The `Algebra.adjoin` operation and complete lattice structure can be found in
`Mathlib/Algebra/Algebra/Subalgebra/Lattice.lean`.
-/

universe u u' v w w'

/-- A subalgebra is a sub(semi)ring that includes the range of `algebraMap`. -/
structure Subalgebra (R : Type u) (A : Type v) [CommSemiring R] [Semiring A] [Algebra R A] : Type v
    extends Subsemiring A where
  /-- The image of `algebraMap` is contained in the underlying set of the subalgebra -/
  algebraMap_mem' : ∀ r, algebraMap R A r ∈ carrier
  zero_mem' := (algebraMap R A).map_zero ▸ algebraMap_mem' 0
  one_mem' := (algebraMap R A).map_one ▸ algebraMap_mem' 1

/-- Reinterpret a `Subalgebra` as a `Subsemiring`. -/
add_decl_doc Subalgebra.toSubsemiring

namespace Subalgebra

variable {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}
variable [CommSemiring R]
variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]

instance : SetLike (Subalgebra R A) A where
  coe s := s.carrier
  coe_injective' p q h := by cases p; cases q; congr; exact SetLike.coe_injective' h

initialize_simps_projections Subalgebra (carrier → coe, as_prefix coe)

/-- The actual `Subalgebra` obtained from an element of a type satisfying `SubsemiringClass` and
`SMulMemClass`. -/
@[simps]
def ofClass {S R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    [SetLike S A] [SubsemiringClass S A] [SMulMemClass S R A] (s : S) :
    Subalgebra R A where
  carrier := s
  add_mem' := add_mem
  zero_mem' := zero_mem _
  mul_mem' := mul_mem
  one_mem' := one_mem _
  algebraMap_mem' r :=
    Algebra.algebraMap_eq_smul_one (A := A) r ▸ SMulMemClass.smul_mem r (one_mem s)

instance (priority := 100) : CanLift (Set A) (Subalgebra R A) (↑)
    (fun s ↦ (∀ {x y}, x ∈ s → y ∈ s → x + y ∈ s) ∧
      (∀ {x y}, x ∈ s → y ∈ s → x * y ∈ s) ∧ ∀ (r : R), algebraMap R A r ∈ s) where
  prf s h :=
    ⟨ { carrier := s
        zero_mem' := by simpa using h.2.2 0
        add_mem' := h.1
        one_mem' := by simpa using h.2.2 1
        mul_mem' := h.2.1
        algebraMap_mem' := h.2.2 },
      rfl ⟩

instance : SubsemiringClass (Subalgebra R A) A where
  add_mem {s} := add_mem (s := s.toSubsemiring)
  mul_mem {s} := mul_mem (s := s.toSubsemiring)
  one_mem {s} := one_mem s.toSubsemiring
  zero_mem {s} := zero_mem s.toSubsemiring

@[simp]
theorem mem_toSubsemiring {S : Subalgebra R A} {x} : x ∈ S.toSubsemiring ↔ x ∈ S :=
  Iff.rfl

theorem mem_carrier {s : Subalgebra R A} {x : A} : x ∈ s.carrier ↔ x ∈ s :=
  Iff.rfl

@[ext]
theorem ext {S T : Subalgebra R A} (h : ∀ x : A, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h

@[simp]
theorem coe_toSubsemiring (S : Subalgebra R A) : (↑S.toSubsemiring : Set A) = S :=
  rfl

theorem toSubsemiring_injective :
    Function.Injective (toSubsemiring : Subalgebra R A → Subsemiring A) := fun S T h =>
  ext fun x => by rw [← mem_toSubsemiring, ← mem_toSubsemiring, h]

theorem toSubsemiring_inj {S U : Subalgebra R A} : S.toSubsemiring = U.toSubsemiring ↔ S = U :=
  toSubsemiring_injective.eq_iff

/-- Copy of a subalgebra with a new `carrier` equal to the old one. Useful to fix definitional
equalities. -/
@[simps coe toSubsemiring]
protected def copy (S : Subalgebra R A) (s : Set A) (hs : s = ↑S) : Subalgebra R A :=
  { S.toSubsemiring.copy s hs with
    carrier := s
    algebraMap_mem' := hs.symm ▸ S.algebraMap_mem' }

theorem copy_eq (S : Subalgebra R A) (s : Set A) (hs : s = ↑S) : S.copy s hs = S :=
  SetLike.coe_injective hs

variable (S : Subalgebra R A)

instance instSMulMemClass : SMulMemClass (Subalgebra R A) R A where
  smul_mem {S} r x hx := (Algebra.smul_def r x).symm ▸ mul_mem (S.algebraMap_mem' r) hx

@[simp, aesop safe (rule_sets := [SetLike])]
theorem _root_.algebraMap_mem {S R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    [SetLike S A] [OneMemClass S A] [SMulMemClass S R A] (s : S) (r : R) :
    algebraMap R A r ∈ s :=
  Algebra.algebraMap_eq_smul_one (A := A) r ▸ SMulMemClass.smul_mem r (one_mem s)

protected theorem algebraMap_mem (r : R) : algebraMap R A r ∈ S :=
  algebraMap_mem S r

theorem rangeS_le : (algebraMap R A).rangeS ≤ S.toSubsemiring := fun _x ⟨r, hr⟩ =>
  hr ▸ S.algebraMap_mem r

theorem range_subset : Set.range (algebraMap R A) ⊆ S := fun _x ⟨r, hr⟩ => hr ▸ S.algebraMap_mem r

theorem range_le : Set.range (algebraMap R A) ≤ S :=
  S.range_subset

theorem smul_mem {x : A} (hx : x ∈ S) (r : R) : r • x ∈ S :=
  SMulMemClass.smul_mem r hx

protected theorem one_mem : (1 : A) ∈ S :=
  one_mem S

protected theorem mul_mem {x y : A} (hx : x ∈ S) (hy : y ∈ S) : x * y ∈ S :=
  mul_mem hx hy

protected theorem pow_mem {x : A} (hx : x ∈ S) (n : ℕ) : x ^ n ∈ S :=
  pow_mem hx n

protected theorem zero_mem : (0 : A) ∈ S :=
  zero_mem S

protected theorem add_mem {x y : A} (hx : x ∈ S) (hy : y ∈ S) : x + y ∈ S :=
  add_mem hx hy

protected theorem nsmul_mem {x : A} (hx : x ∈ S) (n : ℕ) : n • x ∈ S :=
  nsmul_mem hx n

protected theorem natCast_mem (n : ℕ) : (n : A) ∈ S :=
  natCast_mem S n

protected theorem list_prod_mem {L : List A} (h : ∀ x ∈ L, x ∈ S) : L.prod ∈ S :=
  list_prod_mem h

protected theorem list_sum_mem {L : List A} (h : ∀ x ∈ L, x ∈ S) : L.sum ∈ S :=
  list_sum_mem h

protected theorem multiset_sum_mem {m : Multiset A} (h : ∀ x ∈ m, x ∈ S) : m.sum ∈ S :=
  multiset_sum_mem m h

protected theorem sum_mem {ι : Type w} {t : Finset ι} {f : ι → A} (h : ∀ x ∈ t, f x ∈ S) :
    (∑ x ∈ t, f x) ∈ S :=
  sum_mem h

protected theorem multiset_prod_mem {R : Type u} {A : Type v} [CommSemiring R] [CommSemiring A]
    [Algebra R A] (S : Subalgebra R A) {m : Multiset A} (h : ∀ x ∈ m, x ∈ S) : m.prod ∈ S :=
  multiset_prod_mem m h

protected theorem prod_mem {R : Type u} {A : Type v} [CommSemiring R] [CommSemiring A] [Algebra R A]
    (S : Subalgebra R A) {ι : Type w} {t : Finset ι} {f : ι → A} (h : ∀ x ∈ t, f x ∈ S) :
    (∏ x ∈ t, f x) ∈ S :=
  prod_mem h

/-- Turn a `Subalgebra` into a `NonUnitalSubalgebra` by forgetting that it contains `1`. -/
def toNonUnitalSubalgebra (S : Subalgebra R A) : NonUnitalSubalgebra R A where
  __ := S
  smul_mem' r _x hx := S.smul_mem hx r

lemma one_mem_toNonUnitalSubalgebra (S : Subalgebra R A) : (1 : A) ∈ S.toNonUnitalSubalgebra :=
  S.one_mem

instance {R A : Type*} [CommRing R] [Ring A] [Algebra R A] : SubringClass (Subalgebra R A) A :=
  { Subalgebra.instSubsemiringClass with
    neg_mem := fun {S x} hx => neg_one_smul R x ▸ S.smul_mem hx _ }

protected theorem neg_mem {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (S : Subalgebra R A) {x : A} (hx : x ∈ S) : -x ∈ S :=
  neg_mem hx

protected theorem sub_mem {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (S : Subalgebra R A) {x y : A} (hx : x ∈ S) (hy : y ∈ S) : x - y ∈ S :=
  sub_mem hx hy

protected theorem zsmul_mem {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (S : Subalgebra R A) {x : A} (hx : x ∈ S) (n : ℤ) : n • x ∈ S :=
  zsmul_mem hx n

protected theorem intCast_mem {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (S : Subalgebra R A) (n : ℤ) : (n : A) ∈ S :=
  intCast_mem S n

/-- The projection from a subalgebra of `A` to an additive submonoid of `A`. -/
@[simps coe]
def toAddSubmonoid {R : Type u} {A : Type v} [CommSemiring R] [Semiring A] [Algebra R A]
    (S : Subalgebra R A) : AddSubmonoid A :=
  S.toSubsemiring.toAddSubmonoid

/-- A subalgebra over a ring is also a `Subring`. -/
@[simps toSubsemiring]
def toSubring {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A] (S : Subalgebra R A) :
    Subring A :=
  { S.toSubsemiring with neg_mem' := S.neg_mem }

@[simp]
theorem mem_toSubring {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    {S : Subalgebra R A} {x} : x ∈ S.toSubring ↔ x ∈ S :=
  Iff.rfl

@[simp]
theorem coe_toSubring {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (S : Subalgebra R A) : (↑S.toSubring : Set A) = S :=
  rfl

theorem toSubring_injective {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A] :
    Function.Injective (toSubring : Subalgebra R A → Subring A) := fun S T h =>
  ext fun x => by rw [← mem_toSubring, ← mem_toSubring, h]

theorem toSubring_inj {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    {S U : Subalgebra R A} : S.toSubring = U.toSubring ↔ S = U :=
  toSubring_injective.eq_iff

instance : Inhabited S :=
  ⟨(0 : S.toSubsemiring)⟩

section

/-! `Subalgebra`s inherit structure from their `Subsemiring` / `Semiring` coercions. -/


instance toSemiring {R A} [CommSemiring R] [Semiring A] [Algebra R A] (S : Subalgebra R A) :
    Semiring S :=
  S.toSubsemiring.toSemiring

instance toCommSemiring {R A} [CommSemiring R] [CommSemiring A] [Algebra R A] (S : Subalgebra R A) :
    CommSemiring S :=
  S.toSubsemiring.toCommSemiring

instance toRing {R A} [CommRing R] [Ring A] [Algebra R A] (S : Subalgebra R A) : Ring S :=
  S.toSubring.toRing

instance toCommRing {R A} [CommRing R] [CommRing A] [Algebra R A] (S : Subalgebra R A) :
    CommRing S :=
  S.toSubring.toCommRing

end

/-- The forgetful map from `Subalgebra` to `Submodule` as an `OrderEmbedding` -/
def toSubmodule : Subalgebra R A ↪o Submodule R A where
  toEmbedding :=
    { toFun := fun S =>
        { S with
          carrier := S
          smul_mem' := fun c {x} hx ↦
            (Algebra.smul_def c x).symm ▸ mul_mem (S.range_le ⟨c, rfl⟩) hx }
      inj' := fun _ _ h ↦ ext fun x ↦ SetLike.ext_iff.mp h x }
  map_rel_iff' := SetLike.coe_subset_coe.symm.trans SetLike.coe_subset_coe

/- TODO: bundle other forgetful maps between algebraic substructures, e.g.
  `toSubsemiring` and `toSubring` in this file. -/
@[simp]
theorem mem_toSubmodule {x} : x ∈ (toSubmodule S) ↔ x ∈ S := Iff.rfl

@[simp]
theorem coe_toSubmodule (S : Subalgebra R A) : (toSubmodule S : Set A) = S := rfl

theorem toSubmodule_injective : Function.Injective (toSubmodule : Subalgebra R A → Submodule R A) :=
  fun _S₁ _S₂ h => SetLike.ext (SetLike.ext_iff.mp h :)

section

/-! `Subalgebra`s inherit structure from their `Submodule` coercions. -/


instance (priority := low) module' [Semiring R'] [SMul R' R] [Module R' A] [IsScalarTower R' R A] :
    Module R' S :=
  S.toSubmodule.module'

instance : Module R S :=
  S.module'

instance [Semiring R'] [SMul R' R] [Module R' A] [IsScalarTower R' R A] : IsScalarTower R' R S :=
  inferInstanceAs (IsScalarTower R' R (toSubmodule S))

/- More general form of `Subalgebra.algebra`.

This instance should have low priority since it is slow to fail:
before failing, it will cause a search through all `SMul R' R` instances,
which can quickly get expensive.
-/
instance (priority := 500) algebra' [CommSemiring R'] [SMul R' R] [Algebra R' A]
    [IsScalarTower R' R A] :
    Algebra R' S where
  algebraMap := (algebraMap R' A).codRestrict S fun x => by
    rw [Algebra.algebraMap_eq_smul_one, ← smul_one_smul R x (1 : A), ←
      Algebra.algebraMap_eq_smul_one]
    exact algebraMap_mem S _
  commutes' := fun _ _ => Subtype.eq <| Algebra.commutes _ _
  smul_def' := fun _ _ => Subtype.eq <| Algebra.smul_def _ _

instance algebra : Algebra R S := S.algebra'

end

instance noZeroSMulDivisors_bot [NoZeroSMulDivisors R A] : NoZeroSMulDivisors R S :=
  ⟨fun {c} {x : S} h =>
    have : c = 0 ∨ (x : A) = 0 := eq_zero_or_eq_zero_of_smul_eq_zero (congr_arg Subtype.val h)
    this.imp_right (@Subtype.ext_iff _ _ x 0).mpr⟩

protected theorem coe_add (x y : S) : (↑(x + y) : A) = ↑x + ↑y := rfl

protected theorem coe_mul (x y : S) : (↑(x * y) : A) = ↑x * ↑y := rfl

protected theorem coe_zero : ((0 : S) : A) = 0 := rfl

protected theorem coe_one : ((1 : S) : A) = 1 := rfl

protected theorem coe_neg {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    {S : Subalgebra R A} (x : S) : (↑(-x) : A) = -↑x := rfl

protected theorem coe_sub {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    {S : Subalgebra R A} (x y : S) : (↑(x - y) : A) = ↑x - ↑y := rfl

@[simp, norm_cast]
theorem coe_smul [SMul R' R] [SMul R' A] [IsScalarTower R' R A] (r : R') (x : S) :
    (↑(r • x) : A) = r • (x : A) := rfl

@[simp, norm_cast]
theorem coe_algebraMap [CommSemiring R'] [SMul R' R] [Algebra R' A] [IsScalarTower R' R A]
    (r : R') : ↑(algebraMap R' S r) = algebraMap R' A r := rfl

protected theorem coe_pow (x : S) (n : ℕ) : (↑(x ^ n) : A) = (x : A) ^ n :=
  SubmonoidClass.coe_pow x n

protected theorem coe_eq_zero {x : S} : (x : A) = 0 ↔ x = 0 :=
  ZeroMemClass.coe_eq_zero

protected theorem coe_eq_one {x : S} : (x : A) = 1 ↔ x = 1 :=
  OneMemClass.coe_eq_one

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

@[simp]
theorem coe_val : (S.val : S → A) = ((↑) : S → A) := rfl

theorem val_apply (x : S) : S.val x = (x : A) := rfl

@[simp]
theorem toSubsemiring_subtype : S.toSubsemiring.subtype = (S.val : S →+* A) := rfl

@[simp]
theorem toSubring_subtype {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (S : Subalgebra R A) :
    S.toSubring.subtype = (S.val : S →+* A) := rfl

/-- Linear equivalence between `S : Submodule R A` and `S`. Though these types are equal,
we define it as a `LinearEquiv` to avoid type equalities. -/
def toSubmoduleEquiv (S : Subalgebra R A) : toSubmodule S ≃ₗ[R] S :=
  LinearEquiv.ofEq _ _ rfl

/-- Transport a subalgebra via an algebra homomorphism. -/
@[simps! coe toSubsemiring]
def map (f : A →ₐ[R] B) (S : Subalgebra R A) : Subalgebra R B :=
  { S.toSubsemiring.map (f : A →+* B) with
    algebraMap_mem' := fun r => f.commutes r ▸ Set.mem_image_of_mem _ (S.algebraMap_mem r) }

theorem map_mono {S₁ S₂ : Subalgebra R A} {f : A →ₐ[R] B} : S₁ ≤ S₂ → S₁.map f ≤ S₂.map f :=
  Set.image_subset f

theorem map_injective {f : A →ₐ[R] B} (hf : Function.Injective f) : Function.Injective (map f) :=
  fun _S₁ _S₂ ih =>
  ext <| Set.ext_iff.1 <| Set.image_injective.2 hf <| Set.ext <| SetLike.ext_iff.mp ih

@[simp]
theorem map_id (S : Subalgebra R A) : S.map (AlgHom.id R A) = S :=
  SetLike.coe_injective <| Set.image_id _

theorem map_map (S : Subalgebra R A) (g : B →ₐ[R] C) (f : A →ₐ[R] B) :
    (S.map f).map g = S.map (g.comp f) :=
  SetLike.coe_injective <| Set.image_image _ _ _

@[simp]
theorem mem_map {S : Subalgebra R A} {f : A →ₐ[R] B} {y : B} : y ∈ map f S ↔ ∃ x ∈ S, f x = y :=
  Subsemiring.mem_map

theorem map_toSubmodule {S : Subalgebra R A} {f : A →ₐ[R] B} :
    (toSubmodule <| S.map f) = S.toSubmodule.map f.toLinearMap :=
  SetLike.coe_injective rfl

/-- Preimage of a subalgebra under an algebra homomorphism. -/
@[simps! coe toSubsemiring]
def comap (f : A →ₐ[R] B) (S : Subalgebra R B) : Subalgebra R A :=
  { S.toSubsemiring.comap (f : A →+* B) with
    algebraMap_mem' := fun r =>
      show f (algebraMap R A r) ∈ S from (f.commutes r).symm ▸ S.algebraMap_mem r }

attribute [norm_cast] coe_comap

theorem map_le {S : Subalgebra R A} {f : A →ₐ[R] B} {U : Subalgebra R B} :
    map f S ≤ U ↔ S ≤ comap f U :=
  Set.image_subset_iff

theorem gc_map_comap (f : A →ₐ[R] B) : GaloisConnection (map f) (comap f) := fun _S _U => map_le

@[simp]
theorem mem_comap (S : Subalgebra R B) (f : A →ₐ[R] B) (x : A) : x ∈ S.comap f ↔ f x ∈ S :=
  Iff.rfl

instance noZeroDivisors {R A : Type*} [CommSemiring R] [Semiring A] [NoZeroDivisors A]
    [Algebra R A] (S : Subalgebra R A) : NoZeroDivisors S :=
  inferInstanceAs (NoZeroDivisors S.toSubsemiring)

instance isDomain {R A : Type*} [CommRing R] [Ring A] [IsDomain A] [Algebra R A]
    (S : Subalgebra R A) : IsDomain S :=
  inferInstanceAs (IsDomain S.toSubring)

end Subalgebra

namespace SubalgebraClass

variable {S R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
variable [SetLike S A] [SubsemiringClass S A] [hSR : SMulMemClass S R A] (s : S)

instance (priority := 75) toAlgebra : Algebra R s where
  algebraMap := {
    toFun r := ⟨algebraMap R A r, algebraMap_mem s r⟩
    map_one' := Subtype.ext <| by simp
    map_mul' _ _ := Subtype.ext <| by simp
    map_zero' := Subtype.ext <| by simp
    map_add' _ _ := Subtype.ext <| by simp}
  commutes' r x := Subtype.ext <| Algebra.commutes r (x : A)
  smul_def' r x := Subtype.ext <| (algebraMap_smul A r (x : A)).symm

@[simp, norm_cast]
lemma coe_algebraMap (r : R) : (algebraMap R s r : A) = algebraMap R A r := rfl

/-- Embedding of a subalgebra into the algebra, as an algebra homomorphism. -/
def val (s : S) : s →ₐ[R] A :=
  { SubsemiringClass.subtype s, SMulMemClass.subtype s with
    toFun := (↑)
    commutes' := fun _ ↦ rfl }

@[simp]
theorem coe_val : (val s : s → A) = ((↑) : s → A) :=
  rfl

end SubalgebraClass

namespace Submodule

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
variable (p : Submodule R A)

/-- A submodule containing `1` and closed under multiplication is a subalgebra. -/
@[simps coe toSubsemiring]
def toSubalgebra (p : Submodule R A) (h_one : (1 : A) ∈ p)
    (h_mul : ∀ x y, x ∈ p → y ∈ p → x * y ∈ p) : Subalgebra R A :=
  { p with
    mul_mem' := fun hx hy ↦ h_mul _ _ hx hy
    one_mem' := h_one
    algebraMap_mem' := fun r => by
      rw [Algebra.algebraMap_eq_smul_one]
      exact p.smul_mem _ h_one }

@[simp]
theorem mem_toSubalgebra {p : Submodule R A} {h_one h_mul} {x} :
    x ∈ p.toSubalgebra h_one h_mul ↔ x ∈ p := Iff.rfl

theorem toSubalgebra_mk (s : Submodule R A) (h1 hmul) :
    s.toSubalgebra h1 hmul =
      Subalgebra.mk ⟨⟨⟨s, @hmul⟩, h1⟩, s.add_mem, s.zero_mem⟩
        (by intro r; rw [Algebra.algebraMap_eq_smul_one]; apply s.smul_mem _ h1) :=
  rfl

@[simp]
theorem toSubalgebra_toSubmodule (p : Submodule R A) (h_one h_mul) :
    Subalgebra.toSubmodule (p.toSubalgebra h_one h_mul) = p :=
  SetLike.coe_injective rfl

@[simp]
theorem _root_.Subalgebra.toSubmodule_toSubalgebra (S : Subalgebra R A) :
    (S.toSubmodule.toSubalgebra S.one_mem fun _ _ => S.mul_mem) = S :=
  SetLike.coe_injective rfl

end Submodule

namespace AlgHom

variable {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}
variable [CommSemiring R]
variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]
variable (φ : A →ₐ[R] B)

/-- Range of an `AlgHom` as a subalgebra. -/
@[simps! coe toSubsemiring]
protected def range (φ : A →ₐ[R] B) : Subalgebra R B :=
  { φ.toRingHom.rangeS with algebraMap_mem' := fun r => ⟨algebraMap R A r, φ.commutes r⟩ }

@[simp]
theorem mem_range (φ : A →ₐ[R] B) {y : B} : y ∈ φ.range ↔ ∃ x, φ x = y :=
  RingHom.mem_rangeS

theorem mem_range_self (φ : A →ₐ[R] B) (x : A) : φ x ∈ φ.range :=
  φ.mem_range.2 ⟨x, rfl⟩

theorem range_comp (f : A →ₐ[R] B) (g : B →ₐ[R] C) : (g.comp f).range = f.range.map g :=
  SetLike.coe_injective (Set.range_comp g f)

theorem range_comp_le_range (f : A →ₐ[R] B) (g : B →ₐ[R] C) : (g.comp f).range ≤ g.range :=
  SetLike.coe_mono (Set.range_comp_subset_range f g)

/-- Restrict the codomain of an algebra homomorphism. -/
def codRestrict (f : A →ₐ[R] B) (S : Subalgebra R B) (hf : ∀ x, f x ∈ S) : A →ₐ[R] S :=
  { RingHom.codRestrict (f : A →+* B) S hf with commutes' := fun r => Subtype.eq <| f.commutes r }

@[simp]
theorem val_comp_codRestrict (f : A →ₐ[R] B) (S : Subalgebra R B) (hf : ∀ x, f x ∈ S) :
    S.val.comp (f.codRestrict S hf) = f :=
  AlgHom.ext fun _ => rfl

@[simp]
theorem coe_codRestrict (f : A →ₐ[R] B) (S : Subalgebra R B) (hf : ∀ x, f x ∈ S) (x : A) :
    ↑(f.codRestrict S hf x) = f x :=
  rfl

theorem injective_codRestrict (f : A →ₐ[R] B) (S : Subalgebra R B) (hf : ∀ x, f x ∈ S) :
    Function.Injective (f.codRestrict S hf) ↔ Function.Injective f :=
  ⟨fun H _x _y hxy => H <| Subtype.eq hxy, fun H _x _y hxy => H (congr_arg Subtype.val hxy :)⟩

/-- Restrict the codomain of an `AlgHom` `f` to `f.range`.

This is the bundled version of `Set.rangeFactorization`. -/
abbrev rangeRestrict (f : A →ₐ[R] B) : A →ₐ[R] f.range :=
  f.codRestrict f.range f.mem_range_self

theorem rangeRestrict_surjective (f : A →ₐ[R] B) : Function.Surjective (f.rangeRestrict) :=
  fun ⟨_y, hy⟩ =>
    let ⟨x, hx⟩ := hy
    ⟨x, SetCoe.ext hx⟩

/-- The range of a morphism of algebras is a fintype, if the domain is a fintype.

Note that this instance can cause a diamond with `Subtype.fintype` if `B` is also a fintype. -/
instance fintypeRange [Fintype A] [DecidableEq B] (φ : A →ₐ[R] B) : Fintype φ.range :=
  Set.fintypeRange φ

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

@[simp]
theorem ofLeftInverse_apply {g : B → A} {f : A →ₐ[R] B} (h : Function.LeftInverse g f) (x : A) :
    ↑(ofLeftInverse h x) = f x :=
  rfl

@[simp]
theorem ofLeftInverse_symm_apply {g : B → A} {f : A →ₐ[R] B} (h : Function.LeftInverse g f)
    (x : f.range) : (ofLeftInverse h).symm x = g x :=
  rfl

/-- Restrict an injective algebra homomorphism to an algebra isomorphism -/
noncomputable def ofInjective (f : A →ₐ[R] B) (hf : Function.Injective f) : A ≃ₐ[R] f.range :=
  ofLeftInverse (Classical.choose_spec hf.hasLeftInverse)

@[simp]
theorem ofInjective_apply (f : A →ₐ[R] B) (hf : Function.Injective f) (x : A) :
    ↑(ofInjective f hf x) = f x :=
  rfl

/-- Restrict an algebra homomorphism between fields to an algebra isomorphism -/
noncomputable def ofInjectiveField {E F : Type*} [DivisionRing E] [Semiring F] [Nontrivial F]
    [Algebra R E] [Algebra R F] (f : E →ₐ[R] F) : E ≃ₐ[R] f.range :=
  ofInjective f f.toRingHom.injective

/-- Given an equivalence `e : A ≃ₐ[R] B` of `R`-algebras and a subalgebra `S` of `A`,
`subalgebraMap` is the induced equivalence between `S` and `S.map e` -/
@[simps!]
def subalgebraMap (e : A ≃ₐ[R] B) (S : Subalgebra R A) : S ≃ₐ[R] S.map (e : A →ₐ[R] B) :=
  { e.toRingEquiv.subsemiringMap S.toSubsemiring with
    commutes' := fun r => by ext; exact e.commutes r }

end AlgEquiv

namespace Subalgebra

open Algebra

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]
variable (S T U : Subalgebra R A)

instance subsingleton_of_subsingleton [Subsingleton A] : Subsingleton (Subalgebra R A) :=
  ⟨fun B C => ext fun x => by simp only [Subsingleton.elim x 0, zero_mem B, zero_mem C]⟩

theorem range_val : S.val.range = S :=
  ext <| Set.ext_iff.1 <| S.val.coe_range.trans Subtype.range_val

/-- The map `S → T` when `S` is a subalgebra contained in the subalgebra `T`.

This is the subalgebra version of `Submodule.inclusion`, or `Subring.inclusion` -/
def inclusion {S T : Subalgebra R A} (h : S ≤ T) : S →ₐ[R] T where
  toFun := Set.inclusion h
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  commutes' _ := rfl

variable {S T U} (h : S ≤ T)

theorem inclusion_injective : Function.Injective (inclusion h) :=
  fun _ _ => Subtype.ext ∘ Subtype.mk.inj

@[simp]
theorem inclusion_self : inclusion (le_refl S) = AlgHom.id R S :=
  AlgHom.ext fun _x => Subtype.ext rfl

@[simp]
theorem inclusion_mk (x : A) (hx : x ∈ S) : inclusion h ⟨x, hx⟩ = ⟨x, h hx⟩ :=
  rfl

theorem inclusion_right (x : T) (m : (x : A) ∈ S) : inclusion h ⟨x, m⟩ = x :=
  Subtype.ext rfl

@[simp]
theorem inclusion_inclusion (hst : S ≤ T) (htu : T ≤ U) (x : S) :
    inclusion htu (inclusion hst x) = inclusion (le_trans hst htu) x :=
  Subtype.ext rfl

@[simp]
theorem coe_inclusion (s : S) : (inclusion h s : A) = s :=
  rfl

namespace inclusion

scoped instance isScalarTower_left (X) [SMul X R] [SMul X A] [IsScalarTower X R A] :
    letI := (inclusion h).toModule; IsScalarTower X S T :=
  letI := (inclusion h).toModule
  ⟨fun x s t ↦ Subtype.ext <| by
    rw [← one_smul R s, ← smul_assoc, one_smul, ← one_smul R (s • t), ← smul_assoc,
      Algebra.smul_def, Algebra.smul_def]
    apply mul_assoc⟩

scoped instance isScalarTower_right (X) [MulAction A X] :
    letI := (inclusion h).toModule; IsScalarTower S T X :=
  letI := (inclusion h).toModule; ⟨fun _ ↦ mul_smul _⟩

scoped instance faithfulSMul :
    letI := (inclusion h).toModule; FaithfulSMul S T :=
  letI := (inclusion h).toModule
  ⟨fun {x y} h ↦ Subtype.ext <| by
    convert Subtype.ext_iff.mp (h 1) using 1 <;> exact (mul_one _).symm⟩

end inclusion

variable (S)

/-- Two subalgebras that are equal are also equivalent as algebras.

This is the `Subalgebra` version of `LinearEquiv.ofEq` and `Equiv.setCongr`. -/
@[simps apply]
def equivOfEq (S T : Subalgebra R A) (h : S = T) : S ≃ₐ[R] T where
  __ := LinearEquiv.ofEq _ _ (congr_arg toSubmodule h)
  toFun x := ⟨x, h ▸ x.2⟩
  invFun x := ⟨x, h.symm ▸ x.2⟩
  map_mul' _ _ := rfl
  commutes' _ := rfl

@[simp]
theorem equivOfEq_symm (S T : Subalgebra R A) (h : S = T) :
    (equivOfEq S T h).symm = equivOfEq T S h.symm := rfl

@[simp]
theorem equivOfEq_rfl (S : Subalgebra R A) : equivOfEq S S rfl = AlgEquiv.refl := by ext; rfl

@[simp]
theorem equivOfEq_trans (S T U : Subalgebra R A) (hST : S = T) (hTU : T = U) :
    (equivOfEq S T hST).trans (equivOfEq T U hTU) = equivOfEq S U (hST.trans hTU) := rfl

section equivMapOfInjective

variable (f : A →ₐ[R] B)

theorem range_comp_val : (f.comp S.val).range = S.map f := by
  rw [AlgHom.range_comp, range_val]

/-- An `AlgHom` between two rings restricts to an `AlgHom` from any subalgebra of the
domain onto the image of that subalgebra. -/
def _root_.AlgHom.subalgebraMap : S →ₐ[R] S.map f :=
  (f.comp S.val).codRestrict _ fun x ↦ ⟨_, x.2, rfl⟩

variable {S} in
@[simp]
theorem _root_.AlgHom.subalgebraMap_coe_apply (x : S) : f.subalgebraMap S x = f x := rfl

theorem _root_.AlgHom.subalgebraMap_surjective : Function.Surjective (f.subalgebraMap S) :=
  f.toAddMonoidHom.addSubmonoidMap_surjective S.toAddSubmonoid

variable (hf : Function.Injective f)

/-- A subalgebra is isomorphic to its image under an injective `AlgHom` -/
noncomputable def equivMapOfInjective : S ≃ₐ[R] S.map f :=
  (AlgEquiv.ofInjective (f.comp S.val) (hf.comp Subtype.val_injective)).trans
    (equivOfEq _ _ (range_comp_val S f))

@[simp]
theorem coe_equivMapOfInjective_apply (x : S) : ↑(equivMapOfInjective S f hf x) = f x := rfl

end equivMapOfInjective

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

instance smulCommClass_left [SMul A β] [SMul α β] [SMulCommClass A α β] (S : Subalgebra R A) :
    SMulCommClass S α β :=
  S.toSubsemiring.smulCommClass_left

instance smulCommClass_right [SMul α β] [SMul A β] [SMulCommClass α A β] (S : Subalgebra R A) :
    SMulCommClass α S β :=
  S.toSubsemiring.smulCommClass_right

/-- Note that this provides `IsScalarTower S R R` which is needed by `smul_mul_assoc`. -/
instance isScalarTower_left [SMul α β] [SMul A α] [SMul A β] [IsScalarTower A α β]
    (S : Subalgebra R A) : IsScalarTower S α β :=
  inferInstanceAs (IsScalarTower S.toSubsemiring α β)

instance isScalarTower_mid {R S T : Type*} [CommSemiring R] [Semiring S] [AddCommMonoid T]
    [Algebra R S] [Module R T] [Module S T] [IsScalarTower R S T] (S' : Subalgebra R S) :
    IsScalarTower R S' T :=
  ⟨fun _x y _z => smul_assoc _ (y : S) _⟩

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

/-- The action by a subalgebra is the action by the underlying algebra. -/
instance toAlgebra {R A : Type*} [CommSemiring R] [CommSemiring A] [Semiring α] [Algebra R A]
    [Algebra A α] (S : Subalgebra R A) : Algebra S α :=
  Algebra.ofSubsemiring S.toSubsemiring

theorem algebraMap_eq {R A : Type*} [CommSemiring R] [CommSemiring A] [Semiring α] [Algebra R A]
    [Algebra A α] (S : Subalgebra R A) : algebraMap S α = (algebraMap A α).comp S.val :=
  rfl

@[simp]
theorem rangeS_algebraMap {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
    (S : Subalgebra R A) : (algebraMap S A).rangeS = S.toSubsemiring := by
  rw [algebraMap_eq, Algebra.algebraMap_self, RingHom.id_comp, ← toSubsemiring_subtype,
    Subsemiring.rangeS_subtype]

@[simp]
theorem range_algebraMap {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (S : Subalgebra R A) : (algebraMap S A).range = S.toSubring := by
  rw [algebraMap_eq, Algebra.algebraMap_self, RingHom.id_comp, ← toSubring_subtype,
    Subring.range_subtype]

instance noZeroSMulDivisors_top [NoZeroDivisors A] (S : Subalgebra R A) : NoZeroSMulDivisors S A :=
  ⟨fun {c} x h =>
    have : (c : A) = 0 ∨ x = 0 := eq_zero_or_eq_zero_of_mul_eq_zero h
    this.imp_left (@Subtype.ext_iff _ _ c 0).mpr⟩

end Actions

section Center

theorem _root_.Set.algebraMap_mem_center (r : R) : algebraMap R A r ∈ Set.center A := by
  simp only [Semigroup.mem_center_iff, commutes, forall_const]

variable (R A)

/-- The center of an algebra is the set of elements which commute with every element. They form a
subalgebra. -/
@[simps! coe toSubsemiring]
def center : Subalgebra R A :=
  { Subsemiring.center A with algebraMap_mem' := Set.algebraMap_mem_center }

@[simp]
theorem center_toSubring (R A : Type*) [CommRing R] [Ring A] [Algebra R A] :
    (center R A).toSubring = Subring.center A :=
  rfl

variable {R A}

instance : CommSemiring (center R A) :=
  inferInstanceAs (CommSemiring (Subsemiring.center A))

instance {A : Type*} [Ring A] [Algebra R A] : CommRing (center R A) :=
  inferInstanceAs (CommRing (Subring.center A))

theorem mem_center_iff {a : A} : a ∈ center R A ↔ ∀ b : A, b * a = a * b :=
  Subsemigroup.mem_center_iff

end Center

section Centralizer

@[simp]
theorem _root_.Set.algebraMap_mem_centralizer {s : Set A} (r : R) :
    algebraMap R A r ∈ s.centralizer :=
  fun _a _h => (Algebra.commutes _ _).symm

variable (R)

/-- The centralizer of a set as a subalgebra. -/
def centralizer (s : Set A) : Subalgebra R A :=
  { Subsemiring.centralizer s with algebraMap_mem' := Set.algebraMap_mem_centralizer }

@[simp, norm_cast]
theorem coe_centralizer (s : Set A) : (centralizer R s : Set A) = s.centralizer :=
  rfl

theorem mem_centralizer_iff {s : Set A} {z : A} : z ∈ centralizer R s ↔ ∀ g ∈ s, g * z = z * g :=
  Iff.rfl

theorem center_le_centralizer (s) : center R A ≤ centralizer R s :=
  s.center_subset_centralizer

theorem centralizer_le (s t : Set A) (h : s ⊆ t) : centralizer R t ≤ centralizer R s :=
  Set.centralizer_subset h

@[simp]
theorem centralizer_univ : centralizer R Set.univ = center R A :=
  SetLike.ext' (Set.centralizer_univ A)

lemma le_centralizer_centralizer {s : Subalgebra R A} :
    s ≤ centralizer R (centralizer R (s : Set A)) :=
  Set.subset_centralizer_centralizer

@[simp]
lemma centralizer_centralizer_centralizer {s : Set A} :
    centralizer R s.centralizer.centralizer = centralizer R s := by
  apply SetLike.coe_injective
  simp only [coe_centralizer, Set.centralizer_centralizer_centralizer]

end Centralizer

end Subalgebra

section Nat

variable {R : Type*} [Semiring R]

/-- A subsemiring is an `ℕ`-subalgebra. -/
@[simps toSubsemiring]
def subalgebraOfSubsemiring (S : Subsemiring R) : Subalgebra ℕ R :=
  { S with algebraMap_mem' := fun i => natCast_mem S i }

@[simp]
theorem mem_subalgebraOfSubsemiring {x : R} {S : Subsemiring R} :
    x ∈ subalgebraOfSubsemiring S ↔ x ∈ S :=
  Iff.rfl

end Nat

section Int

variable {R : Type*} [Ring R]

/-- A subring is a `ℤ`-subalgebra. -/
@[simps toSubsemiring]
def subalgebraOfSubring (S : Subring R) : Subalgebra ℤ R :=
  { S with
    algebraMap_mem' := fun i =>
      Int.induction_on i (by simp)
        (fun i ih => by simpa using S.add_mem ih S.one_mem) fun i ih =>
        show ((-i - 1 : ℤ) : R) ∈ S by
          rw [Int.cast_sub, Int.cast_one]
          exact S.sub_mem ih S.one_mem }

variable {S : Type*} [Semiring S]

@[simp]
theorem mem_subalgebraOfSubring {x : R} {S : Subring R} : x ∈ subalgebraOfSubring S ↔ x ∈ S :=
  Iff.rfl

end Int

section Equalizer

namespace AlgHom

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]
variable {F : Type*}

/-- The equalizer of two R-algebra homomorphisms -/
@[simps coe toSubsemiring]
def equalizer (ϕ ψ : F) [FunLike F A B] [AlgHomClass F R A B] : Subalgebra R A where
  carrier := { a | ϕ a = ψ a }
  zero_mem' := by simp only [Set.mem_setOf_eq, map_zero]
  one_mem' := by simp only [Set.mem_setOf_eq, map_one]
  add_mem' {x y} (hx : ϕ x = ψ x) (hy : ϕ y = ψ y) := by
    rw [Set.mem_setOf_eq, map_add, map_add, hx, hy]
  mul_mem' {x y} (hx : ϕ x = ψ x) (hy : ϕ y = ψ y) := by
    rw [Set.mem_setOf_eq, map_mul, map_mul, hx, hy]
  algebraMap_mem' x := by
    simp only [Set.mem_setOf_eq, AlgHomClass.commutes]

variable [FunLike F A B] [AlgHomClass F R A B]

@[simp]
theorem mem_equalizer (φ ψ : F) (x : A) : x ∈ equalizer φ ψ ↔ φ x = ψ x :=
  Iff.rfl

theorem equalizer_toSubmodule {φ ψ : F} :
    Subalgebra.toSubmodule (equalizer φ ψ) = LinearMap.eqLocus φ ψ := rfl

theorem le_equalizer {φ ψ : F} {S : Subalgebra R A} : S ≤ equalizer φ ψ ↔ Set.EqOn φ ψ S := Iff.rfl

end AlgHom

end Equalizer

section MapComap

namespace Subalgebra

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem comap_map_eq_self_of_injective
    {f : A →ₐ[R] B} (hf : Function.Injective f) (S : Subalgebra R A) : (S.map f).comap f = S :=
  SetLike.coe_injective (Set.preimage_image_eq _ hf)

end Subalgebra

end MapComap

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

/-- Turn a non-unital subalgebra containing `1` into a subalgebra. -/
def NonUnitalSubalgebra.toSubalgebra (S : NonUnitalSubalgebra R A) (h1 : (1 : A) ∈ S) :
    Subalgebra R A :=
  { S with
    one_mem' := h1
    algebraMap_mem' := fun r =>
      (Algebra.algebraMap_eq_smul_one (R := R) (A := A) r).symm ▸ SMulMemClass.smul_mem r h1 }

lemma Subalgebra.toNonUnitalSubalgebra_toSubalgebra (S : Subalgebra R A) :
    S.toNonUnitalSubalgebra.toSubalgebra S.one_mem = S := by cases S; rfl

lemma NonUnitalSubalgebra.toSubalgebra_toNonUnitalSubalgebra (S : NonUnitalSubalgebra R A)
    (h1 : (1 : A) ∈ S) : (NonUnitalSubalgebra.toSubalgebra S h1).toNonUnitalSubalgebra = S := by
  cases S; rfl
