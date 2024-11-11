/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
import Mathlib.Algebra.Algebra.Operations

/-!
# Subalgebras over Commutative Semiring

In this file we define `Subalgebra`s and the usual operations on them (`map`, `comap`).

More lemmas about `adjoin` can be found in `RingTheory.Adjoin`.
-/

universe u u' v w w'

/-- A subalgebra is a sub(semi)ring that includes the range of `algebraMap`. -/
structure Subalgebra (R : Type u) (A : Type v) [CommSemiring R] [Semiring A] [Algebra R A] extends
  Subsemiring A : Type v where
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

instance SubsemiringClass : SubsemiringClass (Subalgebra R A) A where
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
protected def copy (S : Subalgebra R A) (s : Set A) (hs : s = ↑S) : Subalgebra R A :=
  { S.toSubsemiring.copy s hs with
    carrier := s
    algebraMap_mem' := hs.symm ▸ S.algebraMap_mem' }

@[simp]
theorem coe_copy (S : Subalgebra R A) (s : Set A) (hs : s = ↑S) : (S.copy s hs : Set A) = s :=
  rfl

theorem copy_eq (S : Subalgebra R A) (s : Set A) (hs : s = ↑S) : S.copy s hs = S :=
  SetLike.coe_injective hs

variable (S : Subalgebra R A)

instance instSMulMemClass : SMulMemClass (Subalgebra R A) R A where
  smul_mem {S} r x hx := (Algebra.smul_def r x).symm ▸ mul_mem (S.algebraMap_mem' r) hx

@[aesop safe apply (rule_sets := [SetLike])]
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

instance {R A : Type*} [CommRing R] [Ring A] [Algebra R A] : SubringClass (Subalgebra R A) A :=
  { Subalgebra.SubsemiringClass with
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

@[deprecated natCast_mem (since := "2024-04-05")] alias coe_nat_mem := Subalgebra.natCast_mem
@[deprecated intCast_mem (since := "2024-04-05")] alias coe_int_mem := Subalgebra.intCast_mem

/-- The projection from a subalgebra of `A` to an additive submonoid of `A`. -/
def toAddSubmonoid {R : Type u} {A : Type v} [CommSemiring R] [Semiring A] [Algebra R A]
    (S : Subalgebra R A) : AddSubmonoid A :=
  S.toSubsemiring.toAddSubmonoid

-- Porting note: this field already exists in Lean 4.
-- /-- The projection from a subalgebra of `A` to a submonoid of `A`. -/
-- def toSubmonoid {R : Type u} {A : Type v} [CommSemiring R] [Semiring A] [Algebra R A]
--     (S : Subalgebra R A) : Submonoid A :=
--   S.toSubsemiring.toSubmonoid

/-- A subalgebra over a ring is also a `Subring`. -/
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
    Algebra R' S :=
  { (algebraMap R' A).codRestrict S fun x => by
      rw [Algebra.algebraMap_eq_smul_one, ← smul_one_smul R x (1 : A), ←
        Algebra.algebraMap_eq_smul_one]
      exact algebraMap_mem S
          _ with
    commutes' := fun _ _ => Subtype.eq <| Algebra.commutes _ _
    smul_def' := fun _ _ => Subtype.eq <| Algebra.smul_def _ _ }

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
theorem coe_smul [Semiring R'] [SMul R' R] [Module R' A] [IsScalarTower R' R A] (r : R') (x : S) :
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

theorem map_toSubsemiring {S : Subalgebra R A} {f : A →ₐ[R] B} :
    (S.map f).toSubsemiring = S.toSubsemiring.map f.toRingHom :=
  SetLike.coe_injective rfl

@[simp]
theorem coe_map (S : Subalgebra R A) (f : A →ₐ[R] B) : (S.map f : Set B) = f '' S := rfl

/-- Preimage of a subalgebra under an algebra homomorphism. -/
def comap (f : A →ₐ[R] B) (S : Subalgebra R B) : Subalgebra R A :=
  { S.toSubsemiring.comap (f : A →+* B) with
    algebraMap_mem' := fun r =>
      show f (algebraMap R A r) ∈ S from (f.commutes r).symm ▸ S.algebraMap_mem r }

theorem map_le {S : Subalgebra R A} {f : A →ₐ[R] B} {U : Subalgebra R B} :
    map f S ≤ U ↔ S ≤ comap f U :=
  Set.image_subset_iff

theorem gc_map_comap (f : A →ₐ[R] B) : GaloisConnection (map f) (comap f) := fun _S _U => map_le

@[simp]
theorem mem_comap (S : Subalgebra R B) (f : A →ₐ[R] B) (x : A) : x ∈ S.comap f ↔ f x ∈ S :=
  Iff.rfl

@[simp, norm_cast]
theorem coe_comap (S : Subalgebra R B) (f : A →ₐ[R] B) : (S.comap f : Set A) = f ⁻¹' (S : Set B) :=
  rfl

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
  toFun r := ⟨algebraMap R A r, algebraMap_mem s r⟩
  map_one' := Subtype.ext <| by simp
  map_mul' _ _ := Subtype.ext <| by simp
  map_zero' := Subtype.ext <| by simp
  map_add' _ _ := Subtype.ext <| by simp
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

@[simp]
theorem coe_toSubalgebra (p : Submodule R A) (h_one h_mul) :
    (p.toSubalgebra h_one h_mul : Set A) = p := rfl

-- Porting note: changed statement to reflect new structures
-- @[simp] -- Porting note: as a result, it is no longer a great simp lemma
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
protected def range (φ : A →ₐ[R] B) : Subalgebra R B :=
  { φ.toRingHom.rangeS with algebraMap_mem' := fun r => ⟨algebraMap R A r, φ.commutes r⟩ }

@[simp]
theorem mem_range (φ : A →ₐ[R] B) {y : B} : y ∈ φ.range ↔ ∃ x, φ x = y :=
  RingHom.mem_rangeS

theorem mem_range_self (φ : A →ₐ[R] B) (x : A) : φ x ∈ φ.range :=
  φ.mem_range.2 ⟨x, rfl⟩

@[simp]
theorem coe_range (φ : A →ₐ[R] B) : (φ.range : Set B) = Set.range φ := by
  ext
  rw [SetLike.mem_coe, mem_range]
  rfl

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
  ⟨fun H _x _y hxy => H <| Subtype.eq hxy, fun H _x _y hxy => H (congr_arg Subtype.val hxy : _)⟩

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
    commutes' := fun r => by
      ext; dsimp only; erw [RingEquiv.subsemiringMap_apply_coe]
      exact e.commutes _ }

end AlgEquiv

namespace Algebra

variable (R : Type u) {A : Type v} {B : Type w}
variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

/-- The minimal subalgebra that includes `s`. -/
@[simps toSubsemiring]
def adjoin (s : Set A) : Subalgebra R A :=
  { Subsemiring.closure (Set.range (algebraMap R A) ∪ s) with
    algebraMap_mem' := fun r => Subsemiring.subset_closure <| Or.inl ⟨r, rfl⟩ }

variable {R}

protected theorem gc : GaloisConnection (adjoin R : Set A → Subalgebra R A) (↑) := fun s S =>
  ⟨fun H => le_trans (le_trans Set.subset_union_right Subsemiring.subset_closure) H,
   fun H => show Subsemiring.closure (Set.range (algebraMap R A) ∪ s) ≤ S.toSubsemiring from
      Subsemiring.closure_le.2 <| Set.union_subset S.range_subset H⟩

/-- Galois insertion between `adjoin` and `coe`. -/
protected def gi : GaloisInsertion (adjoin R : Set A → Subalgebra R A) (↑) where
  choice s hs := (adjoin R s).copy s <| le_antisymm (Algebra.gc.le_u_l s) hs
  gc := Algebra.gc
  le_l_u S := (Algebra.gc (S : Set A) (adjoin R S)).1 <| le_rfl
  choice_eq _ _ := Subalgebra.copy_eq _ _ _

instance : CompleteLattice (Subalgebra R A) where
  __ := GaloisInsertion.liftCompleteLattice Algebra.gi
  bot := (Algebra.ofId R A).range
  bot_le _S := fun _a ⟨_r, hr⟩ => hr ▸ algebraMap_mem _ _

theorem sup_def (S T : Subalgebra R A) : S ⊔ T = adjoin R (S ∪ T : Set A) := rfl

theorem sSup_def (S : Set (Subalgebra R A)) : sSup S = adjoin R (⋃₀ (SetLike.coe '' S)) := rfl

@[simp]
theorem coe_top : (↑(⊤ : Subalgebra R A) : Set A) = Set.univ := rfl

@[simp]
theorem mem_top {x : A} : x ∈ (⊤ : Subalgebra R A) := Set.mem_univ x

@[simp]
theorem top_toSubmodule : Subalgebra.toSubmodule (⊤ : Subalgebra R A) = ⊤ := rfl

@[simp]
theorem top_toSubsemiring : (⊤ : Subalgebra R A).toSubsemiring = ⊤ := rfl

@[simp]
theorem top_toSubring {R A : Type*} [CommRing R] [Ring A] [Algebra R A] :
    (⊤ : Subalgebra R A).toSubring = ⊤ := rfl

@[simp]
theorem toSubmodule_eq_top {S : Subalgebra R A} : Subalgebra.toSubmodule S = ⊤ ↔ S = ⊤ :=
  Subalgebra.toSubmodule.injective.eq_iff' top_toSubmodule

@[simp]
theorem toSubsemiring_eq_top {S : Subalgebra R A} : S.toSubsemiring = ⊤ ↔ S = ⊤ :=
  Subalgebra.toSubsemiring_injective.eq_iff' top_toSubsemiring

@[simp]
theorem toSubring_eq_top {R A : Type*} [CommRing R] [Ring A] [Algebra R A] {S : Subalgebra R A} :
    S.toSubring = ⊤ ↔ S = ⊤ :=
  Subalgebra.toSubring_injective.eq_iff' top_toSubring

theorem mem_sup_left {S T : Subalgebra R A} : ∀ {x : A}, x ∈ S → x ∈ S ⊔ T :=
  have : S ≤ S ⊔ T := le_sup_left; (this ·) -- Porting note: need `have` instead of `show`

theorem mem_sup_right {S T : Subalgebra R A} : ∀ {x : A}, x ∈ T → x ∈ S ⊔ T :=
  have : T ≤ S ⊔ T := le_sup_right; (this ·) -- Porting note: need `have` instead of `show`

theorem mul_mem_sup {S T : Subalgebra R A} {x y : A} (hx : x ∈ S) (hy : y ∈ T) : x * y ∈ S ⊔ T :=
  (S ⊔ T).mul_mem (mem_sup_left hx) (mem_sup_right hy)

theorem map_sup (f : A →ₐ[R] B) (S T : Subalgebra R A) : (S ⊔ T).map f = S.map f ⊔ T.map f :=
  (Subalgebra.gc_map_comap f).l_sup

theorem map_inf (f : A →ₐ[R] B) (hf : Function.Injective f) (S T : Subalgebra R A) :
    (S ⊓ T).map f = S.map f ⊓ T.map f := SetLike.coe_injective (Set.image_inter hf)

@[simp, norm_cast]
theorem coe_inf (S T : Subalgebra R A) : (↑(S ⊓ T) : Set A) = (S ∩ T : Set A) := rfl

@[simp]
theorem mem_inf {S T : Subalgebra R A} {x : A} : x ∈ S ⊓ T ↔ x ∈ S ∧ x ∈ T := Iff.rfl

open Subalgebra in
@[simp]
theorem inf_toSubmodule (S T : Subalgebra R A) :
    toSubmodule (S ⊓ T) = toSubmodule S ⊓ toSubmodule T := rfl

@[simp]
theorem inf_toSubsemiring (S T : Subalgebra R A) :
    (S ⊓ T).toSubsemiring = S.toSubsemiring ⊓ T.toSubsemiring :=
  rfl

@[simp]
theorem sup_toSubsemiring (S T : Subalgebra R A) :
    (S ⊔ T).toSubsemiring = S.toSubsemiring ⊔ T.toSubsemiring := by
  rw [← S.toSubsemiring.closure_eq, ← T.toSubsemiring.closure_eq, ← Subsemiring.closure_union]
  simp_rw [sup_def, adjoin_toSubsemiring, Subalgebra.coe_toSubsemiring]
  congr 1
  rw [Set.union_eq_right]
  rintro _ ⟨x, rfl⟩
  exact Set.mem_union_left _ (algebraMap_mem S x)

@[simp, norm_cast]
theorem coe_sInf (S : Set (Subalgebra R A)) : (↑(sInf S) : Set A) = ⋂ s ∈ S, ↑s :=
  sInf_image

theorem mem_sInf {S : Set (Subalgebra R A)} {x : A} : x ∈ sInf S ↔ ∀ p ∈ S, x ∈ p := by
  simp only [← SetLike.mem_coe, coe_sInf, Set.mem_iInter₂]

@[simp]
theorem sInf_toSubmodule (S : Set (Subalgebra R A)) :
    Subalgebra.toSubmodule (sInf S) = sInf (Subalgebra.toSubmodule '' S) :=
  SetLike.coe_injective <| by simp

@[simp]
theorem sInf_toSubsemiring (S : Set (Subalgebra R A)) :
    (sInf S).toSubsemiring = sInf (Subalgebra.toSubsemiring '' S) :=
  SetLike.coe_injective <| by simp

open Subalgebra in
@[simp]
theorem sSup_toSubsemiring (S : Set (Subalgebra R A)) (hS : S.Nonempty) :
    (sSup S).toSubsemiring = sSup (toSubsemiring '' S) := by
  have h : toSubsemiring '' S = Subsemiring.closure '' (SetLike.coe '' S) := by
    rw [Set.image_image]
    congr! with x
    exact x.toSubsemiring.closure_eq.symm
  rw [h, sSup_image, ← Subsemiring.closure_sUnion, sSup_def, adjoin_toSubsemiring]
  congr 1
  rw [Set.union_eq_right]
  rintro _ ⟨x, rfl⟩
  obtain ⟨y, hy⟩ := hS
  simp only [Set.mem_sUnion, Set.mem_image, exists_exists_and_eq_and, SetLike.mem_coe]
  exact ⟨y, hy, algebraMap_mem y x⟩

@[simp, norm_cast]
theorem coe_iInf {ι : Sort*} {S : ι → Subalgebra R A} : (↑(⨅ i, S i) : Set A) = ⋂ i, S i := by
  simp [iInf]

theorem mem_iInf {ι : Sort*} {S : ι → Subalgebra R A} {x : A} : (x ∈ ⨅ i, S i) ↔ ∀ i, x ∈ S i := by
  simp only [iInf, mem_sInf, Set.forall_mem_range]

theorem map_iInf {ι : Sort*} [Nonempty ι] (f : A →ₐ[R] B) (hf : Function.Injective f)
    (s : ι → Subalgebra R A) : (iInf s).map f = ⨅ (i : ι), (s i).map f := by
  apply SetLike.coe_injective
  simpa using (Set.injOn_of_injective hf).image_iInter_eq (s := SetLike.coe ∘ s)

open Subalgebra in
@[simp]
theorem iInf_toSubmodule {ι : Sort*} (S : ι → Subalgebra R A) :
    toSubmodule (⨅ i, S i) = ⨅ i, toSubmodule (S i) :=
  SetLike.coe_injective <| by simp

@[simp]
theorem iInf_toSubsemiring {ι : Sort*} (S : ι → Subalgebra R A) :
    (iInf S).toSubsemiring = ⨅ i, (S i).toSubsemiring := by
  simp only [iInf, sInf_toSubsemiring, ← Set.range_comp, Function.comp_def]

@[simp]
theorem iSup_toSubsemiring {ι : Sort*} [Nonempty ι] (S : ι → Subalgebra R A) :
    (iSup S).toSubsemiring = ⨆ i, (S i).toSubsemiring := by
  simp only [iSup, Set.range_nonempty, sSup_toSubsemiring, ← Set.range_comp, Function.comp_def]

instance : Inhabited (Subalgebra R A) := ⟨⊥⟩

theorem mem_bot {x : A} : x ∈ (⊥ : Subalgebra R A) ↔ x ∈ Set.range (algebraMap R A) := Iff.rfl

/-- TODO: change proof to `rfl` when fixing #18110. -/
theorem toSubmodule_bot : Subalgebra.toSubmodule (⊥ : Subalgebra R A) = 1 :=
  Submodule.one_eq_range.symm

@[simp]
theorem coe_bot : ((⊥ : Subalgebra R A) : Set A) = Set.range (algebraMap R A) := rfl

theorem eq_top_iff {S : Subalgebra R A} : S = ⊤ ↔ ∀ x : A, x ∈ S :=
  ⟨fun h x => by rw [h]; exact mem_top, fun h => by
    ext x; exact ⟨fun _ => mem_top, fun _ => h x⟩⟩

theorem range_top_iff_surjective (f : A →ₐ[R] B) :
    f.range = (⊤ : Subalgebra R B) ↔ Function.Surjective f :=
  Algebra.eq_top_iff

@[simp]
theorem range_id : (AlgHom.id R A).range = ⊤ :=
  SetLike.coe_injective Set.range_id

@[simp]
theorem map_top (f : A →ₐ[R] B) : (⊤ : Subalgebra R A).map f = f.range :=
  SetLike.coe_injective Set.image_univ

@[simp]
theorem map_bot (f : A →ₐ[R] B) : (⊥ : Subalgebra R A).map f = ⊥ :=
  Subalgebra.toSubmodule_injective <| by
    simpa only [Subalgebra.map_toSubmodule, toSubmodule_bot] using Submodule.map_one _

@[simp]
theorem comap_top (f : A →ₐ[R] B) : (⊤ : Subalgebra R B).comap f = ⊤ :=
  eq_top_iff.2 fun _x => mem_top

/-- `AlgHom` to `⊤ : Subalgebra R A`. -/
def toTop : A →ₐ[R] (⊤ : Subalgebra R A) :=
  (AlgHom.id R A).codRestrict ⊤ fun _ => mem_top

theorem surjective_algebraMap_iff :
    Function.Surjective (algebraMap R A) ↔ (⊤ : Subalgebra R A) = ⊥ :=
  ⟨fun h =>
    eq_bot_iff.2 fun y _ =>
      let ⟨_x, hx⟩ := h y
      hx ▸ Subalgebra.algebraMap_mem _ _,
    fun h y => Algebra.mem_bot.1 <| eq_bot_iff.1 h (Algebra.mem_top : y ∈ _)⟩

theorem bijective_algebraMap_iff {R A : Type*} [Field R] [Semiring A] [Nontrivial A]
    [Algebra R A] : Function.Bijective (algebraMap R A) ↔ (⊤ : Subalgebra R A) = ⊥ :=
  ⟨fun h => surjective_algebraMap_iff.1 h.2, fun h =>
    ⟨(algebraMap R A).injective, surjective_algebraMap_iff.2 h⟩⟩

/-- The bottom subalgebra is isomorphic to the base ring. -/
noncomputable def botEquivOfInjective (h : Function.Injective (algebraMap R A)) :
    (⊥ : Subalgebra R A) ≃ₐ[R] R :=
  AlgEquiv.symm <|
    AlgEquiv.ofBijective (Algebra.ofId R _)
      ⟨fun _x _y hxy => h (congr_arg Subtype.val hxy : _), fun ⟨_y, x, hx⟩ => ⟨x, Subtype.eq hx⟩⟩

/-- The bottom subalgebra is isomorphic to the field. -/
@[simps! symm_apply]
noncomputable def botEquiv (F R : Type*) [Field F] [Semiring R] [Nontrivial R] [Algebra F R] :
    (⊥ : Subalgebra F R) ≃ₐ[F] F :=
  botEquivOfInjective (RingHom.injective _)

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
  AlgEquiv.ofAlgHom (Subalgebra.val ⊤) toTop rfl rfl

instance subsingleton_of_subsingleton [Subsingleton A] : Subsingleton (Subalgebra R A) :=
  ⟨fun B C => ext fun x => by simp only [Subsingleton.elim x 0, zero_mem B, zero_mem C]⟩

instance _root_.AlgHom.subsingleton [Subsingleton (Subalgebra R A)] : Subsingleton (A →ₐ[R] B) :=
  ⟨fun f g =>
    AlgHom.ext fun a =>
      have : a ∈ (⊥ : Subalgebra R A) := Subsingleton.elim (⊤ : Subalgebra R A) ⊥ ▸ mem_top
      let ⟨_x, hx⟩ := Set.mem_range.mp (mem_bot.mp this)
      hx ▸ (f.commutes _).trans (g.commutes _).symm⟩

instance _root_.AlgEquiv.subsingleton_left [Subsingleton (Subalgebra R A)] :
    Subsingleton (A ≃ₐ[R] B) :=
  ⟨fun f g => AlgEquiv.ext fun x => AlgHom.ext_iff.mp (Subsingleton.elim f.toAlgHom g.toAlgHom) x⟩

instance _root_.AlgEquiv.subsingleton_right [Subsingleton (Subalgebra R B)] :
    Subsingleton (A ≃ₐ[R] B) :=
  ⟨fun f g => by rw [← f.symm_symm, Subsingleton.elim f.symm g.symm, g.symm_symm]⟩

theorem range_val : S.val.range = S :=
  ext <| Set.ext_iff.1 <| S.val.coe_range.trans Subtype.range_val

instance : Unique (Subalgebra R R) :=
  { inferInstanceAs (Inhabited (Subalgebra R R)) with
    uniq := by
      intro S
      refine le_antisymm ?_ bot_le
      intro _ _
      simp only [Set.mem_range, mem_bot, id.map_eq_self, exists_apply_eq_apply, default] }

/-- The map `S → T` when `S` is a subalgebra contained in the subalgebra `T`.

This is the subalgebra version of `Submodule.inclusion`, or `Subring.inclusion`  -/
def inclusion {S T : Subalgebra R A} (h : S ≤ T) : S →ₐ[R] T where
  toFun := Set.inclusion h
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  commutes' _ := rfl

theorem inclusion_injective {S T : Subalgebra R A} (h : S ≤ T) : Function.Injective (inclusion h) :=
  fun _ _ => Subtype.ext ∘ Subtype.mk.inj

@[simp]
theorem inclusion_self {S : Subalgebra R A} : inclusion (le_refl S) = AlgHom.id R S :=
  AlgHom.ext fun _x => Subtype.ext rfl

@[simp]
theorem inclusion_mk {S T : Subalgebra R A} (h : S ≤ T) (x : A) (hx : x ∈ S) :
    inclusion h ⟨x, hx⟩ = ⟨x, h hx⟩ :=
  rfl

theorem inclusion_right {S T : Subalgebra R A} (h : S ≤ T) (x : T) (m : (x : A) ∈ S) :
    inclusion h ⟨x, m⟩ = x :=
  Subtype.ext rfl

@[simp]
theorem inclusion_inclusion {S T U : Subalgebra R A} (hst : S ≤ T) (htu : T ≤ U) (x : S) :
    inclusion htu (inclusion hst x) = inclusion (le_trans hst htu) x :=
  Subtype.ext rfl

@[simp]
theorem coe_inclusion {S T : Subalgebra R A} (h : S ≤ T) (s : S) : (inclusion h s : A) = s :=
  rfl

/-- Two subalgebras that are equal are also equivalent as algebras.

This is the `Subalgebra` version of `LinearEquiv.ofEq` and `Equiv.Set.ofEq`. -/
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
  ⟨fun _x y _z => (smul_assoc _ (y : S) _ : _)⟩

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
  rw [algebraMap_eq, Algebra.id.map_eq_id, RingHom.id_comp, ← toSubsemiring_subtype,
    Subsemiring.rangeS_subtype]

@[simp]
theorem range_algebraMap {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (S : Subalgebra R A) : (algebraMap S A).range = S.toSubring := by
  rw [algebraMap_eq, Algebra.id.map_eq_id, RingHom.id_comp, ← toSubring_subtype,
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
def center : Subalgebra R A :=
  { Subsemiring.center A with algebraMap_mem' := Set.algebraMap_mem_center }

theorem coe_center : (center R A : Set A) = Set.center A :=
  rfl

@[simp]
theorem center_toSubsemiring : (center R A).toSubsemiring = Subsemiring.center A :=
  rfl

@[simp]
theorem center_toSubring (R A : Type*) [CommRing R] [Ring A] [Algebra R A] :
    (center R A).toSubring = Subring.center A :=
  rfl

@[simp]
theorem center_eq_top (A : Type*) [CommSemiring A] [Algebra R A] : center R A = ⊤ :=
  SetLike.coe_injective (Set.center_eq_univ A)

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
theorem centralizer_eq_top_iff_subset {s : Set A} : centralizer R s = ⊤ ↔ s ⊆ center R A :=
  SetLike.ext'_iff.trans Set.centralizer_eq_top_iff_subset

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
def subalgebraOfSubring (S : Subring R) : Subalgebra ℤ R :=
  { S with
    algebraMap_mem' := fun i =>
      Int.induction_on i (by simpa using S.zero_mem)
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

@[simp]
theorem equalizer_eq_top {φ ψ : F} : equalizer φ ψ = ⊤ ↔ φ = ψ := by
  simp [SetLike.ext_iff, DFunLike.ext_iff]

@[simp]
theorem equalizer_same (φ : F) : equalizer φ φ = ⊤ := equalizer_eq_top.2 rfl

theorem le_equalizer {φ ψ : F} {S : Subalgebra R A} : S ≤ equalizer φ ψ ↔ Set.EqOn φ ψ S := Iff.rfl

theorem eqOn_sup {φ ψ : F} {S T : Subalgebra R A} (hS : Set.EqOn φ ψ S) (hT : Set.EqOn φ ψ T) :
    Set.EqOn φ ψ ↑(S ⊔ T) := by
  rw [← le_equalizer] at hS hT ⊢
  exact sup_le hS hT

theorem ext_on_codisjoint {φ ψ : F} {S T : Subalgebra R A} (hST : Codisjoint S T)
    (hS : Set.EqOn φ ψ S) (hT : Set.EqOn φ ψ T) : φ = ψ :=
  DFunLike.ext _ _ fun _ ↦ eqOn_sup hS hT <| hST.eq_top.symm ▸ trivial

end AlgHom

end Equalizer

section MapComap

namespace Subalgebra

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem map_comap_eq (f : A →ₐ[R] B) (S : Subalgebra R B) : (S.comap f).map f = S ⊓ f.range :=
  SetLike.coe_injective Set.image_preimage_eq_inter_range

theorem map_comap_eq_self
    {f : A →ₐ[R] B} {S : Subalgebra R B} (h : S ≤ f.range) : (S.comap f).map f = S := by
  simpa only [inf_of_le_left h] using map_comap_eq f S

theorem map_comap_eq_self_of_surjective
    {f : A →ₐ[R] B} (hf : Function.Surjective f) (S : Subalgebra R B) : (S.comap f).map f = S :=
  map_comap_eq_self <| by simp [(Algebra.range_top_iff_surjective f).2 hf]

theorem comap_map_eq_self_of_injective
    {f : A →ₐ[R] B} (hf : Function.Injective f) (S : Subalgebra R A) : (S.map f).comap f = S :=
  SetLike.coe_injective (Set.preimage_image_eq _ hf)

end Subalgebra

end MapComap
