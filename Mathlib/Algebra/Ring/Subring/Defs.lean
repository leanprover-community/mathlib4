/-
Copyright (c) 2020 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/
import Mathlib.Algebra.Ring.Subsemiring.Defs
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.RingTheory.NonUnitalSubring.Defs

/-!
# Subrings

Let `R` be a ring. This file defines the "bundled" subring type `Subring R`, a type
whose terms correspond to subrings of `R`. This is the preferred way to talk
about subrings in mathlib. Unbundled subrings (`s : Set R` and `IsSubring s`)
are not in this file, and they will ultimately be deprecated.

We prove that subrings are a complete lattice, and that you can `map` (pushforward) and
`comap` (pull back) them along ring homomorphisms.

We define the `closure` construction from `Set R` to `Subring R`, sending a subset of `R`
to the subring it generates, and prove that it is a Galois insertion.

## Main definitions

Notation used here:

`(R : Type u) [Ring R] (S : Type u) [Ring S] (f g : R →+* S)`
`(A : Subring R) (B : Subring S) (s : Set R)`

* `Subring R` : the type of subrings of a ring `R`.

* `instance : CompleteLattice (Subring R)` : the complete lattice structure on the subrings.

* `Subring.center` : the center of a ring `R`.

* `Subring.closure` : subring closure of a set, i.e., the smallest subring that includes the set.

* `Subring.gi` : `closure : Set M → Subring M` and coercion `(↑) : Subring M → et M`
  form a `GaloisInsertion`.

* `comap f B : Subring A` : the preimage of a subring `B` along the ring homomorphism `f`

* `map f A : Subring B` : the image of a subring `A` along the ring homomorphism `f`.

* `prod A B : Subring (R × S)` : the product of subrings

* `f.range : Subring B` : the range of the ring homomorphism `f`.

* `eqLocus f g : Subring R` : given ring homomorphisms `f g : R →+* S`,
     the subring of `R` where `f x = g x`

## Implementation notes

A subring is implemented as a subsemiring which is also an additive subgroup.
The initial PR was as a submonoid which is also an additive subgroup.

Lattice inclusion (e.g. `≤` and `⊓`) is used rather than set notation (`⊆` and `∩`), although
`∈` is defined as membership of a subring's underlying set.

## Tags
subring, subrings
-/

assert_not_exists OrderedRing

universe u v w

variable {R : Type u} {S : Type v} {T : Type w} [Ring R]

section SubringClass

/-- `SubringClass S R` states that `S` is a type of subsets `s ⊆ R` that
are both a multiplicative submonoid and an additive subgroup. -/
class SubringClass (S : Type*) (R : outParam (Type u)) [Ring R] [SetLike S R] extends
  SubsemiringClass S R, NegMemClass S R : Prop

-- See note [lower instance priority]
instance (priority := 100) SubringClass.addSubgroupClass (S : Type*) (R : Type u)
    [SetLike S R] [Ring R] [h : SubringClass S R] : AddSubgroupClass S R :=
  { h with }

instance (priority := 100) SubringClass.nonUnitalSubringClass (S : Type*) (R : Type u)
    [SetLike S R] [Ring R] [SubringClass S R] : NonUnitalSubringClass S R where

variable [SetLike S R] [hSR : SubringClass S R] (s : S)

@[simp, aesop safe (rule_sets := [SetLike])]
theorem intCast_mem (n : ℤ) : (n : R) ∈ s := by simp only [← zsmul_one, zsmul_mem, one_mem]

@[deprecated _root_.intCast_mem (since := "2024-04-05")] alias coe_int_mem := intCast_mem

namespace SubringClass

instance (priority := 75) toHasIntCast : IntCast s :=
  ⟨fun n => ⟨n, intCast_mem s n⟩⟩

-- Prefer subclasses of `Ring` over subclasses of `SubringClass`.
/-- A subring of a ring inherits a ring structure -/
instance (priority := 75) toRing : Ring s := fast_instance%
  Subtype.coe_injective.ring Subtype.val rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) fun _ => rfl

-- Prefer subclasses of `Ring` over subclasses of `SubringClass`.
/-- A subring of a `CommRing` is a `CommRing`. -/
instance (priority := 75) toCommRing {R} [CommRing R] [SetLike S R] [SubringClass S R] :
    CommRing s := fast_instance%
  Subtype.coe_injective.commRing Subtype.val rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) fun _ => rfl

-- Prefer subclasses of `Ring` over subclasses of `SubringClass`.
/-- A subring of a domain is a domain. -/
instance (priority := 75) {R} [Ring R] [IsDomain R] [SetLike S R] [SubringClass S R] : IsDomain s :=
  NoZeroDivisors.to_isDomain _

/-- The natural ring hom from a subring of ring `R` to `R`. -/
def subtype (s : S) : s →+* R :=
  { SubmonoidClass.subtype s, AddSubgroupClass.subtype s with
    toFun := (↑) }

@[simp]
theorem coeSubtype : (subtype s : s → R) = ((↑) : s → R) :=
  rfl

@[simp, norm_cast]
theorem coe_natCast (n : ℕ) : ((n : s) : R) = n :=
  map_natCast (subtype s) n

@[simp, norm_cast]
theorem coe_intCast (n : ℤ) : ((n : s) : R) = n :=
  map_intCast (subtype s) n

end SubringClass

end SubringClass

variable [Ring S] [Ring T]

/-- `Subring R` is the type of subrings of `R`. A subring of `R` is a subset `s` that is a
  multiplicative submonoid and an additive subgroup. Note in particular that it shares the
  same 0 and 1 as R. -/
structure Subring (R : Type u) [Ring R] extends Subsemiring R, AddSubgroup R

/-- Reinterpret a `Subring` as a `Subsemiring`. -/
add_decl_doc Subring.toSubsemiring

/-- Reinterpret a `Subring` as an `AddSubgroup`. -/
add_decl_doc Subring.toAddSubgroup

namespace Subring

-- Porting note: there is no `Subring.toSubmonoid` but we can't define it because there is a
-- projection `s.toSubmonoid`

instance : SetLike (Subring R) R where
  coe s := s.carrier
  coe_injective' p q h := by cases p; cases q; congr; exact SetLike.ext' h

instance : SubringClass (Subring R) R where
  zero_mem s := s.zero_mem'
  add_mem {s} := s.add_mem'
  one_mem s := s.one_mem'
  mul_mem {s} := s.mul_mem'
  neg_mem {s} := s.neg_mem'

initialize_simps_projections Subring (carrier → coe, as_prefix coe)

/-- Turn a `Subring` into a `NonUnitalSubring` by forgetting that it contains `1`. -/
def toNonUnitalSubring (S : Subring R) : NonUnitalSubring R where __ := S

@[simp]
theorem mem_toSubsemiring {s : Subring R} {x : R} : x ∈ s.toSubsemiring ↔ x ∈ s := Iff.rfl

theorem mem_carrier {s : Subring R} {x : R} : x ∈ s.carrier ↔ x ∈ s :=
  Iff.rfl

@[simp]
theorem mem_mk {S : Subsemiring R} {x : R} (h) : x ∈ (⟨S, h⟩ : Subring R) ↔ x ∈ S := Iff.rfl

@[simp] theorem coe_set_mk (S : Subsemiring R) (h) : ((⟨S, h⟩ : Subring R) : Set R) = S := rfl

@[simp]
theorem mk_le_mk {S S' : Subsemiring R} (h₁ h₂) :
    (⟨S, h₁⟩ : Subring R) ≤ (⟨S', h₂⟩ : Subring R) ↔ S ≤ S' :=
  Iff.rfl

lemma one_mem_toNonUnitalSubring (S : Subring R) : 1 ∈ S.toNonUnitalSubring := S.one_mem

/-- Two subrings are equal if they have the same elements. -/
@[ext]
theorem ext {S T : Subring R} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h

/-- Copy of a subring with a new `carrier` equal to the old one. Useful to fix definitional
equalities. -/
@[simps coe toSubsemiring]
protected def copy (S : Subring R) (s : Set R) (hs : s = ↑S) : Subring R :=
  { S.toSubsemiring.copy s hs with
    carrier := s
    neg_mem' := hs.symm ▸ S.neg_mem' }

theorem copy_eq (S : Subring R) (s : Set R) (hs : s = ↑S) : S.copy s hs = S :=
  SetLike.coe_injective hs

theorem toSubsemiring_injective : Function.Injective (toSubsemiring : Subring R → Subsemiring R)
  | _, _, h => ext (SetLike.ext_iff.mp h :)

theorem toAddSubgroup_injective : Function.Injective (toAddSubgroup : Subring R → AddSubgroup R)
  | _, _, h => ext (SetLike.ext_iff.mp h :)

theorem toSubmonoid_injective : Function.Injective (fun s : Subring R => s.toSubmonoid)
  | _, _, h => ext (SetLike.ext_iff.mp h :)

/-- Construct a `Subring R` from a set `s`, a submonoid `sm`, and an additive
subgroup `sa` such that `x ∈ s ↔ x ∈ sm ↔ x ∈ sa`. -/
@[simps! coe]
protected def mk' (s : Set R) (sm : Submonoid R) (sa : AddSubgroup R) (hm : ↑sm = s)
    (ha : ↑sa = s) : Subring R :=
  { sm.copy s hm.symm, sa.copy s ha.symm with }

@[simp]
theorem mem_mk' {s : Set R} {sm : Submonoid R} (hm : ↑sm = s) {sa : AddSubgroup R} (ha : ↑sa = s)
    {x : R} : x ∈ Subring.mk' s sm sa hm ha ↔ x ∈ s :=
  Iff.rfl

@[simp]
theorem mk'_toSubmonoid {s : Set R} {sm : Submonoid R} (hm : ↑sm = s) {sa : AddSubgroup R}
    (ha : ↑sa = s) : (Subring.mk' s sm sa hm ha).toSubmonoid = sm :=
  SetLike.coe_injective hm.symm

@[simp]
theorem mk'_toAddSubgroup {s : Set R} {sm : Submonoid R} (hm : ↑sm = s) {sa : AddSubgroup R}
    (ha : ↑sa = s) : (Subring.mk' s sm sa hm ha).toAddSubgroup = sa :=
  SetLike.coe_injective ha.symm

end Subring

/-- A `Subsemiring` containing -1 is a `Subring`. -/
@[simps toSubsemiring]
def Subsemiring.toSubring (s : Subsemiring R) (hneg : (-1 : R) ∈ s) : Subring R where
  toSubsemiring := s
  neg_mem' h := by
    rw [← neg_one_mul]
    exact mul_mem hneg h

namespace Subring

variable (s : Subring R)

/-- A subring contains the ring's 1. -/
protected theorem one_mem : (1 : R) ∈ s :=
  one_mem _

/-- A subring contains the ring's 0. -/
protected theorem zero_mem : (0 : R) ∈ s :=
  zero_mem _

/-- A subring is closed under multiplication. -/
protected theorem mul_mem {x y : R} : x ∈ s → y ∈ s → x * y ∈ s :=
  mul_mem

/-- A subring is closed under addition. -/
protected theorem add_mem {x y : R} : x ∈ s → y ∈ s → x + y ∈ s :=
  add_mem

/-- A subring is closed under negation. -/
protected theorem neg_mem {x : R} : x ∈ s → -x ∈ s :=
  neg_mem

/-- A subring is closed under subtraction -/
protected theorem sub_mem {x y : R} (hx : x ∈ s) (hy : y ∈ s) : x - y ∈ s :=
  sub_mem hx hy

/-- A subring of a ring inherits a ring structure -/
instance toRing : Ring s := SubringClass.toRing s

protected theorem zsmul_mem {x : R} (hx : x ∈ s) (n : ℤ) : n • x ∈ s :=
  zsmul_mem hx n

protected theorem pow_mem {x : R} (hx : x ∈ s) (n : ℕ) : x ^ n ∈ s :=
  pow_mem hx n

@[simp, norm_cast]
theorem coe_add (x y : s) : (↑(x + y) : R) = ↑x + ↑y :=
  rfl

@[simp, norm_cast]
theorem coe_neg (x : s) : (↑(-x) : R) = -↑x :=
  rfl

@[simp, norm_cast]
theorem coe_mul (x y : s) : (↑(x * y) : R) = ↑x * ↑y :=
  rfl

@[simp, norm_cast]
theorem coe_zero : ((0 : s) : R) = 0 :=
  rfl

@[simp, norm_cast]
theorem coe_one : ((1 : s) : R) = 1 :=
  rfl

@[simp, norm_cast]
theorem coe_pow (x : s) (n : ℕ) : ↑(x ^ n) = (x : R) ^ n :=
  SubmonoidClass.coe_pow x n

theorem coe_eq_zero_iff {x : s} : (x : R) = 0 ↔ x = 0 :=
  ⟨fun h => Subtype.ext (Trans.trans h s.coe_zero.symm), fun h => h.symm ▸ s.coe_zero⟩

/-- A subring of a `CommRing` is a `CommRing`. -/
instance toCommRing {R} [CommRing R] (s : Subring R) : CommRing s :=
  SubringClass.toCommRing s

/-- A subring of a non-trivial ring is non-trivial. -/
instance {R} [Ring R] [Nontrivial R] (s : Subring R) : Nontrivial s :=
  s.toSubsemiring.nontrivial

/-- A subring of a ring with no zero divisors has no zero divisors. -/
instance {R} [Ring R] [NoZeroDivisors R] (s : Subring R) : NoZeroDivisors s :=
  s.toSubsemiring.noZeroDivisors

/-- A subring of a domain is a domain. -/
instance {R} [Ring R] [IsDomain R] (s : Subring R) : IsDomain s :=
  NoZeroDivisors.to_isDomain _

/-- The natural ring hom from a subring of ring `R` to `R`. -/
def subtype (s : Subring R) : s →+* R :=
  { s.toSubmonoid.subtype, s.toAddSubgroup.subtype with toFun := (↑) }

@[simp]
theorem coeSubtype : ⇑s.subtype = ((↑) : s → R) :=
  rfl

@[norm_cast]
theorem coe_natCast : ∀ n : ℕ, ((n : s) : R) = n :=
  map_natCast s.subtype

@[norm_cast]
theorem coe_intCast : ∀ n : ℤ, ((n : s) : R) = n :=
  map_intCast s.subtype

/-! ## Partial order -/

@[simp]
theorem coe_toSubsemiring (s : Subring R) : (s.toSubsemiring : Set R) = s :=
  rfl

-- Porting note: https://github.com/leanprover-community/mathlib4/issues/10675
-- dsimp cannot prove this
@[simp, nolint simpNF]
theorem mem_toSubmonoid {s : Subring R} {x : R} : x ∈ s.toSubmonoid ↔ x ∈ s :=
  Iff.rfl

@[simp]
theorem coe_toSubmonoid (s : Subring R) : (s.toSubmonoid : Set R) = s :=
  rfl

-- Porting note: https://github.com/leanprover-community/mathlib4/issues/10675
-- dsimp cannot prove this
@[simp, nolint simpNF]
theorem mem_toAddSubgroup {s : Subring R} {x : R} : x ∈ s.toAddSubgroup ↔ x ∈ s :=
  Iff.rfl

@[simp]
theorem coe_toAddSubgroup (s : Subring R) : (s.toAddSubgroup : Set R) = s :=
  rfl

end Subring

/-- Turn a non-unital subring containing `1` into a subring. -/
def NonUnitalSubring.toSubring (S : NonUnitalSubring R) (h1 : (1 : R) ∈ S) : Subring R where
  __ := S
  one_mem' := h1

lemma Subring.toNonUnitalSubring_toSubring (S : Subring R) :
    S.toNonUnitalSubring.toSubring S.one_mem = S := by cases S; rfl

lemma NonUnitalSubring.toSubring_toNonUnitalSubring (S : NonUnitalSubring R) (h1 : (1 : R) ∈ S) :
    (NonUnitalSubring.toSubring S h1).toNonUnitalSubring = S := by cases S; rfl

theorem AddSubgroup.int_mul_mem {G : AddSubgroup R} (k : ℤ) {g : R} (h : g ∈ G) :
    (k : R) * g ∈ G := by
  convert AddSubgroup.zsmul_mem G h k using 1
  simp
