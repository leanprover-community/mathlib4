/-
Copyright (c) 2023 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.RingTheory.NonUnitalSubsemiring.Defs
import Mathlib.Tactic.FastInstance

/-!
# `NonUnitalSubring`s

Let `R` be a non-unital ring. This file defines the "bundled" non-unital subring type
`NonUnitalSubring R`, a type whose terms correspond to non-unital subrings of `R`.
This is the preferred way to talk about non-unital subrings in mathlib.

## Main definitions

Notation used here:

`(R : Type u) [NonUnitalRing R] (S : Type u) [NonUnitalRing S] (f g : R →ₙ+* S)`
`(A : NonUnitalSubring R) (B : NonUnitalSubring S) (s : Set R)`

* `NonUnitalSubring R` : the type of non-unital subrings of a ring `R`.

## Implementation notes

A non-unital subring is implemented as a `NonUnitalSubsemiring` which is also an
additive subgroup.

Lattice inclusion (e.g. `≤` and `⊓`) is used rather than set notation (`⊆` and `∩`), although
`∈` is defined as membership of a non-unital subring's underlying set.

## Tags
non-unital subring
-/

assert_not_exists RelIso

universe u v w

section Basic

variable {R : Type u} {S : Type v} [NonUnitalNonAssocRing R]

section NonUnitalSubringClass

/-- `NonUnitalSubringClass S R` states that `S` is a type of subsets `s ⊆ R` that
are both a multiplicative submonoid and an additive subgroup. -/
class NonUnitalSubringClass (S : Type*) (R : Type u) [NonUnitalNonAssocRing R] [SetLike S R] : Prop
  extends NonUnitalSubsemiringClass S R, NegMemClass S R where

-- See note [lower instance priority]
instance (priority := 100) NonUnitalSubringClass.addSubgroupClass (S : Type*) (R : Type u)
    [SetLike S R] [NonUnitalNonAssocRing R] [h : NonUnitalSubringClass S R] :
    AddSubgroupClass S R :=
  { h with }

variable [SetLike S R] [hSR : NonUnitalSubringClass S R] (s : S)

namespace NonUnitalSubringClass

-- Prefer subclasses of `NonUnitalRing` over subclasses of `NonUnitalSubringClass`.
/-- A non-unital subring of a non-unital ring inherits a non-unital ring structure -/
instance (priority := 75) toNonUnitalNonAssocRing : NonUnitalNonAssocRing s := fast_instance%
  Subtype.val_injective.nonUnitalNonAssocRing _ rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

-- Prefer subclasses of `NonUnitalRing` over subclasses of `NonUnitalSubringClass`.
/-- A non-unital subring of a non-unital ring inherits a non-unital ring structure -/
instance (priority := 75) toNonUnitalRing {R : Type*} [NonUnitalRing R] [SetLike S R]
    [NonUnitalSubringClass S R] (s : S) : NonUnitalRing s := fast_instance%
  Subtype.val_injective.nonUnitalRing _ rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

-- Prefer subclasses of `NonUnitalRing` over subclasses of `NonUnitalSubringClass`.
/-- A non-unital subring of a `NonUnitalCommRing` is a `NonUnitalCommRing`. -/
instance (priority := 75) toNonUnitalCommRing {R} [NonUnitalCommRing R] [SetLike S R]
    [NonUnitalSubringClass S R] : NonUnitalCommRing s := fast_instance%
  Subtype.val_injective.nonUnitalCommRing _ rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

/-- The natural non-unital ring hom from a non-unital subring of a non-unital ring `R` to `R`. -/
def subtype (s : S) : s →ₙ+* R :=
  { NonUnitalSubsemiringClass.subtype s,
    AddSubgroupClass.subtype s with
    toFun := Subtype.val }

variable {s} in
@[simp]
theorem subtype_apply (x : s) : subtype s x = x :=
  rfl

theorem subtype_injective : Function.Injective (subtype s) :=
  Subtype.coe_injective

@[simp]
theorem coe_subtype : (subtype s : s → R) = Subtype.val :=
  rfl

end NonUnitalSubringClass

end NonUnitalSubringClass

/-- `NonUnitalSubring R` is the type of non-unital subrings of `R`. A non-unital subring of `R`
is a subset `s` that is a multiplicative subsemigroup and an additive subgroup. Note in particular
that it shares the same 0 as R. -/
structure NonUnitalSubring (R : Type u) [NonUnitalNonAssocRing R] extends
  NonUnitalSubsemiring R, AddSubgroup R

/-- Reinterpret a `NonUnitalSubring` as a `NonUnitalSubsemiring`. -/
add_decl_doc NonUnitalSubring.toNonUnitalSubsemiring

/-- Reinterpret a `NonUnitalSubring` as an `AddSubgroup`. -/
add_decl_doc NonUnitalSubring.toAddSubgroup

namespace NonUnitalSubring

/-- The underlying submonoid of a `NonUnitalSubring`. -/
def toSubsemigroup (s : NonUnitalSubring R) : Subsemigroup R :=
  { s.toNonUnitalSubsemiring.toSubsemigroup with carrier := s.carrier }

instance : SetLike (NonUnitalSubring R) R where
  coe s := s.carrier
  coe_injective' p q h := by cases p; cases q; congr; exact SetLike.coe_injective h

/-- The actual `NonUnitalSubring` obtained from an element of a `NonUnitalSubringClass`. -/
@[simps]
def ofClass {S R : Type*} [NonUnitalNonAssocRing R] [SetLike S R] [NonUnitalSubringClass S R]
    (s : S) : NonUnitalSubring R where
  carrier := s
  add_mem' := add_mem
  zero_mem' := zero_mem _
  mul_mem' := mul_mem
  neg_mem' := neg_mem

instance (priority := 100) : CanLift (Set R) (NonUnitalSubring R) (↑)
    (fun s ↦ 0 ∈ s ∧ (∀ {x y}, x ∈ s → y ∈ s → x + y ∈ s) ∧
      (∀ {x y}, x ∈ s → y ∈ s → x * y ∈ s) ∧ ∀ {x}, x ∈ s → -x ∈ s) where
  prf s h :=
    ⟨ { carrier := s
        zero_mem' := h.1
        add_mem' := h.2.1
        mul_mem' := h.2.2.1
        neg_mem' := h.2.2.2 },
      rfl ⟩

instance : NonUnitalSubringClass (NonUnitalSubring R) R where
  zero_mem s := s.zero_mem'
  add_mem {s} := s.add_mem'
  mul_mem {s} := s.mul_mem'
  neg_mem {s} := s.neg_mem'

theorem mem_carrier {s : NonUnitalSubring R} {x : R} : x ∈ s.toNonUnitalSubsemiring ↔ x ∈ s :=
  Iff.rfl

@[simp]
theorem mem_mk {S : NonUnitalSubsemiring R} {x : R} (h) :
    x ∈ (⟨S, h⟩ : NonUnitalSubring R) ↔ x ∈ S :=
  Iff.rfl

@[simp]
theorem coe_set_mk (S : NonUnitalSubsemiring R) (h) :
    ((⟨S, h⟩ : NonUnitalSubring R) : Set R) = S :=
  rfl

@[simp]
theorem mk_le_mk {S S' : NonUnitalSubsemiring R} (h h') :
    (⟨S, h⟩ : NonUnitalSubring R) ≤ (⟨S', h'⟩ : NonUnitalSubring R) ↔ S ≤ S' :=
  Iff.rfl

/-- Two non-unital subrings are equal if they have the same elements. -/
@[ext]
theorem ext {S T : NonUnitalSubring R} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h

/-- Copy of a non-unital subring with a new `carrier` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (S : NonUnitalSubring R) (s : Set R) (hs : s = ↑S) : NonUnitalSubring R :=
  { S.toNonUnitalSubsemiring.copy s hs with
    carrier := s
    neg_mem' := hs.symm ▸ S.neg_mem' }

@[simp]
theorem coe_copy (S : NonUnitalSubring R) (s : Set R) (hs : s = ↑S) : (S.copy s hs : Set R) = s :=
  rfl

theorem copy_eq (S : NonUnitalSubring R) (s : Set R) (hs : s = ↑S) : S.copy s hs = S :=
  SetLike.coe_injective hs

theorem toNonUnitalSubsemiring_injective :
    Function.Injective (toNonUnitalSubsemiring : NonUnitalSubring R → NonUnitalSubsemiring R)
  | _r, _s, h => ext (SetLike.ext_iff.mp h :)

@[mono]
theorem toNonUnitalSubsemiring_strictMono :
    StrictMono (toNonUnitalSubsemiring : NonUnitalSubring R → NonUnitalSubsemiring R) := fun _ _ =>
  id

@[mono]
theorem toNonUnitalSubsemiring_mono :
    Monotone (toNonUnitalSubsemiring : NonUnitalSubring R → NonUnitalSubsemiring R) :=
  toNonUnitalSubsemiring_strictMono.monotone

theorem toAddSubgroup_injective :
    Function.Injective (toAddSubgroup : NonUnitalSubring R → AddSubgroup R)
  | _r, _s, h => ext (SetLike.ext_iff.mp h :)

@[mono]
theorem toAddSubgroup_strictMono :
    StrictMono (toAddSubgroup : NonUnitalSubring R → AddSubgroup R) := fun _ _ => id

@[mono]
theorem toAddSubgroup_mono : Monotone (toAddSubgroup : NonUnitalSubring R → AddSubgroup R) :=
  toAddSubgroup_strictMono.monotone

theorem toSubsemigroup_injective :
    Function.Injective (toSubsemigroup : NonUnitalSubring R → Subsemigroup R)
  | _r, _s, h => ext (SetLike.ext_iff.mp h :)

@[mono]
theorem toSubsemigroup_strictMono :
    StrictMono (toSubsemigroup : NonUnitalSubring R → Subsemigroup R) := fun _ _ => id

@[mono]
theorem toSubsemigroup_mono : Monotone (toSubsemigroup : NonUnitalSubring R → Subsemigroup R) :=
  toSubsemigroup_strictMono.monotone

/-- Construct a `NonUnitalSubring R` from a set `s`, a subsemigroup `sm`, and an additive
subgroup `sa` such that `x ∈ s ↔ x ∈ sm ↔ x ∈ sa`. -/
protected def mk' (s : Set R) (sm : Subsemigroup R) (sa : AddSubgroup R) (hm : ↑sm = s)
    (ha : ↑sa = s) : NonUnitalSubring R :=
  { sm.copy s hm.symm, sa.copy s ha.symm with }

@[simp]
theorem coe_mk' {s : Set R} {sm : Subsemigroup R} (hm : ↑sm = s) {sa : AddSubgroup R}
    (ha : ↑sa = s) : (NonUnitalSubring.mk' s sm sa hm ha : Set R) = s :=
  rfl

@[simp]
theorem mem_mk' {s : Set R} {sm : Subsemigroup R} (hm : ↑sm = s) {sa : AddSubgroup R} (ha : ↑sa = s)
    {x : R} : x ∈ NonUnitalSubring.mk' s sm sa hm ha ↔ x ∈ s :=
  Iff.rfl

@[simp]
theorem mk'_toSubsemigroup {s : Set R} {sm : Subsemigroup R} (hm : ↑sm = s) {sa : AddSubgroup R}
    (ha : ↑sa = s) : (NonUnitalSubring.mk' s sm sa hm ha).toSubsemigroup = sm :=
  SetLike.coe_injective hm.symm

@[simp]
theorem mk'_toAddSubgroup {s : Set R} {sm : Subsemigroup R} (hm : ↑sm = s) {sa : AddSubgroup R}
    (ha : ↑sa = s) : (NonUnitalSubring.mk' s sm sa hm ha).toAddSubgroup = sa :=
  SetLike.coe_injective ha.symm

end NonUnitalSubring

namespace NonUnitalSubring

variable (s : NonUnitalSubring R)

/-- A non-unital subring contains the ring's 0. -/
protected theorem zero_mem : (0 : R) ∈ s :=
  zero_mem _

/-- A non-unital subring is closed under multiplication. -/
protected theorem mul_mem {x y : R} : x ∈ s → y ∈ s → x * y ∈ s :=
  mul_mem

/-- A non-unital subring is closed under addition. -/
protected theorem add_mem {x y : R} : x ∈ s → y ∈ s → x + y ∈ s :=
  add_mem

/-- A non-unital subring is closed under negation. -/
protected theorem neg_mem {x : R} : x ∈ s → -x ∈ s :=
  neg_mem

/-- A non-unital subring is closed under subtraction -/
protected theorem sub_mem {x y : R} (hx : x ∈ s) (hy : y ∈ s) : x - y ∈ s :=
  sub_mem hx hy

/-- A non-unital subring of a non-unital ring inherits a non-unital ring structure -/
instance toNonUnitalRing {R : Type*} [NonUnitalRing R] (s : NonUnitalSubring R) :
    NonUnitalRing s := fast_instance%
  Subtype.coe_injective.nonUnitalRing _ rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

protected theorem zsmul_mem {x : R} (hx : x ∈ s) (n : ℤ) : n • x ∈ s :=
  zsmul_mem hx n

@[simp, norm_cast]
theorem val_add (x y : s) : (↑(x + y) : R) = ↑x + ↑y :=
  rfl

@[simp, norm_cast]
theorem val_neg (x : s) : (↑(-x) : R) = -↑x :=
  rfl

@[simp, norm_cast]
theorem val_mul (x y : s) : (↑(x * y) : R) = ↑x * ↑y :=
  rfl

@[simp, norm_cast]
theorem val_zero : ((0 : s) : R) = 0 :=
  rfl

theorem coe_eq_zero_iff {x : s} : (x : R) = 0 ↔ x = 0 := by
  simp

/-- A non-unital subring of a `NonUnitalCommRing` is a `NonUnitalCommRing`. -/
instance toNonUnitalCommRing {R} [NonUnitalCommRing R] (s : NonUnitalSubring R) :
    NonUnitalCommRing s := fast_instance%
  Subtype.coe_injective.nonUnitalCommRing _ rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

/-! ## Partial order -/


@[simp]
theorem mem_toSubsemigroup {s : NonUnitalSubring R} {x : R} : x ∈ s.toSubsemigroup ↔ x ∈ s :=
  Iff.rfl

@[simp]
theorem coe_toSubsemigroup (s : NonUnitalSubring R) : (s.toSubsemigroup : Set R) = s :=
  rfl

@[simp]
theorem mem_toAddSubgroup {s : NonUnitalSubring R} {x : R} : x ∈ s.toAddSubgroup ↔ x ∈ s :=
  Iff.rfl

@[simp]
theorem coe_toAddSubgroup (s : NonUnitalSubring R) : (s.toAddSubgroup : Set R) = s :=
  rfl

@[simp]
theorem mem_toNonUnitalSubsemiring {s : NonUnitalSubring R} {x : R} :
    x ∈ s.toNonUnitalSubsemiring ↔ x ∈ s :=
  Iff.rfl

@[simp]
theorem coe_toNonUnitalSubsemiring (s : NonUnitalSubring R) :
    (s.toNonUnitalSubsemiring : Set R) = s :=
  rfl

end NonUnitalSubring

end Basic

section Hom

namespace NonUnitalSubring

variable {R : Type u} [NonUnitalNonAssocRing R]

open NonUnitalRingHom

/-- The ring homomorphism associated to an inclusion of `NonUnitalSubring`s. -/
def inclusion {S T : NonUnitalSubring R} (h : S ≤ T) : S →ₙ+* T :=
  NonUnitalRingHom.codRestrict (NonUnitalSubringClass.subtype S) _ fun x => h x.2

end NonUnitalSubring

end Hom
