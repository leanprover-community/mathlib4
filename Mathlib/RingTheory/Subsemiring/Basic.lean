/-
Copyright (c) 2020 Yury Kudryashov All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Ring.Prod
import Mathlib.Algebra.Order.Ring.InjSurj
import Mathlib.Algebra.GroupRingAction.Subobjects
import Mathlib.Data.Set.Finite
import Mathlib.GroupTheory.Submonoid.Centralizer
import Mathlib.GroupTheory.Submonoid.Membership

#align_import ring_theory.subsemiring.basic from "leanprover-community/mathlib"@"b915e9392ecb2a861e1e766f0e1df6ac481188ca"

/-!
# Bundled subsemirings

We define bundled subsemirings and some standard constructions: `CompleteLattice` structure,
`Subtype` and `inclusion` ring homomorphisms, subsemiring `map`, `comap` and range (`rangeS`) of
a `RingHom` etc.
-/


open BigOperators

universe u v w

section AddSubmonoidWithOneClass

/-- `AddSubmonoidWithOneClass S R` says `S` is a type of subsets `s ≤ R` that contain `0`, `1`,
and are closed under `(+)` -/
class AddSubmonoidWithOneClass (S R : Type*) [AddMonoidWithOne R]
  [SetLike S R] extends AddSubmonoidClass S R, OneMemClass S R : Prop
#align add_submonoid_with_one_class AddSubmonoidWithOneClass

variable {S R : Type*} [AddMonoidWithOne R] [SetLike S R] (s : S)

theorem natCast_mem [AddSubmonoidWithOneClass S R] (n : ℕ) : (n : R) ∈ s := by
  induction n <;> simp [zero_mem, add_mem, one_mem, *]
  -- ⊢ ↑Nat.zero ∈ s
                  -- 🎉 no goals
                  -- 🎉 no goals
#align nat_cast_mem natCast_mem

instance (priority := 74) AddSubmonoidWithOneClass.toAddMonoidWithOne
    [AddSubmonoidWithOneClass S R] : AddMonoidWithOne s :=
  { AddSubmonoidClass.toAddMonoid s with
    one := ⟨_, one_mem s⟩
    natCast := fun n => ⟨n, natCast_mem s n⟩
    natCast_zero := Subtype.ext Nat.cast_zero
    natCast_succ := fun _ => Subtype.ext (Nat.cast_succ _) }
#align add_submonoid_with_one_class.to_add_monoid_with_one AddSubmonoidWithOneClass.toAddMonoidWithOne

end AddSubmonoidWithOneClass

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

section SubsemiringClass

/-- `SubsemiringClass S R` states that `S` is a type of subsets `s ⊆ R` that
are both a multiplicative and an additive submonoid. -/
class SubsemiringClass (S : Type*) (R : Type u) [NonAssocSemiring R]
  [SetLike S R] extends SubmonoidClass S R, AddSubmonoidClass S R : Prop
#align subsemiring_class SubsemiringClass

-- See note [lower instance priority]
instance (priority := 100) SubsemiringClass.addSubmonoidWithOneClass (S : Type*)
    (R : Type u) [NonAssocSemiring R] [SetLike S R] [h : SubsemiringClass S R] :
    AddSubmonoidWithOneClass S R :=
  { h with }
#align subsemiring_class.add_submonoid_with_one_class SubsemiringClass.addSubmonoidWithOneClass

variable [SetLike S R] [hSR : SubsemiringClass S R] (s : S)

theorem coe_nat_mem (n : ℕ) : (n : R) ∈ s := by
  rw [← nsmul_one]
  -- ⊢ n • 1 ∈ s
  exact nsmul_mem (one_mem _) _
  -- 🎉 no goals
#align coe_nat_mem coe_nat_mem

namespace SubsemiringClass

-- Prefer subclasses of `NonAssocSemiring` over subclasses of `SubsemiringClass`.
/-- A subsemiring of a `NonAssocSemiring` inherits a `NonAssocSemiring` structure -/
instance (priority := 75) toNonAssocSemiring : NonAssocSemiring s :=
  Subtype.coe_injective.nonAssocSemiring (↑) rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ => rfl
#align subsemiring_class.to_non_assoc_semiring SubsemiringClass.toNonAssocSemiring

instance nontrivial [Nontrivial R] : Nontrivial s :=
  nontrivial_of_ne 0 1 fun H => zero_ne_one (congr_arg Subtype.val H)
#align subsemiring_class.nontrivial SubsemiringClass.nontrivial

instance noZeroDivisors [NoZeroDivisors R] : NoZeroDivisors s :=
  Subtype.coe_injective.noZeroDivisors _ rfl fun _ _ => rfl
#align subsemiring_class.no_zero_divisors SubsemiringClass.noZeroDivisors

/-- The natural ring hom from a subsemiring of semiring `R` to `R`. -/
def subtype : s →+* R :=
  { SubmonoidClass.subtype s, AddSubmonoidClass.subtype s with toFun := (↑) }
#align subsemiring_class.subtype SubsemiringClass.subtype

@[simp]
theorem coe_subtype : (subtype s : s → R) = ((↑) : s → R) :=
  rfl
#align subsemiring_class.coe_subtype SubsemiringClass.coe_subtype

-- Prefer subclasses of `Semiring` over subclasses of `SubsemiringClass`.
/-- A subsemiring of a `Semiring` is a `Semiring`. -/
instance (priority := 75) toSemiring {R} [Semiring R] [SetLike S R] [SubsemiringClass S R] :
    Semiring s :=
  Subtype.coe_injective.semiring (↑) rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ => rfl
#align subsemiring_class.to_semiring SubsemiringClass.toSemiring

@[simp, norm_cast]
theorem coe_pow {R} [Semiring R] [SetLike S R] [SubsemiringClass S R] (x : s) (n : ℕ) :
    ((x ^ n : s) : R) = (x : R) ^ n := by
  induction' n with n ih
  -- ⊢ ↑(x ^ Nat.zero) = ↑x ^ Nat.zero
  · simp
    -- 🎉 no goals
  · simp [pow_succ, ih]
    -- 🎉 no goals
#align subsemiring_class.coe_pow SubsemiringClass.coe_pow

/-- A subsemiring of a `CommSemiring` is a `CommSemiring`. -/
instance toCommSemiring {R} [CommSemiring R] [SetLike S R] [SubsemiringClass S R] :
    CommSemiring s :=
  Subtype.coe_injective.commSemiring (↑) rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ => rfl
#align subsemiring_class.to_comm_semiring SubsemiringClass.toCommSemiring

/-- A subsemiring of an `OrderedSemiring` is an `OrderedSemiring`. -/
instance toOrderedSemiring {R} [OrderedSemiring R] [SetLike S R] [SubsemiringClass S R] :
    OrderedSemiring s :=
  Subtype.coe_injective.orderedSemiring (↑) rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl
#align subsemiring_class.to_ordered_semiring SubsemiringClass.toOrderedSemiring

/-- A subsemiring of a `StrictOrderedSemiring` is a `StrictOrderedSemiring`. -/
instance toStrictOrderedSemiring {R} [StrictOrderedSemiring R] [SetLike S R]
    [SubsemiringClass S R] : StrictOrderedSemiring s :=
  Subtype.coe_injective.strictOrderedSemiring (↑) rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl
#align subsemiring_class.to_strict_ordered_semiring SubsemiringClass.toStrictOrderedSemiring

/-- A subsemiring of an `OrderedCommSemiring` is an `OrderedCommSemiring`. -/
instance toOrderedCommSemiring {R} [OrderedCommSemiring R] [SetLike S R] [SubsemiringClass S R] :
    OrderedCommSemiring s :=
  Subtype.coe_injective.orderedCommSemiring (↑) rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl
#align subsemiring_class.to_ordered_comm_semiring SubsemiringClass.toOrderedCommSemiring

/-- A subsemiring of a `StrictOrderedCommSemiring` is a `StrictOrderedCommSemiring`. -/
instance toStrictOrderedCommSemiring {R} [StrictOrderedCommSemiring R] [SetLike S R]
    [SubsemiringClass S R] : StrictOrderedCommSemiring s :=
  Subtype.coe_injective.strictOrderedCommSemiring (↑) rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl
#align subsemiring_class.to_strict_ordered_comm_semiring SubsemiringClass.toStrictOrderedCommSemiring

/-- A subsemiring of a `LinearOrderedSemiring` is a `LinearOrderedSemiring`. -/
instance toLinearOrderedSemiring {R} [LinearOrderedSemiring R] [SetLike S R]
    [SubsemiringClass S R] : LinearOrderedSemiring s :=
  Subtype.coe_injective.linearOrderedSemiring (↑) rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) fun _ _ => rfl
#align subsemiring_class.to_linear_ordered_semiring SubsemiringClass.toLinearOrderedSemiring

/-- A subsemiring of a `LinearOrderedCommSemiring` is a `LinearOrderedCommSemiring`. -/
instance toLinearOrderedCommSemiring {R} [LinearOrderedCommSemiring R] [SetLike S R]
    [SubsemiringClass S R] : LinearOrderedCommSemiring s :=
  Subtype.coe_injective.linearOrderedCommSemiring (↑) rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) fun _ _ => rfl
#align subsemiring_class.to_linear_ordered_comm_semiring SubsemiringClass.toLinearOrderedCommSemiring

end SubsemiringClass

end SubsemiringClass

variable [NonAssocSemiring S] [NonAssocSemiring T]

/-- A subsemiring of a semiring `R` is a subset `s` that is both a multiplicative and an additive
submonoid. -/
structure Subsemiring (R : Type u) [NonAssocSemiring R] extends Submonoid R, AddSubmonoid R
#align subsemiring Subsemiring

/-- Reinterpret a `Subsemiring` as a `Submonoid`. -/
add_decl_doc Subsemiring.toSubmonoid

/-- Reinterpret a `Subsemiring` as an `AddSubmonoid`. -/
add_decl_doc Subsemiring.toAddSubmonoid

namespace Subsemiring

instance : SetLike (Subsemiring R) R
    where
  coe s := s.carrier
  coe_injective' p q h := by cases p; cases q; congr; exact SetLike.coe_injective' h
                             -- ⊢ { toSubmonoid := toSubmonoid✝, add_mem' := add_mem'✝, zero_mem' := zero_mem' …
                                      -- ⊢ { toSubmonoid := toSubmonoid✝¹, add_mem' := add_mem'✝¹, zero_mem' := zero_me …
                                               -- ⊢ toSubmonoid✝¹ = toSubmonoid✝
                                                      -- 🎉 no goals

instance : SubsemiringClass (Subsemiring R) R
    where
  zero_mem := zero_mem'
  add_mem {s} := AddSubsemigroup.add_mem' s.toAddSubmonoid.toAddSubsemigroup
  one_mem {s} := Submonoid.one_mem' s.toSubmonoid
  mul_mem {s} := Subsemigroup.mul_mem' s.toSubmonoid.toSubsemigroup

@[simp]
theorem mem_toSubmonoid {s : Subsemiring R} {x : R} : x ∈ s.toSubmonoid ↔ x ∈ s :=
  Iff.rfl
#align subsemiring.mem_to_submonoid Subsemiring.mem_toSubmonoid

-- `@[simp]` -- Porting note: simp can prove this
theorem mem_carrier {s : Subsemiring R} {x : R} : x ∈ s.carrier ↔ x ∈ s :=
  Iff.rfl
#align subsemiring.mem_carrier Subsemiring.mem_carrier

/-- Two subsemirings are equal if they have the same elements. -/
@[ext]
theorem ext {S T : Subsemiring R} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h
#align subsemiring.ext Subsemiring.ext

/-- Copy of a subsemiring with a new `carrier` equal to the old one. Useful to fix definitional
equalities.-/
protected def copy (S : Subsemiring R) (s : Set R) (hs : s = ↑S) : Subsemiring R :=
  { S.toAddSubmonoid.copy s hs, S.toSubmonoid.copy s hs with carrier := s }
#align subsemiring.copy Subsemiring.copy

@[simp]
theorem coe_copy (S : Subsemiring R) (s : Set R) (hs : s = ↑S) : (S.copy s hs : Set R) = s :=
  rfl
#align subsemiring.coe_copy Subsemiring.coe_copy

theorem copy_eq (S : Subsemiring R) (s : Set R) (hs : s = ↑S) : S.copy s hs = S :=
  SetLike.coe_injective hs
#align subsemiring.copy_eq Subsemiring.copy_eq

theorem toSubmonoid_injective : Function.Injective (toSubmonoid : Subsemiring R → Submonoid R)
  | _, _, h => ext (SetLike.ext_iff.mp h : _)
#align subsemiring.to_submonoid_injective Subsemiring.toSubmonoid_injective

@[mono]
theorem toSubmonoid_strictMono : StrictMono (toSubmonoid : Subsemiring R → Submonoid R) :=
  fun _ _ => id
#align subsemiring.to_submonoid_strict_mono Subsemiring.toSubmonoid_strictMono

@[mono]
theorem toSubmonoid_mono : Monotone (toSubmonoid : Subsemiring R → Submonoid R) :=
  toSubmonoid_strictMono.monotone
#align subsemiring.to_submonoid_mono Subsemiring.toSubmonoid_mono

theorem toAddSubmonoid_injective :
    Function.Injective (toAddSubmonoid : Subsemiring R → AddSubmonoid R)
  | _, _, h => ext (SetLike.ext_iff.mp h : _)
#align subsemiring.to_add_submonoid_injective Subsemiring.toAddSubmonoid_injective

@[mono]
theorem toAddSubmonoid_strictMono : StrictMono (toAddSubmonoid : Subsemiring R → AddSubmonoid R) :=
  fun _ _ => id
#align subsemiring.to_add_submonoid_strict_mono Subsemiring.toAddSubmonoid_strictMono

@[mono]
theorem toAddSubmonoid_mono : Monotone (toAddSubmonoid : Subsemiring R → AddSubmonoid R) :=
  toAddSubmonoid_strictMono.monotone
#align subsemiring.to_add_submonoid_mono Subsemiring.toAddSubmonoid_mono

/-- Construct a `Subsemiring R` from a set `s`, a submonoid `sm`, and an additive
submonoid `sa` such that `x ∈ s ↔ x ∈ sm ↔ x ∈ sa`. -/
protected def mk' (s : Set R) (sm : Submonoid R) (hm : ↑sm = s) (sa : AddSubmonoid R)
    (ha : ↑sa = s) : Subsemiring R where
  carrier := s
  zero_mem' := by exact ha ▸ sa.zero_mem
                  -- 🎉 no goals
                 -- 🎉 no goals
  one_mem' := by exact hm ▸ sm.one_mem
                       -- 🎉 no goals
                       -- 🎉 no goals
  add_mem' {x y} := by simpa only [← ha] using sa.add_mem
  mul_mem' {x y} := by simpa only [← hm] using sm.mul_mem
#align subsemiring.mk' Subsemiring.mk'

@[simp]
theorem coe_mk' {s : Set R} {sm : Submonoid R} (hm : ↑sm = s) {sa : AddSubmonoid R} (ha : ↑sa = s) :
    (Subsemiring.mk' s sm hm sa ha : Set R) = s :=
  rfl
#align subsemiring.coe_mk' Subsemiring.coe_mk'

@[simp]
theorem mem_mk' {s : Set R} {sm : Submonoid R} (hm : ↑sm = s) {sa : AddSubmonoid R} (ha : ↑sa = s)
    {x : R} : x ∈ Subsemiring.mk' s sm hm sa ha ↔ x ∈ s :=
  Iff.rfl
#align subsemiring.mem_mk' Subsemiring.mem_mk'

@[simp]
theorem mk'_toSubmonoid {s : Set R} {sm : Submonoid R} (hm : ↑sm = s) {sa : AddSubmonoid R}
    (ha : ↑sa = s) : (Subsemiring.mk' s sm hm sa ha).toSubmonoid = sm :=
  SetLike.coe_injective hm.symm
#align subsemiring.mk'_to_submonoid Subsemiring.mk'_toSubmonoid

@[simp]
theorem mk'_toAddSubmonoid {s : Set R} {sm : Submonoid R} (hm : ↑sm = s) {sa : AddSubmonoid R}
    (ha : ↑sa = s) : (Subsemiring.mk' s sm hm sa ha).toAddSubmonoid = sa :=
  SetLike.coe_injective ha.symm
#align subsemiring.mk'_to_add_submonoid Subsemiring.mk'_toAddSubmonoid

end Subsemiring

namespace Subsemiring

variable (s : Subsemiring R)

/-- A subsemiring contains the semiring's 1. -/
protected theorem one_mem : (1 : R) ∈ s :=
  one_mem s
#align subsemiring.one_mem Subsemiring.one_mem

/-- A subsemiring contains the semiring's 0. -/
protected theorem zero_mem : (0 : R) ∈ s :=
  zero_mem s
#align subsemiring.zero_mem Subsemiring.zero_mem

/-- A subsemiring is closed under multiplication. -/
protected theorem mul_mem {x y : R} : x ∈ s → y ∈ s → x * y ∈ s :=
  mul_mem
#align subsemiring.mul_mem Subsemiring.mul_mem

/-- A subsemiring is closed under addition. -/
protected theorem add_mem {x y : R} : x ∈ s → y ∈ s → x + y ∈ s :=
  add_mem
#align subsemiring.add_mem Subsemiring.add_mem

/-- Product of a list of elements in a `Subsemiring` is in the `Subsemiring`. -/
nonrec theorem list_prod_mem {R : Type*} [Semiring R] (s : Subsemiring R) {l : List R} :
    (∀ x ∈ l, x ∈ s) → l.prod ∈ s :=
  list_prod_mem
#align subsemiring.list_prod_mem Subsemiring.list_prod_mem

/-- Sum of a list of elements in a `Subsemiring` is in the `Subsemiring`. -/
protected theorem list_sum_mem {l : List R} : (∀ x ∈ l, x ∈ s) → l.sum ∈ s :=
  list_sum_mem
#align subsemiring.list_sum_mem Subsemiring.list_sum_mem

/-- Product of a multiset of elements in a `Subsemiring` of a `CommSemiring`
    is in the `Subsemiring`. -/
protected theorem multiset_prod_mem {R} [CommSemiring R] (s : Subsemiring R) (m : Multiset R) :
    (∀ a ∈ m, a ∈ s) → m.prod ∈ s :=
  multiset_prod_mem m
#align subsemiring.multiset_prod_mem Subsemiring.multiset_prod_mem

/-- Sum of a multiset of elements in a `Subsemiring` of a `Semiring` is
in the `add_subsemiring`. -/
protected theorem multiset_sum_mem (m : Multiset R) : (∀ a ∈ m, a ∈ s) → m.sum ∈ s :=
  multiset_sum_mem m
#align subsemiring.multiset_sum_mem Subsemiring.multiset_sum_mem

/-- Product of elements of a subsemiring of a `CommSemiring` indexed by a `Finset` is in the
    subsemiring. -/
protected theorem prod_mem {R : Type*} [CommSemiring R] (s : Subsemiring R) {ι : Type*}
    {t : Finset ι} {f : ι → R} (h : ∀ c ∈ t, f c ∈ s) : (∏ i in t, f i) ∈ s :=
  prod_mem h
#align subsemiring.prod_mem Subsemiring.prod_mem

/-- Sum of elements in a `Subsemiring` of a `Semiring` indexed by a `Finset`
is in the `add_subsemiring`. -/
protected theorem sum_mem (s : Subsemiring R) {ι : Type*} {t : Finset ι} {f : ι → R}
    (h : ∀ c ∈ t, f c ∈ s) : (∑ i in t, f i) ∈ s :=
  sum_mem h
#align subsemiring.sum_mem Subsemiring.sum_mem

/-- A subsemiring of a `NonAssocSemiring` inherits a `NonAssocSemiring` structure -/
instance toNonAssocSemiring : NonAssocSemiring s :=
  -- Porting note: this used to be a specialized instance which needed to be expensively unified.
  SubsemiringClass.toNonAssocSemiring _
#align subsemiring.to_non_assoc_semiring Subsemiring.toNonAssocSemiring

@[simp, norm_cast]
theorem coe_one : ((1 : s) : R) = (1 : R) :=
  rfl
#align subsemiring.coe_one Subsemiring.coe_one

@[simp, norm_cast]
theorem coe_zero : ((0 : s) : R) = (0 : R) :=
  rfl
#align subsemiring.coe_zero Subsemiring.coe_zero

@[simp, norm_cast]
theorem coe_add (x y : s) : ((x + y : s) : R) = (x + y : R) :=
  rfl
#align subsemiring.coe_add Subsemiring.coe_add

@[simp, norm_cast]
theorem coe_mul (x y : s) : ((x * y : s) : R) = (x * y : R) :=
  rfl
#align subsemiring.coe_mul Subsemiring.coe_mul

instance nontrivial [Nontrivial R] : Nontrivial s :=
  nontrivial_of_ne 0 1 fun H => zero_ne_one (congr_arg Subtype.val H)
#align subsemiring.nontrivial Subsemiring.nontrivial

protected theorem pow_mem {R : Type*} [Semiring R] (s : Subsemiring R) {x : R} (hx : x ∈ s)
    (n : ℕ) : x ^ n ∈ s :=
  pow_mem hx n
#align subsemiring.pow_mem Subsemiring.pow_mem

instance noZeroDivisors [NoZeroDivisors R] : NoZeroDivisors s where
  eq_zero_or_eq_zero_of_mul_eq_zero {_ _} h :=
    (eq_zero_or_eq_zero_of_mul_eq_zero <| Subtype.ext_iff.mp h).imp Subtype.eq Subtype.eq
#align subsemiring.no_zero_divisors Subsemiring.noZeroDivisors

/-- A subsemiring of a `Semiring` is a `Semiring`. -/
instance toSemiring {R} [Semiring R] (s : Subsemiring R) : Semiring s :=
  { s.toNonAssocSemiring, s.toSubmonoid.toMonoid with }
#align subsemiring.to_semiring Subsemiring.toSemiring

@[simp, norm_cast]
theorem coe_pow {R} [Semiring R] (s : Subsemiring R) (x : s) (n : ℕ) :
    ((x ^ n : s) : R) = (x : R) ^ n := by
  induction' n with n ih
  -- ⊢ ↑(x ^ Nat.zero) = ↑x ^ Nat.zero
  · simp
    -- 🎉 no goals
  · simp [pow_succ, ih]
    -- 🎉 no goals
#align subsemiring.coe_pow Subsemiring.coe_pow

/-- A subsemiring of a `CommSemiring` is a `CommSemiring`. -/
instance toCommSemiring {R} [CommSemiring R] (s : Subsemiring R) : CommSemiring s :=
  { s.toSemiring with mul_comm := fun _ _ => Subtype.eq <| mul_comm _ _ }
#align subsemiring.to_comm_semiring Subsemiring.toCommSemiring

/-- The natural ring hom from a subsemiring of semiring `R` to `R`. -/
def subtype : s →+* R :=
  { s.toSubmonoid.subtype, s.toAddSubmonoid.subtype with toFun := (↑) }
#align subsemiring.subtype Subsemiring.subtype

@[simp]
theorem coe_subtype : ⇑s.subtype = ((↑) : s → R) :=
  rfl
#align subsemiring.coe_subtype Subsemiring.coe_subtype

/-- A subsemiring of an `OrderedSemiring` is an `OrderedSemiring`. -/
instance toOrderedSemiring {R} [OrderedSemiring R] (s : Subsemiring R) : OrderedSemiring s :=
  Subtype.coe_injective.orderedSemiring (↑) rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl
#align subsemiring.to_ordered_semiring Subsemiring.toOrderedSemiring

/-- A subsemiring of a `StrictOrderedSemiring` is a `StrictOrderedSemiring`. -/
instance toStrictOrderedSemiring {R} [StrictOrderedSemiring R] (s : Subsemiring R) :
    StrictOrderedSemiring s :=
  Subtype.coe_injective.strictOrderedSemiring (↑) rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl
#align subsemiring.to_strict_ordered_semiring Subsemiring.toStrictOrderedSemiring

/-- A subsemiring of an `OrderedCommSemiring` is an `OrderedCommSemiring`. -/
instance toOrderedCommSemiring {R} [OrderedCommSemiring R] (s : Subsemiring R) :
    OrderedCommSemiring s :=
  Subtype.coe_injective.orderedCommSemiring (↑) rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl
#align subsemiring.to_ordered_comm_semiring Subsemiring.toOrderedCommSemiring

/-- A subsemiring of a `StrictOrderedCommSemiring` is a `StrictOrderedCommSemiring`. -/
instance toStrictOrderedCommSemiring {R} [StrictOrderedCommSemiring R] (s : Subsemiring R) :
    StrictOrderedCommSemiring s :=
  Subtype.coe_injective.strictOrderedCommSemiring (↑) rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl
#align subsemiring.to_strict_ordered_comm_semiring Subsemiring.toStrictOrderedCommSemiring

/-- A subsemiring of a `LinearOrderedSemiring` is a `LinearOrderedSemiring`. -/
instance toLinearOrderedSemiring {R} [LinearOrderedSemiring R] (s : Subsemiring R) :
    LinearOrderedSemiring s :=
  Subtype.coe_injective.linearOrderedSemiring (↑) rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) fun _ _ => rfl
#align subsemiring.to_linear_ordered_semiring Subsemiring.toLinearOrderedSemiring

/-- A subsemiring of a `LinearOrderedCommSemiring` is a `LinearOrderedCommSemiring`. -/
instance toLinearOrderedCommSemiring {R} [LinearOrderedCommSemiring R] (s : Subsemiring R) :
    LinearOrderedCommSemiring s :=
  Subtype.coe_injective.linearOrderedCommSemiring (↑) rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) fun _ _ => rfl
#align subsemiring.to_linear_ordered_comm_semiring Subsemiring.toLinearOrderedCommSemiring

protected theorem nsmul_mem {x : R} (hx : x ∈ s) (n : ℕ) : n • x ∈ s :=
  nsmul_mem hx n
#align subsemiring.nsmul_mem Subsemiring.nsmul_mem

@[simp]
theorem coe_toSubmonoid (s : Subsemiring R) : (s.toSubmonoid : Set R) = s :=
  rfl
#align subsemiring.coe_to_submonoid Subsemiring.coe_toSubmonoid

-- Porting note: adding this as `simp`-normal form for `coe_toAddSubmonoid`
@[simp]
theorem coe_carrier_toSubmonoid (s : Subsemiring R) : (s.toSubmonoid.carrier : Set R) = s :=
  rfl

-- Porting note: can be proven using `SetLike` so removing `@[simp]`
theorem mem_toAddSubmonoid {s : Subsemiring R} {x : R} : x ∈ s.toAddSubmonoid ↔ x ∈ s :=
  Iff.rfl
#align subsemiring.mem_to_add_submonoid Subsemiring.mem_toAddSubmonoid

-- Porting note: new normal form is `coe_carrier_toSubmonoid` so removing `@[simp]`
theorem coe_toAddSubmonoid (s : Subsemiring R) : (s.toAddSubmonoid : Set R) = s :=
  rfl
#align subsemiring.coe_to_add_submonoid Subsemiring.coe_toAddSubmonoid

/-- The subsemiring `R` of the semiring `R`. -/
instance : Top (Subsemiring R) :=
  ⟨{ (⊤ : Submonoid R), (⊤ : AddSubmonoid R) with }⟩

@[simp]
theorem mem_top (x : R) : x ∈ (⊤ : Subsemiring R) :=
  Set.mem_univ x
#align subsemiring.mem_top Subsemiring.mem_top

@[simp]
theorem coe_top : ((⊤ : Subsemiring R) : Set R) = Set.univ :=
  rfl
#align subsemiring.coe_top Subsemiring.coe_top

/-- The ring equiv between the top element of `Subsemiring R` and `R`. -/
@[simps]
def topEquiv : (⊤ : Subsemiring R) ≃+* R where
  toFun r := r
  invFun r := ⟨r, Subsemiring.mem_top r⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' := (⊤ : Subsemiring R).coe_mul
  map_add' := (⊤ : Subsemiring R).coe_add
#align subsemiring.top_equiv Subsemiring.topEquiv

/-- The preimage of a subsemiring along a ring homomorphism is a subsemiring. -/
def comap (f : R →+* S) (s : Subsemiring S) : Subsemiring R :=
  { s.toSubmonoid.comap (f : R →* S), s.toAddSubmonoid.comap (f : R →+ S) with carrier := f ⁻¹' s }
#align subsemiring.comap Subsemiring.comap

@[simp]
theorem coe_comap (s : Subsemiring S) (f : R →+* S) : (s.comap f : Set R) = f ⁻¹' s :=
  rfl
#align subsemiring.coe_comap Subsemiring.coe_comap

@[simp]
theorem mem_comap {s : Subsemiring S} {f : R →+* S} {x : R} : x ∈ s.comap f ↔ f x ∈ s :=
  Iff.rfl
#align subsemiring.mem_comap Subsemiring.mem_comap

theorem comap_comap (s : Subsemiring T) (g : S →+* T) (f : R →+* S) :
    (s.comap g).comap f = s.comap (g.comp f) :=
  rfl
#align subsemiring.comap_comap Subsemiring.comap_comap

/-- The image of a subsemiring along a ring homomorphism is a subsemiring. -/
def map (f : R →+* S) (s : Subsemiring R) : Subsemiring S :=
  { s.toSubmonoid.map (f : R →* S), s.toAddSubmonoid.map (f : R →+ S) with carrier := f '' s }
#align subsemiring.map Subsemiring.map

@[simp]
theorem coe_map (f : R →+* S) (s : Subsemiring R) : (s.map f : Set S) = f '' s :=
  rfl
#align subsemiring.coe_map Subsemiring.coe_map

@[simp]
theorem mem_map {f : R →+* S} {s : Subsemiring R} {y : S} : y ∈ s.map f ↔ ∃ x ∈ s, f x = y := by
  -- Porting note: was `exact Set.mem_image_iff_bex`
  convert Set.mem_image_iff_bex (f := f) (s := s.carrier) (y := y) using 1
  -- ⊢ (∃ x, x ∈ s ∧ ↑f x = y) ↔ ∃ x x_1, ↑f x = y
  simp
  -- 🎉 no goals
#align subsemiring.mem_map Subsemiring.mem_map

@[simp]
theorem map_id : s.map (RingHom.id R) = s :=
  SetLike.coe_injective <| Set.image_id _
#align subsemiring.map_id Subsemiring.map_id

theorem map_map (g : S →+* T) (f : R →+* S) : (s.map f).map g = s.map (g.comp f) :=
  SetLike.coe_injective <| Set.image_image _ _ _
#align subsemiring.map_map Subsemiring.map_map

theorem map_le_iff_le_comap {f : R →+* S} {s : Subsemiring R} {t : Subsemiring S} :
    s.map f ≤ t ↔ s ≤ t.comap f :=
  Set.image_subset_iff
#align subsemiring.map_le_iff_le_comap Subsemiring.map_le_iff_le_comap

theorem gc_map_comap (f : R →+* S) : GaloisConnection (map f) (comap f) := fun _ _ =>
  map_le_iff_le_comap
#align subsemiring.gc_map_comap Subsemiring.gc_map_comap

/-- A subsemiring is isomorphic to its image under an injective function -/
noncomputable def equivMapOfInjective (f : R →+* S) (hf : Function.Injective f) : s ≃+* s.map f :=
  { Equiv.Set.image f s hf with
    map_mul' := fun _ _ => Subtype.ext (f.map_mul _ _)
    map_add' := fun _ _ => Subtype.ext (f.map_add _ _) }
#align subsemiring.equiv_map_of_injective Subsemiring.equivMapOfInjective

@[simp]
theorem coe_equivMapOfInjective_apply (f : R →+* S) (hf : Function.Injective f) (x : s) :
    (equivMapOfInjective s f hf x : S) = f x :=
  rfl
#align subsemiring.coe_equiv_map_of_injective_apply Subsemiring.coe_equivMapOfInjective_apply

end Subsemiring

namespace RingHom

variable (g : S →+* T) (f : R →+* S)

/-- The range of a ring homomorphism is a subsemiring. See Note [range copy pattern]. -/
def rangeS : Subsemiring S :=
  ((⊤ : Subsemiring R).map f).copy (Set.range f) Set.image_univ.symm
#align ring_hom.srange RingHom.rangeS

@[simp]
theorem coe_rangeS : (f.rangeS : Set S) = Set.range f :=
  rfl
#align ring_hom.coe_srange RingHom.coe_rangeS

@[simp]
theorem mem_rangeS {f : R →+* S} {y : S} : y ∈ f.rangeS ↔ ∃ x, f x = y :=
  Iff.rfl
#align ring_hom.mem_srange RingHom.mem_rangeS

theorem rangeS_eq_map (f : R →+* S) : f.rangeS = (⊤ : Subsemiring R).map f := by
  ext
  -- ⊢ x✝ ∈ rangeS f ↔ x✝ ∈ Subsemiring.map f ⊤
  simp
  -- 🎉 no goals
#align ring_hom.srange_eq_map RingHom.rangeS_eq_map

theorem mem_rangeS_self (f : R →+* S) (x : R) : f x ∈ f.rangeS :=
  mem_rangeS.mpr ⟨x, rfl⟩
#align ring_hom.mem_srange_self RingHom.mem_rangeS_self

theorem map_rangeS : f.rangeS.map g = (g.comp f).rangeS := by
  simpa only [rangeS_eq_map] using (⊤ : Subsemiring R).map_map g f
  -- 🎉 no goals
#align ring_hom.map_srange RingHom.map_rangeS

/-- The range of a morphism of semirings is a fintype, if the domain is a fintype.
Note: this instance can form a diamond with `Subtype.fintype` in the
  presence of `Fintype S`.-/
instance fintypeRangeS [Fintype R] [DecidableEq S] (f : R →+* S) : Fintype (rangeS f) :=
  Set.fintypeRange f
#align ring_hom.fintype_srange RingHom.fintypeRangeS

end RingHom

namespace Subsemiring

instance : Bot (Subsemiring R) :=
  ⟨(Nat.castRingHom R).rangeS⟩

instance : Inhabited (Subsemiring R) :=
  ⟨⊥⟩

theorem coe_bot : ((⊥ : Subsemiring R) : Set R) = Set.range ((↑) : ℕ → R) :=
  (Nat.castRingHom R).coe_rangeS
#align subsemiring.coe_bot Subsemiring.coe_bot

theorem mem_bot {x : R} : x ∈ (⊥ : Subsemiring R) ↔ ∃ n : ℕ, ↑n = x :=
  RingHom.mem_rangeS
#align subsemiring.mem_bot Subsemiring.mem_bot

/-- The inf of two subsemirings is their intersection. -/
instance : Inf (Subsemiring R) :=
  ⟨fun s t =>
    { s.toSubmonoid ⊓ t.toSubmonoid, s.toAddSubmonoid ⊓ t.toAddSubmonoid with carrier := s ∩ t }⟩

@[simp]
theorem coe_inf (p p' : Subsemiring R) : ((p ⊓ p' : Subsemiring R) : Set R) = (p : Set R) ∩ p' :=
  rfl
#align subsemiring.coe_inf Subsemiring.coe_inf

@[simp]
theorem mem_inf {p p' : Subsemiring R} {x : R} : x ∈ p ⊓ p' ↔ x ∈ p ∧ x ∈ p' :=
  Iff.rfl
#align subsemiring.mem_inf Subsemiring.mem_inf

instance : InfSet (Subsemiring R) :=
  ⟨fun s =>
    Subsemiring.mk' (⋂ t ∈ s, ↑t) (⨅ t ∈ s, Subsemiring.toSubmonoid t) (by simp)
                                                                           -- 🎉 no goals
      (⨅ t ∈ s, Subsemiring.toAddSubmonoid t)
      (by simp)⟩
          -- 🎉 no goals

@[simp, norm_cast]
theorem coe_sInf (S : Set (Subsemiring R)) : ((sInf S : Subsemiring R) : Set R) = ⋂ s ∈ S, ↑s :=
  rfl
#align subsemiring.coe_Inf Subsemiring.coe_sInf

theorem mem_sInf {S : Set (Subsemiring R)} {x : R} : x ∈ sInf S ↔ ∀ p ∈ S, x ∈ p :=
  Set.mem_iInter₂
#align subsemiring.mem_Inf Subsemiring.mem_sInf

@[simp]
theorem sInf_toSubmonoid (s : Set (Subsemiring R)) :
    (sInf s).toSubmonoid = ⨅ t ∈ s, Subsemiring.toSubmonoid t :=
  mk'_toSubmonoid _ _
#align subsemiring.Inf_to_submonoid Subsemiring.sInf_toSubmonoid

@[simp]
theorem sInf_toAddSubmonoid (s : Set (Subsemiring R)) :
    (sInf s).toAddSubmonoid = ⨅ t ∈ s, Subsemiring.toAddSubmonoid t :=
  mk'_toAddSubmonoid _ _
#align subsemiring.Inf_to_add_submonoid Subsemiring.sInf_toAddSubmonoid

/-- Subsemirings of a semiring form a complete lattice. -/
instance : CompleteLattice (Subsemiring R) :=
  { completeLatticeOfInf (Subsemiring R) fun _ =>
      IsGLB.of_image
        (fun {s t : Subsemiring R} => show (s : Set R) ⊆ t ↔ s ≤ t from SetLike.coe_subset_coe)
        isGLB_biInf with
    bot := ⊥
    bot_le := fun s _ hx =>
      let ⟨n, hn⟩ := mem_bot.1 hx
      hn ▸ coe_nat_mem s n
    top := ⊤
    le_top := fun _ _ _ => trivial
    inf := (· ⊓ ·)
    inf_le_left := fun _ _ _ => And.left
    inf_le_right := fun _ _ _ => And.right
    le_inf := fun _ _ _ h₁ h₂ _ hx => ⟨h₁ hx, h₂ hx⟩ }

theorem eq_top_iff' (A : Subsemiring R) : A = ⊤ ↔ ∀ x : R, x ∈ A :=
  eq_top_iff.trans ⟨fun h m => h <| mem_top m, fun h m _ => h m⟩
#align subsemiring.eq_top_iff' Subsemiring.eq_top_iff'

section Center

/-- The center of a semiring `R` is the set of elements that commute with everything in `R` -/
def center (R) [Semiring R] : Subsemiring R :=
  { Submonoid.center R with
    carrier := Set.center R
    zero_mem' := Set.zero_mem_center R
    add_mem' := Set.add_mem_center }
#align subsemiring.center Subsemiring.center

theorem coe_center (R) [Semiring R] : ↑(center R) = Set.center R :=
  rfl
#align subsemiring.coe_center Subsemiring.coe_center

@[simp]
theorem center_toSubmonoid (R) [Semiring R] : (center R).toSubmonoid = Submonoid.center R :=
  rfl
#align subsemiring.center_to_submonoid Subsemiring.center_toSubmonoid

theorem mem_center_iff {R} [Semiring R] {z : R} : z ∈ center R ↔ ∀ g, g * z = z * g :=
  Iff.rfl
#align subsemiring.mem_center_iff Subsemiring.mem_center_iff

instance decidableMemCenter {R} [Semiring R] [DecidableEq R] [Fintype R] :
    DecidablePred (· ∈ center R) := fun _ => decidable_of_iff' _ mem_center_iff
#align subsemiring.decidable_mem_center Subsemiring.decidableMemCenter

@[simp]
theorem center_eq_top (R) [CommSemiring R] : center R = ⊤ :=
  SetLike.coe_injective (Set.center_eq_univ R)
#align subsemiring.center_eq_top Subsemiring.center_eq_top

/-- The center is commutative. -/
instance commSemiring {R} [Semiring R] : CommSemiring (center R) :=
  { Submonoid.center.commMonoid, (center R).toSemiring with }

end Center

section Centralizer

/-- The centralizer of a set as subsemiring. -/
def centralizer {R} [Semiring R] (s : Set R) : Subsemiring R :=
  { Submonoid.centralizer s with
    carrier := s.centralizer
    zero_mem' := Set.zero_mem_centralizer _
    add_mem' := Set.add_mem_centralizer }
#align subsemiring.centralizer Subsemiring.centralizer

@[simp, norm_cast]
theorem coe_centralizer {R} [Semiring R] (s : Set R) : (centralizer s : Set R) = s.centralizer :=
  rfl
#align subsemiring.coe_centralizer Subsemiring.coe_centralizer

theorem centralizer_toSubmonoid {R} [Semiring R] (s : Set R) :
    (centralizer s).toSubmonoid = Submonoid.centralizer s :=
  rfl
#align subsemiring.centralizer_to_submonoid Subsemiring.centralizer_toSubmonoid

theorem mem_centralizer_iff {R} [Semiring R] {s : Set R} {z : R} :
    z ∈ centralizer s ↔ ∀ g ∈ s, g * z = z * g :=
  Iff.rfl
#align subsemiring.mem_centralizer_iff Subsemiring.mem_centralizer_iff

theorem center_le_centralizer {R} [Semiring R] (s) : center R ≤ centralizer s :=
  s.center_subset_centralizer
#align subsemiring.center_le_centralizer Subsemiring.center_le_centralizer

theorem centralizer_le {R} [Semiring R] (s t : Set R) (h : s ⊆ t) : centralizer t ≤ centralizer s :=
  Set.centralizer_subset h
#align subsemiring.centralizer_le Subsemiring.centralizer_le

@[simp]
theorem centralizer_eq_top_iff_subset {R} [Semiring R] {s : Set R} :
    centralizer s = ⊤ ↔ s ⊆ center R :=
  SetLike.ext'_iff.trans Set.centralizer_eq_top_iff_subset
#align subsemiring.centralizer_eq_top_iff_subset Subsemiring.centralizer_eq_top_iff_subset

@[simp]
theorem centralizer_univ {R} [Semiring R] : centralizer Set.univ = center R :=
  SetLike.ext' (Set.centralizer_univ R)
#align subsemiring.centralizer_univ Subsemiring.centralizer_univ

end Centralizer

/-- The `Subsemiring` generated by a set. -/
def closure (s : Set R) : Subsemiring R :=
  sInf { S | s ⊆ S }
#align subsemiring.closure Subsemiring.closure

theorem mem_closure {x : R} {s : Set R} : x ∈ closure s ↔ ∀ S : Subsemiring R, s ⊆ S → x ∈ S :=
  mem_sInf
#align subsemiring.mem_closure Subsemiring.mem_closure

/-- The subsemiring generated by a set includes the set. -/
@[simp]
theorem subset_closure {s : Set R} : s ⊆ closure s := fun _ hx => mem_closure.2 fun _ hS => hS hx
#align subsemiring.subset_closure Subsemiring.subset_closure

theorem not_mem_of_not_mem_closure {s : Set R} {P : R} (hP : P ∉ closure s) : P ∉ s := fun h =>
  hP (subset_closure h)
#align subsemiring.not_mem_of_not_mem_closure Subsemiring.not_mem_of_not_mem_closure

/-- A subsemiring `S` includes `closure s` if and only if it includes `s`. -/
@[simp]
theorem closure_le {s : Set R} {t : Subsemiring R} : closure s ≤ t ↔ s ⊆ t :=
  ⟨Set.Subset.trans subset_closure, fun h => sInf_le h⟩
#align subsemiring.closure_le Subsemiring.closure_le

/-- Subsemiring closure of a set is monotone in its argument: if `s ⊆ t`,
then `closure s ≤ closure t`. -/
theorem closure_mono ⦃s t : Set R⦄ (h : s ⊆ t) : closure s ≤ closure t :=
  closure_le.2 <| Set.Subset.trans h subset_closure
#align subsemiring.closure_mono Subsemiring.closure_mono

theorem closure_eq_of_le {s : Set R} {t : Subsemiring R} (h₁ : s ⊆ t) (h₂ : t ≤ closure s) :
    closure s = t :=
  le_antisymm (closure_le.2 h₁) h₂
#align subsemiring.closure_eq_of_le Subsemiring.closure_eq_of_le

theorem mem_map_equiv {f : R ≃+* S} {K : Subsemiring R} {x : S} :
    x ∈ K.map (f : R →+* S) ↔ f.symm x ∈ K := by
  convert @Set.mem_image_equiv _ _ (↑K) f.toEquiv x using 1
  -- 🎉 no goals
#align subsemiring.mem_map_equiv Subsemiring.mem_map_equiv

theorem map_equiv_eq_comap_symm (f : R ≃+* S) (K : Subsemiring R) :
    K.map (f : R →+* S) = K.comap f.symm :=
  SetLike.coe_injective (f.toEquiv.image_eq_preimage K)
#align subsemiring.map_equiv_eq_comap_symm Subsemiring.map_equiv_eq_comap_symm

theorem comap_equiv_eq_map_symm (f : R ≃+* S) (K : Subsemiring S) :
    K.comap (f : R →+* S) = K.map f.symm :=
  (map_equiv_eq_comap_symm f.symm K).symm
#align subsemiring.comap_equiv_eq_map_symm Subsemiring.comap_equiv_eq_map_symm

end Subsemiring

namespace Submonoid

/-- The additive closure of a submonoid is a subsemiring. -/
def subsemiringClosure (M : Submonoid R) : Subsemiring R :=
  { AddSubmonoid.closure (M : Set R) with
    one_mem' := AddSubmonoid.mem_closure.mpr fun _ hy => hy M.one_mem
    mul_mem' := MulMemClass.mul_mem_add_closure }
#align submonoid.subsemiring_closure Submonoid.subsemiringClosure

theorem subsemiringClosure_coe :
    (M.subsemiringClosure : Set R) = AddSubmonoid.closure (M : Set R) :=
  rfl
#align submonoid.subsemiring_closure_coe Submonoid.subsemiringClosure_coe

theorem subsemiringClosure_toAddSubmonoid :
    M.subsemiringClosure.toAddSubmonoid = AddSubmonoid.closure (M : Set R) :=
  rfl
#align submonoid.subsemiring_closure_to_add_submonoid Submonoid.subsemiringClosure_toAddSubmonoid

/-- The `Subsemiring` generated by a multiplicative submonoid coincides with the
`Subsemiring.closure` of the submonoid itself . -/
theorem subsemiringClosure_eq_closure : M.subsemiringClosure = Subsemiring.closure (M : Set R) := by
  ext
  -- ⊢ x✝ ∈ subsemiringClosure M ↔ x✝ ∈ Subsemiring.closure ↑M
  refine'
    ⟨fun hx => _, fun hx =>
      (Subsemiring.mem_closure.mp hx) M.subsemiringClosure fun s sM => _⟩
  <;> rintro - ⟨H1, rfl⟩
      -- ⊢ x✝ ∈ (fun t => ⋂ (_ : t ∈ {S | ↑M ⊆ ↑S}), ↑t) H1
      -- ⊢ s ∈ (fun t => ⋂ (_ : t ∈ {S | ↑M ⊆ ↑S}), ↑t) H1
  <;> rintro - ⟨H2, rfl⟩
      -- ⊢ x✝ ∈ (fun h => ↑H1) H2
      -- ⊢ s ∈ (fun h => ↑H1) H2
  · exact AddSubmonoid.mem_closure.mp hx H1.toAddSubmonoid H2
    -- 🎉 no goals
  · exact H2 sM
    -- 🎉 no goals
#align submonoid.subsemiring_closure_eq_closure Submonoid.subsemiringClosure_eq_closure

end Submonoid

namespace Subsemiring

@[simp]
theorem closure_submonoid_closure (s : Set R) : closure ↑(Submonoid.closure s) = closure s :=
  le_antisymm
    (closure_le.mpr fun _ hy =>
      (Submonoid.mem_closure.mp hy) (closure s).toSubmonoid subset_closure)
    (closure_mono Submonoid.subset_closure)
#align subsemiring.closure_submonoid_closure Subsemiring.closure_submonoid_closure

/-- The elements of the subsemiring closure of `M` are exactly the elements of the additive closure
of a multiplicative submonoid `M`. -/
theorem coe_closure_eq (s : Set R) :
    (closure s : Set R) = AddSubmonoid.closure (Submonoid.closure s : Set R) := by
  simp [← Submonoid.subsemiringClosure_toAddSubmonoid, Submonoid.subsemiringClosure_eq_closure]
  -- 🎉 no goals
#align subsemiring.coe_closure_eq Subsemiring.coe_closure_eq

theorem mem_closure_iff {s : Set R} {x} :
    x ∈ closure s ↔ x ∈ AddSubmonoid.closure (Submonoid.closure s : Set R) :=
  Set.ext_iff.mp (coe_closure_eq s) x
#align subsemiring.mem_closure_iff Subsemiring.mem_closure_iff

@[simp]
theorem closure_addSubmonoid_closure {s : Set R} :
    closure ↑(AddSubmonoid.closure s) = closure s := by
  ext x
  -- ⊢ x ∈ closure ↑(AddSubmonoid.closure s) ↔ x ∈ closure s
  refine' ⟨fun hx => _, fun hx => closure_mono AddSubmonoid.subset_closure hx⟩
  -- ⊢ x ∈ closure s
  rintro - ⟨H, rfl⟩
  -- ⊢ x ∈ (fun t => ⋂ (_ : t ∈ {S | s ⊆ ↑S}), ↑t) H
  rintro - ⟨J, rfl⟩
  -- ⊢ x ∈ (fun h => ↑H) J
  refine' (AddSubmonoid.mem_closure.mp (mem_closure_iff.mp hx)) H.toAddSubmonoid fun y hy => _
  -- ⊢ y ∈ ↑(toAddSubmonoid H)
  refine' (Submonoid.mem_closure.mp hy) H.toSubmonoid fun z hz => _
  -- ⊢ z ∈ ↑H.toSubmonoid
  exact (AddSubmonoid.mem_closure.mp hz) H.toAddSubmonoid fun w hw => J hw
  -- 🎉 no goals
#align subsemiring.closure_add_submonoid_closure Subsemiring.closure_addSubmonoid_closure

/-- An induction principle for closure membership. If `p` holds for `0`, `1`, and all elements
of `s`, and is preserved under addition and multiplication, then `p` holds for all elements
of the closure of `s`. -/
@[elab_as_elim]
theorem closure_induction {s : Set R} {p : R → Prop} {x} (h : x ∈ closure s) (Hs : ∀ x ∈ s, p x)
    (H0 : p 0) (H1 : p 1) (Hadd : ∀ x y, p x → p y → p (x + y))
    (Hmul : ∀ x y, p x → p y → p (x * y)) : p x :=
  (@closure_le _ _ _ ⟨⟨⟨p, @Hmul⟩, H1⟩, @Hadd, H0⟩).2 Hs h
#align subsemiring.closure_induction Subsemiring.closure_induction

/-- An induction principle for closure membership for predicates with two arguments. -/
@[elab_as_elim]
theorem closure_induction₂ {s : Set R} {p : R → R → Prop} {x} {y : R} (hx : x ∈ closure s)
    (hy : y ∈ closure s) (Hs : ∀ x ∈ s, ∀ y ∈ s, p x y) (H0_left : ∀ x, p 0 x)
    (H0_right : ∀ x, p x 0) (H1_left : ∀ x, p 1 x) (H1_right : ∀ x, p x 1)
    (Hadd_left : ∀ x₁ x₂ y, p x₁ y → p x₂ y → p (x₁ + x₂) y)
    (Hadd_right : ∀ x y₁ y₂, p x y₁ → p x y₂ → p x (y₁ + y₂))
    (Hmul_left : ∀ x₁ x₂ y, p x₁ y → p x₂ y → p (x₁ * x₂) y)
    (Hmul_right : ∀ x y₁ y₂, p x y₁ → p x y₂ → p x (y₁ * y₂)) : p x y :=
  closure_induction hx
    (fun x₁ x₁s =>
      closure_induction hy (Hs x₁ x₁s) (H0_right x₁) (H1_right x₁) (Hadd_right x₁) (Hmul_right x₁))
    (H0_left y) (H1_left y) (fun z z' => Hadd_left z z' y) fun z z' => Hmul_left z z' y
#align subsemiring.closure_induction₂ Subsemiring.closure_induction₂

theorem mem_closure_iff_exists_list {R} [Semiring R] {s : Set R} {x} :
    x ∈ closure s ↔ ∃ L : List (List R), (∀ t ∈ L, ∀ y ∈ t, y ∈ s) ∧ (L.map List.prod).sum = x := by
  constructor
  -- ⊢ x ∈ closure s → ∃ L, (∀ (t : List R), t ∈ L → ∀ (y : R), y ∈ t → y ∈ s) ∧ Li …
  · intro hx
    -- ⊢ ∃ L, (∀ (t : List R), t ∈ L → ∀ (y : R), y ∈ t → y ∈ s) ∧ List.sum (List.map …
    -- Porting note: needed explicit `p`
    let p : R → Prop := fun x =>
      ∃ (L : List (List R)),
        (∀ (t : List R), t ∈ L → ∀ (y : R), y ∈ t → y ∈ s) ∧ (List.map List.prod L).sum = x
    exact AddSubmonoid.closure_induction (p := p) (mem_closure_iff.1 hx)
      (fun x hx =>
        suffices ∃ t : List R, (∀ y ∈ t, y ∈ s) ∧ t.prod = x from
          let ⟨t, ht1, ht2⟩ := this
          ⟨[t], List.forall_mem_singleton.2 ht1, by
            rw [List.map_singleton, List.sum_singleton, ht2]⟩
        Submonoid.closure_induction hx
          (fun x hx => ⟨[x], List.forall_mem_singleton.2 hx, one_mul x⟩)
          ⟨[], List.forall_mem_nil _, rfl⟩ fun x y ⟨t, ht1, ht2⟩ ⟨u, hu1, hu2⟩ =>
          ⟨t ++ u, List.forall_mem_append.2 ⟨ht1, hu1⟩, by rw [List.prod_append, ht2, hu2]⟩)
      ⟨[], List.forall_mem_nil _, rfl⟩ fun x y ⟨L, HL1, HL2⟩ ⟨M, HM1, HM2⟩ =>
      ⟨L ++ M, List.forall_mem_append.2 ⟨HL1, HM1⟩, by
        rw [List.map_append, List.sum_append, HL2, HM2]⟩
  · rintro ⟨L, HL1, HL2⟩
    -- ⊢ x ∈ closure s
    exact HL2 ▸
      list_sum_mem fun r hr =>
        let ⟨t, ht1, ht2⟩ := List.mem_map.1 hr
        ht2 ▸ list_prod_mem _ fun y hy => subset_closure <| HL1 t ht1 y hy
#align subsemiring.mem_closure_iff_exists_list Subsemiring.mem_closure_iff_exists_list

variable (R)

/-- `closure` forms a Galois insertion with the coercion to set. -/
protected def gi : GaloisInsertion (@closure R _) (↑)
    where
  choice s _ := closure s
  gc _ _ := closure_le
  le_l_u _ := subset_closure
  choice_eq _ _ := rfl
#align subsemiring.gi Subsemiring.gi

variable {R}

/-- Closure of a subsemiring `S` equals `S`. -/
theorem closure_eq (s : Subsemiring R) : closure (s : Set R) = s :=
  (Subsemiring.gi R).l_u_eq s
#align subsemiring.closure_eq Subsemiring.closure_eq

@[simp]
theorem closure_empty : closure (∅ : Set R) = ⊥ :=
  (Subsemiring.gi R).gc.l_bot
#align subsemiring.closure_empty Subsemiring.closure_empty

@[simp]
theorem closure_univ : closure (Set.univ : Set R) = ⊤ :=
  @coe_top R _ ▸ closure_eq ⊤
#align subsemiring.closure_univ Subsemiring.closure_univ

theorem closure_union (s t : Set R) : closure (s ∪ t) = closure s ⊔ closure t :=
  (Subsemiring.gi R).gc.l_sup
#align subsemiring.closure_union Subsemiring.closure_union

theorem closure_iUnion {ι} (s : ι → Set R) : closure (⋃ i, s i) = ⨆ i, closure (s i) :=
  (Subsemiring.gi R).gc.l_iSup
#align subsemiring.closure_Union Subsemiring.closure_iUnion

theorem closure_sUnion (s : Set (Set R)) : closure (⋃₀ s) = ⨆ t ∈ s, closure t :=
  (Subsemiring.gi R).gc.l_sSup
#align subsemiring.closure_sUnion Subsemiring.closure_sUnion

theorem map_sup (s t : Subsemiring R) (f : R →+* S) : (s ⊔ t).map f = s.map f ⊔ t.map f :=
  (gc_map_comap f).l_sup
#align subsemiring.map_sup Subsemiring.map_sup

theorem map_iSup {ι : Sort*} (f : R →+* S) (s : ι → Subsemiring R) :
    (iSup s).map f = ⨆ i, (s i).map f :=
  (gc_map_comap f).l_iSup
#align subsemiring.map_supr Subsemiring.map_iSup

theorem comap_inf (s t : Subsemiring S) (f : R →+* S) : (s ⊓ t).comap f = s.comap f ⊓ t.comap f :=
  (gc_map_comap f).u_inf
#align subsemiring.comap_inf Subsemiring.comap_inf

theorem comap_iInf {ι : Sort*} (f : R →+* S) (s : ι → Subsemiring S) :
    (iInf s).comap f = ⨅ i, (s i).comap f :=
  (gc_map_comap f).u_iInf
#align subsemiring.comap_infi Subsemiring.comap_iInf

@[simp]
theorem map_bot (f : R →+* S) : (⊥ : Subsemiring R).map f = ⊥ :=
  (gc_map_comap f).l_bot
#align subsemiring.map_bot Subsemiring.map_bot

@[simp]
theorem comap_top (f : R →+* S) : (⊤ : Subsemiring S).comap f = ⊤ :=
  (gc_map_comap f).u_top
#align subsemiring.comap_top Subsemiring.comap_top

/-- Given `Subsemiring`s `s`, `t` of semirings `R`, `S` respectively, `s.prod t` is `s × t`
as a subsemiring of `R × S`. -/
def prod (s : Subsemiring R) (t : Subsemiring S) : Subsemiring (R × S) :=
  { s.toSubmonoid.prod t.toSubmonoid, s.toAddSubmonoid.prod t.toAddSubmonoid with
    carrier := s ×ˢ t }
#align subsemiring.prod Subsemiring.prod

@[norm_cast]
theorem coe_prod (s : Subsemiring R) (t : Subsemiring S) :
    (s.prod t : Set (R × S)) = (s : Set R) ×ˢ (t : Set S) :=
  rfl
#align subsemiring.coe_prod Subsemiring.coe_prod

theorem mem_prod {s : Subsemiring R} {t : Subsemiring S} {p : R × S} :
    p ∈ s.prod t ↔ p.1 ∈ s ∧ p.2 ∈ t :=
  Iff.rfl
#align subsemiring.mem_prod Subsemiring.mem_prod

@[mono]
theorem prod_mono ⦃s₁ s₂ : Subsemiring R⦄ (hs : s₁ ≤ s₂) ⦃t₁ t₂ : Subsemiring S⦄ (ht : t₁ ≤ t₂) :
    s₁.prod t₁ ≤ s₂.prod t₂ :=
  Set.prod_mono hs ht
#align subsemiring.prod_mono Subsemiring.prod_mono

theorem prod_mono_right (s : Subsemiring R) : Monotone fun t : Subsemiring S => s.prod t :=
  prod_mono (le_refl s)
#align subsemiring.prod_mono_right Subsemiring.prod_mono_right

theorem prod_mono_left (t : Subsemiring S) : Monotone fun s : Subsemiring R => s.prod t :=
  fun _ _ hs => prod_mono hs (le_refl t)
#align subsemiring.prod_mono_left Subsemiring.prod_mono_left

theorem prod_top (s : Subsemiring R) : s.prod (⊤ : Subsemiring S) = s.comap (RingHom.fst R S) :=
  ext fun x => by simp [mem_prod, MonoidHom.coe_fst]
                  -- 🎉 no goals
#align subsemiring.prod_top Subsemiring.prod_top

theorem top_prod (s : Subsemiring S) : (⊤ : Subsemiring R).prod s = s.comap (RingHom.snd R S) :=
  ext fun x => by simp [mem_prod, MonoidHom.coe_snd]
                  -- 🎉 no goals
#align subsemiring.top_prod Subsemiring.top_prod

@[simp]
theorem top_prod_top : (⊤ : Subsemiring R).prod (⊤ : Subsemiring S) = ⊤ :=
  (top_prod _).trans <| comap_top _
#align subsemiring.top_prod_top Subsemiring.top_prod_top

/-- Product of subsemirings is isomorphic to their product as monoids. -/
def prodEquiv (s : Subsemiring R) (t : Subsemiring S) : s.prod t ≃+* s × t :=
  { Equiv.Set.prod (s : Set R) (t : Set S) with
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl }
#align subsemiring.prod_equiv Subsemiring.prodEquiv

theorem mem_iSup_of_directed {ι} [hι : Nonempty ι] {S : ι → Subsemiring R} (hS : Directed (· ≤ ·) S)
    {x : R} : (x ∈ ⨆ i, S i) ↔ ∃ i, x ∈ S i := by
  refine' ⟨_, fun ⟨i, hi⟩ => (SetLike.le_def.1 <| le_iSup S i) hi⟩
  -- ⊢ x ∈ ⨆ (i : ι), S i → ∃ i, x ∈ S i
  let U : Subsemiring R :=
    Subsemiring.mk' (⋃ i, (S i : Set R)) (⨆ i, (S i).toSubmonoid)
      (Submonoid.coe_iSup_of_directed <| hS.mono_comp _ fun _ _ => id) (⨆ i, (S i).toAddSubmonoid)
      (AddSubmonoid.coe_iSup_of_directed <| hS.mono_comp _ fun _ _ => id)
  -- Porting note: gave the hypothesis an explicit name because `@this` doesn't work
  suffices h : ⨆ i, S i ≤ U by simpa using @h x
  -- ⊢ ⨆ (i : ι), S i ≤ U
  exact iSup_le fun i x hx => Set.mem_iUnion.2 ⟨i, hx⟩
  -- 🎉 no goals
#align subsemiring.mem_supr_of_directed Subsemiring.mem_iSup_of_directed

theorem coe_iSup_of_directed {ι} [hι : Nonempty ι] {S : ι → Subsemiring R}
    (hS : Directed (· ≤ ·) S) : ((⨆ i, S i : Subsemiring R) : Set R) = ⋃ i, ↑(S i) :=
  Set.ext fun x => by simp [mem_iSup_of_directed hS]
                      -- 🎉 no goals
#align subsemiring.coe_supr_of_directed Subsemiring.coe_iSup_of_directed

theorem mem_sSup_of_directedOn {S : Set (Subsemiring R)} (Sne : S.Nonempty)
    (hS : DirectedOn (· ≤ ·) S) {x : R} : x ∈ sSup S ↔ ∃ s ∈ S, x ∈ s := by
  haveI : Nonempty S := Sne.to_subtype
  -- ⊢ x ∈ sSup S ↔ ∃ s, s ∈ S ∧ x ∈ s
  simp only [sSup_eq_iSup', mem_iSup_of_directed hS.directed_val, SetCoe.exists, Subtype.coe_mk,
    exists_prop]
#align subsemiring.mem_Sup_of_directed_on Subsemiring.mem_sSup_of_directedOn

theorem coe_sSup_of_directedOn {S : Set (Subsemiring R)} (Sne : S.Nonempty)
    (hS : DirectedOn (· ≤ ·) S) : (↑(sSup S) : Set R) = ⋃ s ∈ S, ↑s :=
  Set.ext fun x => by simp [mem_sSup_of_directedOn Sne hS]
                      -- 🎉 no goals
#align subsemiring.coe_Sup_of_directed_on Subsemiring.coe_sSup_of_directedOn

end Subsemiring

namespace RingHom

variable [NonAssocSemiring T] {s : Subsemiring R}

variable {σR σS : Type*}

variable [SetLike σR R] [SetLike σS S] [SubsemiringClass σR R] [SubsemiringClass σS S]

open Subsemiring

/-- Restriction of a ring homomorphism to a subsemiring of the domain. -/
def domRestrict (f : R →+* S) (s : σR) : s →+* S :=
  f.comp <| SubsemiringClass.subtype s
#align ring_hom.dom_restrict RingHom.domRestrict

@[simp]
theorem restrict_apply (f : R →+* S) {s : σR} (x : s) : f.domRestrict s x = f x :=
  rfl
#align ring_hom.restrict_apply RingHom.restrict_apply

/-- Restriction of a ring homomorphism to a subsemiring of the codomain. -/
def codRestrict (f : R →+* S) (s : σS) (h : ∀ x, f x ∈ s) : R →+* s :=
  { (f : R →* S).codRestrict s h, (f : R →+ S).codRestrict s h with toFun := fun n => ⟨f n, h n⟩ }
#align ring_hom.cod_restrict RingHom.codRestrict

/-- The ring homomorphism from the preimage of `s` to `s`. -/
def restrict (f : R →+* S) (s' : σR) (s : σS) (h : ∀ x ∈ s', f x ∈ s) : s' →+* s :=
  (f.domRestrict s').codRestrict s fun x => h x x.2
#align ring_hom.restrict RingHom.restrict

@[simp]
theorem coe_restrict_apply (f : R →+* S) (s' : σR) (s : σS) (h : ∀ x ∈ s', f x ∈ s) (x : s') :
    (f.restrict s' s h x : S) = f x :=
  rfl
#align ring_hom.coe_restrict_apply RingHom.coe_restrict_apply

@[simp]
theorem comp_restrict (f : R →+* S) (s' : σR) (s : σS) (h : ∀ x ∈ s', f x ∈ s) :
    (SubsemiringClass.subtype s).comp (f.restrict s' s h) = f.comp (SubsemiringClass.subtype s') :=
  rfl
#align ring_hom.comp_restrict RingHom.comp_restrict

/-- Restriction of a ring homomorphism to its range interpreted as a subsemiring.

This is the bundled version of `Set.rangeFactorization`. -/
def rangeSRestrict (f : R →+* S) : R →+* f.rangeS :=
  f.codRestrict (R := R) (S := S) (σS := Subsemiring S) f.rangeS f.mem_rangeS_self
#align ring_hom.srange_restrict RingHom.rangeSRestrict

@[simp]
theorem coe_rangeSRestrict (f : R →+* S) (x : R) : (f.rangeSRestrict x : S) = f x :=
  rfl
#align ring_hom.coe_srange_restrict RingHom.coe_rangeSRestrict

theorem rangeSRestrict_surjective (f : R →+* S) : Function.Surjective f.rangeSRestrict :=
  fun ⟨_, hy⟩ =>
  let ⟨x, hx⟩ := mem_rangeS.mp hy
  ⟨x, Subtype.ext hx⟩
#align ring_hom.srange_restrict_surjective RingHom.rangeSRestrict_surjective

theorem rangeS_top_iff_surjective {f : R →+* S} :
    f.rangeS = (⊤ : Subsemiring S) ↔ Function.Surjective f :=
  SetLike.ext'_iff.trans <| Iff.trans (by rw [coe_rangeS, coe_top]) Set.range_iff_surjective
                                          -- 🎉 no goals
#align ring_hom.srange_top_iff_surjective RingHom.rangeS_top_iff_surjective

/-- The range of a surjective ring homomorphism is the whole of the codomain. -/
@[simp]
theorem rangeS_top_of_surjective (f : R →+* S) (hf : Function.Surjective f) :
    f.rangeS = (⊤ : Subsemiring S) :=
  rangeS_top_iff_surjective.2 hf
#align ring_hom.srange_top_of_surjective RingHom.rangeS_top_of_surjective

/-- The subsemiring of elements `x : R` such that `f x = g x` -/
def eqLocusS (f g : R →+* S) : Subsemiring R :=
  { (f : R →* S).eqLocusM g, (f : R →+ S).eqLocusM g with carrier := { x | f x = g x } }
#align ring_hom.eq_slocus RingHom.eqLocusS

@[simp]
theorem eqLocusS_same (f : R →+* S) : f.eqLocusS f = ⊤ :=
  SetLike.ext fun _ => eq_self_iff_true _
#align ring_hom.eq_slocus_same RingHom.eqLocusS_same

/-- If two ring homomorphisms are equal on a set, then they are equal on its subsemiring closure. -/
theorem eqOn_sclosure {f g : R →+* S} {s : Set R} (h : Set.EqOn f g s) : Set.EqOn f g (closure s) :=
  show closure s ≤ f.eqLocusS g from closure_le.2 h
#align ring_hom.eq_on_sclosure RingHom.eqOn_sclosure

theorem eq_of_eqOn_stop {f g : R →+* S} (h : Set.EqOn f g (⊤ : Subsemiring R)) : f = g :=
  ext fun _ => h trivial
#align ring_hom.eq_of_eq_on_stop RingHom.eq_of_eqOn_stop

theorem eq_of_eqOn_sdense {s : Set R} (hs : closure s = ⊤) {f g : R →+* S} (h : s.EqOn f g) :
    f = g :=
  eq_of_eqOn_stop <| hs ▸ eqOn_sclosure h
#align ring_hom.eq_of_eq_on_sdense RingHom.eq_of_eqOn_sdense

theorem sclosure_preimage_le (f : R →+* S) (s : Set S) : closure (f ⁻¹' s) ≤ (closure s).comap f :=
  closure_le.2 fun _ hx => SetLike.mem_coe.2 <| mem_comap.2 <| subset_closure hx
#align ring_hom.sclosure_preimage_le RingHom.sclosure_preimage_le

/-- The image under a ring homomorphism of the subsemiring generated by a set equals
the subsemiring generated by the image of the set. -/
theorem map_closureS (f : R →+* S) (s : Set R) : (closure s).map f = closure (f '' s) :=
  le_antisymm
    (map_le_iff_le_comap.2 <|
      le_trans (closure_mono <| Set.subset_preimage_image _ _) (sclosure_preimage_le _ _))
    (closure_le.2 <| Set.image_subset _ subset_closure)
#align ring_hom.map_sclosure RingHom.map_closureS

end RingHom

namespace Subsemiring

open RingHom

/-- The ring homomorphism associated to an inclusion of subsemirings. -/
def inclusion {S T : Subsemiring R} (h : S ≤ T) : S →+* T :=
  S.subtype.codRestrict _ fun x => h x.2
#align subsemiring.inclusion Subsemiring.inclusion

@[simp]
theorem rangeS_subtype (s : Subsemiring R) : s.subtype.rangeS = s :=
  SetLike.coe_injective <| (coe_rangeS _).trans Subtype.range_coe
#align subsemiring.srange_subtype Subsemiring.rangeS_subtype

@[simp]
theorem range_fst : (fst R S).rangeS = ⊤ :=
  (fst R S).rangeS_top_of_surjective <| Prod.fst_surjective
#align subsemiring.range_fst Subsemiring.range_fst

@[simp]
theorem range_snd : (snd R S).rangeS = ⊤ :=
  (snd R S).rangeS_top_of_surjective <| Prod.snd_surjective
#align subsemiring.range_snd Subsemiring.range_snd

@[simp]
theorem prod_bot_sup_bot_prod (s : Subsemiring R) (t : Subsemiring S) :
    s.prod ⊥ ⊔ prod ⊥ t = s.prod t :=
  le_antisymm (sup_le (prod_mono_right s bot_le) (prod_mono_left t bot_le)) fun p hp =>
    Prod.fst_mul_snd p ▸
      mul_mem
        ((le_sup_left : s.prod ⊥ ≤ s.prod ⊥ ⊔ prod ⊥ t) ⟨hp.1, SetLike.mem_coe.2 <| one_mem ⊥⟩)
        ((le_sup_right : prod ⊥ t ≤ s.prod ⊥ ⊔ prod ⊥ t) ⟨SetLike.mem_coe.2 <| one_mem ⊥, hp.2⟩)
#align subsemiring.prod_bot_sup_bot_prod Subsemiring.prod_bot_sup_bot_prod

end Subsemiring

namespace RingEquiv

variable {s t : Subsemiring R}

/-- Makes the identity isomorphism from a proof two subsemirings of a multiplicative
    monoid are equal. -/
def subsemiringCongr (h : s = t) : s ≃+* t :=
  {
    Equiv.setCongr <| congr_arg _ h with
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl }
#align ring_equiv.subsemiring_congr RingEquiv.subsemiringCongr

/-- Restrict a ring homomorphism with a left inverse to a ring isomorphism to its
`RingHom.rangeS`. -/
def ofLeftInverseS {g : S → R} {f : R →+* S} (h : Function.LeftInverse g f) : R ≃+* f.rangeS :=
  { f.rangeSRestrict with
    toFun := fun x => f.rangeSRestrict x
    invFun := fun x => (g ∘ f.rangeS.subtype) x
    left_inv := h
    right_inv := fun x =>
      Subtype.ext <|
        let ⟨x', hx'⟩ := RingHom.mem_rangeS.mp x.prop
        show f (g x) = x by rw [← hx', h x'] }
                            -- 🎉 no goals
#align ring_equiv.sof_left_inverse RingEquiv.ofLeftInverseS

@[simp]
theorem ofLeftInverseS_apply {g : S → R} {f : R →+* S} (h : Function.LeftInverse g f) (x : R) :
    ↑(ofLeftInverseS h x) = f x :=
  rfl
#align ring_equiv.sof_left_inverse_apply RingEquiv.ofLeftInverseS_apply

@[simp]
theorem ofLeftInverseS_symm_apply {g : S → R} {f : R →+* S} (h : Function.LeftInverse g f)
    (x : f.rangeS) : (ofLeftInverseS h).symm x = g x :=
  rfl
#align ring_equiv.sof_left_inverse_symm_apply RingEquiv.ofLeftInverseS_symm_apply

/-- Given an equivalence `e : R ≃+* S` of semirings and a subsemiring `s` of `R`,
`subsemiring_map e s` is the induced equivalence between `s` and `s.map e` -/
@[simps!]
def subsemiringMap (e : R ≃+* S) (s : Subsemiring R) : s ≃+* s.map e.toRingHom :=
  { e.toAddEquiv.addSubmonoidMap s.toAddSubmonoid, e.toMulEquiv.submonoidMap s.toSubmonoid with }
#align ring_equiv.subsemiring_map RingEquiv.subsemiringMap

end RingEquiv

/-! ### Actions by `Subsemiring`s

These are just copies of the definitions about `Submonoid` starting from `submonoid.mul_action`.
The only new result is `subsemiring.module`.

When `R` is commutative, `Algebra.ofSubsemiring` provides a stronger result than those found in
this file, which uses the same scalar action.
-/


section Actions

namespace Subsemiring

variable {R' α β : Type*}

section NonAssocSemiring

variable [NonAssocSemiring R']

/-- The action by a subsemiring is the action by the underlying semiring. -/
instance smul [SMul R' α] (S : Subsemiring R') : SMul S α :=
  S.toSubmonoid.smul

theorem smul_def [SMul R' α] {S : Subsemiring R'} (g : S) (m : α) : g • m = (g : R') • m :=
  rfl
#align subsemiring.smul_def Subsemiring.smul_def

instance smulCommClass_left [SMul R' β] [SMul α β] [SMulCommClass R' α β] (S : Subsemiring R') :
    SMulCommClass S α β :=
  S.toSubmonoid.smulCommClass_left
#align subsemiring.smul_comm_class_left Subsemiring.smulCommClass_left

instance smulCommClass_right [SMul α β] [SMul R' β] [SMulCommClass α R' β] (S : Subsemiring R') :
    SMulCommClass α S β :=
  S.toSubmonoid.smulCommClass_right
#align subsemiring.smul_comm_class_right Subsemiring.smulCommClass_right

/-- Note that this provides `IsScalarTower S R R` which is needed by `smul_mul_assoc`. -/
instance isScalarTower [SMul α β] [SMul R' α] [SMul R' β] [IsScalarTower R' α β]
    (S : Subsemiring R') :
    IsScalarTower S α β :=
  S.toSubmonoid.isScalarTower

instance faithfulSMul [SMul R' α] [FaithfulSMul R' α] (S : Subsemiring R') : FaithfulSMul S α :=
  S.toSubmonoid.faithfulSMul

/-- The action by a subsemiring is the action by the underlying semiring. -/
instance [Zero α] [SMulWithZero R' α] (S : Subsemiring R') : SMulWithZero S α :=
  SMulWithZero.compHom _ S.subtype.toMonoidWithZeroHom.toZeroHom

end NonAssocSemiring

variable [Semiring R']

/-- The action by a subsemiring is the action by the underlying semiring. -/
instance mulAction [MulAction R' α] (S : Subsemiring R') : MulAction S α :=
  S.toSubmonoid.mulAction

/-- The action by a subsemiring is the action by the underlying semiring. -/
instance distribMulAction [AddMonoid α] [DistribMulAction R' α] (S : Subsemiring R') :
    DistribMulAction S α :=
  S.toSubmonoid.distribMulAction

/-- The action by a subsemiring is the action by the underlying semiring. -/
instance mulDistribMulAction [Monoid α] [MulDistribMulAction R' α] (S : Subsemiring R') :
    MulDistribMulAction S α :=
  S.toSubmonoid.mulDistribMulAction

/-- The action by a subsemiring is the action by the underlying semiring. -/
instance mulActionWithZero [Zero α] [MulActionWithZero R' α] (S : Subsemiring R') :
    MulActionWithZero S α :=
  MulActionWithZero.compHom _ S.subtype.toMonoidWithZeroHom

-- Porting note: instance named explicitly for use in `RingTheory/Subring/Basic`
/-- The action by a subsemiring is the action by the underlying semiring. -/
instance module [AddCommMonoid α] [Module R' α] (S : Subsemiring R') : Module S α :=
  -- Porting note: copying over the `smul` field causes a timeout
  -- { Module.compHom _ S.subtype with smul := (· • ·) }
  Module.compHom _ S.subtype

/-- The action by a subsemiring is the action by the underlying semiring. -/
instance [Semiring α] [MulSemiringAction R' α] (S : Subsemiring R') : MulSemiringAction S α :=
  S.toSubmonoid.mulSemiringAction

/-- The center of a semiring acts commutatively on that semiring. -/
instance center.smulCommClass_left : SMulCommClass (center R') R' R' :=
  Submonoid.center.smulCommClass_left
#align subsemiring.center.smul_comm_class_left Subsemiring.center.smulCommClass_left

/-- The center of a semiring acts commutatively on that semiring. -/
instance center.smulCommClass_right : SMulCommClass R' (center R') R' :=
  Submonoid.center.smulCommClass_right
#align subsemiring.center.smul_comm_class_right Subsemiring.center.smulCommClass_right

/-- If all the elements of a set `s` commute, then `closure s` is a commutative monoid. -/
def closureCommSemiringOfComm {s : Set R'} (hcomm : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a) :
    CommSemiring (closure s) :=
  { (closure s).toSemiring with
    mul_comm := fun x y => by
      ext
      -- ⊢ ↑(x * y) = ↑(y * x)
      simp only [Subsemiring.coe_mul]
      -- ⊢ ↑x * ↑y = ↑y * ↑x
      refine'
        closure_induction₂ x.prop y.prop hcomm (fun x => by simp only [zero_mul, mul_zero])
          (fun x => by simp only [zero_mul, mul_zero]) (fun x => by simp only [one_mul, mul_one])
          (fun x => by simp only [one_mul, mul_one])
          (fun x y z h₁ h₂ => by simp only [add_mul, mul_add, h₁, h₂])
          (fun x y z h₁ h₂ => by simp only [add_mul, mul_add, h₁, h₂])
          (fun x y z h₁ h₂ => by rw [mul_assoc, h₂, ← mul_assoc, h₁, mul_assoc]) fun x y z h₁ h₂ =>
          by rw [← mul_assoc, h₁, mul_assoc, h₂, ← mul_assoc] }
#align subsemiring.closure_comm_semiring_of_comm Subsemiring.closureCommSemiringOfComm

end Subsemiring

end Actions

-- While this definition is not about `Subsemiring`s, this is the earliest we have
-- both `StrictOrderedSemiring` and `Submonoid` available.
/-- Submonoid of positive elements of an ordered semiring. -/
def posSubmonoid (R : Type*) [StrictOrderedSemiring R] : Submonoid R
    where
  carrier := { x | 0 < x }
  one_mem' := show (0 : R) < 1 from zero_lt_one
  mul_mem' {x y} (hx : 0 < x) (hy : 0 < y) := mul_pos hx hy
#align pos_submonoid posSubmonoid

@[simp]
theorem mem_posSubmonoid {R : Type*} [StrictOrderedSemiring R] (u : Rˣ) :
    ↑u ∈ posSubmonoid R ↔ (0 : R) < u :=
  Iff.rfl
#align mem_pos_monoid mem_posSubmonoid
