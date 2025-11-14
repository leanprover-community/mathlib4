/-
Copyright (c) 2024 Florent Schaffhauser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florent Schaffhauser, Artie Khovanov
-/
import Mathlib.Algebra.Ring.Subsemiring.Defs
import Mathlib.RingTheory.Ideal.Prime
import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-!
# Ring orderings

Let `R` be a commutative ring. A preordering on `R` is a subset closed under
addition and multiplication that contains all squares, but not `-1`.

The support of a preordering `P` is the set of elements `x` such that both `x` and `-x` lie in `P`.

An ordering `O` on `R` is a preordering such that
1. `O` contains either `x` or `-x` for each `x` in `R` and
2. the support of `O` is a prime ideal.

We define preorderings, supports and orderings.

A ring preordering can intuitively be viewed as a set of "non-negative" ring elements.
Indeed, an ordering `O` with support `p` induces a linear order on `R⧸p` making it
into an ordered ring, and vice versa.

## References

- [*An introduction to real algebra*, T.Y. Lam][lam_1984]

-/

/-!
#### Preorderings
-/

variable (R : Type*) [CommRing R]

/-- A preordering on a ring `R` is a subsemiring of `R` containing all squares,
but not containing `-1`. -/
@[ext]
structure RingPreordering extends Subsemiring R where
  mem_of_isSquare' {x : R} (hx : IsSquare x) : x ∈ carrier := by aesop
  neg_one_notMem' : -1 ∉ carrier := by aesop

namespace RingPreordering

attribute [coe] toSubsemiring

instance : SetLike (RingPreordering R) R where
  coe P := P.carrier
  coe_injective' p q h := by cases p; cases q; congr; exact SetLike.ext' h

initialize_simps_projections RingPreordering (carrier → coe, as_prefix coe)

instance : SubsemiringClass (RingPreordering R) R where
  zero_mem _ := Subsemiring.zero_mem _
  one_mem _ := Subsemiring.one_mem _
  add_mem := Subsemiring.add_mem _
  mul_mem := Subsemiring.mul_mem _

variable {R}

@[aesop unsafe 80% (rule_sets := [SetLike])]
protected theorem mem_of_isSquare (P : RingPreordering R) {x : R} (hx : IsSquare x) : x ∈ P :=
  RingPreordering.mem_of_isSquare' _ hx

@[simp]
protected theorem mul_self_mem (P : RingPreordering R) (x : R) : x * x ∈ P := by aesop

@[simp]
protected theorem pow_two_mem (P : RingPreordering R) (x : R) : x ^ 2 ∈ P := by aesop

@[aesop unsafe 20% forward (rule_sets := [SetLike])]
protected theorem neg_one_notMem (P : RingPreordering R) : -1 ∉ P :=
  RingPreordering.neg_one_notMem' _

theorem toSubsemiring_injective :
    Function.Injective (toSubsemiring : RingPreordering R → _) := fun A B h => by ext; rw [h]

@[simp]
theorem toSubsemiring_inj {P₁ P₂ : RingPreordering R} :
    P₁.toSubsemiring = P₂.toSubsemiring ↔ P₁ = P₂ := toSubsemiring_injective.eq_iff

@[simp]
theorem mem_toSubsemiring {P : RingPreordering R} {x : R} : x ∈ P.toSubsemiring ↔ x ∈ P := .rfl

@[simp, norm_cast]
theorem coe_toSubsemiring (P : RingPreordering R) : (P.toSubsemiring : Set R) = P := rfl

@[simp]
theorem mem_mk {toSubsemiring : Subsemiring R} (mem_of_isSquare neg_one_notMem) {x : R} :
    x ∈ mk toSubsemiring mem_of_isSquare neg_one_notMem ↔ x ∈ toSubsemiring := .rfl

@[simp]
theorem coe_set_mk (toSubsemiring : Subsemiring R) (mem_of_isSquare neg_one_notMem) :
    (mk toSubsemiring mem_of_isSquare neg_one_notMem : Set R) = toSubsemiring := rfl

section copy

variable (P : RingPreordering R) (S : Set R) (hS : S = P)

/-- Copy of a preordering with a new `carrier` equal to the old one. Useful to fix definitional
equalities. -/
@[simps]
protected def copy : RingPreordering R where
  carrier := S
  zero_mem' := by aesop
  add_mem' ha hb := by aesop
  one_mem' := by aesop
  mul_mem' ha hb := by aesop

attribute [norm_cast] coe_copy
@[simp] theorem mem_copy {x} : x ∈ P.copy S hS ↔ x ∈ S := .rfl
theorem copy_eq : P.copy S hS = S := rfl

end copy

variable {P : RingPreordering R}

/-!
#### Support
-/

section supportAddSubgroup

variable (P) in
/--
The support of a ring preordering `P` in a commutative ring `R` is
the set of elements `x` in `R` such that both `x` and `-x` lie in `P`.
-/
def supportAddSubgroup : AddSubgroup R where
  carrier := P ∩ -P
  zero_mem' := by aesop
  add_mem' := by aesop
  neg_mem' := by aesop

theorem mem_supportAddSubgroup {x} : x ∈ P.supportAddSubgroup ↔ x ∈ P ∧ -x ∈ P := .rfl
theorem coe_supportAddSubgroup : P.supportAddSubgroup = (P ∩ -P : Set R) := rfl

end supportAddSubgroup

/-- Typeclass to track whether the support of a preordering forms an ideal. -/
class HasIdealSupport (P : RingPreordering R) : Prop where
  smul_mem_support (P) (x : R) {a : R} (ha : a ∈ P.supportAddSubgroup) :
    x * a ∈ P.supportAddSubgroup

export HasIdealSupport (smul_mem_support)

theorem hasIdealSupport_iff :
    P.HasIdealSupport ↔ ∀ x a : R, a ∈ P → -a ∈ P → x * a ∈ P ∧ -(x * a) ∈ P where
  mp _ := by simpa [mem_supportAddSubgroup] using P.smul_mem_support
  mpr _ := ⟨by simpa [mem_supportAddSubgroup]⟩

instance [HasMemOrNegMem P] : P.HasIdealSupport where
  smul_mem_support x a ha :=
    match mem_or_neg_mem P x with
    | .inl hx => ⟨by simpa using mul_mem hx ha.1, by simpa using mul_mem hx ha.2⟩
    | .inr hx => ⟨by simpa using mul_mem hx ha.2, by simpa using mul_mem hx ha.1⟩

section support

variable [P.HasIdealSupport]

variable (P) in
/--
The support of a ring preordering `P` in a commutative ring `R` is
the set of elements `x` in `R` such that both `x` and `-x` lie in `P`.
-/
def support : Ideal R where
  __ := P.supportAddSubgroup
  smul_mem' := by simpa using smul_mem_support P

theorem mem_support {x} : x ∈ P.support ↔ x ∈ P ∧ -x ∈ P := .rfl
theorem coe_support : P.support = (P : Set R) ∩ -(P : Set R) := rfl

@[simp] theorem supportAddSubgroup_eq : P.supportAddSubgroup = P.support.toAddSubgroup := rfl

end support

/--
An ordering `O` on a ring `R` is a preordering such that
1. `O` contains either `x` or `-x` for each `x` in `R` and
2. the support of `O` is a prime ideal.
-/
class IsOrdering (P : RingPreordering R) extends HasMemOrNegMem P, P.support.IsPrime

end RingPreordering
