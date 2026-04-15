/-
Copyright (c) 2024 Florent Schaffhauser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florent Schaffhauser, Artie Khovanov
-/
module

public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.RingTheory.Ideal.Prime
public import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-!
# Ring orderings

Let `R` be a commutative ring. We define orderings and preorderings on `R`
as predicates on `Subsemiring R`.

## Definitions

* `IsOrdering`: an ordering is a subsemiring `O` such that `O ∪ -O = R` and
the support `O ∩ -O` of `O` forms a prime ideal.
* `IsPreordering`: a preordering is a subsemiring that contains all squares, but not `-1`.

All orderings are preorderings.

## References

- [*An introduction to real algebra*, T.Y. Lam][lam_1984]

-/

@[expose] public section

namespace Subsemiring

variable {R : Type*} [CommRing R] (S : Subsemiring R)

/--
An ordering `O` on a ring `R` is a subsemiring of `R` such that `O ∪ -O = R` and
the support `O ∩ -O` of `O` forms a prime ideal.
-/
class IsOrdering (S : Subsemiring R) : Prop where
  isSpanning (S) : S.IsSpanning
  support_ne_top (S) : S.toAddSubmonoid.support ≠ ⊤
  mem_support_or_mem_support :
    ∀ {x y : R}, x * y ∈ S.toAddSubmonoid.support →
      x ∈ S.toAddSubmonoid.support ∨ y ∈ S.toAddSubmonoid.support

attribute [aesop safe forward] IsOrdering.isSpanning

instance [i : S.IsOrdering] : S.HasIdealSupport := i.isSpanning.hasIdealSupport

instance IsOrdering.support_isPrime [i : S.IsOrdering] : S.support.IsPrime where
  ne_top' := by simpa using i.support_ne_top
  mem_or_mem' := i.mem_support_or_mem_support

variable {S} in
theorem IsOrdering.mk' (hS₁ : S.IsSpanning) (hS₂ : have := hS₁.hasIdealSupport; S.support.IsPrime) :
    S.IsOrdering where
  isSpanning := hS₁
  support_ne_top := by simpa [hS₁.hasIdealSupport] using hS₂.ne_top
  mem_support_or_mem_support := hS₂.mem_or_mem

/-- A preordering on a ring `R` is a subsemiring of `R` that contains all squares, but not `-1`. -/
class IsPreordering (S : Subsemiring R) : Prop where
  mem_of_isSquare (S) {x} (hx : IsSquare x) : x ∈ S := by aesop
  neg_one_notMem (S) : -1 ∉ S := by aesop

export IsPreordering (mem_of_isSquare)
export IsPreordering (neg_one_notMem)

attribute [aesop simp, aesop safe forward] neg_one_notMem

section IsPreordering

variable [IsPreordering S]

@[aesop 80% (rule_sets := [SetLike])]
protected theorem mem_of_isSumSq {x : R} (hx : IsSumSq x) : x ∈ S := by
  induction hx with
  | zero => simp
  | sq_add => aesop (add unsafe mem_of_isSquare)

theorem sumSq_le {R : Type*} [CommRing R] (S : Subsemiring R) [IsPreordering S] :
    Subsemiring.sumSq R ≤ S := fun _ ↦ by aesop

@[simp]
protected theorem mul_self_mem (x : R) : x * x ∈ S := by aesop

@[simp]
protected theorem pow_two_mem (x : R) : x ^ 2 ∈ S := by aesop

end IsPreordering

variable {S} in
theorem IsPreordering.of_support_neq_top
    (hS : S.IsSpanning) (h : have := hS.hasIdealSupport; S.support ≠ ⊤) :
    S.IsPreordering where
  mem_of_isSquare x := by
    rcases x with ⟨y, rfl⟩
    cases S.mem_or_neg_mem hS y with
    | inl h => aesop
    | inr h => simpa using (show -y * -y ∈ S by aesop (config := { enableSimp := false }))
  neg_one_notMem hc := by
    have := hS.hasIdealSupport
    have : 1 ∈ S.support := by simp [mem_support, hc]
    exact h (by simpa [Ideal.eq_top_iff_one])

/- An ordering is a preordering. -/
instance [S.IsOrdering] : S.IsPreordering :=
  .of_support_neq_top (IsOrdering.isSpanning S) (Ideal.IsPrime.ne_top inferInstance)

end Subsemiring

/- ############## DEPRECATE -/


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

instance : PartialOrder (RingPreordering R) := .ofSetLike (RingPreordering R) R

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
