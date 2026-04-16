/-
Copyright (c) 2024 Florent Schaffhauser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florent Schaffhauser, Artie Khovanov
-/
module

public import Mathlib.Algebra.Ring.Subsemiring.Support
public import Mathlib.Algebra.Ring.SumsOfSquares
public import Mathlib.RingTheory.Ideal.Prime

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

@[simp]
protected theorem mul_self_mem (x : R) : x * x ∈ S := by aesop

@[simp]
protected theorem pow_two_mem (x : R) : x ^ 2 ∈ S := by aesop

end IsPreordering

variable {S} in
theorem IsPreordering.of_support_ne_top
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
  .of_support_ne_top (IsOrdering.isSpanning S) (Ideal.IsPrime.ne_top inferInstance)

end Subsemiring

/- Deprecated -/

variable (R : Type*) [CommRing R]

/-- A preordering on a ring `R` is a subsemiring of `R` containing all squares,
but not containing `-1`. -/
@[deprecated "use `Subsemiring.IsPreordering`" (since := "2026-04-15"), ext]
structure RingPreordering extends Subsemiring R where
  mem_of_isSquare' {x : R} (hx : IsSquare x) : x ∈ carrier := by aesop
  neg_one_notMem' : -1 ∉ carrier := by aesop

attribute [deprecated "no replacement" (since := "2026-04-15")] RingPreordering.ext_iff

namespace RingPreordering

attribute [coe] toSubsemiring

set_option linter.deprecated false in
@[deprecated "no replacement" (since := "2026-04-15")]
instance : SetLike (RingPreordering R) R where
  coe P := P.carrier
  coe_injective' p q h := by cases p; cases q; congr; exact SetLike.ext' h

set_option linter.deprecated false in
@[deprecated "no replacement" (since := "2026-04-15")]
instance : PartialOrder (RingPreordering R) := .ofSetLike (RingPreordering R) R

initialize_simps_projections RingPreordering (carrier → coe, as_prefix coe)

set_option linter.deprecated false in
@[deprecated "no replacement" (since := "2026-04-15")]
instance : SubsemiringClass (RingPreordering R) R where
  zero_mem _ := Subsemiring.zero_mem _
  one_mem _ := Subsemiring.one_mem _
  add_mem := Subsemiring.add_mem _
  mul_mem := Subsemiring.mul_mem _

variable {R}

set_option linter.deprecated false in
@[deprecated Subsemiring.mem_of_isSquare (since := "2026-04-15"),
  aesop unsafe 80% (rule_sets := [SetLike])]
protected theorem mem_of_isSquare (P : RingPreordering R) {x : R} (hx : IsSquare x) : x ∈ P :=
  RingPreordering.mem_of_isSquare' _ hx

set_option linter.deprecated false in
@[deprecated Subsemiring.mul_self_mem (since := "2026-04-15"), simp]
protected theorem mul_self_mem (P : RingPreordering R) (x : R) : x * x ∈ P := by aesop

set_option linter.deprecated false in
@[deprecated Subsemiring.pow_two_mem (since := "2026-04-15"), simp]
protected theorem pow_two_mem (P : RingPreordering R) (x : R) : x ^ 2 ∈ P := by aesop

set_option linter.deprecated false in
@[deprecated Subsemiring.neg_one_notMem (since := "2026-04-15"),
  aesop unsafe 20% forward (rule_sets := [SetLike])]
protected theorem neg_one_notMem (P : RingPreordering R) : -1 ∉ P :=
  RingPreordering.neg_one_notMem' _

set_option linter.deprecated false in
@[deprecated "no replacement" (since := "2026-04-15")]
theorem toSubsemiring_injective :
    Function.Injective (toSubsemiring : RingPreordering R → _) := fun A B h => by ext; rw [h]

set_option linter.deprecated false in
@[deprecated "no replacement" (since := "2026-04-15"), simp]
theorem toSubsemiring_inj {P₁ P₂ : RingPreordering R} :
    P₁.toSubsemiring = P₂.toSubsemiring ↔ P₁ = P₂ := toSubsemiring_injective.eq_iff

set_option linter.deprecated false in
@[deprecated "no replacement" (since := "2026-04-15"), simp]
theorem mem_toSubsemiring {P : RingPreordering R} {x : R} : x ∈ P.toSubsemiring ↔ x ∈ P := .rfl

set_option linter.deprecated false in
@[deprecated "no replacement" (since := "2026-04-15"), simp, norm_cast]
theorem coe_toSubsemiring (P : RingPreordering R) : (P.toSubsemiring : Set R) = P := rfl

@[deprecated "no replacement" (since := "2026-04-15"), simp]
theorem mem_mk {toSubsemiring : Subsemiring R} (mem_of_isSquare neg_one_notMem) {x : R} :
    x ∈ mk toSubsemiring mem_of_isSquare neg_one_notMem ↔ x ∈ toSubsemiring := .rfl

@[deprecated "no replacement" (since := "2026-04-15"), simp]
theorem coe_set_mk (toSubsemiring : Subsemiring R) (mem_of_isSquare neg_one_notMem) :
    (mk toSubsemiring mem_of_isSquare neg_one_notMem : Set R) = toSubsemiring := rfl

section copy

set_option linter.deprecated false in
/-- Copy of a preordering with a new `carrier` equal to the old one. Useful to fix definitional
equalities. -/
@[deprecated "no replacement" (since := "2026-04-15"), simps]
protected def copy (P : RingPreordering R) (S : Set R) (hS : S = P) : RingPreordering R where
  carrier := S
  zero_mem' := by aesop
  add_mem' ha hb := by aesop
  one_mem' := by aesop
  mul_mem' ha hb := by aesop

attribute [deprecated "no replacement" (since := "2026-04-15"), norm_cast] coe_copy

set_option linter.deprecated false in
@[deprecated "no replacement" (since := "2026-04-15"), simp]
theorem mem_copy (P : RingPreordering R) (S : Set R) (hS : S = P) {x} :
    x ∈ P.copy S hS ↔ x ∈ S := .rfl

set_option linter.deprecated false in
@[deprecated "no replacement" (since := "2026-04-15")]
theorem copy_eq (P : RingPreordering R) (S : Set R) (hS : S = P) : P.copy S hS = S := rfl

end copy

/-!
#### Support
-/

section supportAddSubgroup

set_option linter.deprecated false in
/--
The support of a ring preordering `P` in a commutative ring `R` is
the set of elements `x` in `R` such that both `x` and `-x` lie in `P`.
-/
@[deprecated AddSubmonoid.support (since := "2026-04-15")]
def supportAddSubgroup (P : RingPreordering R) : AddSubgroup R where
  carrier := P ∩ -P
  zero_mem' := by aesop
  add_mem' := by aesop
  neg_mem' := by aesop

set_option linter.deprecated false in
@[deprecated AddSubmonoid.mem_support (since := "2026-04-15")]
theorem mem_supportAddSubgroup {P : RingPreordering R} {x} :
    x ∈ P.supportAddSubgroup ↔ x ∈ P ∧ -x ∈ P := .rfl

set_option linter.deprecated false in
@[deprecated AddSubmonoid.coe_support (since := "2026-04-15")]
theorem coe_supportAddSubgroup {P : RingPreordering R} :
    P.supportAddSubgroup = (P ∩ -P : Set R) := rfl

end supportAddSubgroup

set_option linter.deprecated false in
/-- Typeclass to track whether the support of a preordering forms an ideal. -/
@[deprecated Subsemiring.HasIdealSupport (since := "2026-04-15")]
class HasIdealSupport (P : RingPreordering R) : Prop where
  smul_mem_support (P) (x : R) {a : R} (ha : a ∈ P.supportAddSubgroup) :
    x * a ∈ P.supportAddSubgroup

export HasIdealSupport (smul_mem_support)

set_option linter.deprecated false in
@[deprecated Subsemiring.hasIdealSupport_iff (since := "2026-04-15")]
theorem hasIdealSupport_iff {P : RingPreordering R} :
    P.HasIdealSupport ↔ ∀ x a : R, a ∈ P → -a ∈ P → x * a ∈ P ∧ -(x * a) ∈ P where
  mp _ := by simpa [mem_supportAddSubgroup] using P.smul_mem_support
  mpr _ := ⟨by simpa [mem_supportAddSubgroup]⟩

set_option linter.deprecated false in
@[deprecated AddSubmonoid.IsSpanning.hasIdealSupport (since := "2026-04-15")]
instance {P : RingPreordering R} [HasMemOrNegMem P] : P.HasIdealSupport where
  smul_mem_support x a ha :=
    match mem_or_neg_mem P x with
    | .inl hx => ⟨by simpa using mul_mem hx ha.1, by simpa using mul_mem hx ha.2⟩
    | .inr hx => ⟨by simpa using mul_mem hx ha.2, by simpa using mul_mem hx ha.1⟩

section support

set_option linter.deprecated false in
variable (P) in
/--
The support of a ring preordering `P` in a commutative ring `R` is
the set of elements `x` in `R` such that both `x` and `-x` lie in `P`.
-/
@[deprecated Subsemiring.support (since := "2026-04-15")]
def support (P : RingPreordering R) [P.HasIdealSupport] : Ideal R where
  __ := P.supportAddSubgroup
  smul_mem' := by simpa using smul_mem_support P

set_option linter.deprecated false in
@[deprecated Subsemiring.mem_support (since := "2026-04-15")]
theorem mem_support {P : RingPreordering R} [P.HasIdealSupport] {x} :
    x ∈ P.support ↔ x ∈ P ∧ -x ∈ P := .rfl

set_option linter.deprecated false in
@[deprecated Subsemiring.coe_support (since := "2026-04-15")]
theorem coe_support {P : RingPreordering R} [P.HasIdealSupport] :
    P.support = (P : Set R) ∩ -(P : Set R) := rfl

set_option linter.deprecated false in
@[deprecated Subsemiring.toAddSubmonoid_support (since := "2026-04-15"), simp]
theorem supportAddSubgroup_eq {P : RingPreordering R} [P.HasIdealSupport] :
    P.supportAddSubgroup = P.support.toAddSubgroup := rfl

end support

set_option linter.deprecated false in
/--
An ordering `O` on a ring `R` is a preordering such that
1. `O` contains either `x` or `-x` for each `x` in `R` and
2. the support of `O` is a prime ideal.
-/
@[deprecated RingPreordering.IsOrdering (since := "2026-04-15")]
class IsOrdering (P : RingPreordering R) extends HasMemOrNegMem P, P.support.IsPrime

end RingPreordering
