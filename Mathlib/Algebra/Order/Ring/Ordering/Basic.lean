/-
Copyright (c) 2024 Florent Schaffhauser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florent Schaffhauser, Artie Khovanov
-/
module

public import Mathlib.Algebra.Field.IsField
public import Mathlib.Algebra.Order.Ring.Ordering.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

/-!
# Ring orderings

We prove basic properties of (pre)orderings on rings.

## References

- [*An introduction to real algebra*, T.Y. Lam][lam_1984]

-/

@[expose] public section

namespace Subsemiring

section CommRing

variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
        (P : Subsemiring R) (P' : Subsemiring S)

namespace IsPreordering

variable [P.IsPreordering]

variable {P} in
theorem of_le {Q : Subsemiring R} (hPQ : P ≤ Q) (hQ : -1 ∉ Q) : Q.IsPreordering where

variable {P} in
@[aesop 90% (rule_sets := [SetLike])]
theorem unitsInv_mem {a : Rˣ} (ha : ↑a ∈ P) : ↑a⁻¹ ∈ P := by
  have : (a * (a⁻¹ * a⁻¹) : R) ∈ P := by aesop (config := { enableSimp := false })
  simp_all

theorem one_notMem_toAddSubmonoid_support : 1 ∉ P.toAddSubmonoid.support :=
  fun h => P.neg_one_notMem h.2

theorem one_notMem_support [P.HasIdealSupport] : 1 ∉ P.support := by
  simpa using one_notMem_toAddSubmonoid_support P

theorem toAddSubmonoid_support_ne_top : P.toAddSubmonoid.support ≠ ⊤ :=
  fun h => one_notMem_toAddSubmonoid_support P (by simp [h])

theorem support_ne_top [P.HasIdealSupport] : P.support ≠ ⊤ := by
  apply_fun Submodule.toAddSubgroup
  simpa using toAddSubmonoid_support_ne_top P

variable {P} in
theorem isOrdering_iff :
    P.IsOrdering ↔ ∀ a b : R, -(a * b) ∈ P → a ∈ P ∨ b ∈ P where
  mp _ a b _ := by
    by_contra
    have : ∀ (a : R), a ∈ P ∨ -a ∈ P := by aesop
    have : a * b ∈ P := by simpa using mul_mem (by grind : -a ∈ P) (by grind : -b ∈ P)
    have : a ∈ P.support ∨ b ∈ P.support :=
      Ideal.IsPrime.mem_or_mem inferInstance (by aesop)
    aesop
  mpr h :=
    have : P.IsSpanning := by aesop
    .mk' this {
      ne_top' :=
        have := this.hasIdealSupport
        IsPreordering.support_ne_top P
      mem_or_mem' {x} {y} := by
        by_contra
        have := h (-x) y
        have := h (-x) (-y)
        have := h x y
        have := h x (-y)
        cases (by simp_all : x ∈ P ∨ -x ∈ P) <;> aesop
    }

theorem hasIdealSupport_of_isUnit_two (h : IsUnit (2 : R)) : P.HasIdealSupport where
  smul_mem_support x a _ := by
    rcases h.exists_right_inv with ⟨half, h2⟩
    set y := (1 + x) * half
    set z := (1 - x) * half
    rw [show x = y ^ 2 - z ^ 2 by
      linear_combination (- x - x * half * 2) * h2]
    ring_nf
    aesop (add simp sub_eq_add_neg)

instance [h : Fact (IsUnit (2 : R))] : P.HasIdealSupport := hasIdealSupport_of_isUnit_two P h.out

end IsPreordering

variable {P} in
theorem IsPreordering.of_isSpanning_of_isPointed [Nontrivial R]
    (hP₁ : P.IsSpanning) (hP₂ : P.IsPointed) : P.IsPreordering :=
  .of_support_ne_top hP₁ (by simp [*])

variable {P} in
instance IsOrdering.of_isSpanning_of_isPointed [IsDomain R]
    (hP₁ : P.IsSpanning) (hP₂ : P.IsPointed) : P.IsOrdering := .mk' hP₁ <| by
  simpa [*] using Ideal.isPrime_bot

variable {P} in
theorem IsPreordering.of_isPointed [Nontrivial R]
    (hP : P.IsPointed) (h : .sumSq R ≤ P) : P.IsPreordering where

end CommRing

section Field

variable {F : Type*} [Field F] (P : Subsemiring F)

namespace IsPreordering

variable [P.IsPreordering]

variable {P} in
@[aesop 90% (rule_sets := [SetLike])]
theorem inv_mem {a : F} (ha : a ∈ P) : a⁻¹ ∈ P := by
  have mem : a * (a⁻¹ * a⁻¹) ∈ P := by aesop
  field_simp at mem
  simp_all

theorem isPointed : P.IsPointed := fun {x} _ _ ↦ by
  by_contra
  have mem : -x * x⁻¹ ∈ P := by aesop (erase simp neg_mul)
  field_simp at mem
  exact P.neg_one_notMem mem

instance : P.HasIdealSupport := (IsPreordering.isPointed P).hasIdealSupport

instance : P.support.IsPrime := by simpa [IsPreordering.isPointed P] using Ideal.isPrime_bot

end IsPreordering

end Field

end Subsemiring


variable {R : Type*} [CommRing R]

namespace RingPreordering

set_option linter.deprecated false in
@[deprecated "no replacement" (since := "2026-04-15"), gcongr]
theorem toSubsemiring_le_toSubsemiring {P₁ P₂ : RingPreordering R} :
    P₁.toSubsemiring ≤ P₂.toSubsemiring ↔ P₁ ≤ P₂ := .rfl

set_option linter.deprecated false in
@[deprecated "no replacement" (since := "2026-04-15"), gcongr]
theorem toSubsemiring_lt_toSubsemiring {P₁ P₂ : RingPreordering R} :
    P₁.toSubsemiring < P₂.toSubsemiring ↔ P₁ < P₂ := .rfl

set_option linter.deprecated false in
@[deprecated "no replacement" (since := "2026-04-15"), mono]
theorem toSubsemiring_mono : Monotone (toSubsemiring : RingPreordering R → _) :=
  fun _ _ => id

set_option linter.deprecated false in
@[deprecated "no replacement" (since := "2026-04-15"), mono]
theorem toSubsemiring_strictMono : StrictMono (toSubsemiring : RingPreordering R → _) :=
  fun _ _ => id

set_option linter.deprecated false in
@[deprecated Subsemiring.IsPreordering.unitsInv_mem (since := "2026-04-15"),
  aesop unsafe 90% apply (rule_sets := [SetLike])]
theorem unitsInv_mem {P : RingPreordering R} {a : Rˣ} (ha : ↑a ∈ P) : ↑a⁻¹ ∈ P := by
  have : (a * (a⁻¹ * a⁻¹) : R) ∈ P := by aesop (config := { enableSimp := false })
  simp_all

set_option linter.deprecated false in
@[deprecated Subsemiring.IsPreordering.inv_mem (since := "2026-04-15"),
  aesop unsafe 90% apply (rule_sets := [SetLike])]
theorem inv_mem {F : Type*} [Field F] {P : RingPreordering F} {a : F} (ha : a ∈ P) :
    a⁻¹ ∈ P := by
  have mem : a * (a⁻¹ * a⁻¹) ∈ P := by aesop
  field_simp at mem
  simp_all

set_option linter.deprecated false in
@[deprecated Subsemiring.mem_of_isSumSq (since := "2026-04-15"),
  aesop unsafe 80% apply (rule_sets := [SetLike])]
theorem mem_of_isSumSq {P : RingPreordering R} {x : R} (hx : IsSumSq x) : x ∈ P := by
  induction hx using IsSumSq.rec' <;> aesop

section mk'

variable {R : Type*} [CommRing R] {P : Set R} {add} {mul} {sq} {neg_one}

set_option linter.deprecated false in
/-- Construct a preordering from a minimal set of axioms. -/
@[deprecated "no replacement" (since := "2026-04-15")]
def mk' {R : Type*} [CommRing R] (P : Set R)
    (add : ∀ {x y : R}, x ∈ P → y ∈ P → x + y ∈ P)
    (mul : ∀ {x y : R}, x ∈ P → y ∈ P → x * y ∈ P)
    (sq : ∀ x : R, x * x ∈ P)
    (neg_one : -1 ∉ P) :
    RingPreordering R where
  carrier := P
  add_mem' {x y} := by simpa using add
  mul_mem' {x y} := by simpa using mul
  zero_mem' := by simpa using sq 0
  one_mem' := by simpa using sq 1

set_option linter.deprecated false in
@[deprecated "no replacement" (since := "2026-04-15"), simp]
theorem mem_mk' {x : R} : x ∈ mk' P add mul sq neg_one ↔ x ∈ P := .rfl

set_option linter.deprecated false in
@[deprecated "no replacement" (since := "2026-04-15"), simp, norm_cast]
theorem coe_mk' : mk' P add mul sq neg_one = P := rfl

end mk'

section ne_top

set_option linter.deprecated false in
@[deprecated Subsemiring.IsPreordering.one_notMem_toAddSubmonoid_support (since := "2026-04-15")]
theorem one_notMem_supportAddSubgroup (P : RingPreordering R) : 1 ∉ P.supportAddSubgroup :=
  fun h => RingPreordering.neg_one_notMem P h.2

set_option linter.deprecated false in
@[deprecated Subsemiring.IsPreordering.one_notMem_support (since := "2026-04-15")]
theorem one_notMem_support (P : RingPreordering R) [P.HasIdealSupport] : 1 ∉ P.support := by
  simpa using one_notMem_supportAddSubgroup P

set_option linter.deprecated false in
@[deprecated Subsemiring.IsPreordering.toAddSubmonoid_support_ne_top (since := "2026-04-15")]
theorem supportAddSubgroup_ne_top (P : RingPreordering R) : P.supportAddSubgroup ≠ ⊤ :=
  fun h => RingPreordering.neg_one_notMem P (by simp [h] : 1 ∈ P.supportAddSubgroup).2

set_option linter.deprecated false in
@[deprecated Subsemiring.IsPreordering.support_ne_top (since := "2026-04-15")]
theorem support_ne_top (P : RingPreordering R) [P.HasIdealSupport] : P.support ≠ ⊤ := by
  apply_fun Submodule.toAddSubgroup
  simpa using supportAddSubgroup_ne_top P

set_option linter.deprecated false in
/-- Constructor for IsOrdering that doesn't require `ne_top'`. -/
@[deprecated Subsemiring.IsOrdering.mk' (since := "2026-04-15")]
theorem IsOrdering.mk' (P : RingPreordering R) [HasMemOrNegMem P]
    (h : ∀ {x y}, x * y ∈ P.support → x ∈ P.support ∨ y ∈ P.support) : P.IsOrdering where
  ne_top' := support_ne_top P
  mem_or_mem' := h

end ne_top

namespace HasIdealSupport

set_option linter.deprecated false in
@[deprecated Subsemiring.smul_mem (since := "2026-04-15")]
theorem smul_mem (P : RingPreordering R) [P.HasIdealSupport]
    (x : R) {a : R} (h₁a : a ∈ P) (h₂a : -a ∈ P) : x * a ∈ P := by
  rw [hasIdealSupport_iff] at ‹P.HasIdealSupport›
  simp [*]

set_option linter.deprecated false in
@[deprecated Subsemiring.neg_smul_mem (since := "2026-04-15")]
theorem neg_smul_mem (P : RingPreordering R) [P.HasIdealSupport]
    (x : R) {a : R} (h₁a : a ∈ P) (h₂a : -a ∈ P) : -(x * a) ∈ P := by
  rw [hasIdealSupport_iff] at ‹P.HasIdealSupport›
  simp [*]

end HasIdealSupport

set_option linter.deprecated false in
@[deprecated Subsemiring.IsPreordering.hasIdealSupport_of_isUnit_two (since := "2026-04-15")]
theorem hasIdealSupport_of_isUnit_two {P : RingPreordering R} (h : IsUnit (2 : R)) :
    P.HasIdealSupport := by
  rw [hasIdealSupport_iff]
  intro x a _ _
  rcases h.exists_right_inv with ⟨half, h2⟩
  set y := (1 + x) * half
  set z := (1 - x) * half
  rw [show x = y ^ 2 - z ^ 2 by
    linear_combination (-x - x * half * 2) * h2]
  ring_nf
  aesop (add simp sub_eq_add_neg)

set_option linter.deprecated false in
@[deprecated Subsemiring.IsPreordering.instHasIdealSupportOfFactIsUnitOfNat (since := "2026-04-15")]
instance (P : RingPreordering R) [h : Fact (IsUnit (2 : R))] : P.HasIdealSupport :=
    hasIdealSupport_of_isUnit_two h.out

section Field

variable {F : Type*} [Field F]

set_option linter.deprecated false in
@[deprecated "use `Subsemiring.IsPreordering.isPointed`" (since := "2026-04-15"),
  aesop unsafe 70% apply]
protected theorem eq_zero_of_mem_of_neg_mem
    {P : RingPreordering F} {x} (h : x ∈ P) (h2 : -x ∈ P) : x = 0 := by
  by_contra
  have mem : -x * x⁻¹ ∈ P := by aesop (erase simp neg_mul)
  field_simp at mem
  exact RingPreordering.neg_one_notMem P mem

set_option linter.deprecated false in
@[deprecated "use `Subsemiring.IsPreordering.isPointed`" (since := "2026-04-15")]
theorem supportAddSubgroup_eq_bot (P : RingPreordering F) : P.supportAddSubgroup = ⊥ := by
  ext; aesop (add simp mem_supportAddSubgroup)

set_option linter.deprecated false in
@[deprecated Subsemiring.IsPreordering.instHasIdealSupport (since := "2026-04-15")]
instance (P : RingPreordering F) : P.HasIdealSupport where
  smul_mem_support := by simp [supportAddSubgroup_eq_bot]

set_option linter.deprecated false in
@[deprecated "use `Subsemiring.IsPreordering.isPointed`" (since := "2026-04-15"), simp]
theorem support_eq_bot (P : RingPreordering F) : P.support = ⊥ := by
  simpa [← Submodule.toAddSubgroup_inj] using supportAddSubgroup_eq_bot P

set_option linter.deprecated false in
@[deprecated Subsemiring.IsPreordering.instIsPrimeSupport (since := "2026-04-15")]
instance (P : RingPreordering F) : P.support.IsPrime := by simpa using Ideal.isPrime_bot

end Field

set_option linter.deprecated false in
@[deprecated Subsemiring.IsPreordering.isOrdering_iff (since := "2026-04-15")]
theorem isOrdering_iff {P : RingPreordering R} :
    P.IsOrdering ↔ ∀ a b : R, -(a * b) ∈ P → a ∈ P ∨ b ∈ P := by
  refine ⟨fun _ a b _ => ?_, fun h => ?_⟩
  · by_contra
    have : a * b ∈ P := by simpa using mul_mem (by aesop : -a ∈ P) (by aesop : -b ∈ P)
    have : a ∈ P.support ∨ b ∈ P.support :=
      Ideal.IsPrime.mem_or_mem inferInstance (by simp_all [mem_support])
    simp_all [mem_support]
  · have : HasMemOrNegMem P := ⟨by simp [h]⟩
    refine IsOrdering.mk' P (fun {x y} _ => ?_)
    by_contra
    have := h (-x) y
    have := h (-x) (-y)
    have := h x y
    have := h x (-y)
    cases (by aesop : x ∈ P ∨ -x ∈ P) <;> simp_all [mem_support]

end RingPreordering
