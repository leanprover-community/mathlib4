/-
Copyright (c) 2024 Florent Schaffhauser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florent Schaffhauser, Artie Khovanov
-/
module

public import Mathlib.Algebra.Order.Ring.Ordering.Defs
public import Mathlib.Algebra.Ring.SumsOfSquares

import Mathlib.Algebra.Field.IsField
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

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
        {P : Subsemiring R} {P' : Subsemiring S}

namespace IsPreordering

theorem mono (hP : P.IsPreordering) {Q : Subsemiring R} (hPQ : P ≤ Q) (hQ : -1 ∉ Q) :
    Q.IsPreordering where

theorem unitsInv_mem (hP : P.IsPreordering) {a : Rˣ} (ha : ↑a ∈ P) : ↑a⁻¹ ∈ P := by
  simpa using show (a * (a⁻¹ * a⁻¹) : R) ∈ P by membership

grind_pattern [membership] unitsInv_mem => P.IsPreordering, ↑a⁻¹ ∈ P

theorem one_notMem_support (hP : P.IsPreordering) : 1 ∉ P.support := fun h ↦ hP.neg_one_notMem h.2

theorem support_ne_top (hP : P.IsPreordering) : P.support ≠ ⊤ := fun h ↦
  one_notMem_support hP (by simp [h])

theorem isOrdering_iff (hP : P.IsPreordering) :
    P.IsOrdering ↔ ∀ a b : R, -(a * b) ∈ P → a ∈ P ∨ b ∈ P where
  mp hP a b _ := by
    by_contra
    have : a * b ∈ P := by
      grind [membership, mul_neg, neg_mul, neg_neg, Subsemiring.isSpanning_def.mp hP.isSpanning]
    have : a ∈ P.support ∨ b ∈ P.support :=
      Ideal.IsPrime.mem_or_mem hP.isPrime_supportIdeal (by simp; grind)
    grind [Subsemiring.mem_support]
  mpr h := by
    refine ⟨?_, hP.support_ne_top, fun {x y} ↦ ?_⟩
    · grind [membership, mul_neg, neg_mul, neg_neg, Subsemiring.isSpanning_def]
    · have := h (-x) y
      grind [membership, mul_neg, neg_mul, neg_neg, Subsemiring.mem_support]

theorem mul_mem_support_of_right (hP : P.IsPreordering) (h : IsUnit (2 : R))
    (x : R) {a : R} (ha : a ∈ P.support) : x * a ∈ P.support := by
  rcases h.exists_right_inv with ⟨half, h2⟩
  rw [Subsemiring.mem_support] at *
  suffices ((1 + x) * half) ^ 2 * a + ((1 - x) * half) ^ 2 * (- a) ∈ P ∧
           ((1 + x) * half) ^ 2 * (- a) + ((1 - x) * half) ^ 2 * a ∈ P by grind
  membership

theorem mul_mem_support_of_left (hP : P.IsPreordering) (h : IsUnit (2 : R))
    (x : R) {a : R} (ha : a ∈ P.support) : a * x ∈ P.support :=
  (mul_comm _ x) ▸ hP.mul_mem_support_of_right h _ ha

end IsPreordering

theorem IsPreordering.of_isSpanning_of_isPointed [Nontrivial R]
    (hP₁ : P.IsSpanning) (hP₂ : P.IsPointed) : P.IsPreordering :=
  .of_ne_top hP₁ fun _ ↦ by simp_all [AddSubmonoid.not_isPointed_top]

theorem IsPreordering.of_isPointed_of_sumSq_le [Nontrivial R]
    (hP : P.IsPointed) (h : .sumSq R ≤ P) : P.IsPreordering where
  mem_of_isSquare hx := by grind [membership, mem_sumSq]
  neg_one_notMem := by grind [membership, Subsemiring.isPointed_def, one_ne_zero]

theorem IsOrdering.of_isSpanning_of_isPointed [IsDomain R]
    (hP₁ : P.IsSpanning) (hP₂ : P.IsPointed) : P.IsOrdering where
  isSpanning := hP₁
  support_ne_top := by simp [hP₂]
  mem_support_or_mem_support := by simp [hP₂]

end CommRing

section Field

variable {F : Type*} [Field F] {P : Subsemiring F}

namespace IsPreordering

theorem inv_mem (hP : IsPreordering P) {a : F} (ha : a ∈ P) : a⁻¹ ∈ P := by
  suffices a * (a⁻¹ * a⁻¹) ∈ P by grind
  membership

grind_pattern [membership] inv_mem => P.IsPreordering, a⁻¹ ∈ P

theorem isPointed (hP : IsPreordering P) : P.IsPointed := by
  grind [membership, Subsemiring.isPointed_def]

end IsPreordering

end Field

/- Deprecated -/

variable {R : Type*} [CommRing R]

namespace RingPreordering

@[deprecated "no replacement" (since := "2026-10-14"), gcongr]
theorem toSubsemiring_le_toSubsemiring {P₁ P₂ : RingPreordering R} :
    P₁.toSubsemiring ≤ P₂.toSubsemiring ↔ P₁ ≤ P₂ := .rfl

@[deprecated "no replacement" (since := "2026-10-14"), gcongr]
theorem toSubsemiring_lt_toSubsemiring {P₁ P₂ : RingPreordering R} :
    P₁.toSubsemiring < P₂.toSubsemiring ↔ P₁ < P₂ := .rfl

@[deprecated "no replacement" (since := "2026-10-14"), mono]
theorem toSubsemiring_mono : Monotone (toSubsemiring : RingPreordering R → _) :=
  fun _ _ => id

@[deprecated "no replacement" (since := "2026-10-14"), mono]
theorem toSubsemiring_strictMono : StrictMono (toSubsemiring : RingPreordering R → _) :=
  fun _ _ => id

set_option linter.deprecated false in
@[deprecated Subsemiring.IsPreordering.unitsInv_mem +typeChanged (since := "2026-10-14"),
  aesop unsafe 90% apply (rule_sets := [SetLike])]
theorem unitsInv_mem {P : RingPreordering R} {a : Rˣ} (ha : ↑a ∈ P) : ↑a⁻¹ ∈ P := by
  have : (a * (a⁻¹ * a⁻¹) : R) ∈ P := by aesop (config := { enableSimp := false })
  simp_all

set_option linter.deprecated false in
@[deprecated Subsemiring.IsPreordering.inv_mem +typeChanged (since := "2026-10-14"),
  aesop unsafe 90% apply (rule_sets := [SetLike])]
theorem inv_mem {F : Type*} [Field F] {P : RingPreordering F} {a : F} (ha : a ∈ P) :
    a⁻¹ ∈ P := by
  have mem : a * (a⁻¹ * a⁻¹) ∈ P := by aesop
  field_simp at mem
  simp_all

set_option linter.deprecated false in
@[deprecated Subsemiring.IsPreordering.mem_of_isSumSq +typeChanged (since := "2026-10-14"),
  aesop unsafe 80% apply (rule_sets := [SetLike])]
theorem mem_of_isSumSq {P : RingPreordering R} {x : R} (hx : IsSumSq x) : x ∈ P := by
  induction hx using IsSumSq.rec' <;> aesop

section mk'

variable {R : Type*} [CommRing R] {P : Set R} {add} {mul} {sq} {neg_one}

/-- Construct a preordering from a minimal set of axioms. -/
@[deprecated "no replacement" (since := "2026-10-14")]
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

@[deprecated "no replacement" (since := "2026-10-14"), simp]
theorem mem_mk' {x : R} : x ∈ mk' P add mul sq neg_one ↔ x ∈ P := .rfl

@[deprecated "no replacement" (since := "2026-10-14"), simp, norm_cast]
theorem coe_mk' : mk' P add mul sq neg_one = P := rfl

end mk'

section ne_top

@[deprecated Subsemiring.IsPreordering.one_notMem_support +typeChanged (since := "2026-10-14")]
theorem one_notMem_supportAddSubgroup (P : RingPreordering R) : 1 ∉ P.supportAddSubgroup :=
  fun h => RingPreordering.neg_one_notMem P h.2

@[deprecated Subsemiring.IsPreordering.one_notMem_support +typeChanged (since := "2026-10-14")]
theorem one_notMem_support (P : RingPreordering R) [P.HasIdealSupport] : 1 ∉ P.support := by
  simpa using one_notMem_supportAddSubgroup P

@[deprecated Subsemiring.IsPreordering.support_ne_top +typeChanged (since := "2026-10-14")]
theorem supportAddSubgroup_ne_top (P : RingPreordering R) : P.supportAddSubgroup ≠ ⊤ :=
  fun h => RingPreordering.neg_one_notMem P (by simp [h] : 1 ∈ P.supportAddSubgroup).2

@[deprecated Subsemiring.IsPreordering.support_ne_top +typeChanged (since := "2026-10-14")]
theorem support_ne_top (P : RingPreordering R) [P.HasIdealSupport] : P.support ≠ ⊤ := by
  apply_fun Submodule.toAddSubgroup
  simpa using supportAddSubgroup_ne_top P

@[deprecated
"no replacement; use `Subsemiring.IsPreordering.support_ne_top`" (since := "2026-10-14")]
theorem IsOrdering.mk' (P : RingPreordering R) [HasMemOrNegMem P]
    (h : ∀ {x y}, x * y ∈ P.support → x ∈ P.support ∨ y ∈ P.support) : P.IsOrdering where
  ne_top' := support_ne_top P
  mem_or_mem' := h

end ne_top

namespace HasIdealSupport

@[deprecated "no replacement" (since := "2026-10-14")]
theorem smul_mem (P : RingPreordering R) [P.HasIdealSupport]
    (x : R) {a : R} (h₁a : a ∈ P) (h₂a : -a ∈ P) : x * a ∈ P := by
  rw [hasIdealSupport_iff] at ‹P.HasIdealSupport›
  simp [*]

@[deprecated "no replacement" (since := "2026-10-14")]
theorem neg_smul_mem (P : RingPreordering R) [P.HasIdealSupport]
    (x : R) {a : R} (h₁a : a ∈ P) (h₂a : -a ∈ P) : -(x * a) ∈ P := by
  rw [hasIdealSupport_iff] at ‹P.HasIdealSupport›
  simp [*]

end HasIdealSupport

@[deprecated
Subsemiring.IsPreordering.mul_mem_support_of_right +typeChanged (since := "2026-10-14")]
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

@[deprecated
Subsemiring.IsPreordering.mul_mem_support_of_right +typeChanged (since := "2026-10-14")]
instance (P : RingPreordering R) [h : Fact (IsUnit (2 : R))] : P.HasIdealSupport :=
    hasIdealSupport_of_isUnit_two h.out

section Field

variable {F : Type*} [Field F]

set_option linter.deprecated false in
@[deprecated "use `Subsemiring.IsPreordering.isPointed`" (since := "2026-10-14"),
  aesop unsafe 70% apply]
protected theorem eq_zero_of_mem_of_neg_mem
    {P : RingPreordering F} {x} (h : x ∈ P) (h2 : -x ∈ P) : x = 0 := by
  by_contra
  have mem : -x * x⁻¹ ∈ P := by aesop (erase simp neg_mul)
  field_simp at mem
  exact RingPreordering.neg_one_notMem P mem

@[deprecated "use `Subsemiring.IsPreordering.isPointed`" (since := "2026-10-14")]
theorem supportAddSubgroup_eq_bot (P : RingPreordering F) : P.supportAddSubgroup = ⊥ := by
  ext; aesop (add simp mem_supportAddSubgroup)

@[deprecated "no replacement" (since := "2026-10-14")]
instance (P : RingPreordering F) : P.HasIdealSupport where
  smul_mem_support := by simp [supportAddSubgroup_eq_bot]

@[deprecated "use `Subsemiring.IsPreordering.isPointed`" (since := "2026-10-14"), simp]
theorem support_eq_bot (P : RingPreordering F) : P.support = ⊥ := by
  simpa [← Submodule.toAddSubgroup_inj] using supportAddSubgroup_eq_bot P

@[deprecated "no replacement" (since := "2026-10-14")]
instance (P : RingPreordering F) : P.support.IsPrime := by simpa using Ideal.isPrime_bot

end Field

@[deprecated Subsemiring.IsPreordering.isOrdering_iff +typeChanged (since := "2026-10-14")]
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

end Subsemiring
