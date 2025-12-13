/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Mario Carneiro, Yuyang Zhao
-/
module

public import Mathlib.RingTheory.Ideal.Lattice

/-!

# Prime ideals

This file contains the definition of `Ideal.IsPrime` for prime ideals.

## TODO

Support right ideals, and two-sided ideals over non-commutative rings.
-/

@[expose] public section


universe u v w

variable {α : Type u} {β : Type v} {F : Type w}

open Set Function

open Pointwise

section Semiring

namespace Ideal

variable [Semiring α] (I : Ideal α) {a b : α}

/-- An ideal `P` of a ring `R` is prime if `P ≠ R` and `(∀ a, x * a * y ∈ P) → x ∈ P ∨ y ∈ P`. -/
class IsPrime (I : Ideal α) : Prop where
  /-- The prime ideal is not the entire ring. -/
  ne_top' : I ≠ ⊤
  /-- If `x * a * y` lies in the prime ideal for all `a`, then at least one element lies in the
  prime ideal. -/
  mem_or_mem_of_forall' : ∀ {x y : α}, (∀ a, x * a * y ∈ I) → x ∈ I ∨ y ∈ I

/--
An ideal `P` of a ring `R` is completely prime if `P ≠ R` and `xy ∈ P → x ∈ P ∨ y ∈ P`.

It's equivalent to `Ideal.IsPrime` in commutative rings.
-/
class IsCompletelyPrime (I : Ideal α) : Prop where
  /-- The prime ideal is not the entire ring. -/
  ne_top' : I ≠ ⊤
  /-- If a product lies in the completely prime ideal, then at least one element lies in the
  completely prime ideal. -/
  mem_or_mem' : ∀ {x y : α}, x * y ∈ I → x ∈ I ∨ y ∈ I

instance (priority := 100) IsCompletelyPrime.isPrime [I.IsCompletelyPrime] : I.IsPrime where
  ne_top' := IsCompletelyPrime.ne_top'
  mem_or_mem_of_forall' h := IsCompletelyPrime.mem_or_mem' (by simpa using h 1)

theorem isPrime_iff {I : Ideal α} :
    IsPrime I ↔ I ≠ ⊤ ∧ ∀ {x y : α}, (∀ a, x * a * y ∈ I) → x ∈ I ∨ y ∈ I :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

theorem IsPrime.ne_top {I : Ideal α} (hI : I.IsPrime) : I ≠ ⊤ :=
  hI.1

theorem IsCompletelyPrime.ne_top {I : Ideal α} (hI : I.IsCompletelyPrime) : I ≠ ⊤ :=
  hI.1

theorem IsPrime.one_notMem {I : Ideal α} (hI : I.IsPrime) : 1 ∉ I :=
  mt (eq_top_iff_one I).2 hI.1

theorem one_notMem (I : Ideal α) [hI : I.IsPrime] : 1 ∉ I :=
  hI.one_notMem

theorem IsCompletelyPrime.mem_or_mem {I : Ideal α} (hI : I.IsCompletelyPrime) {x y : α} :
    x * y ∈ I → x ∈ I ∨ y ∈ I :=
  hI.2

theorem IsCompletelyPrime.mul_mem_iff_mem_or_mem [I.IsTwoSided] (hI : I.IsCompletelyPrime) :
    ∀ {x y : α}, x * y ∈ I ↔ x ∈ I ∨ y ∈ I := @fun x y =>
  ⟨hI.mem_or_mem, by
    rintro (h | h)
    exacts [I.mul_mem_right y h, I.mul_mem_left x h]⟩

theorem IsPrime.mem_or_mem_of_forall {I : Ideal α} (hI : I.IsPrime) {x y : α} :
    (∀ a, x * a * y ∈ I) → x ∈ I ∨ y ∈ I :=
  hI.2

theorem bot_isCompletelyPrime [Nontrivial α] [NoZeroDivisors α] : (⊥ : Ideal α).IsCompletelyPrime :=
  ⟨fun h => one_ne_zero (α := α) (by rwa [Ideal.eq_top_iff_one, Submodule.mem_bot] at h), fun h =>
    mul_eq_zero.mp (by simpa only [Submodule.mem_bot] using h)⟩

theorem bot_prime [Nontrivial α] [NoZeroDivisors α] : (⊥ : Ideal α).IsPrime :=
  bot_isCompletelyPrime.isPrime

lemma IsCompletelyPrime.mul_mem_left_iff {I : Ideal α} [I.IsTwoSided] [I.IsCompletelyPrime]
    {x y : α} (hx : x ∉ I) : x * y ∈ I ↔ y ∈ I := by
  rw [Ideal.IsCompletelyPrime.mul_mem_iff_mem_or_mem] <;> aesop

lemma IsCompletelyPrime.mul_mem_right_iff {I : Ideal α} [I.IsTwoSided] [I.IsCompletelyPrime]
    {x y : α} (hx : y ∉ I) : x * y ∈ I ↔ x ∈ I := by
  rw [Ideal.IsCompletelyPrime.mul_mem_iff_mem_or_mem] <;> aesop

/-- The complement of a prime ideal `P ⊆ R` is a submonoid of `R`. -/
def primeCompl (P : Ideal α) [hp : P.IsCompletelyPrime] : Submonoid α where
  carrier := (Pᶜ : Set α)
  one_mem' := P.one_notMem
  mul_mem' {_ _} hnx hny hxy := Or.casesOn (hp.mem_or_mem hxy) hnx hny

@[simp]
theorem mem_primeCompl_iff [I.IsCompletelyPrime] {x : α} :
    x ∈ I.primeCompl ↔ x ∉ I := Iff.rfl

end Ideal

end Semiring

section CommSemiring

namespace Ideal

variable [CommSemiring α] {I : Ideal α} {a b : α}

theorem IsPrime.of_comm (ne_top : I ≠ ⊤)
    (mem_or_mem : ∀ {x y : α}, x * y ∈ I → x ∈ I ∨ y ∈ I) :
    IsPrime I :=
  ⟨ne_top, fun h ↦ mem_or_mem (by simpa using h 1)⟩

theorem IsPrime.mem_or_mem (hI : I.IsPrime) {x y : α} (h : x * y ∈ I) :
    x ∈ I ∨ y ∈ I :=
  hI.mem_or_mem_of_forall fun a ↦ by simpa [mul_right_comm] using I.mul_mem_right _ h

instance (priority := 50) IsPrime.isCompletelyPrime [I.IsPrime] : I.IsCompletelyPrime where
  ne_top' := IsPrime.ne_top'
  mem_or_mem' := IsPrime.mem_or_mem inferInstance

lemma isCompletelyPrime_iff_isPrime : I.IsCompletelyPrime ↔ I.IsPrime :=
  ⟨(·.isPrime), (·.isCompletelyPrime)⟩

theorem isPrime_iff_of_comm :
    IsPrime I ↔ I ≠ ⊤ ∧ ∀ {x y : α}, x * y ∈ I → x ∈ I ∨ y ∈ I :=
  ⟨fun hI ↦ ⟨hI.1, hI.mem_or_mem⟩, And.elim .of_comm⟩

theorem IsPrime.mul_notMem (hI : I.IsPrime) {x y : α} :
    x ∉ I → y ∉ I → x * y ∉ I := fun hx hy h ↦
  hy ((hI.mem_or_mem h).resolve_left hx)

@[deprecated (since := "2025-05-23")] alias IsPrime.mul_not_mem := IsPrime.mul_notMem

theorem IsPrime.mem_or_mem_of_mul_eq_zero (hI : I.IsPrime) {x y : α} (h : x * y = 0) :
    x ∈ I ∨ y ∈ I :=
  hI.mem_or_mem (h.symm ▸ I.zero_mem)

theorem IsPrime.mem_of_pow_mem (hI : I.IsPrime) {r : α} (n : ℕ) (H : r ^ n ∈ I) :
    r ∈ I := by
  induction n with
  | zero =>
    rw [pow_zero] at H
    exact hI.one_notMem.elim H
  | succ n ih =>
    rw [pow_succ] at H
    exact Or.casesOn (hI.mem_or_mem H) ih id

theorem not_isPrime_iff :
    ¬I.IsPrime ↔ I = ⊤ ∨ ∃ (x : α) (_hx : x ∉ I) (y : α) (_hy : y ∉ I), x * y ∈ I := by
  simp_rw [Ideal.isPrime_iff_of_comm, not_and_or, Ne, Classical.not_not, not_forall, not_or]
  exact
    or_congr Iff.rfl
      ⟨fun ⟨x, y, hxy, hx, hy⟩ => ⟨x, hx, y, hy, hxy⟩, fun ⟨x, hx, y, hy, hxy⟩ =>
        ⟨x, y, hxy, hx, hy⟩⟩

theorem IsPrime.mul_mem_iff_mem_or_mem (hI : I.IsPrime) :
    ∀ {x y : α}, x * y ∈ I ↔ x ∈ I ∨ y ∈ I := @fun x y =>
  ⟨hI.mem_or_mem, by
    rintro (h | h)
    exacts [I.mul_mem_right y h, I.mul_mem_left x h]⟩

theorem IsPrime.pow_mem_iff_mem (hI : I.IsPrime) {r : α} (n : ℕ) (hn : 0 < n) :
    r ^ n ∈ I ↔ r ∈ I :=
  ⟨hI.mem_of_pow_mem n, fun hr => I.pow_mem_of_mem hr n hn⟩

lemma IsPrime.mul_mem_left_iff {I : Ideal α} [I.IsPrime]
    {x y : α} (hx : x ∉ I) : x * y ∈ I ↔ y ∈ I := by
  rw [Ideal.IsPrime.mul_mem_iff_mem_or_mem] <;> aesop

lemma IsPrime.mul_mem_right_iff {I : Ideal α} [I.IsPrime]
    {x y : α} (hx : y ∉ I) : x * y ∈ I ↔ x ∈ I := by
  rw [Ideal.IsPrime.mul_mem_iff_mem_or_mem] <;> aesop

end Ideal

end CommSemiring

section CommRing

theorem IsDomain.of_bot_isPrime (A : Type*) [CommRing A] [hbp : (⊥ : Ideal A).IsPrime] :
    IsDomain A :=
  @NoZeroDivisors.to_isDomain A _ ⟨1, 0, fun h => hbp.one_notMem h⟩ ⟨fun h => hbp.mem_or_mem h⟩

end CommRing

section DivisionSemiring

variable {K : Type u} [DivisionSemiring K] (I : Ideal K)

namespace Ideal

theorem eq_bot_of_prime [h : I.IsPrime] : I = ⊥ :=
  or_iff_not_imp_right.mp I.eq_bot_or_top h.1

end Ideal

end DivisionSemiring
