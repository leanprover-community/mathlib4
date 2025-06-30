/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Mario Carneiro
-/
import Mathlib.RingTheory.Ideal.Lattice

/-!

# Prime ideals

This file contains the definition of `Ideal.IsPrime` for prime ideals.

## TODO

Support right ideals, and two-sided ideals over non-commutative rings.
-/


universe u v w

variable {α : Type u} {β : Type v} {F : Type w}

open Set Function

open Pointwise

section Semiring

namespace Ideal

variable [Semiring α] (I : Ideal α) {a b : α}

/-- An ideal `P` of a ring `R` is prime if `P ≠ R` and `xy ∈ P → x ∈ P ∨ y ∈ P` -/
class IsPrime (I : Ideal α) : Prop where
  /-- The prime ideal is not the entire ring. -/
  ne_top' : I ≠ ⊤
  /-- If a product lies in the prime ideal, then at least one element lies in the prime ideal. -/
  mem_or_mem' : ∀ {x y : α}, x * y ∈ I → x ∈ I ∨ y ∈ I

theorem isPrime_iff {I : Ideal α} : IsPrime I ↔ I ≠ ⊤ ∧ ∀ {x y : α}, x * y ∈ I → x ∈ I ∨ y ∈ I :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

theorem IsPrime.ne_top {I : Ideal α} (hI : I.IsPrime) : I ≠ ⊤ :=
  hI.1

theorem IsPrime.one_notMem {I : Ideal α} (hI : I.IsPrime) : 1 ∉ I :=
  mt (eq_top_iff_one I).2 hI.1

theorem one_notMem (I : Ideal α) [hI : I.IsPrime] : 1 ∉ I :=
  hI.one_notMem

theorem IsPrime.mem_or_mem {I : Ideal α} (hI : I.IsPrime) {x y : α} : x * y ∈ I → x ∈ I ∨ y ∈ I :=
  hI.2

theorem IsPrime.mul_notMem {I : Ideal α} (hI : I.IsPrime) {x y : α} :
    x ∉ I → y ∉ I → x * y ∉ I := fun hx hy h ↦
  hy ((hI.mem_or_mem h).resolve_left hx)

@[deprecated (since := "2025-05-23")] alias IsPrime.mul_not_mem := IsPrime.mul_notMem

theorem IsPrime.mem_or_mem_of_mul_eq_zero {I : Ideal α} (hI : I.IsPrime) {x y : α} (h : x * y = 0) :
    x ∈ I ∨ y ∈ I :=
  hI.mem_or_mem (h.symm ▸ I.zero_mem)

theorem IsPrime.mem_of_pow_mem {I : Ideal α} (hI : I.IsPrime) {r : α} (n : ℕ) (H : r ^ n ∈ I) :
    r ∈ I := by
  induction n with
  | zero =>
    rw [pow_zero] at H
    exact hI.one_notMem.elim H
  | succ n ih =>
    rw [pow_succ] at H
    exact Or.casesOn (hI.mem_or_mem H) ih id

theorem not_isPrime_iff {I : Ideal α} :
    ¬I.IsPrime ↔ I = ⊤ ∨ ∃ (x : α) (_hx : x ∉ I) (y : α) (_hy : y ∉ I), x * y ∈ I := by
  simp_rw [Ideal.isPrime_iff, not_and_or, Ne, Classical.not_not, not_forall, not_or]
  exact
    or_congr Iff.rfl
      ⟨fun ⟨x, y, hxy, hx, hy⟩ => ⟨x, hx, y, hy, hxy⟩, fun ⟨x, hx, y, hy, hxy⟩ =>
        ⟨x, y, hxy, hx, hy⟩⟩

theorem bot_prime [Nontrivial α] [NoZeroDivisors α] : (⊥ : Ideal α).IsPrime :=
  ⟨fun h => one_ne_zero (α := α) (by rwa [Ideal.eq_top_iff_one, Submodule.mem_bot] at h), fun h =>
    mul_eq_zero.mp (by simpa only [Submodule.mem_bot] using h)⟩

theorem IsPrime.mul_mem_iff_mem_or_mem {I : Ideal α} [I.IsTwoSided] (hI : I.IsPrime) :
    ∀ {x y : α}, x * y ∈ I ↔ x ∈ I ∨ y ∈ I := @fun x y =>
  ⟨hI.mem_or_mem, by
    rintro (h | h)
    exacts [I.mul_mem_right y h, I.mul_mem_left x h]⟩

theorem IsPrime.pow_mem_iff_mem {I : Ideal α} (hI : I.IsPrime) {r : α} (n : ℕ) (hn : 0 < n) :
    r ^ n ∈ I ↔ r ∈ I :=
  ⟨hI.mem_of_pow_mem n, fun hr => I.pow_mem_of_mem hr n hn⟩

/-- The complement of a prime ideal `P ⊆ R` is a submonoid of `R`. -/
def primeCompl (P : Ideal α) [hp : P.IsPrime] : Submonoid α where
  carrier := (Pᶜ : Set α)
  one_mem' := P.one_notMem
  mul_mem' {_ _} hnx hny hxy := Or.casesOn (hp.mem_or_mem hxy) hnx hny

end Ideal

end Semiring

section Ring

theorem IsDomain.of_bot_isPrime (A : Type*) [Ring A] [hbp : (⊥ : Ideal A).IsPrime] : IsDomain A :=
  @NoZeroDivisors.to_isDomain A _ ⟨1, 0, fun h => hbp.one_notMem h⟩ ⟨fun h => hbp.2 h⟩

end Ring

section DivisionSemiring

variable {K : Type u} [DivisionSemiring K] (I : Ideal K)

namespace Ideal

theorem eq_bot_of_prime [h : I.IsPrime] : I = ⊥ :=
  or_iff_not_imp_right.mp I.eq_bot_or_top h.1

end Ideal

end DivisionSemiring
