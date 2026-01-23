/-
Copyright (c) 2024 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Primary submodules

A proper submodule `S : Submodule R M` is primary iff
  `r • x ∈ S` implies `x ∈ S` or `∃ n : ℕ, r ^ n • (⊤ : Submodule R M) ≤ S`.

## Main results

* `Submodule.isPrimary_iff_zero_divisor_quotient_imp_nilpotent_smul`:
  A `N : Submodule R M` is primary if any zero divisor on `M ⧸ N` is nilpotent.
  See https://mathoverflow.net/questions/3910/primary-decomposition-for-modules
  for a comparison of this definition (a la Atiyah-Macdonald) vs "locally nilpotent" (Matsumura).

## Implementation details

This is a generalization of `Ideal.IsPrimary`. For brevity, the pointwise instances are used
to define the nilpotency of `r : R`.

## References

* [M. F. Atiyah and I. G. Macdonald, *Introduction to commutative algebra*][atiyah-macdonald]
  Chapter 4, Exercise 21.

-/

@[expose] public section

open Pointwise

namespace Submodule

section CommSemiring

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- A proper submodule `S : Submodule R M` is primary iff
  `r • x ∈ S` implies `x ∈ S` or `∃ n : ℕ, r ^ n • (⊤ : Submodule R M) ≤ S`.
  This generalizes `Ideal.IsPrimary`. -/
protected def IsPrimary (S : Submodule R M) : Prop :=
  S ≠ ⊤ ∧ ∀ {r : R} {x : M}, r • x ∈ S → x ∈ S ∨ ∃ n : ℕ, (r ^ n • ⊤ : Submodule R M) ≤ S

variable {S T : Submodule R M}

lemma IsPrimary.ne_top (h : S.IsPrimary) : S ≠ ⊤ := h.left

lemma IsPrimary.mem_or_mem (h : S.IsPrimary) {r : R} {m : M} (hrm : r • m ∈ S) :
    m ∈ S ∨ r ∈ (S.colon ⊤).radical :=
  h.right hrm

protected lemma IsPrimary.inf (hS : S.IsPrimary) (hT : T.IsPrimary)
    (h : (S.colon Set.univ).radical = (T.colon Set.univ).radical) :
    (S ⊓ T).IsPrimary := by
  obtain ⟨_, hS⟩ := hS
  obtain ⟨_, hT⟩ := hT
  refine ⟨by grind, fun ⟨hS', hT'⟩ ↦ ?_⟩
  simp_rw [← mem_colon_iff_le, ← Ideal.mem_radical_iff, inf_colon, Ideal.radical_inf,
    top_coe, h, inf_idem, mem_inf, and_or_right] at hS hT ⊢
  exact ⟨hS hS', hT hT'⟩

open Finset in
lemma isPrimary_finsetInf {ι : Type*} {s : Finset ι} {f : ι → Submodule R M} {i : ι} (hi : i ∈ s)
    (hs : ∀ ⦃y⦄, y ∈ s → (f y).IsPrimary)
    (hs' : ∀ ⦃y⦄, y ∈ s → ((f y).colon Set.univ).radical = ((f i).colon Set.univ).radical) :
    (s.inf f).IsPrimary := by
  classical
  induction s using Finset.induction_on generalizing i with
  | empty => simp at hi
  | insert a s ha IH =>
    rcases s.eq_empty_or_nonempty with rfl | ⟨y, hy⟩
    · simp only [insert_empty_eq, mem_singleton] at hi
      simpa [hi] using hs
    simp only [inf_insert]
    have H ⦃x⦄ (hx : x ∈ s) : ((f x).colon Set.univ).radical = ((f y).colon Set.univ).radical := by
      rw [hs' (mem_insert_of_mem hx), hs' (mem_insert_of_mem hy)]
    refine IsPrimary.inf (hs (by simp)) (IH hy (fun x hx ↦ hs (by simp [hx])) H) ?_
    rw [colon_finsetInf, Ideal.radical_finset_inf hy H,
      hs' (mem_insert_self _ _), hs' (mem_insert_of_mem hy)]

end CommSemiring

section CommRing

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {S : Submodule R M}

lemma isPrimary_iff_zero_divisor_quotient_imp_nilpotent_smul :
    S.IsPrimary ↔ S ≠ ⊤ ∧ ∀ (r : R) (x : M ⧸ S), x ≠ 0 → r • x = 0 →
      ∃ n : ℕ, r ^ n • (⊤ : Submodule R (M ⧸ S)) = ⊥ := by
  refine (and_congr_right fun _ ↦ ?_)
  simp_rw [S.mkQ_surjective.forall, ← map_smul, ne_eq, ← LinearMap.mem_ker, ker_mkQ]
  congr! 2
  rw [forall_comm, ← or_iff_not_imp_left,
    ← LinearMap.range_eq_top.mpr S.mkQ_surjective, ← map_top]
  simp_rw [eq_bot_iff, ← map_pointwise_smul, map_le_iff_le_comap, comap_bot, ker_mkQ]

end CommRing

end Submodule
