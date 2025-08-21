/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Submodule

/-!
# More lemmas on localization away

This file contains lemmas on localization away from an element requiring more imports.

-/

variable {R : Type*} [CommRing R]

namespace IsLocalization.Away

/-- Given a set `s` in a ring `R` and for every `t : s` a set `p t` of fractions in
a localization of `R` at `t`, this is the function sending a pair `(t, y)`, with
`t : s` and `y : t a`, to `t` multiplied with a numerator of `y`. The range
of this function spans the unit ideal, if `s` and every `p t` do. -/
noncomputable def mulNumerator (s : Set R)
    {Rₜ : s → Type*} [∀ t, CommRing (Rₜ t)] [∀ t, Algebra R (Rₜ t)]
    [∀ t, IsLocalization.Away t.val (Rₜ t)]
    (p : (t : s) → Set (Rₜ t)) (x : (t : s) × p t) : R :=
  x.1 * (IsLocalization.Away.sec x.1.1 x.2.1).1

lemma span_range_mulNumerator_eq_top {s : Set R}
    (hsone : Ideal.span s = ⊤) {Rₜ : s → Type*} [∀ t, CommRing (Rₜ t)] [∀ t, Algebra R (Rₜ t)]
    [∀ t, IsLocalization.Away t.val (Rₜ t)]
    {p : (t : s) → Set (Rₜ t)} (htone : ∀ (r : s), Ideal.span (p r) = ⊤) :
    Ideal.span (Set.range (IsLocalization.Away.mulNumerator s p)) = ⊤ := by
  rw [← Ideal.radical_eq_top, eq_top_iff, ← hsone, Ideal.span_le]
  intro a ha
  haveI : IsLocalization (Submonoid.powers a) (Rₜ ⟨a, ha⟩) :=
    inferInstanceAs <| IsLocalization.Away (⟨a, ha⟩ : s).val (Rₜ ⟨a, ha⟩)
  have h₁ : Ideal.span (p ⟨a, ha⟩) ≤ Ideal.span
      (algebraMap R (Rₜ ⟨a, ha⟩) '' Set.range (IsLocalization.Away.mulNumerator s p)) := by
    rw [Ideal.span_le]
    intro x hx
    rw [SetLike.mem_coe, IsLocalization.mem_span_map (Submonoid.powers a)]
    refine ⟨a * (IsLocalization.Away.sec a x).1, Ideal.subset_span ⟨⟨⟨a, ha⟩, ⟨x, hx⟩⟩, rfl⟩, ?_⟩
    use ⟨a ^ ((IsLocalization.Away.sec a x).2 + 1), _, rfl⟩
    rw [IsLocalization.eq_mk'_iff_mul_eq, map_pow, map_mul, ← map_pow, pow_add, map_mul,
      ← mul_assoc, IsLocalization.Away.sec_spec a x, mul_comm, pow_one]
  have h₂ : IsLocalization.mk' (Rₜ ⟨a, ha⟩) 1 (1 : Submonoid.powers a) ∈ Ideal.span
      (algebraMap R (Rₜ ⟨a, ha⟩) ''
        (Set.range <| IsLocalization.Away.mulNumerator s p)) := by
    rw [IsLocalization.mk'_one]
    apply h₁
    simp [htone]
  rw [IsLocalization.mem_span_map (Submonoid.powers a)] at h₂
  obtain ⟨y, hy, ⟨-, m, rfl⟩, hyz⟩ := h₂
  rw [IsLocalization.eq] at hyz
  obtain ⟨⟨-, n, rfl⟩, hc⟩ := hyz
  simp only [OneMemClass.coe_one, one_mul, mul_one] at hc
  use n + m
  simpa [pow_add, hc] using Ideal.mul_mem_left _ _ hy

lemma quotient_of_isIdempotentElem {e : R} (he : IsIdempotentElem e) :
    IsLocalization.Away e (R ⧸ Ideal.span {1 - e}) :=
  away_of_isIdempotentElem he Ideal.mk_ker Quotient.mk_surjective

end IsLocalization.Away
