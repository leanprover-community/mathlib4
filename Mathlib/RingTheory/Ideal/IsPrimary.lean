/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yakov Pechersky
-/
module

public import Mathlib.RingTheory.IsPrimary
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Primary ideals

A proper ideal `I` is primary iff `xy ∈ I` implies `x ∈ I` or `y ∈ radical I`.

## Main definitions

- `Ideal.IsPrimary`

## Implementation details

Uses a specialized phrasing of `Submodule.IsPrimary` to have better API-piercing usage.

-/

@[expose] public section

namespace Ideal

variable {R S : Type*} [CommSemiring R] [CommSemiring S]

/-- A proper ideal `I` is primary as a submodule. -/
abbrev IsPrimary (I : Ideal R) : Prop :=
  Submodule.IsPrimary I

/-- A proper ideal `I` is primary iff `xy ∈ I` implies `x ∈ I` or `y ∈ radical I`. -/
lemma isPrimary_iff {I : Ideal R} :
    I.IsPrimary ↔ I ≠ ⊤ ∧ ∀ {x y : R}, x * y ∈ I → x ∈ I ∨ y ∈ radical I := by
  rw [IsPrimary, Submodule.IsPrimary, forall_comm]
  simp only [mul_comm, mem_radical_iff,
    ← Submodule.ideal_span_singleton_smul, smul_eq_mul, mul_top, span_singleton_le_iff_mem]

theorem IsPrime.isPrimary {I : Ideal R} (hi : IsPrime I) : I.IsPrimary :=
  isPrimary_iff.mpr
  ⟨hi.1, fun {_ _} hxy => (hi.mem_or_mem hxy).imp id fun hyi => le_radical hyi⟩

theorem isPrime_radical {I : Ideal R} (hi : I.IsPrimary) : IsPrime (radical I) :=
  ⟨mt radical_eq_top.1 hi.1,
   fun {x y} ⟨m, hxy⟩ => by
    rw [mul_pow] at hxy; rcases (isPrimary_iff.mp hi).2 hxy with h | h
    · exact Or.inl ⟨m, h⟩
    · exact Or.inr (mem_radical_of_pow_mem h)⟩

theorem isPrimary_of_isMaximal_radical {I : Ideal R} (hi : IsMaximal (radical I)) :
    I.IsPrimary := by
  rw [isPrimary_iff]
  constructor
  · rintro rfl
    exact (radical_top R ▸ hi).ne_top rfl
  · intro x y hxy
    by_cases h : I + span {y} = ⊤
    · rw [← span_singleton_le_iff_mem, ← mul_top (span {x}), ← h, mul_add,
        span_singleton_mul_span_singleton, add_le_iff, span_singleton_le_iff_mem]
      exact Or.inl ⟨mul_le_left, hxy⟩
    · obtain ⟨m, hm, hy⟩ := exists_le_maximal (I + span {y}) h
      rw [add_le_iff, span_singleton_le_iff_mem, ← hm.isPrime.radical_le_iff] at hy
      exact Or.inr (hi.eq_of_le hm.ne_top hy.1 ▸ hy.2)

theorem IsPrimary.inf {I J : Ideal R} (hi : I.IsPrimary) (hj : J.IsPrimary)
    (hij : radical I = radical J) : (I ⊓ J).IsPrimary :=
  Submodule.IsPrimary.inf hi hj (by simpa)

@[deprecated (since := "2025-01-19")]
alias isPrimary_inf := IsPrimary.inf

lemma isPrimary_finsetInf {ι} {s : Finset ι} {f : ι → Ideal R} {i : ι} (hi : i ∈ s)
    (hs : ∀ ⦃y⦄, y ∈ s → (f y).IsPrimary)
    (hs' : ∀ ⦃y⦄, y ∈ s → (f y).radical = (f i).radical) :
    IsPrimary (s.inf f) :=
  Submodule.isPrimary_finsetInf hi hs (by simpa)

@[deprecated (since := "2026-01-19")]
alias isPrimary_finset_inf := isPrimary_finsetInf

lemma IsPrimary.comap {I : Ideal S} (hI : I.IsPrimary) (φ : R →+* S) : (I.comap φ).IsPrimary := by
  rw [isPrimary_iff] at hI ⊢
  refine hI.imp (comap_ne_top φ) fun h ↦ ?_
  simp only [mem_comap, map_mul, ← comap_radical]
  exact h

end Ideal
