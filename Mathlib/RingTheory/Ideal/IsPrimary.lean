/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yakov Pechersky
-/
import Mathlib.RingTheory.IsPrimary
import Mathlib.RingTheory.Ideal.Operations

/-!
# Primary ideals

A proper ideal `I` is primary iff `xy ∈ I` implies `x ∈ I` or `y ∈ radical I`.

## Main definitions

- `Ideal.IsPrimary`

## Implementation details

Uses a specialized phrasing of `Submodule.IsPrimary` to have better API-piercing usage.

-/

namespace Ideal

variable {R : Type*} [CommSemiring R]

/-- A proper ideal `I` is primary iff `xy ∈ I` implies `x ∈ I` or `y ∈ radical I`. -/
def IsPrimary (I : Ideal R) : Prop :=
  I ≠ ⊤ ∧ ∀ {x y : R}, x * y ∈ I → x ∈ I ∨ y ∈ radical I

lemma isPrimary_iff {I : Ideal R} :
    I.IsPrimary ↔ I ≠ ⊤ ∧ ∀ {x y : R}, x * y ∈ I → x ∈ I ∨ y ∈ radical I :=
  Iff.rfl

/-- An ideal `I : Ideal R` is primary iff it is primary as a submodule. This links
`Ideal.IsPrimary` with `Submodule.IsPrimary`. -/
lemma isPrimary_iff' {I : Ideal R} :
    I.IsPrimary ↔ Submodule.IsPrimary I := by
  rw [isPrimary_iff, Submodule.isPrimary_iff]
  simp only [ne_eq, mem_radical_iff, smul_eq_mul, and_congr_right_iff,
    ← Submodule.ideal_span_singleton_smul, smul_eq_mul, mul_top, span_singleton_le_iff_mem]
  intro
  constructor <;>
  · intro h r x hrx
    rw [mul_comm] at hrx
    exact h hrx

theorem IsPrime.isPrimary {I : Ideal R} (hi : IsPrime I) : IsPrimary I :=
  ⟨hi.1, fun {_ _} hxy => (hi.mem_or_mem hxy).imp id fun hyi => le_radical hyi⟩

theorem isPrime_radical {I : Ideal R} (hi : IsPrimary I) : IsPrime (radical I) :=
  ⟨mt radical_eq_top.1 hi.1,
   fun {x y} ⟨m, hxy⟩ => by
    rw [mul_pow] at hxy; cases' hi.2 hxy with h h
    · exact Or.inl ⟨m, h⟩
    · exact Or.inr (mem_radical_of_pow_mem h)⟩

theorem isPrimary_inf {I J : Ideal R} (hi : IsPrimary I) (hj : IsPrimary J)
    (hij : radical I = radical J) : IsPrimary (I ⊓ J) :=
  ⟨ne_of_lt <| lt_of_le_of_lt inf_le_left (lt_top_iff_ne_top.2 hi.1),
   fun {x y} ⟨hxyi, hxyj⟩ => by
    rw [radical_inf, hij, inf_idem]
    cases' hi.2 hxyi with hxi hyi
    · cases' hj.2 hxyj with hxj hyj
      · exact Or.inl ⟨hxi, hxj⟩
      · exact Or.inr hyj
    · rw [hij] at hyi
      exact Or.inr hyi⟩

end Ideal
