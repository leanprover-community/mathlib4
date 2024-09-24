/-
Copyright (c) 2024 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.LinearAlgebra.Quotient
import Mathlib.RingTheory.Ideal.Operations

/-!
# Primary submodules

A proper submodule `S : Submodule R M` is primary iff
  `r • x ∈ S` implies `x ∈ S` or `∃ n : ℕ, r ^ n • (⊤ : Submodule R M) ≤ S`.

## Main results

* `Submodule.isPrimary_iff_zero_divisor_quotient_imp_nilpotent_smul`:
  A `N : Submodule R M` is primary if any zero divisor on `M ⧸ N` is nilpotent.
  See `https://mathoverflow.net/questions/3910/primary-decomposition-for-modules`
  for a comparison of this definition (a la Atiyah-Macdonald) vs "locally nilpotent" (Matsumura).

## Implementation details

This is a generalization of `Ideal.IsPrimary`. For brevity, the pointwise instances are used
to define the nilpotency of `r : R`.

-/

open Pointwise

namespace Submodule

section CommSemiring

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- A proper submodule `S : Submodule R M` is primary iff
  `r • x ∈ S` implies `x ∈ S` or `∃ n : ℕ, r ^ n • (⊤ : Submodule R M) ≤ S`.
  This generalizes `Ideal.IsPrimary`. -/
def IsPrimary (S : Submodule R M) : Prop :=
  S ≠ ⊤ ∧ ∀ {r : R} {x : M}, r • x ∈ S → x ∈ S ∨ ∃ n : ℕ, (r ^ n • ⊤ : Submodule R M) ≤ S

variable {S : Submodule R M}

lemma isPrimary_iff :
    S.IsPrimary ↔ S ≠ ⊤ ∧
      ∀ {r : R} {x : M}, r • x ∈ S → x ∈ S ∨ ∃ n : ℕ, (r ^ n • ⊤ : Submodule R M) ≤ S :=
  Iff.rfl

lemma IsPrimary.ne_top (h : S.IsPrimary) : S ≠ ⊤ := h.left

end CommSemiring

section CommRing

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {S : Submodule R M}

lemma isPrimary_iff_zero_divisor_quotient_imp_nilpotent_smul :
    S.IsPrimary ↔ S ≠ ⊤ ∧ ∀ (r : R) (x : M ⧸ S), x ≠ 0 → r • x = 0 →
      ∃ n : ℕ, r ^ n • (⊤ : Submodule R (M ⧸ S)) = ⊥ := by
  rw [isPrimary_iff]
  refine and_congr_right fun _ ↦ ?_
  simp_rw [← le_bot_iff, ← mkQ_map_self]
  constructor
  · rintro h r ⟨x⟩ hx hxr
    simp only [Quotient.quot_mk_eq_mk, ne_eq, Quotient.mk_eq_zero, ← Quotient.mk_smul] at hx hxr
    refine ((h hxr).resolve_left hx).imp fun n hn ↦ ?_
    convert map_mono hn
    simp only [map_pointwise_smul, map_top, range_mkQ]
  · intro h r x hrx
    refine (em _).imp_right fun hx ↦ (h r (Quotient.mk x) ?_ ?_).imp fun n hn ↦ ?_
    · simpa using hx
    · simpa [← Quotient.mk_smul] using hrx
    · have := comap_mono (f := mkQ S) hn
      simp only [mkQ_map_self, comap_bot, ker_mkQ] at this
      refine this.trans' ?_
      simp_rw [← ideal_span_singleton_smul, ← comap_top (f := mkQ S)]
      exact smul_comap_le_comap_smul _ _ _

end CommRing

end Submodule
