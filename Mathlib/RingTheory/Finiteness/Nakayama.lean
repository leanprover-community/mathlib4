/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Ideal.Operations

/-!
# Nakayama's lemma

## Main results

* `exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul` is Nakayama's lemma, in the following form:
  if N is a finitely generated submodule of an ambient R-module M and I is an ideal of R
  such that N ⊆ IN, then there exists r ∈ 1 + I such that rN = 0.

-/

namespace Submodule

/-- **Nakayama's Lemma**. Atiyah-Macdonald 2.5, Eisenbud 4.7, Matsumura 2.2. -/
@[stacks 00DV]
theorem exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul {R : Type*} [CommRing R] {M : Type*}
    [AddCommGroup M] [Module R M] (I : Ideal R) (N : Submodule R M) (hn : N.FG) (hin : N ≤ I • N) :
    ∃ r : R, r - 1 ∈ I ∧ ∀ n ∈ N, r • n = (0 : M) := by
  rw [fg_def] at hn
  rcases hn with ⟨s, hfs, hs⟩
  have H : ∃ r : R, r - 1 ∈ I ∧ N ≤ (I • span R s).comap (LinearMap.lsmul R M r) ∧ s ⊆ N := by
    refine ⟨1, ?_, ?_, ?_⟩
    · rw [sub_self]
      exact I.zero_mem
    · rw [hs]
      intro n hn
      rw [mem_comap]
      change (1 : R) • n ∈ I • N
      rw [one_smul]
      exact hin hn
    · rw [← span_le, hs]
  clear hin hs
  induction s, hfs using Set.Finite.induction_on with
  | empty =>
    rcases H with ⟨r, hr1, hrn, _⟩
    refine ⟨r, hr1, fun n hn => ?_⟩
    specialize hrn hn
    rwa [mem_comap, span_empty, smul_bot, mem_bot] at hrn
  | @insert i s _ _ ih =>
  apply ih
  rcases H with ⟨r, hr1, hrn, hs⟩
  rw [← Set.singleton_union, span_union, smul_sup] at hrn
  rw [Set.insert_subset_iff] at hs
  have : ∃ c : R, c - 1 ∈ I ∧ c • i ∈ I • span R s := by
    specialize hrn hs.1
    rw [mem_comap, mem_sup] at hrn
    rcases hrn with ⟨y, hy, z, hz, hyz⟩
    dsimp at hyz
    rw [mem_smul_span_singleton] at hy
    rcases hy with ⟨c, hci, rfl⟩
    use r - c
    constructor
    · rw [sub_right_comm]
      exact I.sub_mem hr1 hci
    · rw [sub_smul, ← hyz, add_sub_cancel_left]
      exact hz
  rcases this with ⟨c, hc1, hci⟩
  refine ⟨c * r, ?_, ?_, hs.2⟩
  · simpa only [mul_sub, mul_one, sub_add_sub_cancel] using I.add_mem (I.mul_mem_left c hr1) hc1
  · intro n hn
    specialize hrn hn
    rw [mem_comap, mem_sup] at hrn
    rcases hrn with ⟨y, hy, z, hz, hyz⟩
    dsimp at hyz
    rw [mem_smul_span_singleton] at hy
    rcases hy with ⟨d, _, rfl⟩
    simp only [mem_comap, LinearMap.lsmul_apply]
    rw [mul_smul, ← hyz, smul_add, smul_smul, mul_comm, mul_smul]
    exact add_mem (smul_mem _ _ hci) (smul_mem _ _ hz)

theorem exists_mem_and_smul_eq_self_of_fg_of_le_smul {R : Type*} [CommRing R] {M : Type*}
    [AddCommGroup M] [Module R M] (I : Ideal R) (N : Submodule R M) (hn : N.FG) (hin : N ≤ I • N) :
    ∃ r ∈ I, ∀ n ∈ N, r • n = n := by
  obtain ⟨r, hr, hr'⟩ := exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I N hn hin
  exact ⟨-(r - 1), I.neg_mem hr, fun n hn => by simpa [sub_smul] using hr' n hn⟩

end Submodule
