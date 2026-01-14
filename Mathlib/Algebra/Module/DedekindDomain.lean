/-
Copyright (c) 2022 Pierre-Alexandre Bazin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre-Alexandre Bazin
-/
import Mathlib.Algebra.Module.Torsion
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

/-!
# Modules over a Dedekind domain

Over a Dedekind domain, an `I`-torsion module is the internal direct sum of its `p i ^ e i`-torsion
submodules, where `I = ∏ i, p i ^ e i` is its unique decomposition in prime ideals.
Therefore, as any finitely generated torsion module is `I`-torsion for some `I`, it is an internal
direct sum of its `p i ^ e i`-torsion submodules for some prime ideals `p i` and numbers `e i`.
-/


universe u v

variable {R : Type u} [CommRing R] [IsDomain R] {M : Type v} [AddCommGroup M] [Module R M]

open scoped DirectSum

namespace Submodule

variable [IsDedekindDomain R]

open UniqueFactorizationMonoid

/-- Over a Dedekind domain, an `I`-torsion module is the internal direct sum of its `p i ^ e i`-
torsion submodules, where `I = ∏ i, p i ^ e i` is its unique decomposition in prime ideals. -/
theorem isInternal_prime_power_torsion_of_is_torsion_by_ideal [DecidableEq (Ideal R)]
    {I : Ideal R} (hI : I ≠ ⊥) (hM : Module.IsTorsionBySet R M I) :
    DirectSum.IsInternal fun p : (factors I).toFinset =>
      torsionBySet R M (p ^ (factors I).count ↑p : Ideal R) := by
  let P := factors I
  have prime_of_mem := fun p (hp : p ∈ P.toFinset) =>
    prime_of_factor p (Multiset.mem_toFinset.mp hp)
  apply torsionBySet_isInternal (p := fun p => p ^ P.count p) _
  · convert hM
    rw [← Finset.inf_eq_iInf, IsDedekindDomain.inf_prime_pow_eq_prod, ← Finset.prod_multiset_count,
      ← associated_iff_eq]
    · exact factors_prod hI
    · exact prime_of_mem
    · exact fun _ _ _ _ ij => ij
  · intro p hp q hq pq; dsimp
    rw [irreducible_pow_sup]
    · suffices (normalizedFactors _).count p = 0 by rw [this, zero_min, pow_zero, Ideal.one_eq_top]
      rw [Multiset.count_eq_zero,
        normalizedFactors_of_irreducible_pow (prime_of_mem q hq).irreducible,
        Multiset.mem_replicate]
      exact fun H => pq <| H.2.trans <| normalize_eq q
    · rw [← Ideal.zero_eq_bot]; apply pow_ne_zero; exact (prime_of_mem q hq).ne_zero
    · exact (prime_of_mem p hp).irreducible

/-- A finitely generated torsion module over a Dedekind domain is an internal direct sum of its
`p i ^ e i`-torsion submodules where `p i` are factors of `(⊤ : Submodule R M).annihilator` and
`e i` are their multiplicities. -/
theorem isInternal_prime_power_torsion [DecidableEq (Ideal R)] [Module.Finite R M]
    (hM : Module.IsTorsion R M) :
    DirectSum.IsInternal fun p : (factors (⊤ : Submodule R M).annihilator).toFinset =>
      torsionBySet R M (p ^ (factors (⊤ : Submodule R M).annihilator).count ↑p : Ideal R) := by
  have hM' := Module.isTorsionBySet_annihilator_top R M
  have hI := Submodule.annihilator_top_inter_nonZeroDivisors hM
  refine isInternal_prime_power_torsion_of_is_torsion_by_ideal ?_ hM'
  rw [← Set.nonempty_iff_ne_empty] at hI; rw [Submodule.ne_bot_iff]
  obtain ⟨x, H, hx⟩ := hI; exact ⟨x, H, nonZeroDivisors.ne_zero hx⟩

/-- A finitely generated torsion module over a Dedekind domain is an internal direct sum of its
`p i ^ e i`-torsion submodules for some prime ideals `p i` and numbers `e i`. -/
theorem exists_isInternal_prime_power_torsion [Module.Finite R M] (hM : Module.IsTorsion R M) :
    ∃ (P : Finset <| Ideal R) (_ : DecidableEq P) (_ : ∀ p ∈ P, Prime p) (e : P → ℕ),
      DirectSum.IsInternal fun p : P => torsionBySet R M (p ^ e p : Ideal R) := by
  classical
  exact ⟨_, _, fun p hp => prime_of_factor p (Multiset.mem_toFinset.mp hp), _,
    isInternal_prime_power_torsion hM⟩

end Submodule
