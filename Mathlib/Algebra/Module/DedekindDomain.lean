/-
Copyright (c) 2022 Pierre-Alexandre Bazin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre-Alexandre Bazin
-/
import Mathlib.Algebra.Module.Torsion
import Mathlib.RingTheory.DedekindDomain.Ideal

#align_import algebra.module.dedekind_domain from "leanprover-community/mathlib"@"cdc34484a07418af43daf8198beaf5c00324bca8"

/-!
# Modules over a Dedekind domain

Over a Dedekind domain, an `I`-torsion module is the internal direct sum of its `p i ^ e i`-torsion
submodules, where `I = ∏ i, p i ^ e i` is its unique decomposition in prime ideals.
Therefore, as any finitely generated torsion module is `I`-torsion for some `I`, it is an internal
direct sum of its `p i ^ e i`-torsion submodules for some prime ideals `p i` and numbers `e i`.
-/


universe u v

open scoped BigOperators

variable {R : Type u} [CommRing R] [IsDomain R] {M : Type v} [AddCommGroup M] [Module R M]

open scoped DirectSum

namespace Submodule

variable [IsDedekindDomain R]

open UniqueFactorizationMonoid

open scoped Classical

/-- Over a Dedekind domain, an `I`-torsion module is the internal direct sum of its `p i ^ e i`-
torsion submodules, where `I = ∏ i, p i ^ e i` is its unique decomposition in prime ideals.-/
theorem isInternal_prime_power_torsion_of_is_torsion_by_ideal {I : Ideal R} (hI : I ≠ ⊥)
    (hM : Module.IsTorsionBySet R M I) :
    DirectSum.IsInternal fun p : (factors I).toFinset =>
      torsionBySet R M ((p : Ideal R) ^ (factors I).count ↑p) := by
  let P := factors I
  -- ⊢ DirectSum.IsInternal fun p => torsionBySet R M ↑(↑p ^ Multiset.count (↑p) (f …
  have prime_of_mem := fun p (hp : p ∈ P.toFinset) =>
    prime_of_factor p (Multiset.mem_toFinset.mp hp)
  apply @torsionBySet_isInternal _ _ _ _ _ _ _ _ (fun p => p ^ P.count p) _
  -- ⊢ Module.IsTorsionBySet R M ↑(⨅ (i : Ideal R) (_ : i ∈ Multiset.toFinset (fact …
  · convert hM
    -- ⊢ ⨅ (i : Ideal R) (_ : i ∈ Multiset.toFinset (factors I)), i ^ Multiset.count  …
    rw [← Finset.inf_eq_iInf, IsDedekindDomain.inf_prime_pow_eq_prod, ← Finset.prod_multiset_count,
      ← associated_iff_eq]
    · exact factors_prod hI
      -- 🎉 no goals
    · exact prime_of_mem
      -- 🎉 no goals
    · exact fun _ _ _ _ ij => ij
      -- 🎉 no goals
  · intro p hp q hq pq; dsimp
    -- ⊢ (fun p => p ^ Multiset.count p P) p ⊔ (fun p => p ^ Multiset.count p P) q = ⊤
                        -- ⊢ p ^ Multiset.count p (factors I) ⊔ q ^ Multiset.count q (factors I) = ⊤
    rw [irreducible_pow_sup]
    · suffices (normalizedFactors _).count p = 0 by rw [this, zero_min, pow_zero, Ideal.one_eq_top]
      -- ⊢ Multiset.count p (normalizedFactors (q ^ Multiset.count q (factors I))) = 0
      · rw [Multiset.count_eq_zero,
          normalizedFactors_of_irreducible_pow (prime_of_mem q hq).irreducible,
          Multiset.mem_replicate]
        exact fun H => pq <| H.2.trans <| normalize_eq q
        -- 🎉 no goals
    · rw [← Ideal.zero_eq_bot]; apply pow_ne_zero; exact (prime_of_mem q hq).ne_zero
      -- ⊢ q ^ Multiset.count q (factors I) ≠ 0
                                -- ⊢ q ≠ 0
                                                   -- 🎉 no goals
    · exact (prime_of_mem p hp).irreducible
      -- 🎉 no goals
#align submodule.is_internal_prime_power_torsion_of_is_torsion_by_ideal Submodule.isInternal_prime_power_torsion_of_is_torsion_by_ideal

/-- A finitely generated torsion module over a Dedekind domain is an internal direct sum of its
`p i ^ e i`-torsion submodules where `p i` are factors of `(⊤ : Submodule R M).annihilator` and
`e i` are their multiplicities. -/
theorem isInternal_prime_power_torsion [Module.Finite R M] (hM : Module.IsTorsion R M) :
    DirectSum.IsInternal fun p : (factors (⊤ : Submodule R M).annihilator).toFinset =>
      torsionBySet R M ((p : Ideal R) ^ (factors (⊤ : Submodule R M).annihilator).count ↑p) := by
  have hM' := Module.isTorsionBySet_annihilator_top R M
  -- ⊢ DirectSum.IsInternal fun p => torsionBySet R M ↑(↑p ^ Multiset.count (↑p) (f …
  have hI := Submodule.annihilator_top_inter_nonZeroDivisors hM
  -- ⊢ DirectSum.IsInternal fun p => torsionBySet R M ↑(↑p ^ Multiset.count (↑p) (f …
  refine' isInternal_prime_power_torsion_of_is_torsion_by_ideal _ hM'
  -- ⊢ annihilator ⊤ ≠ ⊥
  rw [← Set.nonempty_iff_ne_empty] at hI; rw [Submodule.ne_bot_iff]
  -- ⊢ annihilator ⊤ ≠ ⊥
                                          -- ⊢ ∃ x, x ∈ annihilator ⊤ ∧ x ≠ 0
  obtain ⟨x, H, hx⟩ := hI; exact ⟨x, H, nonZeroDivisors.ne_zero hx⟩
  -- ⊢ ∃ x, x ∈ annihilator ⊤ ∧ x ≠ 0
                           -- 🎉 no goals
#align submodule.is_internal_prime_power_torsion Submodule.isInternal_prime_power_torsion

/-- A finitely generated torsion module over a Dedekind domain is an internal direct sum of its
`p i ^ e i`-torsion submodules for some prime ideals `p i` and numbers `e i`.-/
theorem exists_isInternal_prime_power_torsion [Module.Finite R M] (hM : Module.IsTorsion R M) :
    ∃ (P : Finset <| Ideal R) (_ : DecidableEq P) (_ : ∀ p ∈ P, Prime p) (e : P → ℕ),
      DirectSum.IsInternal fun p : P => torsionBySet R M ((p : Ideal R) ^ e p) :=
  ⟨_, _, fun p hp => prime_of_factor p (Multiset.mem_toFinset.mp hp), _,
    isInternal_prime_power_torsion hM⟩
#align submodule.exists_is_internal_prime_power_torsion Submodule.exists_isInternal_prime_power_torsion

end Submodule
