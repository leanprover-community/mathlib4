/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Localization.AtPrime

/-!

# Assocaited primes of localized module

This file mainly proof the relation between `Ass(S⁻¹M)` and `Ass(M)`

# Main Results

* `associatedPrimes.mem_associatePrimes_of_comap_mem_associatePrimes_isLocalizedModule` :
  for an `R` module `M`, if `p` is a prime ideal of `S⁻¹R` and `p ∩ R ∈ Ass(M)` then
  `p ∈ Ass (S⁻¹M)`.

TODO: prove the reverse when `p` is finitely generated and
      get `Ass (S⁻¹M) = Ass(M) ∩ Spec(S⁻¹R)` when `R` noetherian.

TODO: deduce from the above that every minimal element in support is in `Ass(M)`.

-/

variable {R : Type*} [CommRing R] (S : Submonoid R) (R' : Type*)  [CommRing R'] [Algebra R R']
  [IsLocalization S R']

variable {M M' : Type*} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
  (f : M →ₗ[R] M') [IsLocalizedModule S f] [Module R' M'] [IsScalarTower R R' M']

open IsLocalRing LinearMap

namespace Module.associatedPrimes

include S f in
lemma mem_associatePrimes_of_comap_mem_associatePrimes_isLocalizedModule
    (p : Ideal R') [p.IsPrime]
    (ass : p.comap (algebraMap R R') ∈ associatedPrimes R M) :
    p ∈ associatedPrimes R' M' := by
  rcases ass with ⟨hp, x, hx⟩
  constructor
  · /- use the following to  remove `p.IsPrime`
      exact (IsLocalization.isPrime_iff_isPrime_disjoint S _ _).mpr
      ⟨hp, (IsLocalization.disjoint_comap_iff S R' p).mpr (p ≠ ⊤)⟩ -/
    assumption
  · use f x
    ext t
    rcases IsLocalization.mk'_surjective S t with ⟨r, s, hrs⟩
    rw [← IsLocalizedModule.mk'_one S, ← hrs, mem_ker, toSpanSingleton_apply,
      IsLocalizedModule.mk'_smul_mk', mul_one, IsLocalizedModule.mk'_eq_zero']
    refine ⟨fun h ↦ ?_, fun ⟨t, ht⟩ ↦ ?_⟩
    · use 1
      simp only [← toSpanSingleton_apply, one_smul, ← mem_ker, ← hx, Ideal.mem_comap]
      have : (algebraMap R R') r =
        IsLocalization.mk' R' r s * IsLocalization.mk' R' s.1 (1 : S) := by
        rw [← IsLocalization.mk'_one (M := S) R', ← sub_eq_zero, ← IsLocalization.mk'_mul,
          ← IsLocalization.mk'_sub]
        simp
      rw [this]
      exact Ideal.IsTwoSided.mul_mem_of_left _ h
    · have : t • r • x = (t.1 * r) • x := smul_smul t.1 r x
      rw [this, ← LinearMap.toSpanSingleton_apply, ← LinearMap.mem_ker, ← hx, Ideal.mem_comap,
        ← IsLocalization.mk'_one (M := S) R'] at ht
      have : IsLocalization.mk' R' r s =
        IsLocalization.mk' (M := S) R' (t.1 * r) 1 * IsLocalization.mk' R' 1 (t * s) := by
        rw [← IsLocalization.mk'_mul, mul_one, one_mul, ← sub_eq_zero, ← IsLocalization.mk'_sub,
          Submonoid.coe_mul]
        simp [← mul_assoc, mul_comm r t.1, IsLocalization.mk'_zero]
      simpa [this] using Ideal.IsTwoSided.mul_mem_of_left _ ht

lemma mem_associatePrimes_localizedModule_atPrime_of_mem_associated_primes
    {p : Ideal R} [p.IsPrime] (ass : p ∈ associatedPrimes R M) :
    maximalIdeal (Localization.AtPrime p) ∈
    associatedPrimes (Localization.AtPrime p) (LocalizedModule p.primeCompl M) := by
  apply mem_associatePrimes_of_comap_mem_associatePrimes_isLocalizedModule
    p.primeCompl (Localization.AtPrime p) (LocalizedModule.mkLinearMap p.primeCompl M)
  simpa [Localization.AtPrime.comap_maximalIdeal] using ass

include S f in
lemma comap_mem_associatePrimes_of_mem_associatedPrimes_isLocalizedModule_and_fg (p : Ideal R')
    (ass : p ∈ associatedPrimes R' M') (fg : (p.comap (algebraMap R R')).FG) :
    p.comap (algebraMap R R') ∈ associatedPrimes R M := by
  --note : here `p.FG` should imply `(p.comap (algebraMap R R')).FG` however lemmas aren't ready yet
  rcases ass with ⟨hp, ⟨x, hx⟩⟩
  rcases fg with ⟨T, hT⟩
  rcases IsLocalizedModule.mk'_surjective S f x with ⟨⟨m, s⟩, eq⟩
  simp only [← eq, Function.uncurry_apply_pair] at hx
  have mem (a : T) : (algebraMap R R') a ∈ p := by
    simpa [← Ideal.mem_comap, ← hT] using Ideal.subset_span a.2
  simp only [hx, mem_ker, toSpanSingleton_apply, algebraMap_smul,
    ← IsLocalizedModule.mk'_smul] at mem
  let g : T → S := fun a ↦ Classical.choose <| (IsLocalizedModule.mk'_eq_zero' f _).mp (mem a)
  let hg (a : T) : g a • a.1 • m = 0:=
    Classical.choose_spec <| (IsLocalizedModule.mk'_eq_zero' f _).mp (mem a)
  have prime : (Ideal.comap (algebraMap R R') p).IsPrime := Ideal.IsPrime.under R p
  refine ⟨prime, (∏ a, g a).1 • m, ?_⟩
  apply le_antisymm
  · rw [← hT, Ideal.span_le]
    intro a ha
    simp only [SetLike.mem_coe, mem_ker, toSpanSingleton_apply]
    obtain ⟨u, hu⟩ : g ⟨a, ha⟩ ∣ (∏ a, g a) := by
      apply Finset.dvd_prod_of_mem g (Finset.mem_univ ⟨a, ha⟩)
    rw [hu, Submonoid.coe_mul, smul_smul, ← mul_assoc, mul_comm, ← smul_smul, mul_comm, ← smul_smul]
    exact smul_eq_zero_of_right u.1 (hg ⟨a, ha⟩)
  · intro r hr
    simp only [mem_ker, toSpanSingleton_apply, smul_smul] at hr
    have mem : r * (∏ a, g a).1 ∈ Ideal.comap (algebraMap R R') p := by
      simpa only [hx, Ideal.mem_comap, mem_ker, toSpanSingleton_apply, algebraMap_smul,
        ← IsLocalizedModule.mk'_smul, hr] using IsLocalizedModule.mk'_zero f s
    have nmem := Set.disjoint_left.mp ((IsLocalization.disjoint_comap_iff S R' p).mpr
        (Ideal.IsPrime.ne_top hp)) (∏ a, g a).2
    have := (Ideal.IsPrime.mul_mem_iff_mem_or_mem prime).mp mem
    tauto



end Module.associatedPrimes
