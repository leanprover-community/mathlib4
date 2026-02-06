/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Unramified.LocalRing

/-!

# Primes that lie uniquely over another

## Main results

Let `S` be an `R` algebra, `p` be a prime of `R`, and suppose `q` is the unique prime of `S`
lying over `R`, then

- `Localization.localRingHom_injective_of_primesOver_eq_singleton`:
  If `R ⊆ S` is integral, then `R_p → S_q` is injective.
- `Localization.localRingHom_surjective_of_primesOver_eq_singleton`:
  Suppose `S` is `R`-finite and unramified at `q`. If `κ(p) = κ(q)` then `R_p → S_q` is surjective.
- `Localization.exists_awayMap_bijective_of_residueField_surjective`:
  Suppose `R ⊆ S` is finite and unramified at `q`.
  If `κ(p) = κ(q)` then there exists `r ∉ p` such that `R[1/f] = S[1/f]`.
-/

@[expose] public section

open IsLocalRing

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {p : Ideal R} [p.IsPrime]
  {q : Ideal S} [q.IsPrime] (hq : p.primesOver S = {q})

include hq

/-- If `S` is an integral `R`-algebra such that `q` is the unique prime of `S` lying over
a prime `p` of `R`, then any `x ∉ q` divides some `r ∉ p`. -/
lemma exists_notMem_dvd_algebraMap_of_primesOver_eq_singleton
    [Algebra.IsIntegral R S] (x : S) (hx : x ∉ q) : ∃ r ∉ p, x ∣ algebraMap _ _ r := by
  simp only [dvd_def, eq_comm, mul_comm x]
  by_contra!
  obtain ⟨Q, hQ, hxQ, hQp⟩ := Ideal.exists_le_prime_disjoint (.span {x})
    (Algebra.algebraMapSubmonoid _ p.primeCompl)
    (by simpa [Set.disjoint_iff_forall_ne, Ideal.mem_span_singleton',
      Algebra.algebraMapSubmonoid, @forall_comm S])
  have hQp' : Q.under _ ≤ p := by
    intro x hxQ
    by_contra hxp
    exact Set.subset_compl_iff_disjoint_right.mpr hQp hxQ ⟨x, hxp, rfl⟩
  obtain ⟨Q', hQ'Q, hQ', hQ'p⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime _ _ hQp'
  obtain rfl : Q' = q := hq.le ⟨hQ', ⟨hQ'p.symm⟩⟩
  exact hx (hQ'Q (hxQ (Ideal.mem_span_singleton_self _)))

namespace Localization

lemma localRingHom_injective_of_primesOver_eq_singleton
    [Algebra.IsIntegral R S] [FaithfulSMul R S] :
    Function.Injective (localRingHom p q (algebraMap R S) (hq.ge rfl).2.1) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq p.primeCompl x
  obtain ⟨a, haq, e⟩ : ∃ a ∉ q, a * (algebraMap R S) x = 0 := by
    simpa [Localization.localRingHom_mk', IsLocalization.mk'_eq_zero_iff] using hx
  obtain ⟨r, hrp, t, e'⟩ := exists_notMem_dvd_algebraMap_of_primesOver_eq_singleton hq _ haq
  refine (IsLocalization.mk'_eq_zero_iff _ _).mpr
    ⟨⟨r, hrp⟩, FaithfulSMul.algebraMap_injective R S ?_⟩
  simp only [map_mul, e', map_zero]
  grind

lemma finite_of_primesOver_eq_singleton [Module.Finite R S] [q.LiesOver p] :
    Module.Finite (Localization.AtPrime p) (Localization.AtPrime q) := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := S)
  refine ⟨s.image (IsScalarTower.toAlgHom R _ _).toLinearMap, ?_⟩
  rw [Finset.coe_image, ← Submodule.span_span_of_tower R, ← Submodule.map_span, hs,
    Submodule.map_top, LinearMap.coe_range, AlgHom.coe_toLinearMap, IsScalarTower.coe_toAlgHom',
    ← top_le_iff]
  rintro x -
  obtain ⟨x, ⟨s, hsq⟩, rfl⟩ := IsLocalization.exists_mk'_eq q.primeCompl x
  obtain ⟨r, hr, t, e'⟩ := exists_notMem_dvd_algebraMap_of_primesOver_eq_singleton hq _ hsq
  rw [← Submodule.smul_mem_iff_of_isUnit _ (IsLocalization.map_units (M := p.primeCompl) _ ⟨r, hr⟩),
    Algebra.smul_def, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply _ S, e',
      map_mul, mul_assoc, mul_left_comm, IsLocalization.mk'_spec'_mk, ← map_mul]
  exact Submodule.subset_span ⟨_, rfl⟩

lemma localRingHom_surjective_of_primesOver_eq_singleton
    [Module.Finite R S] [q.LiesOver p] [Algebra.IsUnramifiedAt R q]
    (H : Function.Surjective (algebraMap p.ResidueField q.ResidueField)) :
    Function.Surjective (localRingHom p q (algebraMap R S) (q.over_def p)) := by
  have := Localization.finite_of_primesOver_eq_singleton hq
  change Function.Surjective (Algebra.linearMap _ _)
  rw [← LinearMap.range_eq_top, ← top_le_iff]
  apply Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top (maximalIdeal_le_jacobson _)
  rw [Ideal.smul_top_eq_map, Algebra.FormallyUnramified.map_maximalIdeal]
  rintro x -
  obtain ⟨a, ha⟩ := H (algebraMap _ _ x)
  obtain ⟨a, rfl⟩ := residue_surjective a
  rw [← ResidueField.algebraMap_eq, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply _ (Localization.AtPrime q), ResidueField.algebraMap_eq,
    ← sub_eq_zero, ← map_sub, residue_eq_zero_iff] at ha
  rw [← sub_sub_self (algebraMap _ _ a) x]
  refine sub_mem (Submodule.mem_sup_left ⟨_, rfl⟩) (Submodule.mem_sup_right ha)

omit hq in
lemma exists_awayMap_injective_of_localRingHom_injective
    (hRS : (RingHom.ker (algebraMap R S)).FG) [q.LiesOver p]
    (H : Function.Injective (localRingHom p q (algebraMap R S) (q.over_def p))) :
    ∃ r ∉ p, ∀ r', r ∣ r' → Function.Injective (awayMap (algebraMap R S) r') := by
  classical
  obtain ⟨s, hs⟩ := hRS
  have (x : s) : algebraMap R (Localization.AtPrime p) x.1 = 0 := by
    apply H
    simp [localRingHom_to_map, -FaithfulSMul.algebraMap_eq_zero_iff,
      show algebraMap R S _ = 0 from hs.le (Ideal.subset_span x.2)]
  choose m hm using fun x ↦ (IsLocalization.map_eq_zero_iff p.primeCompl _ _).mp (this x)
  have H : RingHom.ker (algebraMap R S) ≤ RingHom.ker
      (algebraMap R (Localization.Away (∏ i, m i).1)) := by
    rw [← hs, Ideal.span_le]
    intro x hxs
    refine (IsLocalization.map_eq_zero_iff (.powers (∏ i, m i).1) _ _).mpr ⟨⟨_, 1, rfl⟩, ?_⟩
    simp only [pow_one]
    rw [Fintype.prod_eq_mul_prod_compl ⟨x, hxs⟩, Submonoid.coe_mul, mul_assoc, mul_left_comm, hm,
      mul_zero]
  refine ⟨_, (∏ i : s, m i).2, ?_⟩
  rintro r' ⟨s, e⟩
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨x, _, rfl⟩ := IsLocalization.exists_mk'_eq (.powers r') x
  simp only [awayMap, IsLocalization.Away.map, IsLocalization.map_mk',
    IsLocalization.mk'_eq_zero_iff] at hx
  obtain ⟨⟨_, n, rfl⟩, hn⟩ := hx
  simp only [← map_pow, ← map_mul] at hn
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.map_eq_zero_iff (.powers (∏ i, m i).1) _ _).mp (H hn)
  refine (IsLocalization.mk'_eq_zero_iff _ _).mpr ⟨⟨_, k + n, rfl⟩, ?_⟩
  dsimp only at hk ⊢
  rw [pow_add, mul_assoc, e, mul_pow, ← e, mul_assoc, mul_left_comm, hk, mul_zero]

lemma exists_awayMap_bijective_of_localRingHom_bijective
    [Module.Finite R S] [q.LiesOver p] (hRS : (RingHom.ker (algebraMap R S)).FG)
    (H : Function.Bijective (localRingHom p q (algebraMap R S) (q.over_def p))) :
    ∃ r ∉ p, ∀ r', r ∣ r' → Function.Bijective (awayMap (algebraMap R S) r') := by
  classical
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := R) (A := S)
  have (x : S) : ∃ a, ∃ b ∉ p, algebraMap R S a = x * algebraMap R S b := by
    have := (IsLocalization.mk'_surjective p.primeCompl).exists.mp (H.2 (algebraMap _ _ x))
    simp only [localRingHom_mk', Prod.exists, Subtype.exists, Ideal.mem_primeCompl_iff,
      IsLocalization.mk'_eq_iff_eq_mul, exists_prop, ← map_mul,
      IsLocalization.eq_iff_exists q.primeCompl] at this
    obtain ⟨a, b, hbp, c, hcq, hc⟩ := this
    obtain ⟨d, hd, e, he⟩ := exists_notMem_dvd_algebraMap_of_primesOver_eq_singleton hq _ hcq
    exact ⟨d * a, d * b, ‹p.IsPrime›.mul_notMem hd hbp, by grind⟩
  choose a b hbp e using this
  obtain ⟨r, hrp, hr⟩ := Localization.exists_awayMap_injective_of_localRingHom_injective hRS H.1
  refine ⟨r * ∏ i ∈ s, b i, mul_mem (s := p.primeCompl) hrp (prod_mem fun _ _ ↦ hbp _), ?_⟩
  refine fun r' hr' ↦ ⟨hr _ (.trans ⟨_, rfl⟩ hr'), ?_⟩
  have H : (IsScalarTower.toAlgHom R S _).range ≤ (awayMapₐ (Algebra.ofId R S) r').range := by
    rw [← Algebra.map_top, Subalgebra.map_le, ← hs, Algebra.adjoin_le_iff]
    intro x hxs
    obtain ⟨r'', hr'⟩ := hr'
    refine ⟨IsLocalization.mk' (M := .powers r') _
      (r'' * r * (∏ i ∈ s.erase x, b i) * a x) ⟨_, 1, rfl⟩, ?_⟩
    dsimp [awayMapₐ, IsLocalization.Away.map]
    simp only [pow_one, IsLocalization.map_mk', IsLocalization.mk'_eq_iff_eq_mul,
      ← map_mul (algebraMap S _), map_mul (algebraMap R _), e]
    congr 1
    rw [hr', ← Finset.prod_erase_mul s b hxs, map_mul, map_mul, map_mul]
    ring_nf
  intro x
  obtain ⟨x, ⟨_, n, rfl⟩, rfl⟩ := IsLocalization.exists_mk'_eq (.powers (algebraMap R S r')) x
  obtain ⟨y, hy : awayMap _ _ _ = _⟩ := H ⟨x, rfl⟩
  dsimp at hy
  refine ⟨y * Localization.Away.invSelf _ ^ n, ?_⟩
  simp only [map_mul, hy]
  simp [Away.invSelf, Localization.mk_eq_mk', awayMap, IsLocalization.Away.map,
    IsLocalization.map_mk', ← Algebra.smul_def, IsLocalization.smul_mk', ← IsLocalization.mk'_pow]

lemma exists_awayMap_bijective_of_residueField_surjective
    [Module.Finite R S] [FaithfulSMul R S] [q.LiesOver p] [Algebra.IsUnramifiedAt R q]
    (H : Function.Surjective (algebraMap p.ResidueField q.ResidueField)) :
    ∃ r ∉ p, ∀ r', r ∣ r' → Function.Bijective (awayMap (algebraMap R S) r') :=
  exists_awayMap_bijective_of_localRingHom_bijective hq (by simpa using Submodule.fg_bot)
    ⟨localRingHom_injective_of_primesOver_eq_singleton hq,
      localRingHom_surjective_of_primesOver_eq_singleton hq H⟩

end Localization
