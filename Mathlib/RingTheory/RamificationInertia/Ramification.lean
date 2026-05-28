/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.NumberTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.RingTheory.LocalRing.Length

/-!
# Ramification index

Let `S/R` be an extension of rings, and let `q` be a prime ideal of `S` lying over a prime ideal
`p` of `R`. Let `Sq` be the localization of `S` and `q`, and let `pSq` be the image of `p` in `Sq`.
Then the ramification index of `q` over `R` is defined to be the length of the quotient `Sq/pSq` as
an `Sq`-module.

## Main definitions

* `Ideal.ramificationIdx' q R`: The ramification index of `q` over `R`.

## Main statements

* `ramificationIdx_eq_ramificationIdx'`: The ramification index agrees with the usual definition in
  the case of Dedekind domains.
* `ramificationIdx'_tower`: Ramification index is multiplicative in towers.

-/

@[expose] public section

namespace Ideal

section

variable {S : Type*} [CommRing S] (q : Ideal S) (R : Type*) [CommRing R] [Algebra R S]

open Classical in
/-- Let `S/R` be an extension of rings, and let `q` be a prime ideal of `S` lying over a prime ideal
`p` of `R`. Let `Sq` be the localization of `S` and `q`, and let `pSq` be the image of `p` in `Sq`.
Then the ramification index of `q` over `R` is defined to be the length of the quotient `Sq/pSq` as
an `Sq`-module.

When `q` is not prime, we use a junk value of `0`.

This will eventually replace the existing definition of `Ideal.ramificationIdx`. -/
noncomputable def ramificationIdx' : ℕ :=
  if _ : q.IsPrime then
    letI Sq := Localization.AtPrime q
    (Module.length Sq (Sq ⧸ (q.under R).map (algebraMap R Sq))).toNat
  else 0

theorem ramificationIdx'_def [q.IsPrime] :
    letI Sq := Localization.AtPrime q
    q.ramificationIdx' R = (Module.length Sq (Sq ⧸ (q.under R).map (algebraMap R Sq))).toNat :=
  dif_pos _

theorem ramificationIdx'_of_not_isPrime (hq : ¬ q.IsPrime) : q.ramificationIdx' R = 0 :=
  dif_neg hq

-- PRed
/-- A ring has krull dimension at most zero if and only if all minimal primes are maximal. -/
theorem _root_.ringKrullDimLE_zero_iff_forall_minimalPrimes_isMaximal
    {R : Type*} [CommRing R] : Ring.KrullDimLE 0 R ↔ ∀ I ∈ minimalPrimes R, I.IsMaximal := by
  rw [Ring.krullDimLE_zero_iff]
  refine ⟨fun h I hI ↦ h I hI.1.1, fun h I hI ↦ ?_⟩
  obtain ⟨J, hJ, hle⟩ := exists_minimalPrimes_le bot_le (J := I)
  rw [← (h J hJ).eq_of_le hI.ne_top hle]
  exact h J hJ

-- PRed
/-- A quotient `R ⧸ I` has krull dimension at most zero if and only if all minimal primes over `I`
are maximal. -/
theorem _root_.ringKrullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal
    {R : Type*} [CommRing R] {I : Ideal R} :
    Ring.KrullDimLE 0 (R ⧸ I) ↔ ∀ J ∈ I.minimalPrimes, J.IsMaximal := by
  have := comap_minimalPrimes_eq_of_surjective (f := Quotient.mk I) Quotient.mk_surjective ⊥
  rw [← RingHom.ker_eq_comap_bot, mk_ker] at this
  rw [this, Set.forall_mem_image, ringKrullDimLE_zero_iff_forall_minimalPrimes_isMaximal]
  refine forall₂_congr fun J hJ ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · exact comap_isMaximal_of_surjective (Quotient.mk I) Quotient.mk_surjective
  · have := map_eq_top_or_isMaximal_of_surjective (Quotient.mk I) Quotient.mk_surjective h
    rw [map_comap_of_surjective (Quotient.mk I) Quotient.mk_surjective] at this
    exact this.resolve_left hJ.1.1.ne_top

-- PRed
theorem _root_.Algebra.IsIntegral.mem_minimalPrimes_map_under
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Algebra.IsIntegral R S]
    (p : Ideal S) [p.IsPrime] : p ∈ ((p.under R).map (algebraMap R S)).minimalPrimes := by
  refine ⟨⟨inferInstance, map_comap_le⟩, fun r ⟨hr, hpr⟩ hrq ↦ ?_⟩
  contrapose! hpr
  exact mt map_le_iff_le_comap.mp (not_le_of_gt (IsIntegral.comap_lt_comap (hrq.lt_of_not_ge hpr)))

theorem ramificationIdx'_pos [hq : q.IsPrime] [IsNoetherianRing S] [Algebra.IsIntegral R S] :
    0 < q.ramificationIdx' R := by
  let Sq := Localization.AtPrime q
  let T := Sq ⧸ (q.under R).map (algebraMap R Sq)
  rw [ramificationIdx'_def]
  apply ENat.toNat_pos
  · rw [← pos_iff_ne_zero, Module.length_pos_iff, Submodule.Quotient.nontrivial_iff,
      IsScalarTower.algebraMap_eq R S, ← map_map, ← lt_top_iff_ne_top]
    grw [map_mono map_comap_le, Localization.AtPrime.map_eq_maximalIdeal]
    exact (IsLocalRing.maximalIdeal.isMaximal _).lt_top
  · rw [Module.length_eq_of_surjective (R := T) Quotient.mk_surjective, Module.length_ne_top_iff,
      ← isArtinianRing_iff_isFiniteLength, isArtinianRing_iff_krullDimLE_zero,
      ringKrullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal,
      IsScalarTower.algebraMap_eq R S, ← map_map]
    intro r hr
    have : r.IsPrime := hr.1.1
    rw [IsLocalization.minimalPrimes_map q.primeCompl, Set.mem_preimage] at hr
    suffices q = r.under S by
      rw [← IsLocalization.map_under q.primeCompl Sq r, ← this,
        Localization.AtPrime.map_eq_maximalIdeal]
      exact IsLocalRing.maximalIdeal.isMaximal Sq
    suffices r.under S ≤ q from
      le_antisymm ((Algebra.IsIntegral.mem_minimalPrimes_map_under q).2 hr.1 this) this
    conv_rhs => rw [← IsLocalization.AtPrime.under_maximalIdeal Sq q]
    exact comap_mono (IsLocalRing.le_maximalIdeal_of_isPrime r)

end

section

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  (p : Ideal R) (q : Ideal S) (r : Ideal T)

theorem ramificationIdx'_eq [q.LiesOver p] [q.IsPrime] :
    letI Sq := Localization.AtPrime q
    q.ramificationIdx' R = (Module.length Sq (Sq ⧸ p.map (algebraMap R Sq))).toNat := by
  rw [ramificationIdx'_def, over_def q p]

open Localization IsLocalization.AtPrime in
theorem ramificationIdx_eq_ramificationIdx'
    [IsDomain R] [IsDedekindDomain S] [Module.IsTorsionFree R S]
    [q.LiesOver p] [hq : q.IsPrime] (hp : p ≠ ⊥) :
    p.ramificationIdx q = q.ramificationIdx' R := by
  have : p.IsPrime := isPrime_of_liesOver q p
  have hq' : q ≠ ⊥ := ne_bot_of_liesOver_of_ne_bot hp q
  have : q.IsMaximal := hq.isMaximal hq'
  have hpS : p.map (algebraMap R S) ≠ ⊥ := map_ne_bot_of_ne_bot hp
  obtain ⟨I, hqI, h⟩ := Ideal.eq_prime_pow_mul_coprime hpS q
  replace hqI : ¬ I ≤ q := by
    contrapose! hqI
    rw [sup_of_le_left hqI]
    exact hq.ne_top
  rw [← IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count hpS hq hq'] at h
  apply_fun (map (algebraMap S (Localization.AtPrime q))) at h
  rw [map_map, ← IsScalarTower.algebraMap_eq, Ideal.map_mul, Ideal.map_pow,
    map_eq_top_of_not_le (Localization.AtPrime q) hqI, mul_top, AtPrime.map_eq_maximalIdeal] at h
  have hSq := isDiscreteValuationRing_of_dedekind_domain S hq' (Localization.AtPrime q)
  rw [ramificationIdx'_eq p q, h, hSq.length_quotient_pow_maximalIdeal, ENat.toNat_coe]

/-- See `ramificationIdx'_tower` for a version that does not assume primality. -/
theorem ramificationIdx'_tower' [q.IsPrime] [r.IsPrime] [r.LiesOver q]
    [Algebra (Localization.AtPrime q) (Localization.AtPrime r)]
    [Localization.AtPrime.IsLiesOverAlgebra q r]
    [Module.Flat (Localization.AtPrime q) (Localization.AtPrime r)] :
    r.ramificationIdx' R = q.ramificationIdx' R * r.ramificationIdx' S := by
  have : q.LiesOver (r.under R) := LiesOver.tower_bot r q (r.under R)
  let f := (Ideal.quotientEquivAlgOfEq (Localization.AtPrime r)
    (by rw [map_map, ← IsScalarTower.algebraMap_eq])).trans
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (Localization.AtPrime r)
        ((r.under R).map (algebraMap R (Localization.AtPrime q))))
  rw [ramificationIdx'_def, ramificationIdx'_eq (r.under R), ramificationIdx'_eq q,
    f.toLinearEquiv.length_eq, IsLocalRing.length_baseChange, ENat.toNat_mul,
    ← Localization.AtPrime.map_eq_maximalIdeal, map_map, ← IsScalarTower.algebraMap_eq]

/-- See `ramificationIdx'_tower'` for a version that only assumes local flatness. -/
theorem ramificationIdx'_tower [r.LiesOver q] [Module.Flat S T] :
    r.ramificationIdx' R = q.ramificationIdx' R * r.ramificationIdx' S := by
  by_cases hr : r.IsPrime
  · have : q.IsPrime := isPrime_of_liesOver r q
    let := Localization.AtPrime.algebraOfLiesOver q r
    apply ramificationIdx'_tower'
  · rw [ramificationIdx'_of_not_isPrime r R hr, ramificationIdx'_of_not_isPrime r S hr, mul_zero]

end

end Ideal
