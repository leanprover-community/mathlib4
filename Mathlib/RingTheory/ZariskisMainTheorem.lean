/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Algebraic Zariski's Main Theorem

In this file we will prove (TODO @erdOne) the algebraic version of Zariski's main theorem

The final statement would be
```
example {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    (p : Ideal S) [p.IsPrime] [Algebra.QuasiFiniteAt R p] : ZariskiMainProperty R p
```

## References
- https://stacks.math.columbia.edu/tag/00PI

-/

@[expose] public section

variable {R S T : Type*} [CommRing R] [CommRing S] [Algebra R S] [CommRing T] [Algebra R T]

open scoped TensorProduct nonZeroDivisors

open Polynomial

namespace Algebra

variable (R) in
/-- We say that an `R` algebra `S` satisfies the Zariski's main property at a prime `p` of `S`
if there exists `r ∉ p` in the integral closure `S'` of `R` in `S`, such that `S'[1/r] = S[1/r]`. -/
def ZariskisMainProperty (p : Ideal S) : Prop :=
  ∃ r : integralClosure R S, r.1 ∉ p ∧ Function.Bijective
    (Localization.awayMap (integralClosure R S).val.toRingHom r)

lemma zariskisMainProperty_iff {p : Ideal S} :
    ZariskisMainProperty R p ↔ ∃ r ∉ p, IsIntegral R r ∧ ∀ x, ∃ m, IsIntegral R (r ^ m * x) := by
  simp only [ZariskisMainProperty, Subtype.exists, ← exists_prop, @exists_comm (_ ∉ p)]
  refine exists₃_congr fun r hr hrp ↦ ?_
  rw [Function.Bijective, and_iff_right
    (by exact IsLocalization.map_injective_of_injective _ _ _ Subtype.val_injective),
    Localization.awayMap_surjective_iff]
  simp [mem_integralClosure_iff]

lemma zariskisMainProperty_iff' {p : Ideal S} :
    ZariskisMainProperty R p ↔ ∃ r ∉ p, ∀ x, ∃ m, IsIntegral R (r ^ m * x) := by
  refine zariskisMainProperty_iff.trans (exists_congr fun r ↦ and_congr_right fun hrp ↦
    and_iff_right_of_imp fun H ↦ ?_)
  obtain ⟨n, hn⟩ := H r
  rw [← pow_succ] at hn
  exact (IsIntegral.pow_iff (by simp)).mp hn

lemma zariskisMainProperty_iff_exists_saturation_eq_top {p : Ideal S} :
    ZariskisMainProperty R p ↔ ∃ r ∉ p, ∃ h : IsIntegral R r,
      (integralClosure R S).saturation (.powers r) (by simpa [Submonoid.powers_le]) = ⊤ := by
  simp [zariskisMainProperty_iff, ← top_le_iff, SetLike.le_def,
    Submonoid.mem_powers_iff, mem_integralClosure_iff]

lemma ZariskisMainProperty.restrictScalars [Algebra S T] [IsScalarTower R S T]
    [Algebra.IsIntegral R S] {p : Ideal T} (H : ZariskisMainProperty S p) :
    ZariskisMainProperty R p := by
  rw [zariskisMainProperty_iff'] at H ⊢
  obtain ⟨r, hrp, H⟩ := H
  exact ⟨r, hrp, fun x ↦ ⟨_, isIntegral_trans _ (H x).choose_spec⟩⟩

lemma ZariskisMainProperty.trans [Algebra S T] [IsScalarTower R S T] (p : Ideal T) [p.IsPrime]
    (h₁ : ZariskisMainProperty R (p.under S))
    (h₂ : ∃ r ∉ p.under S, (⊥ : Subalgebra S T).saturation (.powers (algebraMap _ _ r))
      (by simp [Submonoid.powers_le]) = ⊤) :
    ZariskisMainProperty R p := by
  rw [zariskisMainProperty_iff] at h₁
  rw [zariskisMainProperty_iff']
  obtain ⟨s, hsp, hs, Hs⟩ := h₁
  obtain ⟨t, htp, Ht⟩ := h₂
  obtain ⟨m, hm⟩ := Hs t
  refine ⟨algebraMap _ _ (s ^ (m + 1) * t), ?_, fun x ↦ ?_⟩
  · simpa using ‹p.IsPrime›.mul_notMem
      (mt ((inferInstanceAs (p.under S).IsPrime).mem_of_pow_mem (m + 1)) hsp) htp
  obtain ⟨_, ⟨n, rfl⟩, a, ha⟩ := Ht.ge (Set.mem_univ x)
  obtain ⟨k, hk⟩ := Hs a
  refine ⟨k + n, ?_⟩
  convert_to IsIntegral R (algebraMap S T ((s ^ ((m + 1) * n) * (s ^ m * t) ^ k * (s ^ k * a))))
  · simp only [AlgHom.toRingHom_eq_coe, Algebra.toRingHom_ofId] at ha
    simp only [map_pow, map_mul, ha, pow_add, mul_pow]
    ring
  · exact .algebraMap (.mul ((hs.pow _).mul (hm.pow _)) hk)

lemma ZariskisMainProperty.of_isIntegral (p : Ideal S) [p.IsPrime] [Algebra.IsIntegral R S] :
    ZariskisMainProperty R p :=
  zariskisMainProperty_iff'.mpr ⟨1, p.primeCompl.one_mem,
    fun _ ↦ ⟨0, Algebra.IsIntegral.isIntegral _⟩⟩

end Algebra
