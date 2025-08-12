/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Polynomial.Content

/-!
# Gauss's Lemma

Gauss's Lemma is one of a few results pertaining to irreducibility of primitive polynomials.

## Main Results

- `IsIntegrallyClosed.eq_map_mul_C_of_dvd`: if `R` is integrally closed, `K = Frac(R)` and
  `g : K[X]` divides a monic polynomial with coefficients in `R`, then `g * (C g.leadingCoeff⁻¹)`
  has coefficients in `R`
- `Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map`:
  A monic polynomial over an integrally closed domain is irreducible iff it is irreducible in a
  fraction field
- `isIntegrallyClosed_iff'`:
  Integrally closed domains are precisely the domains for in which Gauss's lemma holds
  for monic polynomials
- `Polynomial.IsPrimitive.irreducible_iff_irreducible_map_fraction_map`:
  A primitive polynomial over a GCD domain is irreducible iff it is irreducible in a fraction field
- `Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast`:
  A primitive polynomial over `ℤ` is irreducible iff it is irreducible over `ℚ`.
- `Polynomial.IsPrimitive.dvd_iff_fraction_map_dvd_fraction_map`:
  Two primitive polynomials over a GCD domain divide each other iff they do in a fraction field.
- `Polynomial.IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast`:
  Two primitive polynomials over `ℤ` divide each other if they do in `ℚ`.

-/


open scoped nonZeroDivisors Polynomial

variable {R : Type*} [CommRing R]

section IsIntegrallyClosed

open Polynomial

open integralClosure

open IsIntegrallyClosed

variable (K : Type*) [Field K] [Algebra R K]

theorem integralClosure.mem_lifts_of_monic_of_dvd_map {f : R[X]} (hf : f.Monic) {g : K[X]}
    (hg : g.Monic) (hd : g ∣ f.map (algebraMap R K)) :
    g ∈ lifts (algebraMap (integralClosure R K) K) := by
  have := mem_lift_of_splits_of_roots_mem_range (integralClosure R g.SplittingField)
    ((splits_id_iff_splits _).2 <| SplittingField.splits g) (hg.map _) fun a ha =>
      (SetLike.ext_iff.mp (integralClosure R g.SplittingField).range_algebraMap _).mpr <|
        roots_mem_integralClosure hf ?_
  · rw [lifts_iff_coeff_lifts, ← RingHom.coe_range, Subalgebra.range_algebraMap] at this
    refine (lifts_iff_coeff_lifts _).2 fun n => ?_
    rw [← RingHom.coe_range, Subalgebra.range_algebraMap]
    obtain ⟨p, hp, he⟩ := SetLike.mem_coe.mp (this n); use p, hp
    rw [IsScalarTower.algebraMap_eq R K, coeff_map, ← eval₂_map, eval₂_at_apply] at he
    rw [eval₂_eq_eval_map]; apply (injective_iff_map_eq_zero _).1 _ _ he
    apply RingHom.injective
  rw [aroots_def, IsScalarTower.algebraMap_eq R K _, ← map_map]
  refine Multiset.mem_of_le (roots.le_of_dvd ((hf.map _).map _).ne_zero ?_) ha
  exact map_dvd (algebraMap K g.SplittingField) hd

variable [IsFractionRing R K]

/-- If `K = Frac(R)` and `g : K[X]` divides a monic polynomial with coefficients in `R`, then
`g * (C g.leadingCoeff⁻¹)` has coefficients in `R` -/
theorem IsIntegrallyClosed.eq_map_mul_C_of_dvd [IsIntegrallyClosed R] {f : R[X]} (hf : f.Monic)
    {g : K[X]} (hg : g ∣ f.map (algebraMap R K)) :
    ∃ g' : R[X], g'.map (algebraMap R K) * (C <| leadingCoeff g) = g := by
  have g_ne_0 : g ≠ 0 := ne_zero_of_dvd_ne_zero (Monic.ne_zero <| hf.map (algebraMap R K)) hg
  suffices lem : ∃ g' : R[X], g'.map (algebraMap R K) = g * C g.leadingCoeff⁻¹ by
    obtain ⟨g', hg'⟩ := lem
    use g'
    rw [hg', mul_assoc, ← C_mul, inv_mul_cancel₀ (leadingCoeff_ne_zero.mpr g_ne_0), C_1, mul_one]
  have g_mul_dvd : g * C g.leadingCoeff⁻¹ ∣ f.map (algebraMap R K) := by
    rwa [Associated.dvd_iff_dvd_left (show Associated (g * C g.leadingCoeff⁻¹) g from _)]
    rw [associated_mul_isUnit_left_iff]
    exact isUnit_C.mpr (inv_ne_zero <| leadingCoeff_ne_zero.mpr g_ne_0).isUnit
  let algeq :=
    (Subalgebra.equivOfEq _ _ <| integralClosure_eq_bot R _).trans
      (Algebra.botEquivOfInjective <| IsFractionRing.injective R <| K)
  have :
    (algebraMap R _).comp algeq.toAlgHom.toRingHom = (integralClosure R _).toSubring.subtype := by
    ext x; (conv_rhs => rw [← algeq.symm_apply_apply x]); rfl
  have H :=
    (mem_lifts _).1
      (integralClosure.mem_lifts_of_monic_of_dvd_map K hf (monic_mul_leadingCoeff_inv g_ne_0)
        g_mul_dvd)
  refine ⟨map algeq.toAlgHom.toRingHom ?_, ?_⟩
  · use! Classical.choose H
  · rw [map_map, this]
    exact Classical.choose_spec H

end IsIntegrallyClosed

namespace Polynomial

section

variable {S : Type*} [CommRing S] [IsDomain S]
variable {φ : R →+* S} (hinj : Function.Injective φ) {f : R[X]} (hf : f.IsPrimitive)
include hinj hf

theorem IsPrimitive.isUnit_iff_isUnit_map_of_injective : IsUnit f ↔ IsUnit (map φ f) := by
  refine ⟨(mapRingHom φ).isUnit_map, fun h => ?_⟩
  rcases isUnit_iff.1 h with ⟨_, ⟨u, rfl⟩, hu⟩
  have hdeg := degree_C u.ne_zero
  rw [hu, degree_map_eq_of_injective hinj] at hdeg
  rw [eq_C_of_degree_eq_zero hdeg] at hf ⊢
  exact isUnit_C.mpr (isPrimitive_iff_isUnit_of_C_dvd.mp hf (f.coeff 0) dvd_rfl)

theorem IsPrimitive.irreducible_of_irreducible_map_of_injective (h_irr : Irreducible (map φ f)) :
    Irreducible f := by
  refine
    ⟨fun h => h_irr.not_isUnit (IsUnit.map (mapRingHom φ) h), fun a b h =>
      (h_irr.isUnit_or_isUnit <| by rw [h, Polynomial.map_mul]).imp ?_ ?_⟩
  all_goals apply ((isPrimitive_of_dvd hf _).isUnit_iff_isUnit_map_of_injective hinj).mpr
  exacts [Dvd.intro _ h.symm, Dvd.intro_left _ h.symm]

end

section FractionMap

variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

theorem IsPrimitive.isUnit_iff_isUnit_map {p : R[X]} (hp : p.IsPrimitive) :
    IsUnit p ↔ IsUnit (p.map (algebraMap R K)) :=
  hp.isUnit_iff_isUnit_map_of_injective (IsFractionRing.injective _ _)

section IsIntegrallyClosed

open IsIntegrallyClosed

/-- **Gauss's Lemma** for integrally closed domains states that a monic polynomial is irreducible
  iff it is irreducible in the fraction field. -/
theorem Monic.irreducible_iff_irreducible_map_fraction_map [IsIntegrallyClosed R] {p : R[X]}
    (h : p.Monic) : Irreducible p ↔ Irreducible (p.map <| algebraMap R K) := by
  /- The ← direction follows from `IsPrimitive.irreducible_of_irreducible_map_of_injective`.
       For the → direction, it is enough to show that if `(p.map <| algebraMap R K) = a * b` and
       `a` is not a unit then `b` is a unit -/
  refine
    ⟨fun hp =>
      irreducible_iff.mpr
        ⟨hp.not_isUnit.imp h.isPrimitive.isUnit_iff_isUnit_map.mpr, fun a b H =>
          or_iff_not_imp_left.mpr fun hₐ => ?_⟩,
      fun hp =>
      h.isPrimitive.irreducible_of_irreducible_map_of_injective (IsFractionRing.injective R K) hp⟩
  obtain ⟨a', ha⟩ := eq_map_mul_C_of_dvd K h (dvd_of_mul_right_eq b H.symm)
  obtain ⟨b', hb⟩ := eq_map_mul_C_of_dvd K h (dvd_of_mul_left_eq a H.symm)
  have : a.leadingCoeff * b.leadingCoeff = 1 := by
    rw [← leadingCoeff_mul, ← H, Monic.leadingCoeff (h.map <| algebraMap R K)]
  rw [← ha, ← hb, mul_comm _ (C b.leadingCoeff), mul_assoc, ← mul_assoc (C a.leadingCoeff), ←
    C_mul, this, C_1, one_mul, ← Polynomial.map_mul] at H
  rw [← hb, ← Polynomial.coe_mapRingHom]
  refine
    IsUnit.mul (IsUnit.map _ (Or.resolve_left (hp.isUnit_or_isUnit ?_) (show ¬IsUnit a' from ?_)))
      (isUnit_iff_exists_inv'.mpr
        -- Porting note(https://github.com/leanprover-community/mathlib4/issues/5073): was `rwa`
        (Exists.intro (C a.leadingCoeff) <| by rw [← C_mul, this, C_1]))
  · exact Polynomial.map_injective _ (IsFractionRing.injective R K) H
  · by_contra h_contra
    refine hₐ ?_
    rw [← ha, ← Polynomial.coe_mapRingHom]
    exact
      IsUnit.mul (IsUnit.map _ h_contra)
        (isUnit_iff_exists_inv.mpr
          -- Porting note(https://github.com/leanprover-community/mathlib4/issues/5073): was `rwa`
          (Exists.intro (C b.leadingCoeff) <| by rw [← C_mul, this, C_1]))

/-- Integrally closed domains are precisely the domains for in which Gauss's lemma holds
for monic polynomials -/
theorem isIntegrallyClosed_iff' [IsDomain R] :
    IsIntegrallyClosed R ↔
      ∀ p : R[X], p.Monic → (Irreducible p ↔ Irreducible (p.map <| algebraMap R K)) := by
  constructor
  · intro hR p hp; exact Monic.irreducible_iff_irreducible_map_fraction_map hp
  · intro H
    refine
      (isIntegrallyClosed_iff K).mpr fun {x} hx =>
        RingHom.mem_range.mp <| minpoly.mem_range_of_degree_eq_one R x ?_
    rw [← Monic.degree_map (minpoly.monic hx) (algebraMap R K)]
    apply
      degree_eq_one_of_irreducible_of_root ((H _ <| minpoly.monic hx).mp (minpoly.irreducible hx))
    rw [IsRoot, eval_map, ← aeval_def, minpoly.aeval R x]

theorem Monic.dvd_of_fraction_map_dvd_fraction_map [IsIntegrallyClosed R] {p q : R[X]}
    (hp : p.Monic) (hq : q.Monic)
    (h : q.map (algebraMap R K) ∣ p.map (algebraMap R K)) : q ∣ p := by
  obtain ⟨r, hr⟩ := h
  obtain ⟨d', hr'⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd K hp (dvd_of_mul_left_eq _ hr.symm)
  rw [Monic.leadingCoeff, C_1, mul_one] at hr'
  · rw [← hr', ← Polynomial.map_mul] at hr
    exact dvd_of_mul_right_eq _ (Polynomial.map_injective _ (IsFractionRing.injective R K) hr.symm)
  · exact Monic.of_mul_monic_left (hq.map (algebraMap R K)) (by simpa [← hr] using hp.map _)

theorem Monic.dvd_iff_fraction_map_dvd_fraction_map [IsIntegrallyClosed R] {p q : R[X]}
    (hp : p.Monic) (hq : q.Monic) : q.map (algebraMap R K) ∣ p.map (algebraMap R K) ↔ q ∣ p :=
  ⟨fun h => hp.dvd_of_fraction_map_dvd_fraction_map hq h, fun ⟨a, b⟩ =>
    ⟨a.map (algebraMap R K), b.symm ▸ Polynomial.map_mul (algebraMap R K)⟩⟩

end IsIntegrallyClosed

open IsLocalization

section NormalizedGCDMonoid

variable [IsDomain R] [NormalizedGCDMonoid R]

theorem isUnit_or_eq_zero_of_isUnit_integerNormalization_primPart {p : K[X]} (h0 : p ≠ 0)
    (h : IsUnit (integerNormalization R⁰ p).primPart) : IsUnit p := by
  rcases isUnit_iff.1 h with ⟨_, ⟨u, rfl⟩, hu⟩
  obtain ⟨⟨c, c0⟩, hc⟩ := integerNormalization_map_to_map R⁰ p
  rw [Subtype.coe_mk, Algebra.smul_def, algebraMap_apply] at hc
  apply isUnit_of_mul_isUnit_right
  rw [← hc, (integerNormalization R⁰ p).eq_C_content_mul_primPart, ← hu, ← RingHom.map_mul,
    isUnit_iff]
  refine
    ⟨algebraMap R K ((integerNormalization R⁰ p).content * ↑u), isUnit_iff_ne_zero.2 fun con => ?_,
      by simp⟩
  replace con := (injective_iff_map_eq_zero (algebraMap R K)).1 (IsFractionRing.injective _ _) _ con
  rw [mul_eq_zero, content_eq_zero_iff, IsFractionRing.integerNormalization_eq_zero_iff] at con
  rcases con with (con | con)
  · apply h0 con
  · apply Units.ne_zero _ con

/-- **Gauss's Lemma** for GCD domains states that a primitive polynomial is irreducible iff it is
  irreducible in the fraction field. -/
theorem IsPrimitive.irreducible_iff_irreducible_map_fraction_map {p : R[X]} (hp : p.IsPrimitive) :
    Irreducible p ↔ Irreducible (p.map (algebraMap R K)) := by
  -- Porting note: was `(IsFractionRing.injective _ _)`
  refine
    ⟨fun hi => ⟨fun h => hi.not_isUnit (hp.isUnit_iff_isUnit_map.2 h), fun a b hab => ?_⟩,
      hp.irreducible_of_irreducible_map_of_injective (IsFractionRing.injective R K)⟩
  obtain ⟨⟨c, c0⟩, hc⟩ := integerNormalization_map_to_map R⁰ a
  obtain ⟨⟨d, d0⟩, hd⟩ := integerNormalization_map_to_map R⁰ b
  rw [Algebra.smul_def, algebraMap_apply, Subtype.coe_mk] at hc hd
  rw [mem_nonZeroDivisors_iff_ne_zero] at c0 d0
  have hcd0 : c * d ≠ 0 := mul_ne_zero c0 d0
  rw [Ne, ← C_eq_zero] at hcd0
  have h1 : C c * C d * p = integerNormalization R⁰ a * integerNormalization R⁰ b := by
    apply map_injective (algebraMap R K) (IsFractionRing.injective _ _) _
    rw [Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_mul, hc, hd, map_C, map_C, hab]
    ring
  obtain ⟨u, hu⟩ :
    Associated (c * d)
      (content (integerNormalization R⁰ a) * content (integerNormalization R⁰ b)) := by
    rw [← dvd_dvd_iff_associated, ← normalize_eq_normalize_iff, normalize.map_mul,
      normalize.map_mul, normalize_content, normalize_content, ←
      mul_one (normalize c * normalize d), ← hp.content_eq_one, ← content_C, ← content_C, ←
      content_mul, ← content_mul, ← content_mul, h1]
  rw [← RingHom.map_mul, eq_comm, (integerNormalization R⁰ a).eq_C_content_mul_primPart,
    (integerNormalization R⁰ b).eq_C_content_mul_primPart, mul_assoc, mul_comm _ (C _ * _), ←
    mul_assoc, ← mul_assoc, ← RingHom.map_mul, ← hu, RingHom.map_mul, mul_assoc, mul_assoc, ←
    mul_assoc (C (u : R))] at h1
  have h0 : a ≠ 0 ∧ b ≠ 0 := by
    classical
    rw [Ne, Ne, ← not_or, ← mul_eq_zero, ← hab]
    intro con
    apply hp.ne_zero (map_injective (algebraMap R K) (IsFractionRing.injective _ _) _)
    simp [con]
  rcases hi.isUnit_or_isUnit (mul_left_cancel₀ hcd0 h1).symm with (h | h)
  · right
    apply
      isUnit_or_eq_zero_of_isUnit_integerNormalization_primPart h0.2
        (isUnit_of_mul_isUnit_right h)
  · left
    apply isUnit_or_eq_zero_of_isUnit_integerNormalization_primPart h0.1 h

theorem IsPrimitive.dvd_of_fraction_map_dvd_fraction_map {p q : R[X]} (hp : p.IsPrimitive)
    (hq : q.IsPrimitive) (h_dvd : p.map (algebraMap R K) ∣ q.map (algebraMap R K)) : p ∣ q := by
  rcases h_dvd with ⟨r, hr⟩
  obtain ⟨⟨s, s0⟩, hs⟩ := integerNormalization_map_to_map R⁰ r
  rw [Subtype.coe_mk, Algebra.smul_def, algebraMap_apply] at hs
  have h : p ∣ q * C s := by
    use integerNormalization R⁰ r
    apply map_injective (algebraMap R K) (IsFractionRing.injective _ _)
    rw [Polynomial.map_mul, Polynomial.map_mul, hs, hr, mul_assoc, mul_comm r]
    simp
  rw [← hp.dvd_primPart_iff_dvd, primPart_mul, hq.primPart_eq, Associated.dvd_iff_dvd_right] at h
  · exact h
  · symm
    rcases isUnit_primPart_C s with ⟨u, hu⟩
    use u
    rw [hu]
  iterate 2
    apply mul_ne_zero hq.ne_zero
    rw [Ne, C_eq_zero]
    contrapose! s0
    simp [s0, mem_nonZeroDivisors_iff_ne_zero]

variable (K)

theorem IsPrimitive.dvd_iff_fraction_map_dvd_fraction_map {p q : R[X]} (hp : p.IsPrimitive)
    (hq : q.IsPrimitive) : p ∣ q ↔ p.map (algebraMap R K) ∣ q.map (algebraMap R K) :=
  ⟨fun ⟨a, b⟩ => ⟨a.map (algebraMap R K), b.symm ▸ Polynomial.map_mul (algebraMap R K)⟩, fun h =>
    hp.dvd_of_fraction_map_dvd_fraction_map hq h⟩

end NormalizedGCDMonoid

end FractionMap

/-- **Gauss's Lemma** for `ℤ` states that a primitive integer polynomial is irreducible iff it is
  irreducible over `ℚ`. -/
theorem IsPrimitive.Int.irreducible_iff_irreducible_map_cast {p : ℤ[X]} (hp : p.IsPrimitive) :
    Irreducible p ↔ Irreducible (p.map (Int.castRingHom ℚ)) :=
  hp.irreducible_iff_irreducible_map_fraction_map

theorem IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast (p q : ℤ[X]) (hp : p.IsPrimitive)
    (hq : q.IsPrimitive) : p ∣ q ↔ p.map (Int.castRingHom ℚ) ∣ q.map (Int.castRingHom ℚ) :=
  hp.dvd_iff_fraction_map_dvd_fraction_map ℚ hq

end Polynomial
