/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.IntegrallyClosed

#align_import ring_theory.polynomial.gauss_lemma from "leanprover-community/mathlib"@"e3f4be1fcb5376c4948d7f095bec45350bfb9d1a"

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
    -- ⊢ g ∈ lifts (algebraMap { x // x ∈ integralClosure R K } K)
    refine' (lifts_iff_coeff_lifts _).2 fun n => _
    -- ⊢ coeff g n ∈ Set.range ↑(algebraMap { x // x ∈ integralClosure R K } K)
    rw [← RingHom.coe_range, Subalgebra.range_algebraMap]
    -- ⊢ coeff g n ∈ ↑(Subalgebra.toSubring (integralClosure R K))
    obtain ⟨p, hp, he⟩ := SetLike.mem_coe.mp (this n); use p, hp
    -- ⊢ coeff g n ∈ ↑(Subalgebra.toSubring (integralClosure R K))
                                                       -- ⊢ eval₂ (algebraMap R K) (coeff g n) p = 0
    rw [IsScalarTower.algebraMap_eq R K, coeff_map, ← eval₂_map, eval₂_at_apply] at he
    -- ⊢ eval₂ (algebraMap R K) (coeff g n) p = 0
    rw [eval₂_eq_eval_map]; apply (injective_iff_map_eq_zero _).1 _ _ he
    -- ⊢ eval (coeff g n) (map (algebraMap R K) p) = 0
                            -- ⊢ Function.Injective ↑(algebraMap K (SplittingField g))
    · apply RingHom.injective
      -- 🎉 no goals
  rw [IsScalarTower.algebraMap_eq R K _, ← map_map]
  -- ⊢ a ∈ roots (map (algebraMap K (SplittingField g)) (map (algebraMap R K) f))
  refine' Multiset.mem_of_le (roots.le_of_dvd ((hf.map _).map _).ne_zero _) ha
  -- ⊢ map (algebraMap K (SplittingField g)) g ∣ map (algebraMap K (SplittingField  …
  exact map_dvd (algebraMap K g.SplittingField) hd
  -- 🎉 no goals
#align integral_closure.mem_lifts_of_monic_of_dvd_map integralClosure.mem_lifts_of_monic_of_dvd_map

variable [IsDomain R] [IsFractionRing R K]

/-- If `K = Frac(R)` and `g : K[X]` divides a monic polynomial with coefficients in `R`, then
    `g * (C g.leadingCoeff⁻¹)` has coefficients in `R` -/
theorem IsIntegrallyClosed.eq_map_mul_C_of_dvd [IsIntegrallyClosed R] {f : R[X]} (hf : f.Monic)
    {g : K[X]} (hg : g ∣ f.map (algebraMap R K)) :
    ∃ g' : R[X], g'.map (algebraMap R K) * (C <| leadingCoeff g) = g := by
  have g_ne_0 : g ≠ 0 := ne_zero_of_dvd_ne_zero (Monic.ne_zero <| hf.map (algebraMap R K)) hg
  -- ⊢ ∃ g', map (algebraMap R K) g' * ↑C (leadingCoeff g) = g
  suffices lem : ∃ g' : R[X], g'.map (algebraMap R K) = g * C g.leadingCoeff⁻¹
  -- ⊢ ∃ g', map (algebraMap R K) g' * ↑C (leadingCoeff g) = g
  · obtain ⟨g', hg'⟩ := lem
    -- ⊢ ∃ g', map (algebraMap R K) g' * ↑C (leadingCoeff g) = g
    use g'
    -- ⊢ map (algebraMap R K) g' * ↑C (leadingCoeff g) = g
    rw [hg', mul_assoc, ← C_mul, inv_mul_cancel (leadingCoeff_ne_zero.mpr g_ne_0), C_1, mul_one]
    -- 🎉 no goals
  have g_mul_dvd : g * C g.leadingCoeff⁻¹ ∣ f.map (algebraMap R K) := by
    rwa [Associated.dvd_iff_dvd_left (show Associated (g * C g.leadingCoeff⁻¹) g from _)]
    rw [associated_mul_isUnit_left_iff]
    exact isUnit_C.mpr (inv_ne_zero <| leadingCoeff_ne_zero.mpr g_ne_0).isUnit
  let algeq :=
    (Subalgebra.equivOfEq _ _ <| integralClosure_eq_bot R _).trans
      (Algebra.botEquivOfInjective <| IsFractionRing.injective R <| K)
  have :
    (algebraMap R _).comp algeq.toAlgHom.toRingHom = (integralClosure R _).toSubring.subtype :=
    by ext x; conv_rhs => rw [← algeq.symm_apply_apply x]; rfl
  have H :=
    (mem_lifts _).1
      (integralClosure.mem_lifts_of_monic_of_dvd_map K hf (monic_mul_leadingCoeff_inv g_ne_0)
        g_mul_dvd)
  refine' ⟨map algeq.toAlgHom.toRingHom _, _⟩
  -- ⊢ { x // x ∈ integralClosure R K }[X]
  · use! Classical.choose H
    -- 🎉 no goals
  · rw [map_map, this]
    -- ⊢ map (Subring.subtype (Subalgebra.toSubring (integralClosure R K))) (Classica …
    exact Classical.choose_spec H
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align is_integrally_closed.eq_map_mul_C_of_dvd IsIntegrallyClosed.eq_map_mul_C_of_dvd

end IsIntegrallyClosed

namespace Polynomial

section

variable {S : Type*} [CommRing S] [IsDomain S]

variable {φ : R →+* S} (hinj : Function.Injective φ) {f : R[X]} (hf : f.IsPrimitive)

theorem IsPrimitive.isUnit_iff_isUnit_map_of_injective : IsUnit f ↔ IsUnit (map φ f) := by
  refine' ⟨(mapRingHom φ).isUnit_map, fun h => _⟩
  -- ⊢ IsUnit f
  rcases isUnit_iff.1 h with ⟨_, ⟨u, rfl⟩, hu⟩
  -- ⊢ IsUnit f
  have hdeg := degree_C u.ne_zero
  -- ⊢ IsUnit f
  rw [hu, degree_map_eq_of_injective hinj] at hdeg
  -- ⊢ IsUnit f
  rw [eq_C_of_degree_eq_zero hdeg] at hf ⊢
  -- ⊢ IsUnit (↑C (coeff f 0))
  exact isUnit_C.mpr (isPrimitive_iff_isUnit_of_C_dvd.mp hf (f.coeff 0) dvd_rfl)
  -- 🎉 no goals
#align polynomial.is_primitive.is_unit_iff_is_unit_map_of_injective Polynomial.IsPrimitive.isUnit_iff_isUnit_map_of_injective

theorem IsPrimitive.irreducible_of_irreducible_map_of_injective (h_irr : Irreducible (map φ f)) :
    Irreducible f := by
  refine'
    ⟨fun h => h_irr.not_unit (IsUnit.map (mapRingHom φ) h), fun a b h =>
      (h_irr.isUnit_or_isUnit <| by rw [h, Polynomial.map_mul]).imp _ _⟩
  all_goals apply ((isPrimitive_of_dvd hf _).isUnit_iff_isUnit_map_of_injective hinj).mpr
  -- ⊢ a ∣ f
  exacts [Dvd.intro _ h.symm, Dvd.intro_left _ h.symm]
  -- 🎉 no goals
#align polynomial.is_primitive.irreducible_of_irreducible_map_of_injective Polynomial.IsPrimitive.irreducible_of_irreducible_map_of_injective

end

section FractionMap

variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

theorem IsPrimitive.isUnit_iff_isUnit_map {p : R[X]} (hp : p.IsPrimitive) :
    IsUnit p ↔ IsUnit (p.map (algebraMap R K)) :=
  hp.isUnit_iff_isUnit_map_of_injective (IsFractionRing.injective _ _)
#align polynomial.is_primitive.is_unit_iff_is_unit_map Polynomial.IsPrimitive.isUnit_iff_isUnit_map

variable [IsDomain R]

section IsIntegrallyClosed

open IsIntegrallyClosed

/-- **Gauss's Lemma** for integrally closed domains states that a monic polynomial is irreducible
  iff it is irreducible in the fraction field. -/
theorem Monic.irreducible_iff_irreducible_map_fraction_map [IsIntegrallyClosed R] {p : R[X]}
    (h : p.Monic) : Irreducible p ↔ Irreducible (p.map <| algebraMap R K) := by
  /- The ← direction follows from `IsPrimitive.irreducible_of_irreducible_map_of_injective`.
       For the → direction, it is enought to show that if `(p.map $ algebraMap R K) = a * b` and
       `a` is not a unit then `b` is a unit -/
  refine'
    ⟨fun hp =>
      irreducible_iff.mpr
        ⟨hp.not_unit.imp h.isPrimitive.isUnit_iff_isUnit_map.mpr, fun a b H =>
          or_iff_not_imp_left.mpr fun hₐ => _⟩,
      fun hp =>
      h.isPrimitive.irreducible_of_irreducible_map_of_injective (IsFractionRing.injective R K) hp⟩
  obtain ⟨a', ha⟩ := eq_map_mul_C_of_dvd K h (dvd_of_mul_right_eq b H.symm)
  -- ⊢ IsUnit b
  obtain ⟨b', hb⟩ := eq_map_mul_C_of_dvd K h (dvd_of_mul_left_eq a H.symm)
  -- ⊢ IsUnit b
  have : a.leadingCoeff * b.leadingCoeff = 1 := by
    rw [← leadingCoeff_mul, ← H, Monic.leadingCoeff (h.map <| algebraMap R K)]
  rw [← ha, ← hb, mul_comm _ (C b.leadingCoeff), mul_assoc, ← mul_assoc (C a.leadingCoeff), ←
    C_mul, this, C_1, one_mul, ← Polynomial.map_mul] at H
  rw [← hb, ← Polynomial.coe_mapRingHom]
  -- ⊢ IsUnit (↑(mapRingHom (algebraMap R K)) b' * ↑C (Polynomial.leadingCoeff b))
  refine'
    IsUnit.mul (IsUnit.map _ (Or.resolve_left (hp.isUnit_or_isUnit _) (show ¬IsUnit a' from _)))
      (isUnit_iff_exists_inv'.mpr
        -- Porting note(https://github.com/leanprover-community/mathlib4/issues/5073): was `rwa`
        (Exists.intro (C a.leadingCoeff) <| by rw [← C_mul, this, C_1]))
  · exact Polynomial.map_injective _ (IsFractionRing.injective R K) H
    -- 🎉 no goals
  · by_contra h_contra
    -- ⊢ False
    refine' hₐ _
    -- ⊢ IsUnit a
    rw [← ha, ← Polynomial.coe_mapRingHom]
    -- ⊢ IsUnit (↑(mapRingHom (algebraMap R K)) a' * ↑C (Polynomial.leadingCoeff a))
    exact
      IsUnit.mul (IsUnit.map _ h_contra)
        (isUnit_iff_exists_inv.mpr
          -- Porting note(https://github.com/leanprover-community/mathlib4/issues/5073): was `rwa`
          (Exists.intro (C b.leadingCoeff) <| by rw [← C_mul, this, C_1]))
#align polynomial.monic.irreducible_iff_irreducible_map_fraction_map Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map

/-- Integrally closed domains are precisely the domains for in which Gauss's lemma holds
    for monic polynomials -/
theorem isIntegrallyClosed_iff' :
    IsIntegrallyClosed R ↔
      ∀ p : R[X], p.Monic → (Irreducible p ↔ Irreducible (p.map <| algebraMap R K)) := by
  constructor
  -- ⊢ IsIntegrallyClosed R → ∀ (p : R[X]), Monic p → (Irreducible p ↔ Irreducible  …
  · intro hR p hp; exact Monic.irreducible_iff_irreducible_map_fraction_map hp
    -- ⊢ Irreducible p ↔ Irreducible (map (algebraMap R K) p)
                   -- 🎉 no goals
  · intro H
    -- ⊢ IsIntegrallyClosed R
    refine'
      (isIntegrallyClosed_iff K).mpr fun {x} hx =>
        RingHom.mem_range.mp <| minpoly.mem_range_of_degree_eq_one R x _
    rw [← Monic.degree_map (minpoly.monic hx) (algebraMap R K)]
    -- ⊢ degree (map (algebraMap R K) (minpoly R x)) = 1
    apply
      degree_eq_one_of_irreducible_of_root ((H _ <| minpoly.monic hx).mp (minpoly.irreducible hx))
    rw [IsRoot, eval_map, ← aeval_def, minpoly.aeval R x]
    -- 🎉 no goals
#align polynomial.is_integrally_closed_iff' Polynomial.isIntegrallyClosed_iff'

theorem Monic.dvd_of_fraction_map_dvd_fraction_map [IsIntegrallyClosed R] {p q : R[X]}
    (hp : p.Monic) (hq : q.Monic)
    (h : q.map (algebraMap R K) ∣ p.map (algebraMap R K)) : q ∣ p := by
  obtain ⟨r, hr⟩ := h
  -- ⊢ q ∣ p
  obtain ⟨d', hr'⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd K hp (dvd_of_mul_left_eq _ hr.symm)
  -- ⊢ q ∣ p
  rw [Monic.leadingCoeff, C_1, mul_one] at hr'
  -- ⊢ q ∣ p
  rw [← hr', ← Polynomial.map_mul] at hr
  -- ⊢ q ∣ p
  exact dvd_of_mul_right_eq _ (Polynomial.map_injective _ (IsFractionRing.injective R K) hr.symm)
  -- ⊢ Monic r
  · exact Monic.of_mul_monic_left (hq.map (algebraMap R K)) (by simpa [← hr] using hp.map _)
    -- 🎉 no goals
#align polynomial.monic.dvd_of_fraction_map_dvd_fraction_map Polynomial.Monic.dvd_of_fraction_map_dvd_fraction_map

theorem Monic.dvd_iff_fraction_map_dvd_fraction_map [IsIntegrallyClosed R] {p q : R[X]}
    (hp : p.Monic) (hq : q.Monic) : q.map (algebraMap R K) ∣ p.map (algebraMap R K) ↔ q ∣ p :=
  ⟨fun h => hp.dvd_of_fraction_map_dvd_fraction_map hq h, fun ⟨a, b⟩ =>
    ⟨a.map (algebraMap R K), b.symm ▸ Polynomial.map_mul (algebraMap R K)⟩⟩
#align polynomial.monic.dvd_iff_fraction_map_dvd_fraction_map Polynomial.Monic.dvd_iff_fraction_map_dvd_fraction_map

end IsIntegrallyClosed

open IsLocalization

section NormalizedGCDMonoid

variable [NormalizedGCDMonoid R]

theorem isUnit_or_eq_zero_of_isUnit_integerNormalization_primPart {p : K[X]} (h0 : p ≠ 0)
    (h : IsUnit (integerNormalization R⁰ p).primPart) : IsUnit p := by
  rcases isUnit_iff.1 h with ⟨_, ⟨u, rfl⟩, hu⟩
  -- ⊢ IsUnit p
  obtain ⟨⟨c, c0⟩, hc⟩ := integerNormalization_map_to_map R⁰ p
  -- ⊢ IsUnit p
  rw [Subtype.coe_mk, Algebra.smul_def, algebraMap_apply] at hc
  -- ⊢ IsUnit p
  apply isUnit_of_mul_isUnit_right
  -- ⊢ IsUnit (?intro.intro.intro.intro.mk.x * p)
  rw [← hc, (integerNormalization R⁰ p).eq_C_content_mul_primPart, ← hu, ← RingHom.map_mul,
    isUnit_iff]
  refine'
    ⟨algebraMap R K ((integerNormalization R⁰ p).content * ↑u), isUnit_iff_ne_zero.2 fun con => _,
      by simp⟩
  replace con := (injective_iff_map_eq_zero (algebraMap R K)).1 (IsFractionRing.injective _ _) _ con
  -- ⊢ False
  rw [mul_eq_zero, content_eq_zero_iff, IsFractionRing.integerNormalization_eq_zero_iff] at con
  -- ⊢ False
  rcases con with (con | con)
  -- ⊢ False
  · apply h0 con
    -- 🎉 no goals
  · apply Units.ne_zero _ con
    -- 🎉 no goals
#align polynomial.is_unit_or_eq_zero_of_is_unit_integer_normalization_prim_part Polynomial.isUnit_or_eq_zero_of_isUnit_integerNormalization_primPart

/-- **Gauss's Lemma** for GCD domains states that a primitive polynomial is irreducible iff it is
  irreducible in the fraction field. -/
theorem IsPrimitive.irreducible_iff_irreducible_map_fraction_map {p : R[X]} (hp : p.IsPrimitive) :
    Irreducible p ↔ Irreducible (p.map (algebraMap R K)) := by
  -- Porting note: was `(IsFractionRing.injective _ _)`
  refine'
    ⟨fun hi => ⟨fun h => hi.not_unit (hp.isUnit_iff_isUnit_map.2 h), fun a b hab => _⟩,
      hp.irreducible_of_irreducible_map_of_injective (IsFractionRing.injective R K)⟩
  obtain ⟨⟨c, c0⟩, hc⟩ := integerNormalization_map_to_map R⁰ a
  -- ⊢ IsUnit a ∨ IsUnit b
  obtain ⟨⟨d, d0⟩, hd⟩ := integerNormalization_map_to_map R⁰ b
  -- ⊢ IsUnit a ∨ IsUnit b
  rw [Algebra.smul_def, algebraMap_apply, Subtype.coe_mk] at hc hd
  -- ⊢ IsUnit a ∨ IsUnit b
  rw [mem_nonZeroDivisors_iff_ne_zero] at c0 d0
  -- ⊢ IsUnit a ∨ IsUnit b
  have hcd0 : c * d ≠ 0 := mul_ne_zero c0 d0
  -- ⊢ IsUnit a ∨ IsUnit b
  rw [Ne.def, ← C_eq_zero] at hcd0
  -- ⊢ IsUnit a ∨ IsUnit b
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
    rw [Ne.def, Ne.def, ← not_or, ← mul_eq_zero, ← hab]
    intro con
    apply hp.ne_zero (map_injective (algebraMap R K) (IsFractionRing.injective _ _) _)
    simp [con]
  rcases hi.isUnit_or_isUnit (mul_left_cancel₀ hcd0 h1).symm with (h | h)
  -- ⊢ IsUnit a ∨ IsUnit b
  · right
    -- ⊢ IsUnit b
    apply
      isUnit_or_eq_zero_of_isUnit_integerNormalization_primPart h0.2
        (isUnit_of_mul_isUnit_right h)
  · left
    -- ⊢ IsUnit a
    apply isUnit_or_eq_zero_of_isUnit_integerNormalization_primPart h0.1 h
    -- 🎉 no goals
#align polynomial.is_primitive.irreducible_iff_irreducible_map_fraction_map Polynomial.IsPrimitive.irreducible_iff_irreducible_map_fraction_map

theorem IsPrimitive.dvd_of_fraction_map_dvd_fraction_map {p q : R[X]} (hp : p.IsPrimitive)
    (hq : q.IsPrimitive) (h_dvd : p.map (algebraMap R K) ∣ q.map (algebraMap R K)) : p ∣ q := by
  rcases h_dvd with ⟨r, hr⟩
  -- ⊢ p ∣ q
  obtain ⟨⟨s, s0⟩, hs⟩ := integerNormalization_map_to_map R⁰ r
  -- ⊢ p ∣ q
  rw [Subtype.coe_mk, Algebra.smul_def, algebraMap_apply] at hs
  -- ⊢ p ∣ q
  have h : p ∣ q * C s := by
    use integerNormalization R⁰ r
    apply map_injective (algebraMap R K) (IsFractionRing.injective _ _)
    rw [Polynomial.map_mul, Polynomial.map_mul, hs, hr, mul_assoc, mul_comm r]
    simp
  rw [← hp.dvd_primPart_iff_dvd, primPart_mul, hq.primPart_eq, Associated.dvd_iff_dvd_right] at h
  · exact h
    -- 🎉 no goals
  · symm
    -- ⊢ Associated q (q * primPart (↑C s))
    rcases isUnit_primPart_C s with ⟨u, hu⟩
    -- ⊢ Associated q (q * primPart (↑C s))
    use u
    -- ⊢ q * ↑u = q * primPart (↑C s)
    rw [hu]
    -- 🎉 no goals
  iterate 2
    apply mul_ne_zero hq.ne_zero
    rw [Ne.def, C_eq_zero]
    contrapose! s0
    simp [s0, mem_nonZeroDivisors_iff_ne_zero]
#align polynomial.is_primitive.dvd_of_fraction_map_dvd_fraction_map Polynomial.IsPrimitive.dvd_of_fraction_map_dvd_fraction_map

variable (K)

theorem IsPrimitive.dvd_iff_fraction_map_dvd_fraction_map {p q : R[X]} (hp : p.IsPrimitive)
    (hq : q.IsPrimitive) : p ∣ q ↔ p.map (algebraMap R K) ∣ q.map (algebraMap R K) :=
  ⟨fun ⟨a, b⟩ => ⟨a.map (algebraMap R K), b.symm ▸ Polynomial.map_mul (algebraMap R K)⟩, fun h =>
    hp.dvd_of_fraction_map_dvd_fraction_map hq h⟩
#align polynomial.is_primitive.dvd_iff_fraction_map_dvd_fraction_map Polynomial.IsPrimitive.dvd_iff_fraction_map_dvd_fraction_map

end NormalizedGCDMonoid

end FractionMap

/-- **Gauss's Lemma** for `ℤ` states that a primitive integer polynomial is irreducible iff it is
  irreducible over `ℚ`. -/
theorem IsPrimitive.Int.irreducible_iff_irreducible_map_cast {p : ℤ[X]} (hp : p.IsPrimitive) :
    Irreducible p ↔ Irreducible (p.map (Int.castRingHom ℚ)) :=
  hp.irreducible_iff_irreducible_map_fraction_map
#align polynomial.is_primitive.int.irreducible_iff_irreducible_map_cast Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast

theorem IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast (p q : ℤ[X]) (hp : p.IsPrimitive)
    (hq : q.IsPrimitive) : p ∣ q ↔ p.map (Int.castRingHom ℚ) ∣ q.map (Int.castRingHom ℚ) :=
  hp.dvd_iff_fraction_map_dvd_fraction_map ℚ hq
#align polynomial.is_primitive.int.dvd_iff_map_cast_dvd_map_cast Polynomial.IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast

end Polynomial
