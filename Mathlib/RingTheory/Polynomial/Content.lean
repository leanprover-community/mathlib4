/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Polynomial.CancelLeads
import Mathlib.Algebra.Polynomial.EraseLead
import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# GCD structures on polynomials

Definitions and basic results about polynomials over GCD domains, particularly their contents
and primitive polynomials.

## Main Definitions
Let `p : R[X]`.
- `p.content` is the `gcd` of the coefficients of `p`.
- `p.IsPrimitive` indicates that `p.content = 1`.

## Main Results
- `Polynomial.content_mul`: if `p q : R[X]`, then `(p * q).content = p.content * q.content`.
- `Polynomial.NormalizedGcdMonoid`: the polynomial ring of a GCD domain is itself a GCD domain.

## Note

This has nothing to do with minimal polynomials of primitive elements in finite fields.

-/


namespace Polynomial

section Primitive

variable {R : Type*} [CommSemiring R]

/-- A polynomial is primitive when the only constant polynomials dividing it are units.
Note: This has nothing to do with minimal polynomials of primitive elements in finite fields. -/
def IsPrimitive (p : R[X]) : Prop :=
  ∀ r : R, C r ∣ p → IsUnit r

theorem isPrimitive_iff_isUnit_of_C_dvd {p : R[X]} : p.IsPrimitive ↔ ∀ r : R, C r ∣ p → IsUnit r :=
  Iff.rfl

@[simp]
theorem isPrimitive_one : IsPrimitive (1 : R[X]) := fun _ h =>
  isUnit_C.mp (isUnit_of_dvd_one h)

theorem Monic.isPrimitive {p : R[X]} (hp : p.Monic) : p.IsPrimitive := by
  rintro r ⟨q, h⟩
  exact isUnit_of_mul_eq_one r (q.coeff p.natDegree) (by rwa [← coeff_C_mul, ← h])

theorem IsPrimitive.ne_zero [Nontrivial R] {p : R[X]} (hp : p.IsPrimitive) : p ≠ 0 := by
  rintro rfl
  exact (hp 0 (dvd_zero (C 0))).ne_zero rfl

theorem isPrimitive_of_dvd {p q : R[X]} (hp : IsPrimitive p) (hq : q ∣ p) : IsPrimitive q :=
  fun a ha => isPrimitive_iff_isUnit_of_C_dvd.mp hp a (dvd_trans ha hq)

/-- An irreducible nonconstant polynomial over a domain is primitive. -/
theorem _root_.Irreducible.isPrimitive [NoZeroDivisors R]
    {p : Polynomial R} (hp : Irreducible p) (hp' : p.natDegree ≠ 0) : p.IsPrimitive := by
  rintro r ⟨q, hq⟩
  suffices ¬IsUnit q by simpa using ((hp.2 hq).resolve_right this).map Polynomial.constantCoeff
  intro H
  have hr : r ≠ 0 := by rintro rfl; simp_all
  obtain ⟨s, hs, rfl⟩ := Polynomial.isUnit_iff.mp H
  simp [hq, Polynomial.natDegree_C_mul hr] at hp'

end Primitive

variable {R : Type*} [CommRing R] [IsDomain R]

section NormalizedGCDMonoid

variable [NormalizedGCDMonoid R]

/-- `p.content` is the `gcd` of the coefficients of `p`. -/
def content (p : R[X]) : R :=
  p.support.gcd p.coeff

theorem content_dvd_coeff {p : R[X]} (n : ℕ) : p.content ∣ p.coeff n := by
  by_cases h : n ∈ p.support
  · apply Finset.gcd_dvd h
  rw [mem_support_iff, Classical.not_not] at h
  rw [h]
  apply dvd_zero

@[simp]
theorem content_C {r : R} : (C r).content = normalize r := by
  rw [content]
  by_cases h0 : r = 0
  · simp [h0]
  have h : (C r).support = {0} := support_monomial _ h0
  simp [h]

@[simp]
theorem content_zero : content (0 : R[X]) = 0 := by rw [← C_0, content_C, normalize_zero]

@[simp]
theorem content_one : content (1 : R[X]) = 1 := by rw [← C_1, content_C, normalize_one]

theorem content_X_mul {p : R[X]} : content (X * p) = content p := by
  rw [content, content, Finset.gcd_def, Finset.gcd_def]
  refine congr rfl ?_
  have h : (X * p).support = p.support.map ⟨Nat.succ, Nat.succ_injective⟩ := by
    ext a
    simp only [Finset.mem_map, Function.Embedding.coeFn_mk, Ne, mem_support_iff]
    rcases a with - | a
    · simp
    rw [mul_comm, coeff_mul_X]
    constructor
    · intro h
      use a
    · rintro ⟨b, ⟨h1, h2⟩⟩
      rw [← Nat.succ_injective h2]
      apply h1
  rw [h]
  simp only [Finset.map_val, Function.comp_apply, Function.Embedding.coeFn_mk, Multiset.map_map]
  refine congr (congr rfl ?_) rfl
  ext a
  rw [mul_comm]
  simp [coeff_mul_X]

@[simp]
theorem content_X_pow {k : ℕ} : content ((X : R[X]) ^ k) = 1 := by
  induction' k with k hi
  · simp
  rw [pow_succ', content_X_mul, hi]

@[simp]
theorem content_X : content (X : R[X]) = 1 := by rw [← mul_one X, content_X_mul, content_one]

theorem content_C_mul (r : R) (p : R[X]) : (C r * p).content = normalize r * p.content := by
  by_cases h0 : r = 0; · simp [h0]
  rw [content]; rw [content]; rw [← Finset.gcd_mul_left]
  refine congr (congr rfl ?_) ?_ <;> ext <;> simp [h0, mem_support_iff]

@[simp]
theorem content_monomial {r : R} {k : ℕ} : content (monomial k r) = normalize r := by
  rw [← C_mul_X_pow_eq_monomial, content_C_mul, content_X_pow, mul_one]

theorem content_eq_zero_iff {p : R[X]} : content p = 0 ↔ p = 0 := by
  rw [content, Finset.gcd_eq_zero_iff]
  constructor <;> intro h
  · ext n
    by_cases h0 : n ∈ p.support
    · rw [h n h0, coeff_zero]
    · rw [mem_support_iff] at h0
      push_neg at h0
      simp [h0]
  · intro x
    simp [h]

-- Porting note: this reduced with simp so created `normUnit_content` and put simp on it
theorem normalize_content {p : R[X]} : normalize p.content = p.content :=
  Finset.normalize_gcd

@[simp]
theorem normUnit_content {p : R[X]} : normUnit (content p) = 1 := by
  by_cases hp0 : p.content = 0
  · simp [hp0]
  · ext
    apply mul_left_cancel₀ hp0
    rw [← normalize_apply, normalize_content, Units.val_one, mul_one]

theorem content_eq_gcd_range_of_lt (p : R[X]) (n : ℕ) (h : p.natDegree < n) :
    p.content = (Finset.range n).gcd p.coeff := by
  apply dvd_antisymm_of_normalize_eq normalize_content Finset.normalize_gcd
  · rw [Finset.dvd_gcd_iff]
    intro i _
    apply content_dvd_coeff _
  · apply Finset.gcd_mono
    intro i
    simp only [mem_support_iff, Ne, Finset.mem_range]
    contrapose!
    intro h1
    apply coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le h h1)

theorem content_eq_gcd_range_succ (p : R[X]) :
    p.content = (Finset.range p.natDegree.succ).gcd p.coeff :=
  content_eq_gcd_range_of_lt _ _ (Nat.lt_succ_self _)

theorem content_eq_gcd_leadingCoeff_content_eraseLead (p : R[X]) :
    p.content = GCDMonoid.gcd p.leadingCoeff (eraseLead p).content := by
  by_cases h : p = 0
  · simp [h]
  rw [← leadingCoeff_eq_zero, leadingCoeff, ← Ne, ← mem_support_iff] at h
  rw [content, ← Finset.insert_erase h, Finset.gcd_insert, leadingCoeff, content,
    eraseLead_support]
  refine congr rfl (Finset.gcd_congr rfl fun i hi => ?_)
  rw [Finset.mem_erase] at hi
  rw [eraseLead_coeff, if_neg hi.1]

theorem dvd_content_iff_C_dvd {p : R[X]} {r : R} : r ∣ p.content ↔ C r ∣ p := by
  rw [C_dvd_iff_dvd_coeff]
  constructor
  · intro h i
    apply h.trans (content_dvd_coeff _)
  · intro h
    rw [content, Finset.dvd_gcd_iff]
    intro i _
    apply h i

theorem C_content_dvd (p : R[X]) : C p.content ∣ p :=
  dvd_content_iff_C_dvd.1 dvd_rfl

theorem isPrimitive_iff_content_eq_one {p : R[X]} : p.IsPrimitive ↔ p.content = 1 := by
  rw [← normalize_content, normalize_eq_one, IsPrimitive]
  simp_rw [← dvd_content_iff_C_dvd]
  exact ⟨fun h => h p.content (dvd_refl p.content), fun h r hdvd => isUnit_of_dvd_unit hdvd h⟩

theorem IsPrimitive.content_eq_one {p : R[X]} (hp : p.IsPrimitive) : p.content = 1 :=
  isPrimitive_iff_content_eq_one.mp hp

section PrimPart

/-- The primitive part of a polynomial `p` is the primitive polynomial gained by dividing `p` by
  `p.content`. If `p = 0`, then `p.primPart = 1`. -/
noncomputable def primPart (p : R[X]) : R[X] :=
  letI := Classical.decEq R
  if p = 0 then 1 else Classical.choose (C_content_dvd p)

theorem eq_C_content_mul_primPart (p : R[X]) : p = C p.content * p.primPart := by
  by_cases h : p = 0; · simp [h]
  rw [primPart, if_neg h, ← Classical.choose_spec (C_content_dvd p)]

@[simp]
theorem primPart_zero : primPart (0 : R[X]) = 1 :=
  if_pos rfl

theorem isPrimitive_primPart (p : R[X]) : p.primPart.IsPrimitive := by
  by_cases h : p = 0; · simp [h]
  rw [← content_eq_zero_iff] at h
  rw [isPrimitive_iff_content_eq_one]
  apply mul_left_cancel₀ h
  conv_rhs => rw [p.eq_C_content_mul_primPart, mul_one, content_C_mul, normalize_content]

theorem content_primPart (p : R[X]) : p.primPart.content = 1 :=
  p.isPrimitive_primPart.content_eq_one

theorem primPart_ne_zero (p : R[X]) : p.primPart ≠ 0 :=
  p.isPrimitive_primPart.ne_zero

theorem natDegree_primPart (p : R[X]) : p.primPart.natDegree = p.natDegree := by
  by_cases h : C p.content = 0
  · rw [C_eq_zero, content_eq_zero_iff] at h
    simp [h]
  conv_rhs =>
    rw [p.eq_C_content_mul_primPart, natDegree_mul h p.primPart_ne_zero, natDegree_C, zero_add]

@[simp]
theorem IsPrimitive.primPart_eq {p : R[X]} (hp : p.IsPrimitive) : p.primPart = p := by
  rw [← one_mul p.primPart, ← C_1, ← hp.content_eq_one, ← p.eq_C_content_mul_primPart]

theorem isUnit_primPart_C (r : R) : IsUnit (C r).primPart := by
  by_cases h0 : r = 0
  · simp [h0]
  unfold IsUnit
  refine
    ⟨⟨C ↑(normUnit r)⁻¹, C ↑(normUnit r), by rw [← RingHom.map_mul, Units.inv_mul, C_1], by
        rw [← RingHom.map_mul, Units.mul_inv, C_1]⟩,
      ?_⟩
  rw [← normalize_eq_zero, ← C_eq_zero] at h0
  apply mul_left_cancel₀ h0
  conv_rhs => rw [← content_C, ← (C r).eq_C_content_mul_primPart]
  simp only [normalize_apply, RingHom.map_mul]
  rw [mul_assoc, ← RingHom.map_mul, Units.mul_inv, C_1, mul_one]

theorem primPart_dvd (p : R[X]) : p.primPart ∣ p :=
  Dvd.intro_left (C p.content) p.eq_C_content_mul_primPart.symm

theorem aeval_primPart_eq_zero {S : Type*} [Ring S] [IsDomain S] [Algebra R S]
    [NoZeroSMulDivisors R S] {p : R[X]} {s : S} (hpzero : p ≠ 0) (hp : aeval s p = 0) :
    aeval s p.primPart = 0 := by
  rw [eq_C_content_mul_primPart p, map_mul, aeval_C] at hp
  have hcont : p.content ≠ 0 := fun h => hpzero (content_eq_zero_iff.1 h)
  replace hcont := Function.Injective.ne (FaithfulSMul.algebraMap_injective R S) hcont
  rw [map_zero] at hcont
  exact eq_zero_of_ne_zero_of_mul_left_eq_zero hcont hp

theorem eval₂_primPart_eq_zero {S : Type*} [CommSemiring S] [IsDomain S] {f : R →+* S}
    (hinj : Function.Injective f) {p : R[X]} {s : S} (hpzero : p ≠ 0) (hp : eval₂ f s p = 0) :
    eval₂ f s p.primPart = 0 := by
  rw [eq_C_content_mul_primPart p, eval₂_mul, eval₂_C] at hp
  have hcont : p.content ≠ 0 := fun h => hpzero (content_eq_zero_iff.1 h)
  replace hcont := Function.Injective.ne hinj hcont
  rw [map_zero] at hcont
  exact eq_zero_of_ne_zero_of_mul_left_eq_zero hcont hp

end PrimPart

theorem gcd_content_eq_of_dvd_sub {a : R} {p q : R[X]} (h : C a ∣ p - q) :
    GCDMonoid.gcd a p.content = GCDMonoid.gcd a q.content := by
  rw [content_eq_gcd_range_of_lt p (max p.natDegree q.natDegree).succ
      (lt_of_le_of_lt (le_max_left _ _) (Nat.lt_succ_self _))]
  rw [content_eq_gcd_range_of_lt q (max p.natDegree q.natDegree).succ
      (lt_of_le_of_lt (le_max_right _ _) (Nat.lt_succ_self _))]
  apply Finset.gcd_eq_of_dvd_sub
  intro x _
  obtain ⟨w, hw⟩ := h
  use w.coeff x
  rw [← coeff_sub, hw, coeff_C_mul]

theorem content_mul_aux {p q : R[X]} :
    GCDMonoid.gcd (p * q).eraseLead.content p.leadingCoeff =
      GCDMonoid.gcd (p.eraseLead * q).content p.leadingCoeff := by
  rw [gcd_comm (content _) _, gcd_comm (content _) _]
  apply gcd_content_eq_of_dvd_sub
  rw [← self_sub_C_mul_X_pow, ← self_sub_C_mul_X_pow, sub_mul, sub_sub, add_comm, sub_add,
    sub_sub_cancel, leadingCoeff_mul, RingHom.map_mul, mul_assoc, mul_assoc]
  apply dvd_sub (Dvd.intro _ rfl) (Dvd.intro _ rfl)

@[simp]
theorem content_mul {p q : R[X]} : (p * q).content = p.content * q.content := by
  classical
    suffices h :
        ∀ (n : ℕ) (p q : R[X]), (p * q).degree < n → (p * q).content = p.content * q.content by
      apply h
      apply lt_of_le_of_lt degree_le_natDegree (WithBot.coe_lt_coe.2 (Nat.lt_succ_self _))
    intro n
    induction' n with n ih
    · intro p q hpq
      rw [Nat.cast_zero,
        Nat.WithBot.lt_zero_iff, degree_eq_bot, mul_eq_zero] at hpq
      rcases hpq with (rfl | rfl) <;> simp
    intro p q hpq
    by_cases p0 : p = 0
    · simp [p0]
    by_cases q0 : q = 0
    · simp [q0]
    rw [degree_eq_natDegree (mul_ne_zero p0 q0), Nat.cast_lt,
      Nat.lt_succ_iff_lt_or_eq, ← Nat.cast_lt (α := WithBot ℕ),
      ← degree_eq_natDegree (mul_ne_zero p0 q0), natDegree_mul p0 q0] at hpq
    rcases hpq with (hlt | heq)
    · apply ih _ _ hlt
    rw [← p.natDegree_primPart, ← q.natDegree_primPart, ← Nat.cast_inj (R := WithBot ℕ),
      Nat.cast_add, ← degree_eq_natDegree p.primPart_ne_zero,
      ← degree_eq_natDegree q.primPart_ne_zero] at heq
    rw [p.eq_C_content_mul_primPart, q.eq_C_content_mul_primPart]
    suffices h : (q.primPart * p.primPart).content = 1 by
      rw [mul_assoc, content_C_mul, content_C_mul, mul_comm p.primPart, mul_assoc, content_C_mul,
        content_C_mul, h, mul_one, content_primPart, content_primPart, mul_one, mul_one]
    rw [← normalize_content, normalize_eq_one, isUnit_iff_dvd_one,
      content_eq_gcd_leadingCoeff_content_eraseLead, leadingCoeff_mul, gcd_comm]
    apply (gcd_mul_dvd_mul_gcd _ _ _).trans
    rw [content_mul_aux, ih, content_primPart, mul_one, gcd_comm, ←
      content_eq_gcd_leadingCoeff_content_eraseLead, content_primPart, one_mul,
      mul_comm q.primPart, content_mul_aux, ih, content_primPart, mul_one, gcd_comm, ←
      content_eq_gcd_leadingCoeff_content_eraseLead, content_primPart]
    · rw [← heq, degree_mul, WithBot.add_lt_add_iff_right]
      · apply degree_erase_lt p.primPart_ne_zero
      · rw [Ne, degree_eq_bot]
        apply q.primPart_ne_zero
    · rw [mul_comm, ← heq, degree_mul, WithBot.add_lt_add_iff_left]
      · apply degree_erase_lt q.primPart_ne_zero
      · rw [Ne, degree_eq_bot]
        apply p.primPart_ne_zero

theorem IsPrimitive.mul {p q : R[X]} (hp : p.IsPrimitive) (hq : q.IsPrimitive) :
    (p * q).IsPrimitive := by
  rw [isPrimitive_iff_content_eq_one, content_mul, hp.content_eq_one, hq.content_eq_one, mul_one]

@[simp]
theorem primPart_mul {p q : R[X]} (h0 : p * q ≠ 0) :
    (p * q).primPart = p.primPart * q.primPart := by
  rw [Ne, ← content_eq_zero_iff, ← C_eq_zero] at h0
  apply mul_left_cancel₀ h0
  conv_lhs =>
    rw [← (p * q).eq_C_content_mul_primPart, p.eq_C_content_mul_primPart,
      q.eq_C_content_mul_primPart]
  rw [content_mul, RingHom.map_mul]
  ring

theorem IsPrimitive.dvd_primPart_iff_dvd {p q : R[X]} (hp : p.IsPrimitive) (hq : q ≠ 0) :
    p ∣ q.primPart ↔ p ∣ q := by
  refine ⟨fun h => h.trans (Dvd.intro_left _ q.eq_C_content_mul_primPart.symm), fun h => ?_⟩
  rcases h with ⟨r, rfl⟩
  apply Dvd.intro _
  rw [primPart_mul hq, hp.primPart_eq]

theorem exists_primitive_lcm_of_isPrimitive {p q : R[X]} (hp : p.IsPrimitive) (hq : q.IsPrimitive) :
    ∃ r : R[X], r.IsPrimitive ∧ ∀ s : R[X], p ∣ s ∧ q ∣ s ↔ r ∣ s := by
  classical
    have h : ∃ (n : ℕ) (r : R[X]), r.natDegree = n ∧ r.IsPrimitive ∧ p ∣ r ∧ q ∣ r :=
      ⟨(p * q).natDegree, p * q, rfl, hp.mul hq, dvd_mul_right _ _, dvd_mul_left _ _⟩
    rcases Nat.find_spec h with ⟨r, rdeg, rprim, pr, qr⟩
    refine ⟨r, rprim, fun s => ⟨?_, fun rs => ⟨pr.trans rs, qr.trans rs⟩⟩⟩
    suffices hs : ∀ (n : ℕ) (s : R[X]), s.natDegree = n → p ∣ s ∧ q ∣ s → r ∣ s from
      hs s.natDegree s rfl
    clear s
    by_contra! con
    rcases Nat.find_spec con with ⟨s, sdeg, ⟨ps, qs⟩, rs⟩
    have s0 : s ≠ 0 := by
      contrapose! rs
      simp [rs]
    have hs :=
      Nat.find_min' h
        ⟨_, s.natDegree_primPart, s.isPrimitive_primPart, (hp.dvd_primPart_iff_dvd s0).2 ps,
          (hq.dvd_primPart_iff_dvd s0).2 qs⟩
    rw [← rdeg] at hs
    by_cases sC : s.natDegree ≤ 0
    · rw [eq_C_of_natDegree_le_zero (le_trans hs sC), isPrimitive_iff_content_eq_one, content_C,
        normalize_eq_one] at rprim
      rw [eq_C_of_natDegree_le_zero (le_trans hs sC), ← dvd_content_iff_C_dvd] at rs
      apply rs rprim.dvd
    have hcancel := natDegree_cancelLeads_lt_of_natDegree_le_natDegree hs (lt_of_not_ge sC)
    rw [sdeg] at hcancel
    apply Nat.find_min con hcancel
    refine
      ⟨_, rfl, ⟨dvd_cancelLeads_of_dvd_of_dvd pr ps, dvd_cancelLeads_of_dvd_of_dvd qr qs⟩,
        fun rcs => rs ?_⟩
    rw [← rprim.dvd_primPart_iff_dvd s0]
    rw [cancelLeads, tsub_eq_zero_iff_le.mpr hs, pow_zero, mul_one] at rcs
    have h :=
      dvd_add rcs (Dvd.intro_left (C (leadingCoeff s) * X ^ (natDegree s - natDegree r)) rfl)
    have hC0 := rprim.ne_zero
    rw [Ne, ← leadingCoeff_eq_zero, ← C_eq_zero] at hC0
    rw [sub_add_cancel, ← rprim.dvd_primPart_iff_dvd (mul_ne_zero hC0 s0)] at h
    rcases isUnit_primPart_C r.leadingCoeff with ⟨u, hu⟩
    apply h.trans (Associated.symm ⟨u, _⟩).dvd
    rw [primPart_mul (mul_ne_zero hC0 s0), hu, mul_comm]

theorem dvd_iff_content_dvd_content_and_primPart_dvd_primPart {p q : R[X]} (hq : q ≠ 0) :
    p ∣ q ↔ p.content ∣ q.content ∧ p.primPart ∣ q.primPart := by
  constructor
  · rintro ⟨r, rfl⟩
    rw [content_mul, p.isPrimitive_primPart.dvd_primPart_iff_dvd hq]
    exact ⟨dvd_mul_right .., dvd_mul_of_dvd_left p.primPart_dvd _⟩
  · rintro ⟨h₁, h₂⟩
    rw [p.eq_C_content_mul_primPart, q.eq_C_content_mul_primPart]
    gcongr

noncomputable instance (priority := 100) normalizedGcdMonoid : NormalizedGCDMonoid R[X] :=
  letI := Classical.decEq R
  normalizedGCDMonoidOfExistsLCM fun p q => by
    rcases exists_primitive_lcm_of_isPrimitive p.isPrimitive_primPart
        q.isPrimitive_primPart with
      ⟨r, rprim, hr⟩
    refine ⟨C (lcm p.content q.content) * r, fun s => ?_⟩
    by_cases hs : s = 0
    · simp [hs]
    by_cases hpq : C (lcm p.content q.content) = 0
    · rw [C_eq_zero, lcm_eq_zero_iff, content_eq_zero_iff, content_eq_zero_iff] at hpq
      rcases hpq with (hpq | hpq) <;> simp [hpq, hs]
    iterate 3 rw [dvd_iff_content_dvd_content_and_primPart_dvd_primPart hs]
    rw [content_mul, rprim.content_eq_one, mul_one, content_C, normalize_lcm, lcm_dvd_iff,
      primPart_mul (mul_ne_zero hpq rprim.ne_zero), rprim.primPart_eq,
      (isUnit_primPart_C (lcm p.content q.content)).mul_left_dvd, ← hr s.primPart]
    tauto

theorem degree_gcd_le_left {p : R[X]} (hp : p ≠ 0) (q) : (gcd p q).degree ≤ p.degree := by
  have := natDegree_le_iff_degree_le.mp (natDegree_le_of_dvd (gcd_dvd_left p q) hp)
  rwa [degree_eq_natDegree hp]

theorem degree_gcd_le_right (p) {q : R[X]} (hq : q ≠ 0) : (gcd p q).degree ≤ q.degree := by
  rw [gcd_comm]
  exact degree_gcd_le_left hq p

end NormalizedGCDMonoid

end Polynomial
