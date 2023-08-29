/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Polynomial.FieldDivision
import Mathlib.Data.Polynomial.EraseLead
import Mathlib.Data.Polynomial.CancelLeads

#align_import ring_theory.polynomial.content from "leanprover-community/mathlib"@"7a030ab8eb5d99f05a891dccc49c5b5b90c947d3"

/-!
# GCD structures on polynomials

Definitions and basic results about polynomials over GCD domains, particularly their contents
and primitive polynomials.

## Main Definitions
Let `p : R[X]`.
 - `p.content` is the `gcd` of the coefficients of `p`.
 - `p.IsPrimitive` indicates that `p.content = 1`.

## Main Results
 - `Polynomial.content_mul`:
  If `p q : R[X]`, then `(p * q).content = p.content * q.content`.
 - `Polynomial.NormalizedGcdMonoid`:
  The polynomial ring of a GCD domain is itself a GCD domain.

-/


namespace Polynomial

open Polynomial

section Primitive

variable {R : Type*} [CommSemiring R]

/-- A polynomial is primitive when the only constant polynomials dividing it are units -/
def IsPrimitive (p : R[X]) : Prop :=
  ∀ r : R, C r ∣ p → IsUnit r
#align polynomial.is_primitive Polynomial.IsPrimitive

theorem isPrimitive_iff_isUnit_of_C_dvd {p : R[X]} : p.IsPrimitive ↔ ∀ r : R, C r ∣ p → IsUnit r :=
  Iff.rfl
set_option linter.uppercaseLean3 false in
#align polynomial.is_primitive_iff_is_unit_of_C_dvd Polynomial.isPrimitive_iff_isUnit_of_C_dvd

@[simp]
theorem isPrimitive_one : IsPrimitive (1 : R[X]) := fun _ h =>
  isUnit_C.mp (isUnit_of_dvd_one h)
#align polynomial.is_primitive_one Polynomial.isPrimitive_one

theorem Monic.isPrimitive {p : R[X]} (hp : p.Monic) : p.IsPrimitive := by
  rintro r ⟨q, h⟩
  -- ⊢ IsUnit r
  exact isUnit_of_mul_eq_one r (q.coeff p.natDegree) (by rwa [← coeff_C_mul, ← h])
  -- 🎉 no goals
#align polynomial.monic.is_primitive Polynomial.Monic.isPrimitive

theorem IsPrimitive.ne_zero [Nontrivial R] {p : R[X]} (hp : p.IsPrimitive) : p ≠ 0 := by
  rintro rfl
  -- ⊢ False
  exact (hp 0 (dvd_zero (C 0))).ne_zero rfl
  -- 🎉 no goals
#align polynomial.is_primitive.ne_zero Polynomial.IsPrimitive.ne_zero

theorem isPrimitive_of_dvd {p q : R[X]} (hp : IsPrimitive p) (hq : q ∣ p) : IsPrimitive q :=
  fun a ha => isPrimitive_iff_isUnit_of_C_dvd.mp hp a (dvd_trans ha hq)
#align polynomial.is_primitive_of_dvd Polynomial.isPrimitive_of_dvd

end Primitive

variable {R : Type*} [CommRing R] [IsDomain R]

section NormalizedGCDMonoid

variable [NormalizedGCDMonoid R]

/-- `p.content` is the `gcd` of the coefficients of `p`. -/
def content (p : R[X]) : R :=
  p.support.gcd p.coeff
#align polynomial.content Polynomial.content

theorem content_dvd_coeff {p : R[X]} (n : ℕ) : p.content ∣ p.coeff n := by
  by_cases h : n ∈ p.support
  -- ⊢ content p ∣ coeff p n
  · apply Finset.gcd_dvd h
    -- 🎉 no goals
  rw [mem_support_iff, Classical.not_not] at h
  -- ⊢ content p ∣ coeff p n
  rw [h]
  -- ⊢ content p ∣ 0
  apply dvd_zero
  -- 🎉 no goals
#align polynomial.content_dvd_coeff Polynomial.content_dvd_coeff

@[simp]
theorem content_C {r : R} : (C r).content = normalize r := by
  rw [content]
  -- ⊢ Finset.gcd (support (↑C r)) (coeff (↑C r)) = ↑normalize r
  by_cases h0 : r = 0
  -- ⊢ Finset.gcd (support (↑C r)) (coeff (↑C r)) = ↑normalize r
  · simp [h0]
    -- 🎉 no goals
  have h : (C r).support = {0} := support_monomial _ h0
  -- ⊢ Finset.gcd (support (↑C r)) (coeff (↑C r)) = ↑normalize r
  simp [h]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.content_C Polynomial.content_C

@[simp]
theorem content_zero : content (0 : R[X]) = 0 := by rw [← C_0, content_C, normalize_zero]
                                                    -- 🎉 no goals
#align polynomial.content_zero Polynomial.content_zero

@[simp]
theorem content_one : content (1 : R[X]) = 1 := by rw [← C_1, content_C, normalize_one]
                                                   -- 🎉 no goals
#align polynomial.content_one Polynomial.content_one

theorem content_X_mul {p : R[X]} : content (X * p) = content p := by
  rw [content, content, Finset.gcd_def, Finset.gcd_def]
  -- ⊢ Multiset.gcd (Multiset.map (coeff (X * p)) (support (X * p)).val) = Multiset …
  refine' congr rfl _
  -- ⊢ Multiset.map (coeff (X * p)) (support (X * p)).val = Multiset.map (coeff p)  …
  have h : (X * p).support = p.support.map ⟨Nat.succ, Nat.succ_injective⟩ := by
    ext a
    simp only [exists_prop, Finset.mem_map, Function.Embedding.coeFn_mk, Ne.def, mem_support_iff]
    cases' a with a
    · simp [coeff_X_mul_zero, Nat.succ_ne_zero]
    rw [mul_comm, coeff_mul_X]
    constructor
    · intro h
      use a
    · rintro ⟨b, ⟨h1, h2⟩⟩
      rw [← Nat.succ_injective h2]
      apply h1
  rw [h]
  -- ⊢ Multiset.map (coeff (X * p)) (Finset.map { toFun := Nat.succ, inj' := Nat.su …
  simp only [Finset.map_val, Function.comp_apply, Function.Embedding.coeFn_mk, Multiset.map_map]
  -- ⊢ Multiset.map (fun x => coeff (X * p) (Nat.succ x)) (support p).val = Multise …
  refine' congr (congr rfl _) rfl
  -- ⊢ (fun x => coeff (X * p) (Nat.succ x)) = coeff p
  ext a
  -- ⊢ coeff (X * p) (Nat.succ a) = coeff p a
  rw [mul_comm]
  -- ⊢ coeff (p * X) (Nat.succ a) = coeff p a
  simp [coeff_mul_X]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.content_X_mul Polynomial.content_X_mul

@[simp]
theorem content_X_pow {k : ℕ} : content ((X : R[X]) ^ k) = 1 := by
  induction' k with k hi
  -- ⊢ content (X ^ Nat.zero) = 1
  · simp
    -- 🎉 no goals
  rw [pow_succ, content_X_mul, hi]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.content_X_pow Polynomial.content_X_pow

@[simp]
theorem content_X : content (X : R[X]) = 1 := by rw [← mul_one X, content_X_mul, content_one]
                                                 -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.content_X Polynomial.content_X

theorem content_C_mul (r : R) (p : R[X]) : (C r * p).content = normalize r * p.content := by
  by_cases h0 : r = 0; · simp [h0]
  -- ⊢ content (↑C r * p) = ↑normalize r * content p
                         -- 🎉 no goals
  rw [content]; rw [content]; rw [← Finset.gcd_mul_left]
  -- ⊢ Finset.gcd (support (↑C r * p)) (coeff (↑C r * p)) = ↑normalize r * content p
                -- ⊢ Finset.gcd (support (↑C r * p)) (coeff (↑C r * p)) = ↑normalize r * Finset.g …
                              -- ⊢ Finset.gcd (support (↑C r * p)) (coeff (↑C r * p)) = Finset.gcd (support p)  …
  refine' congr (congr rfl _) _ <;> ext <;> simp [h0, mem_support_iff]
  -- ⊢ support (↑C r * p) = support p
                                    -- ⊢ a✝ ∈ support (↑C r * p) ↔ a✝ ∈ support p
                                    -- ⊢ coeff (↑C r * p) x✝ = r * coeff p x✝
                                            -- 🎉 no goals
                                            -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.content_C_mul Polynomial.content_C_mul

@[simp]
theorem content_monomial {r : R} {k : ℕ} : content (monomial k r) = normalize r := by
  rw [← C_mul_X_pow_eq_monomial, content_C_mul, content_X_pow, mul_one]
  -- 🎉 no goals
#align polynomial.content_monomial Polynomial.content_monomial

theorem content_eq_zero_iff {p : R[X]} : content p = 0 ↔ p = 0 := by
  rw [content, Finset.gcd_eq_zero_iff]
  -- ⊢ (∀ (x : ℕ), x ∈ support p → coeff p x = 0) ↔ p = 0
  constructor <;> intro h
  -- ⊢ (∀ (x : ℕ), x ∈ support p → coeff p x = 0) → p = 0
                  -- ⊢ p = 0
                  -- ⊢ ∀ (x : ℕ), x ∈ support p → coeff p x = 0
  · ext n
    -- ⊢ coeff p n = coeff 0 n
    by_cases h0 : n ∈ p.support
    -- ⊢ coeff p n = coeff 0 n
    · rw [h n h0, coeff_zero]
      -- 🎉 no goals
    · rw [mem_support_iff] at h0
      -- ⊢ coeff p n = coeff 0 n
      push_neg at h0
      -- ⊢ coeff p n = coeff 0 n
      simp [h0]
      -- 🎉 no goals
  · intro x
    -- ⊢ x ∈ support p → coeff p x = 0
    simp [h]
    -- 🎉 no goals
#align polynomial.content_eq_zero_iff Polynomial.content_eq_zero_iff

-- Porting note: this reduced with simp so created `normUnit_content` and put simp on it
theorem normalize_content {p : R[X]} : normalize p.content = p.content :=
  Finset.normalize_gcd
#align polynomial.normalize_content Polynomial.normalize_content

@[simp]
theorem normUnit_content {p : R[X]} : normUnit (content p) = 1 := by
  by_cases hp0 : p.content = 0
  -- ⊢ normUnit (content p) = 1
  · simp [hp0]
    -- 🎉 no goals
  · ext
    -- ⊢ ↑(normUnit (content p)) = ↑1
    apply mul_left_cancel₀ hp0
    -- ⊢ content p * ↑(normUnit (content p)) = content p * ↑1
    erw [← normalize_apply, normalize_content, mul_one]
    -- 🎉 no goals

theorem content_eq_gcd_range_of_lt (p : R[X]) (n : ℕ) (h : p.natDegree < n) :
    p.content = (Finset.range n).gcd p.coeff := by
  apply dvd_antisymm_of_normalize_eq normalize_content Finset.normalize_gcd
  -- ⊢ content p ∣ Finset.gcd (Finset.range n) (coeff p)
  · rw [Finset.dvd_gcd_iff]
    -- ⊢ ∀ (b : ℕ), b ∈ Finset.range n → content p ∣ coeff p b
    intro i _
    -- ⊢ content p ∣ coeff p i
    apply content_dvd_coeff _
    -- 🎉 no goals
  · apply Finset.gcd_mono
    -- ⊢ support p ⊆ Finset.range n
    intro i
    -- ⊢ i ∈ support p → i ∈ Finset.range n
    simp only [Nat.lt_succ_iff, mem_support_iff, Ne.def, Finset.mem_range]
    -- ⊢ ¬coeff p i = 0 → i < n
    contrapose!
    -- ⊢ n ≤ i → coeff p i = 0
    intro h1
    -- ⊢ coeff p i = 0
    apply coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le h h1)
    -- 🎉 no goals
#align polynomial.content_eq_gcd_range_of_lt Polynomial.content_eq_gcd_range_of_lt

theorem content_eq_gcd_range_succ (p : R[X]) :
    p.content = (Finset.range p.natDegree.succ).gcd p.coeff :=
  content_eq_gcd_range_of_lt _ _ (Nat.lt_succ_self _)
#align polynomial.content_eq_gcd_range_succ Polynomial.content_eq_gcd_range_succ

theorem content_eq_gcd_leadingCoeff_content_eraseLead (p : R[X]) :
    p.content = GCDMonoid.gcd p.leadingCoeff (eraseLead p).content := by
  by_cases h : p = 0
  -- ⊢ content p = gcd (leadingCoeff p) (content (eraseLead p))
  · simp [h]
    -- 🎉 no goals
  rw [← leadingCoeff_eq_zero, leadingCoeff, ← Ne.def, ← mem_support_iff] at h
  -- ⊢ content p = gcd (leadingCoeff p) (content (eraseLead p))
  rw [content, ← Finset.insert_erase h, Finset.gcd_insert, leadingCoeff, content,
    eraseLead_support]
  refine' congr rfl (Finset.gcd_congr rfl fun i hi => _)
  -- ⊢ coeff p i = coeff (eraseLead p) i
  rw [Finset.mem_erase] at hi
  -- ⊢ coeff p i = coeff (eraseLead p) i
  rw [eraseLead_coeff, if_neg hi.1]
  -- 🎉 no goals
#align polynomial.content_eq_gcd_leading_coeff_content_erase_lead Polynomial.content_eq_gcd_leadingCoeff_content_eraseLead

theorem dvd_content_iff_C_dvd {p : R[X]} {r : R} : r ∣ p.content ↔ C r ∣ p := by
  rw [C_dvd_iff_dvd_coeff]
  -- ⊢ r ∣ content p ↔ ∀ (i : ℕ), r ∣ coeff p i
  constructor
  -- ⊢ r ∣ content p → ∀ (i : ℕ), r ∣ coeff p i
  · intro h i
    -- ⊢ r ∣ coeff p i
    apply h.trans (content_dvd_coeff _)
    -- 🎉 no goals
  · intro h
    -- ⊢ r ∣ content p
    rw [content, Finset.dvd_gcd_iff]
    -- ⊢ ∀ (b : ℕ), b ∈ support p → r ∣ coeff p b
    intro i _
    -- ⊢ r ∣ coeff p i
    apply h i
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.dvd_content_iff_C_dvd Polynomial.dvd_content_iff_C_dvd

theorem C_content_dvd (p : R[X]) : C p.content ∣ p :=
  dvd_content_iff_C_dvd.1 dvd_rfl
set_option linter.uppercaseLean3 false in
#align polynomial.C_content_dvd Polynomial.C_content_dvd

theorem isPrimitive_iff_content_eq_one {p : R[X]} : p.IsPrimitive ↔ p.content = 1 := by
  rw [← normalize_content, normalize_eq_one, IsPrimitive]
  -- ⊢ (∀ (r : R), ↑C r ∣ p → IsUnit r) ↔ IsUnit (content p)
  simp_rw [← dvd_content_iff_C_dvd]
  -- ⊢ (∀ (r : R), r ∣ content p → IsUnit r) ↔ IsUnit (content p)
  exact ⟨fun h => h p.content (dvd_refl p.content), fun h r hdvd => isUnit_of_dvd_unit hdvd h⟩
  -- 🎉 no goals
#align polynomial.is_primitive_iff_content_eq_one Polynomial.isPrimitive_iff_content_eq_one

theorem IsPrimitive.content_eq_one {p : R[X]} (hp : p.IsPrimitive) : p.content = 1 :=
  isPrimitive_iff_content_eq_one.mp hp
#align polynomial.is_primitive.content_eq_one Polynomial.IsPrimitive.content_eq_one

open Classical

section PrimPart

/-- The primitive part of a polynomial `p` is the primitive polynomial gained by dividing `p` by
  `p.content`. If `p = 0`, then `p.primPart = 1`.  -/
noncomputable def primPart (p : R[X]) : R[X] :=
  if p = 0 then 1 else Classical.choose (C_content_dvd p)
#align polynomial.prim_part Polynomial.primPart

theorem eq_C_content_mul_primPart (p : R[X]) : p = C p.content * p.primPart := by
  by_cases h : p = 0; · simp [h]
  -- ⊢ p = ↑C (content p) * primPart p
                        -- 🎉 no goals
  rw [primPart, if_neg h, ← Classical.choose_spec (C_content_dvd p)]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.eq_C_content_mul_prim_part Polynomial.eq_C_content_mul_primPart

@[simp]
theorem primPart_zero : primPart (0 : R[X]) = 1 :=
  if_pos rfl
#align polynomial.prim_part_zero Polynomial.primPart_zero

theorem isPrimitive_primPart (p : R[X]) : p.primPart.IsPrimitive := by
  by_cases h : p = 0; · simp [h]
  -- ⊢ IsPrimitive (primPart p)
                        -- 🎉 no goals
  rw [← content_eq_zero_iff] at h
  -- ⊢ IsPrimitive (primPart p)
  rw [isPrimitive_iff_content_eq_one]
  -- ⊢ content (primPart p) = 1
  apply mul_left_cancel₀ h
  -- ⊢ content p * content (primPart p) = content p * 1
  conv_rhs => rw [p.eq_C_content_mul_primPart, mul_one, content_C_mul, normalize_content]
  -- 🎉 no goals
#align polynomial.is_primitive_prim_part Polynomial.isPrimitive_primPart

theorem content_primPart (p : R[X]) : p.primPart.content = 1 :=
  p.isPrimitive_primPart.content_eq_one
#align polynomial.content_prim_part Polynomial.content_primPart

theorem primPart_ne_zero (p : R[X]) : p.primPart ≠ 0 :=
  p.isPrimitive_primPart.ne_zero
#align polynomial.prim_part_ne_zero Polynomial.primPart_ne_zero

theorem natDegree_primPart (p : R[X]) : p.primPart.natDegree = p.natDegree := by
  by_cases h : C p.content = 0
  -- ⊢ natDegree (primPart p) = natDegree p
  · rw [C_eq_zero, content_eq_zero_iff] at h
    -- ⊢ natDegree (primPart p) = natDegree p
    simp [h]
    -- 🎉 no goals
  conv_rhs =>
    rw [p.eq_C_content_mul_primPart, natDegree_mul h p.primPart_ne_zero, natDegree_C, zero_add]
#align polynomial.nat_degree_prim_part Polynomial.natDegree_primPart

@[simp]
theorem IsPrimitive.primPart_eq {p : R[X]} (hp : p.IsPrimitive) : p.primPart = p := by
  rw [← one_mul p.primPart, ← C_1, ← hp.content_eq_one, ← p.eq_C_content_mul_primPart]
  -- 🎉 no goals
#align polynomial.is_primitive.prim_part_eq Polynomial.IsPrimitive.primPart_eq

theorem isUnit_primPart_C (r : R) : IsUnit (C r).primPart := by
  by_cases h0 : r = 0
  -- ⊢ IsUnit (primPart (↑C r))
  · simp [h0]
    -- 🎉 no goals
  unfold IsUnit
  -- ⊢ ∃ u, ↑u = primPart (↑C r)
  refine'
    ⟨⟨C ↑(normUnit r)⁻¹, C ↑(normUnit r), by rw [← RingHom.map_mul, Units.inv_mul, C_1], by
        rw [← RingHom.map_mul, Units.mul_inv, C_1]⟩,
      _⟩
  rw [← normalize_eq_zero, ← C_eq_zero] at h0
  -- ⊢ ↑{ val := ↑C ↑(normUnit r)⁻¹, inv := ↑C ↑(normUnit r), val_inv := (_ : ↑C ↑( …
  apply mul_left_cancel₀ h0
  -- ⊢ ↑C (↑normalize r) * ↑{ val := ↑C ↑(normUnit r)⁻¹, inv := ↑C ↑(normUnit r), v …
  conv_rhs => rw [← content_C, ← (C r).eq_C_content_mul_primPart]
  -- ⊢ ↑C (↑normalize r) * ↑{ val := ↑C ↑(normUnit r)⁻¹, inv := ↑C ↑(normUnit r), v …
  simp only [Units.val_mk, normalize_apply, RingHom.map_mul]
  -- ⊢ ↑C r * ↑C ↑(normUnit r) * ↑C ↑(normUnit r)⁻¹ = ↑C r
  rw [mul_assoc, ← RingHom.map_mul, Units.mul_inv, C_1, mul_one]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.is_unit_prim_part_C Polynomial.isUnit_primPart_C

theorem primPart_dvd (p : R[X]) : p.primPart ∣ p :=
  Dvd.intro_left (C p.content) p.eq_C_content_mul_primPart.symm
#align polynomial.prim_part_dvd Polynomial.primPart_dvd

theorem aeval_primPart_eq_zero {S : Type*} [Ring S] [IsDomain S] [Algebra R S]
    [NoZeroSMulDivisors R S] {p : R[X]} {s : S} (hpzero : p ≠ 0) (hp : aeval s p = 0) :
    aeval s p.primPart = 0 := by
  rw [eq_C_content_mul_primPart p, map_mul, aeval_C] at hp
  -- ⊢ ↑(aeval s) (primPart p) = 0
  have hcont : p.content ≠ 0 := fun h => hpzero (content_eq_zero_iff.1 h)
  -- ⊢ ↑(aeval s) (primPart p) = 0
  replace hcont := Function.Injective.ne (NoZeroSMulDivisors.algebraMap_injective R S) hcont
  -- ⊢ ↑(aeval s) (primPart p) = 0
  rw [map_zero] at hcont
  -- ⊢ ↑(aeval s) (primPart p) = 0
  exact eq_zero_of_ne_zero_of_mul_left_eq_zero hcont hp
  -- 🎉 no goals
#align polynomial.aeval_prim_part_eq_zero Polynomial.aeval_primPart_eq_zero

theorem eval₂_primPart_eq_zero {S : Type*} [CommRing S] [IsDomain S] {f : R →+* S}
    (hinj : Function.Injective f) {p : R[X]} {s : S} (hpzero : p ≠ 0) (hp : eval₂ f s p = 0) :
    eval₂ f s p.primPart = 0 := by
  rw [eq_C_content_mul_primPart p, eval₂_mul, eval₂_C] at hp
  -- ⊢ eval₂ f s (primPart p) = 0
  have hcont : p.content ≠ 0 := fun h => hpzero (content_eq_zero_iff.1 h)
  -- ⊢ eval₂ f s (primPart p) = 0
  replace hcont := Function.Injective.ne hinj hcont
  -- ⊢ eval₂ f s (primPart p) = 0
  rw [map_zero] at hcont
  -- ⊢ eval₂ f s (primPart p) = 0
  exact eq_zero_of_ne_zero_of_mul_left_eq_zero hcont hp
  -- 🎉 no goals
#align polynomial.eval₂_prim_part_eq_zero Polynomial.eval₂_primPart_eq_zero

end PrimPart

theorem gcd_content_eq_of_dvd_sub {a : R} {p q : R[X]} (h : C a ∣ p - q) :
    GCDMonoid.gcd a p.content = GCDMonoid.gcd a q.content := by
  rw [content_eq_gcd_range_of_lt p (max p.natDegree q.natDegree).succ
      (lt_of_le_of_lt (le_max_left _ _) (Nat.lt_succ_self _))]
  rw [content_eq_gcd_range_of_lt q (max p.natDegree q.natDegree).succ
      (lt_of_le_of_lt (le_max_right _ _) (Nat.lt_succ_self _))]
  apply Finset.gcd_eq_of_dvd_sub
  -- ⊢ ∀ (x : ℕ), x ∈ Finset.range (Nat.succ (max (natDegree p) (natDegree q))) → a …
  intro x _
  -- ⊢ a ∣ coeff p x - coeff q x
  cases' h with w hw
  -- ⊢ a ∣ coeff p x - coeff q x
  use w.coeff x
  -- ⊢ coeff p x - coeff q x = a * coeff w x
  rw [← coeff_sub, hw, coeff_C_mul]
  -- 🎉 no goals
#align polynomial.gcd_content_eq_of_dvd_sub Polynomial.gcd_content_eq_of_dvd_sub

theorem content_mul_aux {p q : R[X]} :
    GCDMonoid.gcd (p * q).eraseLead.content p.leadingCoeff =
      GCDMonoid.gcd (p.eraseLead * q).content p.leadingCoeff := by
  rw [gcd_comm (content _) _, gcd_comm (content _) _]
  -- ⊢ gcd (leadingCoeff p) (content (eraseLead (p * q))) = gcd (leadingCoeff p) (c …
  apply gcd_content_eq_of_dvd_sub
  -- ⊢ ↑C (leadingCoeff p) ∣ eraseLead (p * q) - eraseLead p * q
  rw [← self_sub_C_mul_X_pow, ← self_sub_C_mul_X_pow, sub_mul, sub_sub, add_comm, sub_add,
    sub_sub_cancel, leadingCoeff_mul, RingHom.map_mul, mul_assoc, mul_assoc]
  apply dvd_sub (Dvd.intro _ rfl) (Dvd.intro _ rfl)
  -- 🎉 no goals
#align polynomial.content_mul_aux Polynomial.content_mul_aux

@[simp]
theorem content_mul {p q : R[X]} : (p * q).content = p.content * q.content := by
  classical
    suffices h :
      ∀ (n : ℕ) (p q : R[X]), (p * q).degree < n → (p * q).content = p.content * q.content
    · apply h
      apply lt_of_le_of_lt degree_le_natDegree (WithBot.coe_lt_coe.2 (Nat.lt_succ_self _))
    intro n
    induction' n with n ih
    · intro p q hpq
      dsimp at hpq
      rw [Nat.cast_withBot, WithBot.coe_zero,
        Nat.WithBot.lt_zero_iff, degree_eq_bot, mul_eq_zero] at hpq
      rcases hpq with (rfl | rfl) <;> simp
    intro p q hpq
    by_cases p0 : p = 0
    · simp [p0]
    by_cases q0 : q = 0
    · simp [q0]
    rw [degree_eq_natDegree (mul_ne_zero p0 q0), Nat.cast_withBot,
      Nat.cast_withBot, WithBot.coe_lt_coe, Nat.lt_succ_iff_lt_or_eq, ←
      WithBot.coe_lt_coe, ←Nat.cast_withBot, ← degree_eq_natDegree (mul_ne_zero p0 q0),
      natDegree_mul p0 q0] at hpq
    rcases hpq with (hlt | heq)
    · apply ih _ _ hlt
    rw [← p.natDegree_primPart, ← q.natDegree_primPart, ← WithBot.coe_eq_coe,
      WithBot.coe_add, ← Nat.cast_withBot, ←degree_eq_natDegree p.primPart_ne_zero,
      ← Nat.cast_withBot, ← degree_eq_natDegree q.primPart_ne_zero] at heq
    rw [p.eq_C_content_mul_primPart, q.eq_C_content_mul_primPart]
    suffices h : (q.primPart * p.primPart).content = 1
    · rw [mul_assoc, content_C_mul, content_C_mul, mul_comm p.primPart, mul_assoc, content_C_mul,
        content_C_mul, h, mul_one, content_primPart, content_primPart, mul_one, mul_one]
    rw [← normalize_content, normalize_eq_one, isUnit_iff_dvd_one,
      content_eq_gcd_leadingCoeff_content_eraseLead, leadingCoeff_mul, gcd_comm]
    apply (gcd_mul_dvd_mul_gcd _ _ _).trans
    rw [content_mul_aux, ih, content_primPart, mul_one, gcd_comm, ←
      content_eq_gcd_leadingCoeff_content_eraseLead, content_primPart, one_mul,
      mul_comm q.primPart, content_mul_aux, ih, content_primPart, mul_one, gcd_comm, ←
      content_eq_gcd_leadingCoeff_content_eraseLead, content_primPart]
    · rw [Nat.cast_withBot, ← heq, degree_mul, WithBot.add_lt_add_iff_right]
      · apply degree_erase_lt p.primPart_ne_zero
      · rw [Ne.def, degree_eq_bot]
        apply q.primPart_ne_zero
    · rw [mul_comm, Nat.cast_withBot, ← heq, degree_mul, WithBot.add_lt_add_iff_left]
      · apply degree_erase_lt q.primPart_ne_zero
      · rw [Ne.def, degree_eq_bot]
        apply p.primPart_ne_zero
#align polynomial.content_mul Polynomial.content_mul

theorem IsPrimitive.mul {p q : R[X]} (hp : p.IsPrimitive) (hq : q.IsPrimitive) :
    (p * q).IsPrimitive := by
  rw [isPrimitive_iff_content_eq_one, content_mul, hp.content_eq_one, hq.content_eq_one, mul_one]
  -- 🎉 no goals
#align polynomial.is_primitive.mul Polynomial.IsPrimitive.mul

@[simp]
theorem primPart_mul {p q : R[X]} (h0 : p * q ≠ 0) :
    (p * q).primPart = p.primPart * q.primPart := by
  rw [Ne.def, ← content_eq_zero_iff, ← C_eq_zero] at h0
  -- ⊢ primPart (p * q) = primPart p * primPart q
  apply mul_left_cancel₀ h0
  -- ⊢ ↑C (content (p * q)) * primPart (p * q) = ↑C (content (p * q)) * (primPart p …
  conv_lhs =>
    rw [← (p * q).eq_C_content_mul_primPart, p.eq_C_content_mul_primPart,
      q.eq_C_content_mul_primPart]
  rw [content_mul, RingHom.map_mul]
  -- ⊢ ↑C (content p) * primPart p * (↑C (content q) * primPart q) = ↑C (content p) …
  ring
  -- 🎉 no goals
#align polynomial.prim_part_mul Polynomial.primPart_mul

theorem IsPrimitive.dvd_primPart_iff_dvd {p q : R[X]} (hp : p.IsPrimitive) (hq : q ≠ 0) :
    p ∣ q.primPart ↔ p ∣ q := by
  refine' ⟨fun h => h.trans (Dvd.intro_left _ q.eq_C_content_mul_primPart.symm), fun h => _⟩
  -- ⊢ p ∣ primPart q
  rcases h with ⟨r, rfl⟩
  -- ⊢ p ∣ primPart (p * r)
  apply Dvd.intro _
  -- ⊢ p * ?m.658553 = primPart (p * r)
  rw [primPart_mul hq, hp.primPart_eq]
  -- 🎉 no goals
#align polynomial.is_primitive.dvd_prim_part_iff_dvd Polynomial.IsPrimitive.dvd_primPart_iff_dvd

theorem exists_primitive_lcm_of_isPrimitive {p q : R[X]} (hp : p.IsPrimitive) (hq : q.IsPrimitive) :
    ∃ r : R[X], r.IsPrimitive ∧ ∀ s : R[X], p ∣ s ∧ q ∣ s ↔ r ∣ s := by
  classical
    have h : ∃ (n : ℕ) (r : R[X]), r.natDegree = n ∧ r.IsPrimitive ∧ p ∣ r ∧ q ∣ r :=
      ⟨(p * q).natDegree, p * q, rfl, hp.mul hq, dvd_mul_right _ _, dvd_mul_left _ _⟩
    rcases Nat.find_spec h with ⟨r, rdeg, rprim, pr, qr⟩
    refine' ⟨r, rprim, fun s => ⟨_, fun rs => ⟨pr.trans rs, qr.trans rs⟩⟩⟩
    suffices hs : ∀ (n : ℕ) (s : R[X]), s.natDegree = n → p ∣ s ∧ q ∣ s → r ∣ s
    · apply hs s.natDegree s rfl
    clear s
    by_contra' con
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
    refine'
      ⟨_, rfl, ⟨dvd_cancelLeads_of_dvd_of_dvd pr ps, dvd_cancelLeads_of_dvd_of_dvd qr qs⟩,
        fun rcs => rs _⟩
    rw [← rprim.dvd_primPart_iff_dvd s0]
    rw [cancelLeads, tsub_eq_zero_iff_le.mpr hs, pow_zero, mul_one] at rcs
    have h :=
      dvd_add rcs (Dvd.intro_left (C (leadingCoeff s) * X ^ (natDegree s - natDegree r)) rfl)
    have hC0 := rprim.ne_zero
    rw [Ne.def, ← leadingCoeff_eq_zero, ← C_eq_zero] at hC0
    rw [sub_add_cancel, ← rprim.dvd_primPart_iff_dvd (mul_ne_zero hC0 s0)] at h
    rcases isUnit_primPart_C r.leadingCoeff with ⟨u, hu⟩
    apply h.trans (Associated.symm ⟨u, _⟩).dvd
    rw [primPart_mul (mul_ne_zero hC0 s0), hu, mul_comm]
#align polynomial.exists_primitive_lcm_of_is_primitive Polynomial.exists_primitive_lcm_of_isPrimitive

theorem dvd_iff_content_dvd_content_and_primPart_dvd_primPart {p q : R[X]} (hq : q ≠ 0) :
    p ∣ q ↔ p.content ∣ q.content ∧ p.primPart ∣ q.primPart := by
  constructor <;> intro h
  -- ⊢ p ∣ q → content p ∣ content q ∧ primPart p ∣ primPart q
                  -- ⊢ content p ∣ content q ∧ primPart p ∣ primPart q
                  -- ⊢ p ∣ q
  · rcases h with ⟨r, rfl⟩
    -- ⊢ content p ∣ content (p * r) ∧ primPart p ∣ primPart (p * r)
    rw [content_mul, p.isPrimitive_primPart.dvd_primPart_iff_dvd hq]
    -- ⊢ content p ∣ content p * content r ∧ primPart p ∣ p * r
    exact ⟨Dvd.intro _ rfl, p.primPart_dvd.trans (Dvd.intro _ rfl)⟩
    -- 🎉 no goals
  · rw [p.eq_C_content_mul_primPart, q.eq_C_content_mul_primPart]
    -- ⊢ ↑C (content p) * primPart p ∣ ↑C (content q) * primPart q
    exact mul_dvd_mul (RingHom.map_dvd C h.1) h.2
    -- 🎉 no goals
#align polynomial.dvd_iff_content_dvd_content_and_prim_part_dvd_prim_part Polynomial.dvd_iff_content_dvd_content_and_primPart_dvd_primPart

noncomputable instance (priority := 100) normalizedGcdMonoid : NormalizedGCDMonoid R[X] :=
  normalizedGCDMonoidOfExistsLCM fun p q => by
    rcases exists_primitive_lcm_of_isPrimitive p.isPrimitive_primPart
        q.isPrimitive_primPart with
      ⟨r, rprim, hr⟩
    refine' ⟨C (lcm p.content q.content) * r, fun s => _⟩
    -- ⊢ p ∣ s ∧ q ∣ s ↔ ↑C (lcm (content p) (content q)) * r ∣ s
    by_cases hs : s = 0
    -- ⊢ p ∣ s ∧ q ∣ s ↔ ↑C (lcm (content p) (content q)) * r ∣ s
    · simp [hs]
      -- 🎉 no goals
    by_cases hpq : C (lcm p.content q.content) = 0
    -- ⊢ p ∣ s ∧ q ∣ s ↔ ↑C (lcm (content p) (content q)) * r ∣ s
    · rw [C_eq_zero, lcm_eq_zero_iff, content_eq_zero_iff, content_eq_zero_iff] at hpq
      -- ⊢ p ∣ s ∧ q ∣ s ↔ ↑C (lcm (content p) (content q)) * r ∣ s
      rcases hpq with (hpq | hpq) <;> simp [hpq, hs]
      -- ⊢ p ∣ s ∧ q ∣ s ↔ ↑C (lcm (content p) (content q)) * r ∣ s
                                      -- 🎉 no goals
                                      -- 🎉 no goals
    iterate 3 rw [dvd_iff_content_dvd_content_and_primPart_dvd_primPart hs]
    -- ⊢ (content p ∣ content s ∧ primPart p ∣ primPart s) ∧ content q ∣ content s ∧  …
    rw [content_mul, rprim.content_eq_one, mul_one, content_C, normalize_lcm, lcm_dvd_iff,
      primPart_mul (mul_ne_zero hpq rprim.ne_zero), rprim.primPart_eq,
      IsUnit.mul_left_dvd _ _ _ (isUnit_primPart_C (lcm p.content q.content)), ← hr s.primPart]
    tauto
    -- 🎉 no goals
#align polynomial.normalized_gcd_monoid Polynomial.normalizedGcdMonoid

theorem degree_gcd_le_left {p : R[X]} (hp : p ≠ 0) (q) : (gcd p q).degree ≤ p.degree := by
  have := natDegree_le_iff_degree_le.mp (natDegree_le_of_dvd (gcd_dvd_left p q) hp)
  -- ⊢ degree (gcd p q) ≤ degree p
  rwa [degree_eq_natDegree hp]
  -- 🎉 no goals
#align polynomial.degree_gcd_le_left Polynomial.degree_gcd_le_left

theorem degree_gcd_le_right (p) {q : R[X]} (hq : q ≠ 0) : (gcd p q).degree ≤ q.degree := by
  rw [gcd_comm]
  -- ⊢ degree (gcd q p) ≤ degree q
  exact degree_gcd_le_left hq p
  -- 🎉 no goals
#align polynomial.degree_gcd_le_right Polynomial.degree_gcd_le_right

end NormalizedGCDMonoid

end Polynomial
