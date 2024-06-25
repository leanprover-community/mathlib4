/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker
-/
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.EuclideanDomain

#align_import data.polynomial.field_division from "leanprover-community/mathlib"@"bbeb185db4ccee8ed07dc48449414ebfa39cb821"

/-!
# Theory of univariate polynomials

This file starts looking like the ring theory of $R[X]$

-/


noncomputable section

open Polynomial

namespace Polynomial

universe u v w y z

variable {R : Type u} {S : Type v} {k : Type y} {A : Type z} {a b : R} {n : ℕ}

section CommRing

variable [CommRing R]

theorem rootMultiplicity_sub_one_le_derivative_rootMultiplicity_of_ne_zero
    (p : R[X]) (t : R) (hnezero : derivative p ≠ 0) :
    p.rootMultiplicity t - 1 ≤ p.derivative.rootMultiplicity t :=
  (le_rootMultiplicity_iff hnezero).2 <|
    pow_sub_one_dvd_derivative_of_pow_dvd (p.pow_rootMultiplicity_dvd t)

theorem derivative_rootMultiplicity_of_root_of_mem_nonZeroDivisors
    {p : R[X]} {t : R} (hpt : Polynomial.IsRoot p t)
    (hnzd : (p.rootMultiplicity t : R) ∈ nonZeroDivisors R) :
    (derivative p).rootMultiplicity t = p.rootMultiplicity t - 1 := by
  by_cases h : p = 0
  · simp only [h, map_zero, rootMultiplicity_zero]
  obtain ⟨g, hp, hndvd⟩ := p.exists_eq_pow_rootMultiplicity_mul_and_not_dvd h t
  set m := p.rootMultiplicity t
  have hm : m - 1 + 1 = m := Nat.sub_add_cancel <| (rootMultiplicity_pos h).2 hpt
  have hndvd : ¬(X - C t) ^ m ∣ derivative p := by
    rw [hp, derivative_mul, dvd_add_left (dvd_mul_right _ _),
      derivative_X_sub_C_pow, ← hm, pow_succ, hm, mul_comm (C _), mul_assoc,
      dvd_cancel_left_mem_nonZeroDivisors (monic_X_sub_C t |>.pow _ |>.mem_nonZeroDivisors)]
    rw [dvd_iff_isRoot, IsRoot] at hndvd ⊢
    rwa [eval_mul, eval_C, mul_left_mem_nonZeroDivisors_eq_zero_iff hnzd]
  have hnezero : derivative p ≠ 0 := fun h ↦ hndvd (by rw [h]; exact dvd_zero _)
  exact le_antisymm (by rwa [rootMultiplicity_le_iff hnezero, hm])
    (rootMultiplicity_sub_one_le_derivative_rootMultiplicity_of_ne_zero _ t hnezero)

theorem isRoot_iterate_derivative_of_lt_rootMultiplicity {p : R[X]} {t : R} {n : ℕ}
    (hn : n < p.rootMultiplicity t) : (derivative^[n] p).IsRoot t :=
  dvd_iff_isRoot.mp <| (dvd_pow_self _ <| Nat.sub_ne_zero_of_lt hn).trans
    (pow_sub_dvd_iterate_derivative_of_pow_dvd _ <| p.pow_rootMultiplicity_dvd t)

open Finset in
theorem eval_iterate_derivative_rootMultiplicity {p : R[X]} {t : R} :
    (derivative^[p.rootMultiplicity t] p).eval t =
      (p.rootMultiplicity t).factorial • (p /ₘ (X - C t) ^ p.rootMultiplicity t).eval t := by
  set m := p.rootMultiplicity t with hm
  conv_lhs => rw [← p.pow_mul_divByMonic_rootMultiplicity_eq t, ← hm]
  rw [iterate_derivative_mul, eval_finset_sum, sum_eq_single_of_mem _ (mem_range.mpr m.succ_pos)]
  · rw [m.choose_zero_right, one_smul, eval_mul, m.sub_zero, iterate_derivative_X_sub_pow_self,
      eval_natCast, nsmul_eq_mul]; rfl
  · intro b hb hb0
    rw [iterate_derivative_X_sub_pow, eval_smul, eval_mul, eval_smul, eval_pow,
      Nat.sub_sub_self (mem_range_succ_iff.mp hb), eval_sub, eval_X, eval_C, sub_self,
      zero_pow hb0, smul_zero, zero_mul, smul_zero]

theorem lt_rootMultiplicity_of_isRoot_iterate_derivative_of_mem_nonZeroDivisors
    {p : R[X]} {t : R} {n : ℕ} (h : p ≠ 0)
    (hroot : ∀ m ≤ n, (derivative^[m] p).IsRoot t)
    (hnzd : (n.factorial : R) ∈ nonZeroDivisors R) :
    n < p.rootMultiplicity t := by
  by_contra! h'
  replace hroot := hroot _ h'
  simp only [IsRoot, eval_iterate_derivative_rootMultiplicity] at hroot
  obtain ⟨q, hq⟩ := Nat.cast_dvd_cast (α := R) <| Nat.factorial_dvd_factorial h'
  rw [hq, mul_mem_nonZeroDivisors] at hnzd
  rw [nsmul_eq_mul, mul_left_mem_nonZeroDivisors_eq_zero_iff hnzd.1] at hroot
  exact eval_divByMonic_pow_rootMultiplicity_ne_zero t h hroot

theorem lt_rootMultiplicity_of_isRoot_iterate_derivative_of_mem_nonZeroDivisors'
    {p : R[X]} {t : R} {n : ℕ} (h : p ≠ 0)
    (hroot : ∀ m ≤ n, (derivative^[m] p).IsRoot t)
    (hnzd : ∀ m ≤ n, m ≠ 0 → (m : R) ∈ nonZeroDivisors R) :
    n < p.rootMultiplicity t := by
  apply lt_rootMultiplicity_of_isRoot_iterate_derivative_of_mem_nonZeroDivisors h hroot
  clear hroot
  induction' n with n ih
  · simp only [Nat.zero_eq, Nat.factorial_zero, Nat.cast_one]
    exact Submonoid.one_mem _
  · rw [Nat.factorial_succ, Nat.cast_mul, mul_mem_nonZeroDivisors]
    exact ⟨hnzd _ le_rfl n.succ_ne_zero, ih fun m h ↦ hnzd m (h.trans n.le_succ)⟩

theorem lt_rootMultiplicity_iff_isRoot_iterate_derivative_of_mem_nonZeroDivisors
    {p : R[X]} {t : R} {n : ℕ} (h : p ≠ 0)
    (hnzd : (n.factorial : R) ∈ nonZeroDivisors R) :
    n < p.rootMultiplicity t ↔ ∀ m ≤ n, (derivative^[m] p).IsRoot t :=
  ⟨fun hn _ hm ↦ isRoot_iterate_derivative_of_lt_rootMultiplicity <| hm.trans_lt hn,
    fun hr ↦ lt_rootMultiplicity_of_isRoot_iterate_derivative_of_mem_nonZeroDivisors h hr hnzd⟩

theorem lt_rootMultiplicity_iff_isRoot_iterate_derivative_of_mem_nonZeroDivisors'
    {p : R[X]} {t : R} {n : ℕ} (h : p ≠ 0)
    (hnzd : ∀ m ≤ n, m ≠ 0 → (m : R) ∈ nonZeroDivisors R) :
    n < p.rootMultiplicity t ↔ ∀ m ≤ n, (derivative^[m] p).IsRoot t :=
  ⟨fun hn _ hm ↦ isRoot_iterate_derivative_of_lt_rootMultiplicity <| Nat.lt_of_le_of_lt hm hn,
    fun hr ↦ lt_rootMultiplicity_of_isRoot_iterate_derivative_of_mem_nonZeroDivisors' h hr hnzd⟩

theorem one_lt_rootMultiplicity_iff_isRoot_iterate_derivative
    {p : R[X]} {t : R} (h : p ≠ 0) :
    1 < p.rootMultiplicity t ↔ ∀ m ≤ 1, (derivative^[m] p).IsRoot t :=
  lt_rootMultiplicity_iff_isRoot_iterate_derivative_of_mem_nonZeroDivisors h
    (by rw [Nat.factorial_one, Nat.cast_one]; exact Submonoid.one_mem _)

theorem one_lt_rootMultiplicity_iff_isRoot
    {p : R[X]} {t : R} (h : p ≠ 0) :
    1 < p.rootMultiplicity t ↔ p.IsRoot t ∧ (derivative p).IsRoot t := by
  rw [one_lt_rootMultiplicity_iff_isRoot_iterate_derivative h]
  refine ⟨fun h ↦ ⟨h 0 (by norm_num), h 1 (by norm_num)⟩, fun ⟨h0, h1⟩ m hm ↦ ?_⟩
  obtain (_|_|m) := m
  exacts [h0, h1, by omega]

end CommRing

section IsDomain

variable [CommRing R] [IsDomain R]

theorem one_lt_rootMultiplicity_iff_isRoot_gcd
    [GCDMonoid R[X]] {p : R[X]} {t : R} (h : p ≠ 0) :
    1 < p.rootMultiplicity t ↔ (gcd p (derivative p)).IsRoot t := by
  simp_rw [one_lt_rootMultiplicity_iff_isRoot h, ← dvd_iff_isRoot, dvd_gcd_iff]

theorem derivative_rootMultiplicity_of_root [CharZero R] {p : R[X]} {t : R} (hpt : p.IsRoot t) :
    p.derivative.rootMultiplicity t = p.rootMultiplicity t - 1 := by
  by_cases h : p = 0
  · rw [h, map_zero, rootMultiplicity_zero]
  exact derivative_rootMultiplicity_of_root_of_mem_nonZeroDivisors hpt <|
    mem_nonZeroDivisors_of_ne_zero <| Nat.cast_ne_zero.2 ((rootMultiplicity_pos h).2 hpt).ne'
#align polynomial.derivative_root_multiplicity_of_root Polynomial.derivative_rootMultiplicity_of_root

theorem rootMultiplicity_sub_one_le_derivative_rootMultiplicity [CharZero R] (p : R[X]) (t : R) :
    p.rootMultiplicity t - 1 ≤ p.derivative.rootMultiplicity t := by
  by_cases h : p.IsRoot t
  · exact (derivative_rootMultiplicity_of_root h).symm.le
  · rw [rootMultiplicity_eq_zero h, zero_tsub]
    exact zero_le _
#align polynomial.root_multiplicity_sub_one_le_derivative_root_multiplicity Polynomial.rootMultiplicity_sub_one_le_derivative_rootMultiplicity

theorem lt_rootMultiplicity_of_isRoot_iterate_derivative
    [CharZero R] {p : R[X]} {t : R} {n : ℕ} (h : p ≠ 0)
    (hroot : ∀ m ≤ n, (derivative^[m] p).IsRoot t) :
    n < p.rootMultiplicity t :=
  lt_rootMultiplicity_of_isRoot_iterate_derivative_of_mem_nonZeroDivisors h hroot <|
    mem_nonZeroDivisors_of_ne_zero <| Nat.cast_ne_zero.2 <| Nat.factorial_ne_zero n

theorem lt_rootMultiplicity_iff_isRoot_iterate_derivative
    [CharZero R] {p : R[X]} {t : R} {n : ℕ} (h : p ≠ 0) :
    n < p.rootMultiplicity t ↔ ∀ m ≤ n, (derivative^[m] p).IsRoot t :=
  ⟨fun hn _ hm ↦ isRoot_iterate_derivative_of_lt_rootMultiplicity <| Nat.lt_of_le_of_lt hm hn,
    fun hr ↦ lt_rootMultiplicity_of_isRoot_iterate_derivative h hr⟩

section NormalizationMonoid

variable [NormalizationMonoid R]

instance instNormalizationMonoid : NormalizationMonoid R[X] where
  normUnit p :=
    ⟨C ↑(normUnit p.leadingCoeff), C ↑(normUnit p.leadingCoeff)⁻¹, by
      rw [← RingHom.map_mul, Units.mul_inv, C_1], by rw [← RingHom.map_mul, Units.inv_mul, C_1]⟩
  normUnit_zero := Units.ext (by simp)
  normUnit_mul hp0 hq0 :=
    Units.ext
      (by
        dsimp
        rw [Ne, ← leadingCoeff_eq_zero] at *
        rw [leadingCoeff_mul, normUnit_mul hp0 hq0, Units.val_mul, C_mul])
  normUnit_coe_units u :=
    Units.ext
      (by
        dsimp
        rw [← mul_one u⁻¹, Units.val_mul, Units.eq_inv_mul_iff_mul_eq]
        rcases Polynomial.isUnit_iff.1 ⟨u, rfl⟩ with ⟨_, ⟨w, rfl⟩, h2⟩
        rw [← h2, leadingCoeff_C, normUnit_coe_units, ← C_mul, Units.mul_inv, C_1]
        rfl)

@[simp]
theorem coe_normUnit {p : R[X]} : (normUnit p : R[X]) = C ↑(normUnit p.leadingCoeff) := by
  simp [normUnit]
#align polynomial.coe_norm_unit Polynomial.coe_normUnit

theorem leadingCoeff_normalize (p : R[X]) :
    leadingCoeff (normalize p) = normalize (leadingCoeff p) := by simp
#align polynomial.leading_coeff_normalize Polynomial.leadingCoeff_normalize

theorem Monic.normalize_eq_self {p : R[X]} (hp : p.Monic) : normalize p = p := by
  simp only [Polynomial.coe_normUnit, normalize_apply, hp.leadingCoeff, normUnit_one,
    Units.val_one, Polynomial.C.map_one, mul_one]
#align polynomial.monic.normalize_eq_self Polynomial.Monic.normalize_eq_self

theorem roots_normalize {p : R[X]} : (normalize p).roots = p.roots := by
  rw [normalize_apply, mul_comm, coe_normUnit, roots_C_mul _ (normUnit (leadingCoeff p)).ne_zero]
#align polynomial.roots_normalize Polynomial.roots_normalize

theorem normUnit_X : normUnit (X : Polynomial R) = 1 := by
  have := coe_normUnit (R := R) (p := X)
  rwa [leadingCoeff_X, normUnit_one, Units.val_one, map_one, Units.val_eq_one] at this

theorem X_eq_normalize : (X : Polynomial R) = normalize X := by
  simp only [normalize_apply, normUnit_X, Units.val_one, mul_one]

end NormalizationMonoid

end IsDomain

section DivisionRing

variable [DivisionRing R] {p q : R[X]}

theorem degree_pos_of_ne_zero_of_nonunit (hp0 : p ≠ 0) (hp : ¬IsUnit p) : 0 < degree p :=
  lt_of_not_ge fun h => by
    rw [eq_C_of_degree_le_zero h] at hp0 hp
    exact hp (IsUnit.map C (IsUnit.mk0 (coeff p 0) (mt C_inj.2 (by simpa using hp0))))
#align polynomial.degree_pos_of_ne_zero_of_nonunit Polynomial.degree_pos_of_ne_zero_of_nonunit

@[simp]
theorem map_eq_zero [Semiring S] [Nontrivial S] (f : R →+* S) : p.map f = 0 ↔ p = 0 := by
  simp only [Polynomial.ext_iff]
  congr!
  simp [map_eq_zero, coeff_map, coeff_zero]
#align polynomial.map_eq_zero Polynomial.map_eq_zero

theorem map_ne_zero [Semiring S] [Nontrivial S] {f : R →+* S} (hp : p ≠ 0) : p.map f ≠ 0 :=
  mt (map_eq_zero f).1 hp
#align polynomial.map_ne_zero Polynomial.map_ne_zero

@[simp]
theorem degree_map [Semiring S] [Nontrivial S] (p : R[X]) (f : R →+* S) :
    degree (p.map f) = degree p :=
  p.degree_map_eq_of_injective f.injective
#align polynomial.degree_map Polynomial.degree_map

@[simp]
theorem natDegree_map [Semiring S] [Nontrivial S] (f : R →+* S) :
    natDegree (p.map f) = natDegree p :=
  natDegree_eq_of_degree_eq (degree_map _ f)
#align polynomial.nat_degree_map Polynomial.natDegree_map

@[simp]
theorem leadingCoeff_map [Semiring S] [Nontrivial S] (f : R →+* S) :
    leadingCoeff (p.map f) = f (leadingCoeff p) := by
  simp only [← coeff_natDegree, coeff_map f, natDegree_map]
#align polynomial.leading_coeff_map Polynomial.leadingCoeff_map

theorem monic_map_iff [Semiring S] [Nontrivial S] {f : R →+* S} {p : R[X]} :
    (p.map f).Monic ↔ p.Monic := by
  rw [Monic, leadingCoeff_map, ← f.map_one, Function.Injective.eq_iff f.injective, Monic]
#align polynomial.monic_map_iff Polynomial.monic_map_iff

end DivisionRing

section Field

variable [Field R] {p q : R[X]}

theorem isUnit_iff_degree_eq_zero : IsUnit p ↔ degree p = 0 :=
  ⟨degree_eq_zero_of_isUnit, fun h =>
    have : degree p ≤ 0 := by simp [*, le_refl]
    have hc : coeff p 0 ≠ 0 := fun hc => by
      rw [eq_C_of_degree_le_zero this, hc] at h; simp only [map_zero] at h; contradiction
    isUnit_iff_dvd_one.2
      ⟨C (coeff p 0)⁻¹, by
        conv in p => rw [eq_C_of_degree_le_zero this]
        rw [← C_mul, _root_.mul_inv_cancel hc, C_1]⟩⟩
#align polynomial.is_unit_iff_degree_eq_zero Polynomial.isUnit_iff_degree_eq_zero

/-- Division of polynomials. See `Polynomial.divByMonic` for more details. -/
def div (p q : R[X]) :=
  C (leadingCoeff q)⁻¹ * (p /ₘ (q * C (leadingCoeff q)⁻¹))
#align polynomial.div Polynomial.div

/-- Remainder of polynomial division. See `Polynomial.modByMonic` for more details. -/
def mod (p q : R[X]) :=
  p %ₘ (q * C (leadingCoeff q)⁻¹)
#align polynomial.mod Polynomial.mod

private theorem quotient_mul_add_remainder_eq_aux (p q : R[X]) : q * div p q + mod p q = p := by
  by_cases h : q = 0
  · simp only [h, zero_mul, mod, modByMonic_zero, zero_add]
  · conv =>
      rhs
      rw [← modByMonic_add_div p (monic_mul_leadingCoeff_inv h)]
    rw [div, mod, add_comm, mul_assoc]

private theorem remainder_lt_aux (p : R[X]) (hq : q ≠ 0) : degree (mod p q) < degree q := by
  rw [← degree_mul_leadingCoeff_inv q hq]
  exact degree_modByMonic_lt p (monic_mul_leadingCoeff_inv hq)

instance : Div R[X] :=
  ⟨div⟩

instance : Mod R[X] :=
  ⟨mod⟩

theorem div_def : p / q = C (leadingCoeff q)⁻¹ * (p /ₘ (q * C (leadingCoeff q)⁻¹)) :=
  rfl
#align polynomial.div_def Polynomial.div_def

theorem mod_def : p % q = p %ₘ (q * C (leadingCoeff q)⁻¹) := rfl
#align polynomial.mod_def Polynomial.mod_def

theorem modByMonic_eq_mod (p : R[X]) (hq : Monic q) : p %ₘ q = p % q :=
  show p %ₘ q = p %ₘ (q * C (leadingCoeff q)⁻¹) by
    simp only [Monic.def.1 hq, inv_one, mul_one, C_1]
#align polynomial.mod_by_monic_eq_mod Polynomial.modByMonic_eq_mod

theorem divByMonic_eq_div (p : R[X]) (hq : Monic q) : p /ₘ q = p / q :=
  show p /ₘ q = C (leadingCoeff q)⁻¹ * (p /ₘ (q * C (leadingCoeff q)⁻¹)) by
    simp only [Monic.def.1 hq, inv_one, C_1, one_mul, mul_one]
#align polynomial.div_by_monic_eq_div Polynomial.divByMonic_eq_div

theorem mod_X_sub_C_eq_C_eval (p : R[X]) (a : R) : p % (X - C a) = C (p.eval a) :=
  modByMonic_eq_mod p (monic_X_sub_C a) ▸ modByMonic_X_sub_C_eq_C_eval _ _
set_option linter.uppercaseLean3 false in
#align polynomial.mod_X_sub_C_eq_C_eval Polynomial.mod_X_sub_C_eq_C_eval

theorem mul_div_eq_iff_isRoot : (X - C a) * (p / (X - C a)) = p ↔ IsRoot p a :=
  divByMonic_eq_div p (monic_X_sub_C a) ▸ mul_divByMonic_eq_iff_isRoot
#align polynomial.mul_div_eq_iff_is_root Polynomial.mul_div_eq_iff_isRoot

instance instEuclideanDomain : EuclideanDomain R[X] :=
  { Polynomial.commRing,
    Polynomial.nontrivial with
    quotient := (· / ·)
    quotient_zero := by simp [div_def]
    remainder := (· % ·)
    r := _
    r_wellFounded := degree_lt_wf
    quotient_mul_add_remainder_eq := quotient_mul_add_remainder_eq_aux
    remainder_lt := fun p q hq => remainder_lt_aux _ hq
    mul_left_not_lt := fun p q hq => not_lt_of_ge (degree_le_mul_left _ hq) }

theorem mod_eq_self_iff (hq0 : q ≠ 0) : p % q = p ↔ degree p < degree q :=
  ⟨fun h => h ▸ EuclideanDomain.mod_lt _ hq0, fun h => by
    classical
    have : ¬degree (q * C (leadingCoeff q)⁻¹) ≤ degree p :=
      not_le_of_gt <| by rwa [degree_mul_leadingCoeff_inv q hq0]
    rw [mod_def, modByMonic, dif_pos (monic_mul_leadingCoeff_inv hq0)]
    unfold divModByMonicAux
    dsimp
    simp only [this, false_and_iff, if_false]⟩
#align polynomial.mod_eq_self_iff Polynomial.mod_eq_self_iff

theorem div_eq_zero_iff (hq0 : q ≠ 0) : p / q = 0 ↔ degree p < degree q :=
  ⟨fun h => by
    have := EuclideanDomain.div_add_mod p q;
      rwa [h, mul_zero, zero_add, mod_eq_self_iff hq0] at this,
    fun h => by
    have hlt : degree p < degree (q * C (leadingCoeff q)⁻¹) := by
      rwa [degree_mul_leadingCoeff_inv q hq0]
    have hm : Monic (q * C (leadingCoeff q)⁻¹) := monic_mul_leadingCoeff_inv hq0
    rw [div_def, (divByMonic_eq_zero_iff hm).2 hlt, mul_zero]⟩
#align polynomial.div_eq_zero_iff Polynomial.div_eq_zero_iff

theorem degree_add_div (hq0 : q ≠ 0) (hpq : degree q ≤ degree p) :
    degree q + degree (p / q) = degree p := by
  have : degree (p % q) < degree (q * (p / q)) :=
    calc
      degree (p % q) < degree q := EuclideanDomain.mod_lt _ hq0
      _ ≤ _ := degree_le_mul_left _ (mt (div_eq_zero_iff hq0).1 (not_lt_of_ge hpq))

  conv_rhs =>
    rw [← EuclideanDomain.div_add_mod p q, degree_add_eq_left_of_degree_lt this, degree_mul]
#align polynomial.degree_add_div Polynomial.degree_add_div

theorem degree_div_le (p q : R[X]) : degree (p / q) ≤ degree p := by
  by_cases hq : q = 0
  · simp [hq]
  · rw [div_def, mul_comm, degree_mul_leadingCoeff_inv _ hq]; exact degree_divByMonic_le _ _
#align polynomial.degree_div_le Polynomial.degree_div_le

theorem degree_div_lt (hp : p ≠ 0) (hq : 0 < degree q) : degree (p / q) < degree p := by
  have hq0 : q ≠ 0 := fun hq0 => by simp [hq0] at hq
  rw [div_def, mul_comm, degree_mul_leadingCoeff_inv _ hq0];
    exact
      degree_divByMonic_lt _ (monic_mul_leadingCoeff_inv hq0) hp
        (by rw [degree_mul_leadingCoeff_inv _ hq0]; exact hq)
#align polynomial.degree_div_lt Polynomial.degree_div_lt

theorem isUnit_map [Field k] (f : R →+* k) : IsUnit (p.map f) ↔ IsUnit p := by
  simp_rw [isUnit_iff_degree_eq_zero, degree_map]
#align polynomial.is_unit_map Polynomial.isUnit_map

theorem map_div [Field k] (f : R →+* k) : (p / q).map f = p.map f / q.map f := by
  if hq0 : q = 0 then simp [hq0]
  else
    rw [div_def, div_def, Polynomial.map_mul, map_divByMonic f (monic_mul_leadingCoeff_inv hq0),
      Polynomial.map_mul, map_C, leadingCoeff_map, map_inv₀]
#align polynomial.map_div Polynomial.map_div

theorem map_mod [Field k] (f : R →+* k) : (p % q).map f = p.map f % q.map f := by
  by_cases hq0 : q = 0
  · simp [hq0]
  · rw [mod_def, mod_def, leadingCoeff_map f, ← map_inv₀ f, ← map_C f, ← Polynomial.map_mul f,
      map_modByMonic f (monic_mul_leadingCoeff_inv hq0)]
#align polynomial.map_mod Polynomial.map_mod

section

open EuclideanDomain

theorem gcd_map [Field k] [DecidableEq R] [DecidableEq k] (f : R →+* k) :
    gcd (p.map f) (q.map f) = (gcd p q).map f :=
  GCD.induction p q (fun x => by simp_rw [Polynomial.map_zero, EuclideanDomain.gcd_zero_left])
    fun x y _ ih => by rw [gcd_val, ← map_mod, ih, ← gcd_val]
#align polynomial.gcd_map Polynomial.gcd_map

end

theorem eval₂_gcd_eq_zero [CommSemiring k] [DecidableEq R]
    {ϕ : R →+* k} {f g : R[X]} {α : k} (hf : f.eval₂ ϕ α = 0)
    (hg : g.eval₂ ϕ α = 0) : (EuclideanDomain.gcd f g).eval₂ ϕ α = 0 := by
  rw [EuclideanDomain.gcd_eq_gcd_ab f g, Polynomial.eval₂_add, Polynomial.eval₂_mul,
    Polynomial.eval₂_mul, hf, hg, zero_mul, zero_mul, zero_add]
#align polynomial.eval₂_gcd_eq_zero Polynomial.eval₂_gcd_eq_zero

theorem eval_gcd_eq_zero [DecidableEq R] {f g : R[X]} {α : R}
    (hf : f.eval α = 0) (hg : g.eval α = 0) : (EuclideanDomain.gcd f g).eval α = 0 :=
  eval₂_gcd_eq_zero hf hg
#align polynomial.eval_gcd_eq_zero Polynomial.eval_gcd_eq_zero

theorem root_left_of_root_gcd [CommSemiring k] [DecidableEq R] {ϕ : R →+* k} {f g : R[X]} {α : k}
    (hα : (EuclideanDomain.gcd f g).eval₂ ϕ α = 0) : f.eval₂ ϕ α = 0 := by
  cases' EuclideanDomain.gcd_dvd_left f g with p hp
  rw [hp, Polynomial.eval₂_mul, hα, zero_mul]
#align polynomial.root_left_of_root_gcd Polynomial.root_left_of_root_gcd

theorem root_right_of_root_gcd [CommSemiring k] [DecidableEq R] {ϕ : R →+* k} {f g : R[X]} {α : k}
    (hα : (EuclideanDomain.gcd f g).eval₂ ϕ α = 0) : g.eval₂ ϕ α = 0 := by
  cases' EuclideanDomain.gcd_dvd_right f g with p hp
  rw [hp, Polynomial.eval₂_mul, hα, zero_mul]
#align polynomial.root_right_of_root_gcd Polynomial.root_right_of_root_gcd

theorem root_gcd_iff_root_left_right [CommSemiring k] [DecidableEq R]
    {ϕ : R →+* k} {f g : R[X]} {α : k} :
    (EuclideanDomain.gcd f g).eval₂ ϕ α = 0 ↔ f.eval₂ ϕ α = 0 ∧ g.eval₂ ϕ α = 0 :=
  ⟨fun h => ⟨root_left_of_root_gcd h, root_right_of_root_gcd h⟩, fun h => eval₂_gcd_eq_zero h.1 h.2⟩
#align polynomial.root_gcd_iff_root_left_right Polynomial.root_gcd_iff_root_left_right

theorem isRoot_gcd_iff_isRoot_left_right [DecidableEq R] {f g : R[X]} {α : R} :
    (EuclideanDomain.gcd f g).IsRoot α ↔ f.IsRoot α ∧ g.IsRoot α :=
  root_gcd_iff_root_left_right
#align polynomial.is_root_gcd_iff_is_root_left_right Polynomial.isRoot_gcd_iff_isRoot_left_right

theorem isCoprime_map [Field k] (f : R →+* k) : IsCoprime (p.map f) (q.map f) ↔ IsCoprime p q := by
  classical
  rw [← EuclideanDomain.gcd_isUnit_iff, ← EuclideanDomain.gcd_isUnit_iff, gcd_map, isUnit_map]
#align polynomial.is_coprime_map Polynomial.isCoprime_map

theorem mem_roots_map [CommRing k] [IsDomain k] {f : R →+* k} {x : k} (hp : p ≠ 0) :
    x ∈ (p.map f).roots ↔ p.eval₂ f x = 0 := by
  rw [mem_roots (map_ne_zero hp), IsRoot, Polynomial.eval_map]
#align polynomial.mem_roots_map Polynomial.mem_roots_map

theorem rootSet_monomial [CommRing S] [IsDomain S] [Algebra R S] {n : ℕ} (hn : n ≠ 0) {a : R}
    (ha : a ≠ 0) : (monomial n a).rootSet S = {0} := by
  classical
  rw [rootSet, aroots_monomial ha,
    Multiset.toFinset_nsmul _ _ hn, Multiset.toFinset_singleton, Finset.coe_singleton]
#align polynomial.root_set_monomial Polynomial.rootSet_monomial

theorem rootSet_C_mul_X_pow [CommRing S] [IsDomain S] [Algebra R S] {n : ℕ} (hn : n ≠ 0) {a : R}
    (ha : a ≠ 0) : rootSet (C a * X ^ n) S = {0} := by
  rw [C_mul_X_pow_eq_monomial, rootSet_monomial hn ha]
set_option linter.uppercaseLean3 false in
#align polynomial.root_set_C_mul_X_pow Polynomial.rootSet_C_mul_X_pow

theorem rootSet_X_pow [CommRing S] [IsDomain S] [Algebra R S] {n : ℕ} (hn : n ≠ 0) :
    (X ^ n : R[X]).rootSet S = {0} := by
  rw [← one_mul (X ^ n : R[X]), ← C_1, rootSet_C_mul_X_pow hn]
  exact one_ne_zero
set_option linter.uppercaseLean3 false in
#align polynomial.root_set_X_pow Polynomial.rootSet_X_pow

theorem rootSet_prod [CommRing S] [IsDomain S] [Algebra R S] {ι : Type*} (f : ι → R[X])
    (s : Finset ι) (h : s.prod f ≠ 0) : (s.prod f).rootSet S = ⋃ i ∈ s, (f i).rootSet S := by
  classical
  simp only [rootSet, aroots, ← Finset.mem_coe]
  rw [Polynomial.map_prod, roots_prod, Finset.bind_toFinset, s.val_toFinset, Finset.coe_biUnion]
  rwa [← Polynomial.map_prod, Ne, map_eq_zero]
#align polynomial.root_set_prod Polynomial.rootSet_prod

theorem exists_root_of_degree_eq_one (h : degree p = 1) : ∃ x, IsRoot p x :=
  ⟨-(p.coeff 0 / p.coeff 1), by
    have : p.coeff 1 ≠ 0 := by
      have h' := natDegree_eq_of_degree_eq_some h
      change natDegree p = 1 at h'; rw [← h']
      exact mt leadingCoeff_eq_zero.1 fun h0 => by simp [h0] at h
    conv in p => rw [eq_X_add_C_of_degree_le_one (show degree p ≤ 1 by rw [h])]
    simp [IsRoot, mul_div_cancel₀ _ this]⟩
#align polynomial.exists_root_of_degree_eq_one Polynomial.exists_root_of_degree_eq_one

theorem coeff_inv_units (u : R[X]ˣ) (n : ℕ) : ((↑u : R[X]).coeff n)⁻¹ = (↑u⁻¹ : R[X]).coeff n := by
  rw [eq_C_of_degree_eq_zero (degree_coe_units u), eq_C_of_degree_eq_zero (degree_coe_units u⁻¹),
    coeff_C, coeff_C, inv_eq_one_div]
  split_ifs
  · rw [div_eq_iff_mul_eq (coeff_coe_units_zero_ne_zero u), coeff_zero_eq_eval_zero,
        coeff_zero_eq_eval_zero, ← eval_mul, ← Units.val_mul, inv_mul_self]
    simp
  · simp
#align polynomial.coeff_inv_units Polynomial.coeff_inv_units

theorem monic_normalize [DecidableEq R] (hp0 : p ≠ 0) : Monic (normalize p) := by
  rw [Ne, ← leadingCoeff_eq_zero, ← Ne, ← isUnit_iff_ne_zero] at hp0
  rw [Monic, leadingCoeff_normalize, normalize_eq_one]
  apply hp0
#align polynomial.monic_normalize Polynomial.monic_normalize

theorem leadingCoeff_div (hpq : q.degree ≤ p.degree) :
    (p / q).leadingCoeff = p.leadingCoeff / q.leadingCoeff := by
  by_cases hq : q = 0
  · simp [hq]
  rw [div_def, leadingCoeff_mul, leadingCoeff_C,
    leadingCoeff_divByMonic_of_monic (monic_mul_leadingCoeff_inv hq) _, mul_comm,
    div_eq_mul_inv]
  rwa [degree_mul_leadingCoeff_inv q hq]
#align polynomial.leading_coeff_div Polynomial.leadingCoeff_div

theorem div_C_mul : p / (C a * q) = C a⁻¹ * (p / q) := by
  by_cases ha : a = 0
  · simp [ha]
  simp only [div_def, leadingCoeff_mul, mul_inv, leadingCoeff_C, C.map_mul, mul_assoc]
  congr 3
  rw [mul_left_comm q, ← mul_assoc, ← C.map_mul, mul_inv_cancel ha, C.map_one, one_mul]
set_option linter.uppercaseLean3 false in
#align polynomial.div_C_mul Polynomial.div_C_mul

theorem C_mul_dvd (ha : a ≠ 0) : C a * p ∣ q ↔ p ∣ q :=
  ⟨fun h => dvd_trans (dvd_mul_left _ _) h, fun ⟨r, hr⟩ =>
    ⟨C a⁻¹ * r, by
      rw [mul_assoc, mul_left_comm p, ← mul_assoc, ← C.map_mul, _root_.mul_inv_cancel ha, C.map_one,
        one_mul, hr]⟩⟩
set_option linter.uppercaseLean3 false in
#align polynomial.C_mul_dvd Polynomial.C_mul_dvd

theorem dvd_C_mul (ha : a ≠ 0) : p ∣ Polynomial.C a * q ↔ p ∣ q :=
  ⟨fun ⟨r, hr⟩ =>
    ⟨C a⁻¹ * r, by
      rw [mul_left_comm p, ← hr, ← mul_assoc, ← C.map_mul, _root_.inv_mul_cancel ha, C.map_one,
        one_mul]⟩,
    fun h => dvd_trans h (dvd_mul_left _ _)⟩
set_option linter.uppercaseLean3 false in
#align polynomial.dvd_C_mul Polynomial.dvd_C_mul

theorem coe_normUnit_of_ne_zero [DecidableEq R] (hp : p ≠ 0) :
    (normUnit p : R[X]) = C p.leadingCoeff⁻¹ := by
  have : p.leadingCoeff ≠ 0 := mt leadingCoeff_eq_zero.mp hp
  simp [CommGroupWithZero.coe_normUnit _ this]
#align polynomial.coe_norm_unit_of_ne_zero Polynomial.coe_normUnit_of_ne_zero

theorem normalize_monic [DecidableEq R] (h : Monic p) : normalize p = p := by simp [h]
#align polynomial.normalize_monic Polynomial.normalize_monic

theorem map_dvd_map' [Field k] (f : R →+* k) {x y : R[X]} : x.map f ∣ y.map f ↔ x ∣ y := by
  by_cases H : x = 0
  · rw [H, Polynomial.map_zero, zero_dvd_iff, zero_dvd_iff, map_eq_zero]
  · classical
    rw [← normalize_dvd_iff, ← @normalize_dvd_iff R[X], normalize_apply, normalize_apply,
      coe_normUnit_of_ne_zero H, coe_normUnit_of_ne_zero (mt (map_eq_zero f).1 H),
      leadingCoeff_map, ← map_inv₀ f, ← map_C, ← Polynomial.map_mul,
      map_dvd_map _ f.injective (monic_mul_leadingCoeff_inv H)]
#align polynomial.map_dvd_map' Polynomial.map_dvd_map'

theorem degree_normalize [DecidableEq R] : degree (normalize p) = degree p := by simp
#align polynomial.degree_normalize Polynomial.degree_normalize

theorem prime_of_degree_eq_one (hp1 : degree p = 1) : Prime p := by
  classical
  have : Prime (normalize p) :=
    Monic.prime_of_degree_eq_one (hp1 ▸ degree_normalize)
      (monic_normalize fun hp0 => absurd hp1 (hp0.symm ▸ by simp [degree_zero]))
  exact (normalize_associated _).prime this
#align polynomial.prime_of_degree_eq_one Polynomial.prime_of_degree_eq_one

theorem irreducible_of_degree_eq_one (hp1 : degree p = 1) : Irreducible p :=
  (prime_of_degree_eq_one hp1).irreducible
#align polynomial.irreducible_of_degree_eq_one Polynomial.irreducible_of_degree_eq_one

theorem not_irreducible_C (x : R) : ¬Irreducible (C x) := by
  by_cases H : x = 0
  · rw [H, C_0]
    exact not_irreducible_zero
  · exact fun hx => Irreducible.not_unit hx <| isUnit_C.2 <| isUnit_iff_ne_zero.2 H
set_option linter.uppercaseLean3 false in
#align polynomial.not_irreducible_C Polynomial.not_irreducible_C

theorem degree_pos_of_irreducible (hp : Irreducible p) : 0 < p.degree :=
  lt_of_not_ge fun hp0 =>
    have := eq_C_of_degree_le_zero hp0
    not_irreducible_C (p.coeff 0) <| this ▸ hp
#align polynomial.degree_pos_of_irreducible Polynomial.degree_pos_of_irreducible

/- Porting note: factored out a have statement from isCoprime_of_is_root_of_eval_derivative_ne_zero
into multiple decls because the original proof was timing out -/
theorem X_sub_C_mul_divByMonic_eq_sub_modByMonic {K : Type*} [Field K] (f : K[X]) (a : K) :
    (X - C a) * (f /ₘ (X - C a)) = f - f %ₘ (X - C a) := by
  rw [eq_sub_iff_add_eq, ← eq_sub_iff_add_eq', modByMonic_eq_sub_mul_div]
  exact monic_X_sub_C a

/- Porting note: factored out a have statement from isCoprime_of_is_root_of_eval_derivative_ne_zero
because the original proof was timing out -/
theorem divByMonic_add_X_sub_C_mul_derivate_divByMonic_eq_derivative
    {K : Type*} [Field K] (f : K[X]) (a : K) :
    f /ₘ (X - C a) + (X - C a) * derivative (f /ₘ (X - C a)) = derivative f := by
  have key := by apply congrArg derivative <| X_sub_C_mul_divByMonic_eq_sub_modByMonic f a
  rw [modByMonic_X_sub_C_eq_C_eval] at key
  rw [derivative_mul,derivative_sub,derivative_X,derivative_sub] at key
  rw [derivative_C,sub_zero,one_mul] at key
  rw [derivative_C,sub_zero] at key
  assumption

/- Porting note: factored out another have statement from
isCoprime_of_is_root_of_eval_derivative_ne_zero because the original proof was timing out -/
theorem X_sub_C_dvd_derivative_of_X_sub_C_dvd_divByMonic {K : Type*} [Field K] (f : K[X]) {a : K}
    (hf : (X - C a) ∣ f /ₘ (X - C a)) : X - C a ∣ derivative f := by
  have key := divByMonic_add_X_sub_C_mul_derivate_divByMonic_eq_derivative f a
  have ⟨u,hu⟩ := hf
  rw [← key, hu, ← mul_add (X - C a) u _]
  use (u + derivative ((X - C a) * u))

/-- If `f` is a polynomial over a field, and `a : K` satisfies `f' a ≠ 0`,
then `f / (X - a)` is coprime with `X - a`.
Note that we do not assume `f a = 0`, because `f / (X - a) = (f - f a) / (X - a)`. -/
theorem isCoprime_of_is_root_of_eval_derivative_ne_zero {K : Type*} [Field K] (f : K[X]) (a : K)
    (hf' : f.derivative.eval a ≠ 0) : IsCoprime (X - C a : K[X]) (f /ₘ (X - C a)) := by
  classical
  refine Or.resolve_left
      (EuclideanDomain.dvd_or_coprime (X - C a) (f /ₘ (X - C a))
        (irreducible_of_degree_eq_one (Polynomial.degree_X_sub_C a))) ?_
  contrapose! hf' with h
  have : X - C a ∣ derivative f := X_sub_C_dvd_derivative_of_X_sub_C_dvd_divByMonic f h
  rw [← modByMonic_eq_zero_iff_dvd (monic_X_sub_C _), modByMonic_X_sub_C_eq_C_eval] at this
  rwa [← C_inj, C_0]
#align polynomial.is_coprime_of_is_root_of_eval_derivative_ne_zero Polynomial.isCoprime_of_is_root_of_eval_derivative_ne_zero

/-- To check a polynomial over a field is irreducible, it suffices to check only for
divisors that have smaller degree.

See also: `Polynomial.Monic.irreducible_iff_natDegree`.
-/
theorem irreducible_iff_degree_lt (p : R[X]) (hp0 : p ≠ 0) (hpu : ¬ IsUnit p) :
    Irreducible p ↔ ∀ q, q.degree ≤ ↑(natDegree p / 2) → q ∣ p → IsUnit q := by
  rw [← irreducible_mul_leadingCoeff_inv,
      (monic_mul_leadingCoeff_inv hp0).irreducible_iff_degree_lt]
  · simp [hp0, natDegree_mul_leadingCoeff_inv]
  · contrapose! hpu
    exact isUnit_of_mul_eq_one _ _ hpu

/-- To check a polynomial `p` over a field is irreducible, it suffices to check there are no
divisors of degree `0 < d ≤ degree p / 2`.

See also: `Polynomial.Monic.irreducible_iff_natDegree'`.
-/
theorem irreducible_iff_lt_natDegree_lt {p : R[X]} (hp0 : p ≠ 0) (hpu : ¬ IsUnit p) :
    Irreducible p ↔ ∀ q, Monic q → natDegree q ∈ Finset.Ioc 0 (natDegree p / 2) → ¬ q ∣ p := by
  have : p * C (leadingCoeff p)⁻¹ ≠ 1 := by
    contrapose! hpu
    exact isUnit_of_mul_eq_one _ _ hpu
  rw [← irreducible_mul_leadingCoeff_inv,
      (monic_mul_leadingCoeff_inv hp0).irreducible_iff_lt_natDegree_lt this,
      natDegree_mul_leadingCoeff_inv _ hp0]
  simp only [IsUnit.dvd_mul_right
    (isUnit_C.mpr (IsUnit.mk0 (leadingCoeff p)⁻¹ (inv_ne_zero (leadingCoeff_ne_zero.mpr hp0))))]

end Field

end Polynomial

/-- An irreducible polynomial over a field must have positive degree. -/
theorem Irreducible.natDegree_pos {F : Type*} [Field F] {f : F[X]} (h : Irreducible f) :
    0 < f.natDegree := Nat.pos_of_ne_zero fun H ↦ by
  obtain ⟨x, hf⟩ := natDegree_eq_zero.1 H
  by_cases hx : x = 0
  · rw [← hf, hx, map_zero] at h; exact not_irreducible_zero h
  exact h.1 (hf ▸ isUnit_C.2 (Ne.isUnit hx))
