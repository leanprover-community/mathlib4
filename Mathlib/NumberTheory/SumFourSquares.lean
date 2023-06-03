/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes

! This file was ported from Lean 3 source module number_theory.sum_four_squares
! leanprover-community/mathlib commit bd9851ca476957ea4549eb19b40e7b5ade9428cc
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.GroupPower.Identities
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Int.Parity
import Mathlib.Data.Fintype.BigOperators

/-!
# Lagrange's four square theorem

The main result in this file is `sum_four_squares`,
a proof that every natural number is the sum of four square numbers.

## Implementation Notes

The proof used is close to Lagrange's original proof.
-/


open Finset Polynomial FiniteField Equiv

open scoped BigOperators

/-- **Euler's four-square identity**. -/
theorem euler_four_squares {R : Type _} [CommRing R] (a b c d x y z w : R) :
    (a * x - b * y - c * z - d * w) ^ 2 + (a * y + b * x + c * w - d * z) ^ 2 +
      (a * z - b * w + c * x + d * y) ^ 2 + (a * w + b * z - c * y + d * x) ^ 2 =
      (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) * (x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2) := by ring

/-- **Euler's four-square identity**, a version for natural numbers. -/
theorem Nat.euler_four_squares (a b c d x y z w : ℕ) :
    ((a : ℤ) * x - b * y - c * z - d * w).natAbs ^ 2 +
      ((a : ℤ) * y + b * x + c * w - d * z).natAbs ^ 2 +
      ((a : ℤ) * z - b * w + c * x + d * y).natAbs ^ 2 +
      ((a : ℤ) * w + b * z - c * y + d * x).natAbs ^ 2 =
      (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) * (x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2) := by
  rw [← Int.coe_nat_inj']
  push_cast
  simp only [sq_abs, _root_.euler_four_squares]

namespace Int

theorem sq_add_sq_of_two_mul_sq_add_sq {m x y : ℤ} (h : 2 * m = x ^ 2 + y ^ 2) :
    m = ((x - y) / 2) ^ 2 + ((x + y) / 2) ^ 2 :=
  have : Even (x ^ 2 + y ^ 2) := by simp [← h, even_mul]
  have hxaddy : Even (x + y) := by simpa [sq, parity_simps]
  have hxsuby : Even (x - y) := by simpa [sq, parity_simps]
  mul_right_injective₀ (show (2 * 2 : ℤ) ≠ 0 by decide) <|
    calc
      2 * 2 * m = (x - y) ^ 2 + (x + y) ^ 2 := by rw [mul_assoc, h]; ring
      _ = (2 * ((x - y) / 2)) ^ 2 + (2 * ((x + y) / 2)) ^ 2 := by
        rw [even_iff_two_dvd] at hxsuby hxaddy 
        rw [Int.mul_ediv_cancel' hxsuby, Int.mul_ediv_cancel' hxaddy]
      _ = 2 * 2 * (((x - y) / 2) ^ 2 + ((x + y) / 2) ^ 2) := by
        simp [mul_add, pow_succ, mul_comm, mul_assoc, mul_left_comm]
#align int.sq_add_sq_of_two_mul_sq_add_sq Int.sq_add_sq_of_two_mul_sq_add_sq

-- porting note: new theorem
theorem lt_of_sum_four_squares_eq_mul {a b c d k m : ℕ}
    (h : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = k * m)
    (ha : 2 * a < m) (hb : 2 * b < m) (hc : 2 * c < m) (hd : 2 * d < m) :
    k < m := by
  refine lt_of_mul_lt_mul_right (lt_of_mul_lt_mul_left ?_ (zero_le (2 ^ 2))) (zero_le m)
  calc
    2 ^ 2 * (k * ↑m) = ∑ i : Fin 4, (2 * ![a, b, c, d] i) ^ 2 := by
      simp [← h, Fin.sum_univ_succ, mul_add, mul_pow, add_assoc]
    _ < ∑ i : Fin 4, m ^ 2 := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _ ↦ by
      refine pow_lt_pow_of_lt_left ?_ (zero_le _) two_pos
      fin_cases i <;> assumption
    _ = 2 ^ 2 * (m * m) := by simp; ring

-- porting note: new theorem
theorem exists_sq_add_sq_add_one_eq_mul (p : ℕ) [hp : Fact p.Prime] :
    ∃ (a b k : ℕ), 0 < k ∧ k < p ∧ a ^ 2 + b ^ 2 + 1 = k * p := by
  rcases hp.1.eq_two_or_odd' with (rfl | hodd)
  · use 1, 0, 1; simp
  rcases Nat.sq_add_sq_zmodEq p (-1) with ⟨a, b, ha, hb, hab⟩
  rcases Int.modEq_iff_dvd.1 hab.symm with ⟨k, hk⟩
  rw [sub_neg_eq_add, mul_comm] at hk
  have hk₀ : 0 < k
  · refine pos_of_mul_pos_left  ?_ (Nat.cast_nonneg p)
    rw [← hk]
    positivity
  lift k to ℕ using hk₀.le
  refine ⟨a, b, k, Nat.cast_pos.1 hk₀, ?_, by exact_mod_cast hk⟩
  replace hk : a ^ 2 + b ^ 2 + 1 ^ 2 + 0 ^ 2 = k * p
  · exact_mod_cast hk
  refine lt_of_sum_four_squares_eq_mul hk ?_ ?_ ?_ ?_
  · 
  · exact (Nat.le_div_iff_mul_le two_pos).2 hp.1.two_le
  · rintro ⟨-, -, rfl, h⟩
    simp at h

@[deprecated exists_sq_add_sq_add_one_eq_mul]
theorem exists_sq_add_sq_add_one_eq_k (p : ℕ) [Fact p.Prime] :
    ∃ (a b : ℤ) (k : ℕ), a ^ 2 + b ^ 2 + 1 = k * p ∧ k < p :=
  let ⟨a, b, k, _, hkp, hk⟩ := exists_sq_add_sq_add_one_eq_mul p
  ⟨a, b, k, by exact_mod_cast hk, hkp⟩
#align int.exists_sq_add_sq_add_one_eq_k Int.exists_sq_add_sq_add_one_eq_k

end Int

namespace Nat

open Int

open scoped Classical

private theorem sum_four_squares_of_two_mul_sum_four_squares {m a b c d : ℤ}
    (h : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 2 * m) :
    ∃ w x y z : ℤ, w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 = m :=
  have : ∀ f : Fin 4 → ZMod 2, f 0 ^ 2 + f 1 ^ 2 + f 2 ^ 2 + f 3 ^ 2 = 0 → ∃ i : Fin 4,
      f i ^ 2 + f (swap i 0 1) ^ 2 = 0 ∧ f (swap i 0 2) ^ 2 + f (swap i 0 3) ^ 2 = 0 := by
    decide
  let f : Fin 4 → ℤ := ![a, b, c, d]
  let ⟨i, hσ⟩ := this (fun x => ↑(f x)) <| by
    rw [← @zero_mul (ZMod 2) _ m, ← show ((2 : ℤ) : ZMod 2) = 0 from rfl, ← Int.cast_mul, ← h]
    simp only [Int.cast_add, Int.cast_pow]
    rfl
  let σ := swap i 0
  have h01 : 2 ∣ f (σ 0) ^ 2 + f (σ 1) ^ 2 :=
    (CharP.int_cast_eq_zero_iff (ZMod 2) 2 _).1 <| by
      simpa only [Int.cast_pow, Int.cast_add, Equiv.swap_apply_right, ZMod.pow_card] using hσ.1
  have h23 : 2 ∣ f (σ 2) ^ 2 + f (σ 3) ^ 2 :=
    (CharP.int_cast_eq_zero_iff (ZMod 2) 2 _).1 <| by
      simpa only [Int.cast_pow, Int.cast_add, ZMod.pow_card] using hσ.2
  let ⟨x, hx⟩ := h01
  let ⟨y, hy⟩ := h23
  ⟨(f (σ 0) - f (σ 1)) / 2, (f (σ 0) + f (σ 1)) / 2, (f (σ 2) - f (σ 3)) / 2,
    (f (σ 2) + f (σ 3)) / 2, by
    rw [← Int.sq_add_sq_of_two_mul_sq_add_sq hx.symm, add_assoc, ←
      Int.sq_add_sq_of_two_mul_sq_add_sq hy.symm, ← mul_right_inj' (show (2 : ℤ) ≠ 0 by decide), ←
      h, mul_add, ← hx, ← hy]
    have : (∑ x, f (σ x) ^ 2) = ∑ x, f x ^ 2 := by conv_rhs => rw [← Equiv.sum_comp σ]
    simpa only [Fin.sum_univ_four, add_assoc] using this⟩

private theorem prime_sum_four_squares (p : ℕ) [hp : Fact p.Prime] :
    ∃ a b c d : ℕ, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = p := by
  -- Find `a`, `b`, `c`, `d`, `0 < m < p` such that `a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = m * p`
  have hm : ∃ m < p, 0 < m ∧ ∃ a b c d : ℕ, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = m * p
  · obtain ⟨a, b, k, hk₀, hkp, hk⟩ := exists_sq_add_sq_add_one_eq_mul p
    refine ⟨k, hkp, hk₀, a, b, 1, 0, ?_⟩
    simpa
  -- Take the minimal possible `m`
  rcases Nat.findX hm with ⟨m, ⟨hmp, hm₀, a, b, c, d, habcd⟩, hmin⟩
  -- If `m = 1`, then we are done
  rcases (Nat.one_le_iff_ne_zero.2 hm₀.ne').eq_or_gt with rfl | hm₁
  · use a, b, c, d; simpa using habcd
  -- Otherwise, let us find a contradiction
  exfalso
  have : NeZero m := ⟨hm₀.ne'⟩
  -- by_cases hm : 2 ∣ m
  -- · rcases hm with ⟨m, rfl⟩
  --   rw [Nat.cast_mul, Nat.cast_ofNat, mul_assoc] at habcd
  --   rw [zero_lt_mul_left two_pos] at hm₀
  --   have hm₂ : m < 2 * m := by simpa [two_mul]
  --   refine hmin m hm₂ ⟨hm₂.trans hmp, hm₀, sum_four_squares_of_two_mul_sum_four_squares habcd⟩
  -- · 
  have : ∀ x : ℕ, ∃ y : ℤ, y.natAbs ≤ m / 2 ∧ (y : ZMod m) = x := fun x ↦
    ⟨(x : ZMod m).valMinAbs, (x : ZMod m).natAbs_valMinAbs_le, (x : ZMod m).coe_valMinAbs⟩
  choose f hfle hf using this
  have hmp' : ¬(m ^ 2 ∣ a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2)
  · rw [habcd, sq, mul_dvd_mul_iff_left hm₀.ne']
    exact fun h ↦ (hp.1.eq_one_or_self_of_dvd _ h).elim hm₁.ne' hmp.ne
  obtain ⟨r, hr₀, hrm, hr⟩ : ∃ r : ℕ, 0 < r ∧ r < m ∧
      (f a) ^ 2 + (f b) ^ 2 + (f c) ^ 2 + (f d) ^ 2 = m * r
  · obtain ⟨r, hr⟩ : m ∣ (f a).natAbs ^ 2 + (f b).natAbs ^ 2 + (f c).natAbs ^ 2 + (f d).natAbs ^ 2
    · simp only [← Int.coe_nat_dvd, ← ZMod.int_cast_zmod_eq_zero_iff_dvd]
      push_cast [hf, sq_abs]
      norm_cast
      simp [habcd]
    rcases (zero_le r).eq_or_gt with (rfl | hr₀)
    · replace hr : f a = 0 ∧ f b = 0 ∧ f c = 0 ∧ f d = 0; · simpa [and_assoc] using hr
      obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩, ⟨c, rfl⟩, ⟨d, rfl⟩⟩ : m ∣ a ∧ m ∣ b ∧ m ∣ c ∧ m ∣ d
      · simp only [← ZMod.nat_cast_zmod_eq_zero_iff_dvd, ← hf, hr, Int.cast_zero]
      refine (hmp' ⟨a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2, mul_left_cancel₀ hm₀.ne' <| ?_⟩).elim
      ring
    · refine ⟨r, hr₀, ?_, ?_⟩
      · rw [mul_comm] at hr
        refine lt_of_sum_four_squares_eq_mul hr (hfle _) (hfle _) (hfle _) (hfle _) fun h ↦ ?_
        obtain ⟨m, rfl⟩ : 2 ∣ m := ⟨(f a).natAbs, h.1.symm⟩
        simp only [mul_right_inj' two_ne_zero] at h
        have H₁ : ∀ x : ℕ, (f x).natAbs = m → x ^ 2 ≡ m ^ 2 [MOD (2 * m) ^ 2]
        · rintro x rfl
          specialize hf x
          rw [← Int.cast_ofNat, ZMod.int_cast_eq_int_cast_iff_dvd_sub] at hf
          rcases hf with ⟨c, hc⟩
          push_cast [← Int.coe_nat_modEq_iff, sub_eq_iff_eq_add.1 hc]
          simp only [add_sq, mul_pow, sq_abs, Int.modEq_iff_dvd, sub_add_cancel'', dvd_neg]
          refine (dvd_mul_right _ _).add ?_
          calc
            2 ^ 2 * f x ^ 2 = 2 * 2 * f x * f x := by simp only [sq]; ac_rfl
            _ ∣ (2 * 2 * f x * c) * |f x| := mul_dvd_mul (dvd_mul_right _ _) (self_dvd_abs _)
            _ = _ := by ac_rfl
        have H₂ : ∀ i : Fin 4, (f <| ![a, b, c, d] i).natAbs = m
        · simpa only [Fin.forall_fin_succ (n := 3), Fin.forall_fin_succ (n := 2),
            Fin.forall_fin_two]
        refine hmp' (Nat.modEq_zero_iff_dvd.1 ?_)
        calc
          a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 ≡ m ^ 2 + m ^ 2 + m ^ 2 + m ^ 2 [MOD (2 * m) ^ 2] :=
            (((H₁ a (H₂ 0)).add (H₁ b (H₂ 1))).add (H₁ c (H₂ 2))).add (H₁ d (H₂ 3))
          _ = (2 * m) ^ 2 := by ring
          _ ≡ 0 [MOD (2 * m) ^ 2] := by simp only [Nat.modEq_zero_iff_dvd, dvd_refl]
      · rw [← Nat.cast_mul, ← hr]
        push_cast [sq_abs]; rfl
  have := congr_arg₂ (· * ·) (congr_arg Nat.cast habcd) hr
  push_cast [← _root_.euler_four_squares] at this
  
  --   fun hm2 : m % 2 = 1 =>
  --   if hm1 : m = 1 then ⟨a, b, c, d, by simp only [hm1, habcd, Int.ofNat_one, one_mul]⟩
  --   else
  --     let w := (a : ZMod m).valMinAbs
  --     let x := (b : ZMod m).valMinAbs
  --     let y := (c : ZMod m).valMinAbs
  --     let z := (d : ZMod m).valMinAbs
  --     have hnat_abs :
  --       w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 =
  --         (w.natAbs ^ 2 + x.natAbs ^ 2 + y.natAbs ^ 2 + z.natAbs ^ 2 : ℕ) :=
  --       by push_cast ; simp_rw [sq_abs]
  --     have hwxyzlt : w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 < m ^ 2 :=
  --       calc
  --         w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 =
  --             (w.natAbs ^ 2 + x.natAbs ^ 2 + y.natAbs ^ 2 + z.natAbs ^ 2 : ℕ) :=
  --           hnat_abs
  --         _ ≤ ((m / 2) ^ 2 + (m / 2) ^ 2 + (m / 2) ^ 2 + (m / 2) ^ 2 : ℕ) :=
  --           (Int.ofNat_le.2 <|
  --             add_le_add
  --               (add_le_add
  --                 (add_le_add (Nat.pow_le_pow_of_le_left (ZMod.natAbs_valMinAbs_le _) _)
  --                   (Nat.pow_le_pow_of_le_left (ZMod.natAbs_valMinAbs_le _) _))
  --                 (Nat.pow_le_pow_of_le_left (ZMod.natAbs_valMinAbs_le _) _))
  --               (Nat.pow_le_pow_of_le_left (ZMod.natAbs_valMinAbs_le _) _))
  --         _ = 4 * (m / 2 : ℕ) ^ 2 := by
  --           simp only [bit0_mul, one_mul, two_smul, Nat.cast_add, Nat.cast_pow, add_assoc]
  --         _ < 4 * (m / 2 : ℕ) ^ 2 + ((4 * (m / 2) : ℕ) * (m % 2 : ℕ) + (m % 2 : ℕ) ^ 2) :=
  --           ((lt_add_iff_pos_right _).2
  --             (by
  --               rw [hm2, Int.ofNat_one, one_pow, mul_one]
  --               exact add_pos_of_nonneg_of_pos (Int.coe_nat_nonneg _) zero_lt_one))
  --         _ = m ^ 2 := by
  --           conv_rhs => rw [← Nat.mod_add_div m 2]
  --           simp [-Nat.mod_add_div, mul_add, add_mul, bit0, bit1, mul_comm, mul_assoc,
  --             mul_left_comm, pow_add, add_comm, add_left_comm]
          
  --     have hwxyzabcd :
  --       ((w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 : ℤ) : ZMod m) =
  --         ((a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 : ℤ) : ZMod m) :=
  --       by push_cast
  --     have hwxyz0 : ((w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 : ℤ) : ZMod m) = 0 := by
  --       rw [hwxyzabcd, habcd, Int.cast_mul, cast_coe_nat, ZMod.nat_cast_self, MulZeroClass.zero_mul]
  --     let ⟨n, hn⟩ := (CharP.int_cast_eq_zero_iff _ m _).1 hwxyz0
  --     have hn0 : 0 < n.natAbs :=
  --       Int.natAbs_pos_of_ne_zero fun hn0 =>
  --         have hwxyz0 : (w.natAbs ^ 2 + x.natAbs ^ 2 + y.natAbs ^ 2 + z.natAbs ^ 2 : ℕ) = 0 := by
  --           rw [← Int.coe_nat_eq_zero, ← hnat_abs]; rwa [hn0, MulZeroClass.mul_zero] at hn 
  --         have habcd0 : (m : ℤ) ∣ a ∧ (m : ℤ) ∣ b ∧ (m : ℤ) ∣ c ∧ (m : ℤ) ∣ d := by
  --           simpa only [add_eq_zero_iff, Int.natAbs_eq_zero, ZMod.valMinAbs_eq_zero, and_assoc,
  --             pow_eq_zero_iff two_pos, CharP.int_cast_eq_zero_iff _ m _] using hwxyz0
  --         let ⟨ma, hma⟩ := habcd0.1
  --         let ⟨mb, hmb⟩ := habcd0.2.1
  --         let ⟨mc, hmc⟩ := habcd0.2.2.1
  --         let ⟨md, hmd⟩ := habcd0.2.2.2
  --         have hmdvdp : m ∣ p :=
  --           Int.coe_nat_dvd.1
  --             ⟨ma ^ 2 + mb ^ 2 + mc ^ 2 + md ^ 2,
  --               (mul_right_inj' (show (m : ℤ) ≠ 0 from Int.coe_nat_ne_zero.2 hm0.1)).1 <| by
  --                 rw [← habcd, hma, hmb, hmc, hmd]; ring⟩
  --         (hp.1.eq_one_or_self_of_dvd _ hmdvdp).elim hm1 fun hmeqp => by
  --           simpa [lt_irrefl, hmeqp] using hmp
  --     have hawbxcydz : ((m : ℕ) : ℤ) ∣ a * w + b * x + c * y + d * z :=
  --       (CharP.int_cast_eq_zero_iff (ZMod m) m _).1 <| by rw [← hwxyz0]; simp_rw [sq]; push_cast
  --     have haxbwczdy : ((m : ℕ) : ℤ) ∣ a * x - b * w - c * z + d * y :=
  --       (CharP.int_cast_eq_zero_iff (ZMod m) m _).1 <| by push_cast ; ring
  --     have haybzcwdx : ((m : ℕ) : ℤ) ∣ a * y + b * z - c * w - d * x :=
  --       (CharP.int_cast_eq_zero_iff (ZMod m) m _).1 <| by push_cast ; ring
  --     have hazbycxdw : ((m : ℕ) : ℤ) ∣ a * z - b * y + c * x - d * w :=
  --       (CharP.int_cast_eq_zero_iff (ZMod m) m _).1 <| by push_cast ; ring
  --     let ⟨s, hs⟩ := hawbxcydz
  --     let ⟨t, ht⟩ := haxbwczdy
  --     let ⟨u, hu⟩ := haybzcwdx
  --     let ⟨v, hv⟩ := hazbycxdw
  --     have hn_nonneg : 0 ≤ n :=
  --       nonneg_of_mul_nonneg_right
  --         (by erw [← hn]; repeat' try refine' add_nonneg _ _; try exact sq_nonneg _)
  --         (Int.coe_nat_pos.2 <| NeZero.pos m)
  --     have hnm : n.natAbs < m :=
  --       Int.ofNat_lt.1
  --         (lt_of_mul_lt_mul_left (by rw [Int.natAbs_of_nonneg hn_nonneg, ← hn, ← sq]; exact hwxyzlt)
  --           (Int.coe_nat_nonneg m))
  --     have hstuv : s ^ 2 + t ^ 2 + u ^ 2 + v ^ 2 = n.natAbs * p :=
  --       (mul_right_inj'
  --             (show (m ^ 2 : ℤ) ≠ 0 from pow_ne_zero 2 (Int.coe_nat_ne_zero.2 hm0.1))).1 <|
  --         calc
  --           (m : ℤ) ^ 2 * (s ^ 2 + t ^ 2 + u ^ 2 + v ^ 2) =
  --               ((m : ℕ) * s) ^ 2 + ((m : ℕ) * t) ^ 2 + ((m : ℕ) * u) ^ 2 + ((m : ℕ) * v) ^ 2 :=
  --             by simp [mul_pow]; ring
  --           _ = (w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2) * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
  --             simp only [hs.symm, ht.symm, hu.symm, hv.symm]; ring
  --           _ = _ := by rw [hn, habcd, Int.natAbs_of_nonneg hn_nonneg]; dsimp [m]; ring
            
  --     False.elim <| Nat.find_min hm hnm ⟨lt_trans hnm hmp, hn0, s, t, u, v, hstuv⟩

/-- **Four squares theorem** -/
theorem sum_four_squares : ∀ n : ℕ, ∃ a b c d : ℕ, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = n
  | 0 => ⟨0, 0, 0, 0, rfl⟩
  | 1 => ⟨1, 0, 0, 0, rfl⟩
  | n@(k + 2) =>
    have hm : Fact (minFac (k + 2)).Prime := ⟨minFac_prime (by decide)⟩
    have : n / minFac n < n := factors_lemma
    let ⟨a, b, c, d, h₁⟩ :=
      show ∃ a b c d : ℤ, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = minFac n from
        prime_sum_four_squares (min_fac (k + 2))
    let ⟨w, x, y, z, h₂⟩ := sum_four_squares (n / minFac n)
    ⟨(a * w - b * x - c * y - d * z).natAbs, (a * x + b * w + c * z - d * y).natAbs,
      (a * y - b * z + c * w + d * x).natAbs, (a * z + b * y - c * x + d * w).natAbs, by
      rw [← Int.coe_nat_inj', ← Nat.mul_div_cancel' (min_fac_dvd (k + 2)), Int.ofNat_mul, ← h₁, ←
        h₂]
      simp [sum_four_sq_mul_sum_four_sq]⟩
#align nat.sum_four_squares Nat.sum_four_squares

end Nat
