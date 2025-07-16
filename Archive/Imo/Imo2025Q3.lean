import Mathlib

/-! Following https://www.youtube.com/watch?v=vPqUTG4CW8w -/

open Nat

/- We allow the function to have a value at 0, but without conditions on it. -/
def Bonza (f : ℕ → ℕ) : Prop :=
  (∀ {a}, a ≠ 0 → f a ≠ 0) ∧ ∀ {a b : ℕ}, a ≠ 0 → b ≠ 0 → (f a : ℤ) ∣ b ^ a - f b ^ f a

section Basic

lemma Int.self_modEq_zero (a : ℤ) : a ≡ 0 [ZMOD a] := Int.dvd_refl _ |>.modEq_zero_int
lemma Nat.self_modEq_zero (a : ℕ) : a ≡ 0 [MOD a] := Nat.dvd_refl _ |>.modEq_zero_nat

lemma padicValNat_mono {p a b : ℕ} [Fact p.Prime] (hb : b ≠ 0) (h : a ∣ b) :
    padicValNat p a ≤ padicValNat p b := by
  rw [← padicValNat_dvd_iff_le hb]
  exact pow_padicValNat_dvd.trans h

-- lemma Int.ModEq.pow_prime {p : ℕ} (hp : p.Prime) (n : ℤ) : n ^ p ≡ n [ZMOD p] := by
--   by_cases hpn : IsCoprime n p
--   · calc
--       n ^ p = n ^ ((p - 1) + 1) := by congr; exact (succ_pred_prime hp).symm
--       _ = n ^ (p - 1) * n := by rfl
--       _ ≡ 1 * n [ZMOD p] := by gcongr; exact pow_card_sub_one_eq_one hp hpn
--       _ = n := by rw [one_mul]

lemma Nat.ModEq.pow_sub_one {p : ℕ} (hp : p.Prime) {n : ℕ} (hpn : n.Coprime p) :
    n ^ (p - 1) ≡ 1 [MOD p] := by
  rw [← isCoprime_iff_coprime] at hpn
  rw [← Int.natCast_modEq_iff]
  exact_mod_cast Int.ModEq.pow_card_sub_one_eq_one hp hpn

lemma Nat.ModEq.pow_prime {p : ℕ} (hp : p.Prime) {n : ℕ} : n ^ p ≡ n [MOD p] := by
  by_cases hpn : n.Coprime p
  · calc
      n ^ p = n ^ ((p - 1) + 1) := by congr; exact (succ_pred_prime hp).symm
      _ = n ^ (p - 1) * n := by rfl
      _ ≡ 1 * n [MOD p] := by gcongr; exact pow_sub_one hp hpn
      _ = n := by rw [one_mul]
  rw [Nat.coprime_comm, ← Nat.Prime.dvd_iff_not_coprime hp] at hpn
  grw [hpn.modEq_zero_nat, zero_pow hp.ne_zero]

lemma Nat.ModEq.pow_prime_pow {p : ℕ} (hp : p.Prime) {n k : ℕ} : n ^ p ^ k ≡ n [MOD p] := by
  induction k with
  | zero => simp [Nat.ModEq.rfl]
  | succ k ih => grw [pow_succ, pow_mul, ih, Nat.ModEq.pow_prime hp]

lemma Nat.modEq_iff_dvd_dist {a b n : ℕ} : a ≡ b [MOD n] ↔ n ∣ a.dist b := by
  obtain h|h := le_total a b
  · simp [h, Nat.modEq_iff_dvd', Nat.dist_eq_sub_of_le]
  simp [dist_comm a b, ModEq.comm (a := a), h, Nat.modEq_iff_dvd', Nat.dist_eq_sub_of_le]

lemma Nat.dist_le_of_modEq {a b n : ℕ} (h : a ≡ b [MOD n]) (hab : a ≠ b) : n ≤ a.dist b := by
  rw [Nat.modEq_iff_dvd_dist] at h
  exact Nat.le_of_dvd (Nat.dist_pos_of_ne hab) h

-- to Mathlib.NumberTheory.LSeries.PrimesInAP
lemma Nat.forall_exists_prime_gt_and_modEq {q a n : ℕ} (hq : q ≠ 0) (h : a.Coprime q) :
    ∃ p > n, Prime p ∧ p ≡ a [MOD q] := by
  have : NeZero q := ⟨hq⟩
  have : IsUnit (a : ZMod q) := (ZMod.isUnit_iff_coprime a q).mpr h
  simp_rw [← ZMod.natCast_eq_natCast_iff]
  exact forall_exists_prime_gt_and_eq_mod this n

lemma two_pow_dvd_three_pow_sub_one (k : ℕ) : 2 ^ (k + 2) ∣ 3 ^ 2 ^ k - 1 := by sorry

lemma not_two_pow_dvd_three_pow_sub_one (k : ℕ) : ¬ 2 ^ (k + 3) ∣ 3 ^ 2 ^ k - 1 := by sorry

lemma padicValNat_two_three_pow_pow_sub_one {k : ℕ} :
    padicValNat 2 (3 ^ 2 ^ k - 1) = k + 2 := by
  sorry

lemma Odd.padicValNat_two_three_pow_mul_pow_sub_one {k m : ℕ} (hm : Odd m) :
    padicValNat 2 (3 ^ (m * 2 ^ k) - 1) = k + 2 := by
  sorry

end Basic

namespace Bonza

variable {f : ℕ → ℕ} (hf : Bonza f) {a b n p q p₀ q₀ : ℕ}
  [hp : Fact p.Prime] [hq : Fact q.Prime] [hp₀ : Fact p₀.Prime] [hq₀ : Fact q₀.Prime]
include hf

lemma ne_zero (ha : a ≠ 0) : f a ≠ 0 :=
  hf.1 ha

lemma zdvd (ha : a ≠ 0) (hb : b ≠ 0) : (f a : ℤ) ∣ b ^ a - f b ^ f a :=
  hf.2 ha hb

lemma zmodEq (ha : a ≠ 0) (hb : b ≠ 0) : f b ^ f a ≡ b ^ a [ZMOD f a] :=
  Int.modEq_iff_dvd.mpr (hf.zdvd ha hb)

lemma modEq (ha : a ≠ 0) (hb : b ≠ 0) : f b ^ f a ≡ b ^ a [MOD f a] := by
  rw [← Int.natCast_modEq_iff]
  exact_mod_cast hf.zmodEq ha hb

lemma div_pow_self (ha : a ≠ 0) : f a ∣ a ^ a := by
  have h1 := hf.modEq ha ha
  nth_grw 2 [Nat.self_modEq_zero (f a)] at h1
  rw [zero_pow (hf.ne_zero ha)] at h1
  exact dvd_of_mod_eq_zero h1.symm

-- lemma div_pow_self (ha : a ≠ 0) : f a ∣ a ^ a := by exact_mod_cast hf.zdiv_pow_self ha

def c (f : ℕ → ℕ) (p : ℕ) := if p.Prime then padicValNat p (f p) else padicValNat 2 (f p)

variable (p) in
lemma eq_pow_c : f p = p ^ c f p := by
  have h1 : f p ∣ p ^ p := hf.div_pow_self hp.out.ne_zero
  obtain ⟨k, hk, h2k⟩ := Nat.dvd_prime_pow hp.out |>.mp h1
  simp [c, h2k, hp.out]

lemma c_le : c f p ≤ p := by
  have := hp.out.ne_zero
  calc
    c f p = padicValNat p (f p) := by simp [c, hp.out]
    _ ≤ padicValNat p (p ^ p) :=
        padicValNat_mono (by positivity) (hf.div_pow_self this)
    _ = p := by simp

lemma dvd_iff_c_ne_zero : p ∣ f p ↔ c f p ≠ 0 := by
  simp [c, hp.out, hp.out.ne_one, hf.ne_zero, hp.out.ne_zero]

lemma eq_one_iff_c_eq_zero : f p = 1 ↔ c f p = 0 := by
  simp [hf.eq_pow_c, hp.out.ne_one]

lemma f_eq_one (case1 : ∀ p : ℕ, p.Prime → c f p = 0) (ha : a ≠ 0) : f a = 1 := by
  by_contra! h2a
  obtain ⟨p, hp, h2p⟩ := exists_prime_and_dvd h2a
  have : Fact p.Prime := ⟨hp⟩
  have := hf.modEq ha hp.ne_zero
  simp [hf.eq_one_iff_c_eq_zero.mpr <| case1 p hp] at this
  have := this.of_dvd h2p
  nth_grw 2 [Nat.self_modEq_zero p] at this
  rw [zero_pow ha] at this
  have := dvd_of_mod_eq_zero this
  simp only [dvd_one] at this
  exact hp.ne_one this

lemma modEq_of_c_ne_zero (hcp : c f p ≠ 0) (hb : b ≠ 0) : f b ^ f p ≡ b ^ p [MOD p] :=
  hf.modEq hp.out.ne_zero hb |>.of_dvd <| hf.dvd_iff_c_ne_zero.mpr hcp

lemma f_eq_self (case2 : { p : ℕ | p.Prime ∧ c f p ≠ 0 }.Infinite) (ha : a ≠ 0) : f a = a := by
  by_contra! h2a
  rw [← Nat.frequently_atTop_iff_infinite] at case2
  obtain ⟨p, hap, hp, hcp⟩ := case2.forall_exists_of_atTop (a.dist (f a) + 1)
  have : Fact p.Prime := ⟨hp⟩
  have := hf.modEq_of_c_ne_zero hcp ha
  grw [hf.eq_pow_c p, Nat.ModEq.pow_prime_pow hp, Nat.ModEq.pow_prime hp] at this
  have := Nat.dist_le_of_modEq this h2a
  rw [ge_iff_le, add_one_le_iff, dist_comm] at hap
  exact this.not_gt hap

variable (case3 : { p : ℕ | p.Prime ∧ c f p ≠ 0 }.Finite)
include case3

lemma eq_2_of_c_ne_zero (h2p : c f p ≠ 0) : p = 2 := by
  have := Nat.infinite_setOf_prime
  -- let q be a prime not in case3
  -- obtain ⟨q, hq, h2q⟩ := case3.infinite_compl.nonempty
  -- have := hf.modEq_of_c_ne_zero h2p hq.out.ne_zero
  -- grw [hf.eq_one_iff_c_eq_zero.mpr h2q, one_pow, Nat.ModEq.pow_prime] at this
  sorry

-- reusing the same function c might not be super nice
lemma eq_two_pow_c (ha : a ≠ 0) : f a = 2 ^ c f a := by
  sorry

lemma eq_one_of_odd (ha : Odd a) : f a = 1 := by
  sorry

lemma two_pow_c_dvd (ha : a ≠ 0) (h2a : Even a) : 2 ^ c f a ∣ 3 ^ a - 1 := by
  sorry

lemma c_le_of_even (ha : a ≠ 0) (h2a : Even a) : c f a ≤ padicValNat 2 a + 2 := by
  sorry

lemma f_le_of_even (ha : a ≠ 0) : f a ≤ 4 * a := by
  sorry


end Bonza

def solution : ℝ := 4

def f4 (n : ℕ) : ℕ := if n = 4 then 16 else if Even n then 2 else 1

lemma bonza_f4 : Bonza f4 := by
  sorry

lemma imo2025_3 :
    solution = sInf { c : ℝ | ∀ f : ℕ → ℕ, ∀ n : ℕ, Bonza f → n ≠ 0 → f n ≤ c * n } := by
  sorry
