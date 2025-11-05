/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
import Mathlib.Algebra.Group.Nat.Units
import Mathlib.Algebra.GroupWithZero.Divisibility
import Mathlib.Algebra.GroupWithZero.Nat

/-!
# Properties of `Nat.gcd`, `Nat.lcm`, and `Nat.Coprime`

Definitions are provided in batteries.

Generalizations of these are provided in a later file as `GCDMonoid.gcd` and
`GCDMonoid.lcm`.

Note that the global `IsCoprime` is not a straightforward generalization of `Nat.Coprime`, see
`Nat.isCoprime_iff_coprime` for the connection between the two.

Most of this file could be moved to batteries as well.
-/

assert_not_exists IsOrderedMonoid

namespace Nat
variable {a a₁ a₂ b b₁ b₂ c : ℕ}

/-! ### `gcd` -/

theorem gcd_greatest {a b d : ℕ} (hda : d ∣ a) (hdb : d ∣ b) (hd : ∀ e : ℕ, e ∣ a → e ∣ b → e ∣ d) :
    d = a.gcd b :=
  (dvd_antisymm (hd _ (gcd_dvd_left a b) (gcd_dvd_right a b)) (dvd_gcd hda hdb)).symm

/-! Lemmas where one argument consists of addition of a multiple of the other -/

@[simp]
theorem pow_sub_one_mod_pow_sub_one (a b c : ℕ) : (a ^ c - 1) % (a ^ b - 1) = a ^ (c % b) - 1 := by
  rcases eq_zero_or_pos a with rfl | ha0
  · simp [zero_pow_eq]; split_ifs <;> simp
  rcases Nat.eq_or_lt_of_le ha0 with rfl | ha1
  · simp
  rcases eq_zero_or_pos b with rfl | hb0
  · simp
  rcases lt_or_ge c b with h | h
  · rw [mod_eq_of_lt, mod_eq_of_lt h]
    rwa [Nat.sub_lt_sub_iff_right (one_le_pow c a ha0), Nat.pow_lt_pow_iff_right ha1]
  · suffices a ^ (c - b + b) - 1 = a ^ (c - b) * (a ^ b - 1) + (a ^ (c - b) - 1) by
      rw [← Nat.sub_add_cancel h, add_mod_right, this, add_mod, mul_mod, mod_self,
        mul_zero, zero_mod, zero_add, mod_mod, pow_sub_one_mod_pow_sub_one]
    rw [← Nat.add_sub_assoc (one_le_pow (c - b) a ha0), ← mul_add_one, pow_add,
      Nat.sub_add_cancel (one_le_pow b a ha0)]

@[simp]
theorem pow_sub_one_gcd_pow_sub_one (a b c : ℕ) :
    gcd (a ^ b - 1) (a ^ c - 1) = a ^ gcd b c - 1 := by
  rcases eq_zero_or_pos b with rfl | hb
  · simp
  replace hb : c % b < b := mod_lt c hb
  rw [gcd_rec, pow_sub_one_mod_pow_sub_one, pow_sub_one_gcd_pow_sub_one, ← gcd_rec]

/-! ### `lcm` and divisibility -/

theorem dvd_lcm_of_dvd_left (h : a ∣ b) (c : ℕ) : a ∣ lcm b c :=
  h.trans (dvd_lcm_left b c)

alias Dvd.dvd.nat_lcm_right := dvd_lcm_of_dvd_left

theorem dvd_of_lcm_right_dvd {a b c : ℕ} (h : lcm a b ∣ c) : a ∣ c :=
  (dvd_lcm_left a b).trans h

theorem dvd_lcm_of_dvd_right {a b : ℕ} (h : a ∣ b) (c : ℕ) : a ∣ lcm c b :=
  h.trans (dvd_lcm_right c b)

alias Dvd.dvd.nat_lcm_left := dvd_lcm_of_dvd_right

theorem dvd_of_lcm_left_dvd {a b c : ℕ} (h : lcm a b ∣ c) : b ∣ c :=
  (dvd_lcm_right a b).trans h

/-!
### `Coprime`

See also `Nat.coprime_of_dvd` and `Nat.coprime_of_dvd'` to prove `Nat.Coprime m n`.
-/

theorem Coprime.lcm_eq_mul {m n : ℕ} (h : Coprime m n) : lcm m n = m * n := by
  rw [← one_mul (lcm m n), ← h.gcd_eq_one, gcd_mul_lcm]

theorem Coprime.symmetric : Symmetric Coprime := fun _ _ => Coprime.symm

theorem Coprime.dvd_mul_right {m n k : ℕ} (H : Coprime k n) : k ∣ m * n ↔ k ∣ m :=
  ⟨H.dvd_of_dvd_mul_right, fun h => dvd_mul_of_dvd_left h n⟩

theorem Coprime.dvd_mul_left {m n k : ℕ} (H : Coprime k m) : k ∣ m * n ↔ k ∣ n :=
  ⟨H.dvd_of_dvd_mul_left, fun h => dvd_mul_of_dvd_right h m⟩

@[simp]
theorem coprime_add_self_right {m n : ℕ} : Coprime m (n + m) ↔ Coprime m n := by
  rw [Coprime, Coprime, gcd_add_self_right]

@[simp]
theorem coprime_self_add_right {m n : ℕ} : Coprime m (m + n) ↔ Coprime m n := by
  rw [add_comm, coprime_add_self_right]

@[simp]
theorem coprime_add_self_left {m n : ℕ} : Coprime (m + n) n ↔ Coprime m n := by
  rw [Coprime, Coprime, gcd_add_self_left]

@[simp]
theorem coprime_self_add_left {m n : ℕ} : Coprime (m + n) m ↔ Coprime n m := by
  rw [Coprime, Coprime, gcd_self_add_left]

@[simp]
theorem coprime_add_mul_right_right (m n k : ℕ) : Coprime m (n + k * m) ↔ Coprime m n := by
  rw [Coprime, Coprime, gcd_add_mul_right_right]

@[simp]
theorem coprime_add_mul_left_right (m n k : ℕ) : Coprime m (n + m * k) ↔ Coprime m n := by
  rw [Coprime, Coprime, gcd_add_mul_left_right]

@[simp]
theorem coprime_mul_right_add_right (m n k : ℕ) : Coprime m (k * m + n) ↔ Coprime m n := by
  rw [Coprime, Coprime, gcd_mul_right_add_right]

@[simp]
theorem coprime_mul_left_add_right (m n k : ℕ) : Coprime m (m * k + n) ↔ Coprime m n := by
  rw [Coprime, Coprime, gcd_mul_left_add_right]

@[simp]
theorem coprime_add_mul_right_left (m n k : ℕ) : Coprime (m + k * n) n ↔ Coprime m n := by
  rw [Coprime, Coprime, gcd_add_mul_right_left]

@[simp]
theorem coprime_add_mul_left_left (m n k : ℕ) : Coprime (m + n * k) n ↔ Coprime m n := by
  rw [Coprime, Coprime, gcd_add_mul_left_left]

@[simp]
theorem coprime_mul_right_add_left (m n k : ℕ) : Coprime (k * n + m) n ↔ Coprime m n := by
  rw [Coprime, Coprime, gcd_mul_right_add_left]

@[simp]
theorem coprime_mul_left_add_left (m n k : ℕ) : Coprime (n * k + m) n ↔ Coprime m n := by
  rw [Coprime, Coprime, gcd_mul_left_add_left]

lemma add_coprime_iff_left (h : c ∣ b) : Coprime (a + b) c ↔ Coprime a c := by
  obtain ⟨n, rfl⟩ := h; simp

lemma add_coprime_iff_right (h : c ∣ a) : Coprime (a + b) c ↔ Coprime b c := by
  obtain ⟨n, rfl⟩ := h; simp

lemma coprime_add_iff_left (h : a ∣ c) : Coprime a (b + c) ↔ Coprime a b := by
  obtain ⟨n, rfl⟩ := h; simp

lemma coprime_add_iff_right (h : a ∣ b) : Coprime a (b + c) ↔ Coprime a c := by
  obtain ⟨n, rfl⟩ := h; simp

-- TODO: Replace `Nat.Coprime.coprime_dvd_left`
lemma Coprime.of_dvd_left (ha : a₁ ∣ a₂) (h : Coprime a₂ b) : Coprime a₁ b := h.coprime_dvd_left ha

-- TODO: Replace `Nat.Coprime.coprime_dvd_right`
lemma Coprime.of_dvd_right (hb : b₁ ∣ b₂) (h : Coprime a b₂) : Coprime a b₁ :=
  h.coprime_dvd_right hb

lemma Coprime.of_dvd (ha : a₁ ∣ a₂) (hb : b₁ ∣ b₂) (h : Coprime a₂ b₂) : Coprime a₁ b₁ :=
  (h.of_dvd_left ha).of_dvd_right hb

@[simp]
theorem coprime_sub_self_left {m n : ℕ} (h : m ≤ n) : Coprime (n - m) m ↔ Coprime n m := by
  rw [Coprime, Coprime, gcd_sub_self_left h]

@[simp]
theorem coprime_sub_self_right {m n : ℕ} (h : m ≤ n) : Coprime m (n - m) ↔ Coprime m n := by
  rw [Coprime, Coprime, gcd_sub_self_right h]

@[simp]
theorem coprime_self_sub_left {m n : ℕ} (h : m ≤ n) : Coprime (n - m) n ↔ Coprime m n := by
  rw [Coprime, Coprime, gcd_self_sub_left h]

@[simp]
theorem coprime_self_sub_right {m n : ℕ} (h : m ≤ n) : Coprime n (n - m) ↔ Coprime n m := by
  rw [Coprime, Coprime, gcd_self_sub_right h]

@[simp]
theorem coprime_pow_left_iff {n : ℕ} (hn : 0 < n) (a b : ℕ) :
    Nat.Coprime (a ^ n) b ↔ Nat.Coprime a b := by
  obtain ⟨n, rfl⟩ := exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [Nat.pow_succ, Nat.coprime_mul_iff_left]
  exact ⟨And.right, fun hab => ⟨hab.pow_left _, hab⟩⟩

@[simp]
theorem coprime_pow_right_iff {n : ℕ} (hn : 0 < n) (a b : ℕ) :
    Nat.Coprime a (b ^ n) ↔ Nat.Coprime a b := by
  rw [Nat.coprime_comm, coprime_pow_left_iff hn, Nat.coprime_comm]

theorem not_coprime_zero_zero : ¬Coprime 0 0 := by simp

theorem coprime_one_left_iff (n : ℕ) : Coprime 1 n ↔ True := by simp [Coprime]

theorem coprime_one_right_iff (n : ℕ) : Coprime n 1 ↔ True := by simp [Coprime]

theorem gcd_mul_of_coprime_of_dvd {a b c : ℕ} (hac : Coprime a c) (b_dvd_c : b ∣ c) :
    gcd (a * b) c = b := by
  rcases exists_eq_mul_left_of_dvd b_dvd_c with ⟨d, rfl⟩
  rw [gcd_mul_right]
  convert one_mul b
  exact Coprime.coprime_mul_right_right hac

theorem Coprime.eq_of_mul_eq_zero {m n : ℕ} (h : m.Coprime n) (hmn : m * n = 0) :
    m = 0 ∧ n = 1 ∨ m = 1 ∧ n = 0 :=
  (Nat.mul_eq_zero.mp hmn).imp (fun hm => ⟨hm, n.coprime_zero_left.mp <| hm ▸ h⟩) fun hn =>
    let eq := hn ▸ h.symm
    ⟨m.coprime_zero_left.mp <| eq, hn⟩

theorem coprime_iff_isRelPrime {m n : ℕ} : m.Coprime n ↔ IsRelPrime m n := by
  simp_rw [coprime_iff_gcd_eq_one, IsRelPrime, ← and_imp, ← dvd_gcd_iff, isUnit_iff_dvd_one]
  exact ⟨fun h _ ↦ (h ▸ ·), (dvd_one.mp <| · dvd_rfl)⟩

/-- If `k:ℕ` divides coprime `a` and `b` then `k = 1` -/
theorem eq_one_of_dvd_coprimes {a b k : ℕ} (h_ab_coprime : Coprime a b) (hka : k ∣ a)
    (hkb : k ∣ b) : k = 1 :=
  dvd_one.mp (isUnit_iff_dvd_one.mp <| coprime_iff_isRelPrime.mp h_ab_coprime hka hkb)

theorem Coprime.mul_add_mul_ne_mul {m n a b : ℕ} (cop : Coprime m n) (ha : a ≠ 0) (hb : b ≠ 0) :
    a * m + b * n ≠ m * n := by
  intro h
  obtain ⟨x, rfl⟩ : n ∣ a :=
    cop.symm.dvd_of_dvd_mul_right
      ((Nat.dvd_add_iff_left (Nat.dvd_mul_left n b)).mpr
        ((congr_arg _ h).mpr (Nat.dvd_mul_left n m)))
  obtain ⟨y, rfl⟩ : m ∣ b :=
    cop.dvd_of_dvd_mul_right
      ((Nat.dvd_add_iff_right (Nat.dvd_mul_left m (n * x))).mpr
        ((congr_arg _ h).mpr (Nat.dvd_mul_right m n)))
  rw [mul_comm, mul_ne_zero_iff, ← one_le_iff_ne_zero] at ha hb
  refine mul_ne_zero hb.2 ha.2 (eq_zero_of_mul_eq_self_left (ne_of_gt (add_le_add ha.1 hb.1)) ?_)
  rw [← mul_assoc, ← h, Nat.add_mul, Nat.add_mul, mul_comm _ n, ← mul_assoc, mul_comm y]

variable {x n m k : ℕ}

theorem gcd_mul_gcd_eq_iff_dvd_mul_of_coprime (hcop : Coprime n m) :
    gcd x n * gcd x m = x ↔ x ∣ n * m := by
  refine ⟨fun h ↦ ?_, (dvd_antisymm ?_ <| dvd_gcd_mul_gcd_iff_dvd_mul.mpr ·)⟩
  refine h ▸ Nat.mul_dvd_mul ?_ ?_ <;> exact x.gcd_dvd_right _
  refine (hcop.gcd_both x x).mul_dvd_of_dvd_of_dvd ?_ ?_ <;> exact x.gcd_dvd_left _

lemma div_mul_div (hkm : m ∣ k) (hkn : n ∣ m) : (k / m) * (m / n) = k / n := by
  rcases n.eq_zero_or_pos with hn | hn
  · simp [hn]
  refine (Nat.div_eq_of_eq_mul_left hn ?_).symm
  rw [mul_assoc, Nat.div_mul_cancel hkn, Nat.div_mul_cancel hkm]

lemma div_dvd_div_left (hkm : m ∣ k) (hkn : n ∣ m) : k / m ∣ k / n :=
  ⟨_, (div_mul_div hkm hkn).symm⟩

lemma div_lcm_eq_div_gcd (hkm : m ∣ k) (hkn : n ∣ k) : (k / m).lcm (k / n) = k / (m.gcd n) := by
  rw [Nat.lcm_eq_iff]
  refine ⟨div_dvd_div_left hkm (Nat.gcd_dvd_left m n),
        div_dvd_div_left hkn (Nat.gcd_dvd_right m n), fun c hmc hnc ↦ ?_⟩
  rcases m.eq_zero_or_pos with hm | hm
  · simp_all
  rcases n.eq_zero_or_pos with hn | hn
  · simp_all
  rw [Nat.div_dvd_iff_dvd_mul hkm hm] at hmc
  rw [Nat.div_dvd_iff_dvd_mul hkn hn] at hnc
  simpa [Nat.div_dvd_iff_dvd_mul (Nat.dvd_trans (Nat.gcd_dvd_left m n) hkm)
    (gcd_pos_of_pos_left n hm), Nat.gcd_mul_right m c n] using (Nat.dvd_gcd hmc hnc)

end Nat
