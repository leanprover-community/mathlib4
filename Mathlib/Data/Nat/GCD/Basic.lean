/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
import Batteries.Data.Nat.Gcd
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

assert_not_exists OrderedCommMonoid

namespace Nat
variable {a a₁ a₂ b b₁ b₂ c : ℕ}

/-! ### `gcd` -/

theorem gcd_greatest {a b d : ℕ} (hda : d ∣ a) (hdb : d ∣ b) (hd : ∀ e : ℕ, e ∣ a → e ∣ b → e ∣ d) :
    d = a.gcd b :=
  (dvd_antisymm (hd _ (gcd_dvd_left a b) (gcd_dvd_right a b)) (dvd_gcd hda hdb)).symm

/-! Lemmas where one argument consists of addition of a multiple of the other -/

@[simp]
theorem gcd_add_mul_right_right (m n k : ℕ) : gcd m (n + k * m) = gcd m n := by
  simp [gcd_rec m (n + k * m), gcd_rec m n]

@[simp]
theorem gcd_add_mul_left_right (m n k : ℕ) : gcd m (n + m * k) = gcd m n := by
  simp [gcd_rec m (n + m * k), gcd_rec m n]

@[simp]
theorem gcd_mul_right_add_right (m n k : ℕ) : gcd m (k * m + n) = gcd m n := by simp [add_comm _ n]

@[simp]
theorem gcd_mul_left_add_right (m n k : ℕ) : gcd m (m * k + n) = gcd m n := by simp [add_comm _ n]

@[simp]
theorem gcd_add_mul_right_left (m n k : ℕ) : gcd (m + k * n) n = gcd m n := by
  rw [gcd_comm, gcd_add_mul_right_right, gcd_comm]

@[simp]
theorem gcd_add_mul_left_left (m n k : ℕ) : gcd (m + n * k) n = gcd m n := by
  rw [gcd_comm, gcd_add_mul_left_right, gcd_comm]

@[simp]
theorem gcd_mul_right_add_left (m n k : ℕ) : gcd (k * n + m) n = gcd m n := by
  rw [gcd_comm, gcd_mul_right_add_right, gcd_comm]

@[simp]
theorem gcd_mul_left_add_left (m n k : ℕ) : gcd (n * k + m) n = gcd m n := by
  rw [gcd_comm, gcd_mul_left_add_right, gcd_comm]

/-! Lemmas where one argument consists of an addition of the other -/

@[simp]
theorem gcd_add_self_right (m n : ℕ) : gcd m (n + m) = gcd m n :=
  Eq.trans (by rw [one_mul]) (gcd_add_mul_right_right m n 1)

@[simp]
theorem gcd_add_self_left (m n : ℕ) : gcd (m + n) n = gcd m n := by
  rw [gcd_comm, gcd_add_self_right, gcd_comm]

@[simp]
theorem gcd_self_add_left (m n : ℕ) : gcd (m + n) m = gcd n m := by rw [add_comm, gcd_add_self_left]

@[simp]
theorem gcd_self_add_right (m n : ℕ) : gcd m (m + n) = gcd m n := by
  rw [add_comm, gcd_add_self_right]

/-! Lemmas where one argument consists of a subtraction of the other -/

@[simp]
theorem gcd_sub_self_left {m n : ℕ} (h : m ≤ n) : gcd (n - m) m = gcd n m := by
  calc
    gcd (n - m) m = gcd (n - m + m) m := by rw [← gcd_add_self_left (n - m) m]
                _ = gcd n m := by rw [Nat.sub_add_cancel h]

@[simp]
theorem gcd_sub_self_right {m n : ℕ} (h : m ≤ n) : gcd m (n - m) = gcd m n := by
  rw [gcd_comm, gcd_sub_self_left h, gcd_comm]

@[simp]
theorem gcd_self_sub_left {m n : ℕ} (h : m ≤ n) : gcd (n - m) n = gcd m n := by
  have := Nat.sub_add_cancel h
  rw [gcd_comm m n, ← this, gcd_add_self_left (n - m) m]
  have : gcd (n - m) n = gcd (n - m) m := by
    nth_rw 2 [← Nat.add_sub_cancel' h]
    rw [gcd_add_self_right, gcd_comm]
  convert this

@[simp]
theorem gcd_self_sub_right {m n : ℕ} (h : m ≤ n) : gcd n (n - m) = gcd n m := by
  rw [gcd_comm, gcd_self_sub_left h, gcd_comm]

/-! ### `lcm` -/

theorem lcm_dvd_mul (m n : ℕ) : lcm m n ∣ m * n :=
  lcm_dvd (dvd_mul_right _ _) (dvd_mul_left _ _)

theorem lcm_dvd_iff {m n k : ℕ} : lcm m n ∣ k ↔ m ∣ k ∧ n ∣ k :=
  ⟨fun h => ⟨(dvd_lcm_left _ _).trans h, (dvd_lcm_right _ _).trans h⟩, and_imp.2 lcm_dvd⟩

theorem lcm_pos {m n : ℕ} : 0 < m → 0 < n → 0 < m.lcm n := by
  simp_rw [Nat.pos_iff_ne_zero]
  exact lcm_ne_zero

theorem lcm_mul_left {m n k : ℕ} : (m * n).lcm (m * k) = m * n.lcm k := by
  apply dvd_antisymm
  · exact lcm_dvd (mul_dvd_mul_left m (dvd_lcm_left n k)) (mul_dvd_mul_left m (dvd_lcm_right n k))
  · have h : m ∣ lcm (m * n) (m * k) := (dvd_mul_right m n).trans (dvd_lcm_left (m * n) (m * k))
    rw [← dvd_div_iff_mul_dvd h, lcm_dvd_iff, dvd_div_iff_mul_dvd h, dvd_div_iff_mul_dvd h,
      ← lcm_dvd_iff]

theorem lcm_mul_right {m n k : ℕ} : (m * n).lcm (k * n) = m.lcm k * n := by
 rw [mul_comm, mul_comm k n, lcm_mul_left, mul_comm]

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

/-- Represent a divisor of `m * n` as a product of a divisor of `m` and a divisor of `n`.

See `exists_dvd_and_dvd_of_dvd_mul` for the more general but less constructive version for other
`GCDMonoid`s. -/
def prodDvdAndDvdOfDvdProd {m n k : ℕ} (H : k ∣ m * n) :
    { d : { m' // m' ∣ m } × { n' // n' ∣ n } // k = d.1 * d.2 } := by
  cases h0 : gcd k m with
  | zero =>
    obtain rfl : k = 0 := eq_zero_of_gcd_eq_zero_left h0
    obtain rfl : m = 0 := eq_zero_of_gcd_eq_zero_right h0
    exact ⟨⟨⟨0, dvd_refl 0⟩, ⟨n, dvd_refl n⟩⟩, (zero_mul n).symm⟩
  | succ tmp =>
    have hpos : 0 < gcd k m := h0.symm ▸ Nat.zero_lt_succ _; clear h0 tmp
    have hd : gcd k m * (k / gcd k m) = k := Nat.mul_div_cancel' (gcd_dvd_left k m)
    refine ⟨⟨⟨gcd k m, gcd_dvd_right k m⟩, ⟨k / gcd k m, ?_⟩⟩, hd.symm⟩
    apply Nat.dvd_of_mul_dvd_mul_left hpos
    rw [hd, ← gcd_mul_right]
    exact dvd_gcd (dvd_mul_right _ _) H

theorem dvd_mul {x m n : ℕ} : x ∣ m * n ↔ ∃ y z, y ∣ m ∧ z ∣ n ∧ y * z = x := by
  constructor
  · intro h
    obtain ⟨⟨⟨y, hy⟩, ⟨z, hz⟩⟩, rfl⟩ := prod_dvd_and_dvd_of_dvd_prod h
    exact ⟨y, z, hy, hz, rfl⟩
  · rintro ⟨y, z, hy, hz, rfl⟩
    exact mul_dvd_mul hy hz

theorem pow_dvd_pow_iff {a b n : ℕ} (n0 : n ≠ 0) : a ^ n ∣ b ^ n ↔ a ∣ b := by
  refine ⟨fun h => ?_, fun h => pow_dvd_pow_of_dvd h _⟩
  rcases Nat.eq_zero_or_pos (gcd a b) with g0 | g0
  · simp [eq_zero_of_gcd_eq_zero_right g0]
  rcases exists_coprime' g0 with ⟨g, a', b', g0', co, rfl, rfl⟩
  rw [mul_pow, mul_pow] at h
  replace h := Nat.dvd_of_mul_dvd_mul_right (Nat.pow_pos g0') h
  have := pow_dvd_pow a' <| Nat.pos_of_ne_zero n0
  rw [pow_one, (co.pow n n).eq_one_of_dvd h] at this
  simp [eq_one_of_dvd_one this]

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

variable {x n m : ℕ}

theorem dvd_gcd_mul_iff_dvd_mul : x ∣ gcd x n * m ↔ x ∣ n * m := by
  refine ⟨(·.trans <| mul_dvd_mul_right (x.gcd_dvd_right n) m), fun ⟨y, hy⟩ ↦ ?_⟩
  rw [← gcd_mul_right, hy, gcd_mul_left]
  exact dvd_mul_right x (gcd m y)

theorem dvd_mul_gcd_iff_dvd_mul : x ∣ n * gcd x m ↔ x ∣ n * m := by
  rw [mul_comm, dvd_gcd_mul_iff_dvd_mul, mul_comm]

theorem dvd_gcd_mul_gcd_iff_dvd_mul : x ∣ gcd x n * gcd x m ↔ x ∣ n * m := by
  rw [dvd_gcd_mul_iff_dvd_mul, dvd_mul_gcd_iff_dvd_mul]

theorem gcd_mul_gcd_eq_iff_dvd_mul_of_coprime (hcop : Coprime n m) :
    gcd x n * gcd x m = x ↔ x ∣ n * m := by
  refine ⟨fun h ↦ ?_, (dvd_antisymm ?_ <| dvd_gcd_mul_gcd_iff_dvd_mul.mpr ·)⟩
  refine h ▸ Nat.mul_dvd_mul ?_ ?_ <;> exact x.gcd_dvd_right _
  refine (hcop.gcd_both x x).mul_dvd_of_dvd_of_dvd ?_ ?_ <;> exact x.gcd_dvd_left _

end Nat
