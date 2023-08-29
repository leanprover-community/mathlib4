/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
import Mathlib.Algebra.GroupPower.Basic
import Mathlib.Algebra.GroupWithZero.Divisibility
import Mathlib.Data.Nat.Order.Lemmas

#align_import data.nat.gcd.basic from "leanprover-community/mathlib"@"e8638a0fcaf73e4500469f368ef9494e495099b3"

/-!
# Definitions and properties of `Nat.gcd`, `Nat.lcm`, and `Nat.coprime`

Generalizations of these are provided in a later file as `GCDMonoid.gcd` and
`GCDMonoid.lcm`.

Note that the global `IsCoprime` is not a straightforward generalization of `Nat.coprime`, see
`Nat.isCoprime_iff_coprime` for the connection between the two.

-/

namespace Nat

/-! ### `gcd` -/

theorem gcd_greatest {a b d : ℕ} (hda : d ∣ a) (hdb : d ∣ b) (hd : ∀ e : ℕ, e ∣ a → e ∣ b → e ∣ d) :
    d = a.gcd b :=
  (dvd_antisymm (hd _ (gcd_dvd_left a b) (gcd_dvd_right a b)) (dvd_gcd hda hdb)).symm
#align nat.gcd_greatest Nat.gcd_greatest

-- Lemmas where one argument consists of addition of a multiple of the other
@[simp]
theorem gcd_add_mul_right_right (m n k : ℕ) : gcd m (n + k * m) = gcd m n := by
  simp [gcd_rec m (n + k * m), gcd_rec m n]
  -- 🎉 no goals
#align nat.gcd_add_mul_right_right Nat.gcd_add_mul_right_right

@[simp]
theorem gcd_add_mul_left_right (m n k : ℕ) : gcd m (n + m * k) = gcd m n := by
  simp [gcd_rec m (n + m * k), gcd_rec m n]
  -- 🎉 no goals
#align nat.gcd_add_mul_left_right Nat.gcd_add_mul_left_right

@[simp]
theorem gcd_mul_right_add_right (m n k : ℕ) : gcd m (k * m + n) = gcd m n := by simp [add_comm _ n]
                                                                                -- 🎉 no goals
#align nat.gcd_mul_right_add_right Nat.gcd_mul_right_add_right

@[simp]
theorem gcd_mul_left_add_right (m n k : ℕ) : gcd m (m * k + n) = gcd m n := by simp [add_comm _ n]
                                                                               -- 🎉 no goals
#align nat.gcd_mul_left_add_right Nat.gcd_mul_left_add_right

@[simp]
theorem gcd_add_mul_right_left (m n k : ℕ) : gcd (m + k * n) n = gcd m n := by
  rw [gcd_comm, gcd_add_mul_right_right, gcd_comm]
  -- 🎉 no goals
#align nat.gcd_add_mul_right_left Nat.gcd_add_mul_right_left

@[simp]
theorem gcd_add_mul_left_left (m n k : ℕ) : gcd (m + n * k) n = gcd m n := by
  rw [gcd_comm, gcd_add_mul_left_right, gcd_comm]
  -- 🎉 no goals
#align nat.gcd_add_mul_left_left Nat.gcd_add_mul_left_left

@[simp]
theorem gcd_mul_right_add_left (m n k : ℕ) : gcd (k * n + m) n = gcd m n := by
  rw [gcd_comm, gcd_mul_right_add_right, gcd_comm]
  -- 🎉 no goals
#align nat.gcd_mul_right_add_left Nat.gcd_mul_right_add_left

@[simp]
theorem gcd_mul_left_add_left (m n k : ℕ) : gcd (n * k + m) n = gcd m n := by
  rw [gcd_comm, gcd_mul_left_add_right, gcd_comm]
  -- 🎉 no goals
#align nat.gcd_mul_left_add_left Nat.gcd_mul_left_add_left

-- Lemmas where one argument consists of an addition of the other
@[simp]
theorem gcd_add_self_right (m n : ℕ) : gcd m (n + m) = gcd m n :=
  Eq.trans (by rw [one_mul]) (gcd_add_mul_right_right m n 1)
               -- 🎉 no goals
#align nat.gcd_add_self_right Nat.gcd_add_self_right

@[simp]
theorem gcd_add_self_left (m n : ℕ) : gcd (m + n) n = gcd m n := by
  rw [gcd_comm, gcd_add_self_right, gcd_comm]
  -- 🎉 no goals
#align nat.gcd_add_self_left Nat.gcd_add_self_left

@[simp]
theorem gcd_self_add_left (m n : ℕ) : gcd (m + n) m = gcd n m := by rw [add_comm, gcd_add_self_left]
                                                                    -- 🎉 no goals
#align nat.gcd_self_add_left Nat.gcd_self_add_left

@[simp]
theorem gcd_self_add_right (m n : ℕ) : gcd m (m + n) = gcd m n := by
  rw [add_comm, gcd_add_self_right]
  -- 🎉 no goals
#align nat.gcd_self_add_right Nat.gcd_self_add_right

/-! ### `lcm` -/

theorem lcm_dvd_mul (m n : ℕ) : lcm m n ∣ m * n :=
  lcm_dvd (dvd_mul_right _ _) (dvd_mul_left _ _)
#align nat.lcm_dvd_mul Nat.lcm_dvd_mul

theorem lcm_dvd_iff {m n k : ℕ} : lcm m n ∣ k ↔ m ∣ k ∧ n ∣ k :=
  ⟨fun h => ⟨(dvd_lcm_left _ _).trans h, (dvd_lcm_right _ _).trans h⟩, and_imp.2 lcm_dvd⟩
#align nat.lcm_dvd_iff Nat.lcm_dvd_iff

theorem lcm_pos {m n : ℕ} : 0 < m → 0 < n → 0 < m.lcm n := by
  simp_rw [pos_iff_ne_zero]
  -- ⊢ m ≠ 0 → n ≠ 0 → lcm m n ≠ 0
  exact lcm_ne_zero
  -- 🎉 no goals
#align nat.lcm_pos Nat.lcm_pos

/-!
### `coprime`

See also `Nat.coprime_of_dvd` and `Nat.coprime_of_dvd'` to prove `Nat.coprime m n`.
-/

instance (m n : ℕ) : Decidable (coprime m n) := inferInstanceAs (Decidable (gcd m n = 1))

theorem coprime.lcm_eq_mul {m n : ℕ} (h : coprime m n) : lcm m n = m * n := by
  rw [← one_mul (lcm m n), ← h.gcd_eq_one, gcd_mul_lcm]
  -- 🎉 no goals
#align nat.coprime.lcm_eq_mul Nat.coprime.lcm_eq_mul

theorem coprime.symmetric : Symmetric coprime := fun _ _ => coprime.symm
#align nat.coprime.symmetric Nat.coprime.symmetric

theorem coprime.dvd_mul_right {m n k : ℕ} (H : coprime k n) : k ∣ m * n ↔ k ∣ m :=
  ⟨H.dvd_of_dvd_mul_right, fun h => dvd_mul_of_dvd_left h n⟩
#align nat.coprime.dvd_mul_right Nat.coprime.dvd_mul_right

theorem coprime.dvd_mul_left {m n k : ℕ} (H : coprime k m) : k ∣ m * n ↔ k ∣ n :=
  ⟨H.dvd_of_dvd_mul_left, fun h => dvd_mul_of_dvd_right h m⟩
#align nat.coprime.dvd_mul_left Nat.coprime.dvd_mul_left

@[simp]
theorem coprime_add_self_right {m n : ℕ} : coprime m (n + m) ↔ coprime m n := by
  rw [coprime, coprime, gcd_add_self_right]
  -- 🎉 no goals
#align nat.coprime_add_self_right Nat.coprime_add_self_right

@[simp]
theorem coprime_self_add_right {m n : ℕ} : coprime m (m + n) ↔ coprime m n := by
  rw [add_comm, coprime_add_self_right]
  -- 🎉 no goals
#align nat.coprime_self_add_right Nat.coprime_self_add_right

@[simp]
theorem coprime_add_self_left {m n : ℕ} : coprime (m + n) n ↔ coprime m n := by
  rw [coprime, coprime, gcd_add_self_left]
  -- 🎉 no goals
#align nat.coprime_add_self_left Nat.coprime_add_self_left

@[simp]
theorem coprime_self_add_left {m n : ℕ} : coprime (m + n) m ↔ coprime n m := by
  rw [coprime, coprime, gcd_self_add_left]
  -- 🎉 no goals
#align nat.coprime_self_add_left Nat.coprime_self_add_left

@[simp]
theorem coprime_add_mul_right_right (m n k : ℕ) : coprime m (n + k * m) ↔ coprime m n := by
  rw [coprime, coprime, gcd_add_mul_right_right]
  -- 🎉 no goals
#align nat.coprime_add_mul_right_right Nat.coprime_add_mul_right_right

@[simp]
theorem coprime_add_mul_left_right (m n k : ℕ) : coprime m (n + m * k) ↔ coprime m n := by
  rw [coprime, coprime, gcd_add_mul_left_right]
  -- 🎉 no goals
#align nat.coprime_add_mul_left_right Nat.coprime_add_mul_left_right

@[simp]
theorem coprime_mul_right_add_right (m n k : ℕ) : coprime m (k * m + n) ↔ coprime m n := by
  rw [coprime, coprime, gcd_mul_right_add_right]
  -- 🎉 no goals
#align nat.coprime_mul_right_add_right Nat.coprime_mul_right_add_right

@[simp]
theorem coprime_mul_left_add_right (m n k : ℕ) : coprime m (m * k + n) ↔ coprime m n := by
  rw [coprime, coprime, gcd_mul_left_add_right]
  -- 🎉 no goals
#align nat.coprime_mul_left_add_right Nat.coprime_mul_left_add_right

@[simp]
theorem coprime_add_mul_right_left (m n k : ℕ) : coprime (m + k * n) n ↔ coprime m n := by
  rw [coprime, coprime, gcd_add_mul_right_left]
  -- 🎉 no goals
#align nat.coprime_add_mul_right_left Nat.coprime_add_mul_right_left

@[simp]
theorem coprime_add_mul_left_left (m n k : ℕ) : coprime (m + n * k) n ↔ coprime m n := by
  rw [coprime, coprime, gcd_add_mul_left_left]
  -- 🎉 no goals
#align nat.coprime_add_mul_left_left Nat.coprime_add_mul_left_left

@[simp]
theorem coprime_mul_right_add_left (m n k : ℕ) : coprime (k * n + m) n ↔ coprime m n := by
  rw [coprime, coprime, gcd_mul_right_add_left]
  -- 🎉 no goals
#align nat.coprime_mul_right_add_left Nat.coprime_mul_right_add_left

@[simp]
theorem coprime_mul_left_add_left (m n k : ℕ) : coprime (n * k + m) n ↔ coprime m n := by
  rw [coprime, coprime, gcd_mul_left_add_left]
  -- 🎉 no goals
#align nat.coprime_mul_left_add_left Nat.coprime_mul_left_add_left

@[simp]
theorem coprime_pow_left_iff {n : ℕ} (hn : 0 < n) (a b : ℕ) :
    Nat.coprime (a ^ n) b ↔ Nat.coprime a b := by
  obtain ⟨n, rfl⟩ := exists_eq_succ_of_ne_zero hn.ne'
  -- ⊢ coprime (a ^ succ n) b ↔ coprime a b
  rw [pow_succ, Nat.coprime_mul_iff_left]
  -- ⊢ coprime (a ^ n) b ∧ coprime a b ↔ coprime a b
  exact ⟨And.right, fun hab => ⟨hab.pow_left _, hab⟩⟩
  -- 🎉 no goals
#align nat.coprime_pow_left_iff Nat.coprime_pow_left_iff

@[simp]
theorem coprime_pow_right_iff {n : ℕ} (hn : 0 < n) (a b : ℕ) :
    Nat.coprime a (b ^ n) ↔ Nat.coprime a b := by
  rw [Nat.coprime_comm, coprime_pow_left_iff hn, Nat.coprime_comm]
  -- 🎉 no goals
#align nat.coprime_pow_right_iff Nat.coprime_pow_right_iff

theorem not_coprime_zero_zero : ¬coprime 0 0 := by simp
                                                   -- 🎉 no goals
#align nat.not_coprime_zero_zero Nat.not_coprime_zero_zero

theorem coprime_one_left_iff (n : ℕ) : coprime 1 n ↔ True := by simp [coprime]
                                                                -- 🎉 no goals
#align nat.coprime_one_left_iff Nat.coprime_one_left_iff

theorem coprime_one_right_iff (n : ℕ) : coprime n 1 ↔ True := by simp [coprime]
                                                                 -- 🎉 no goals
#align nat.coprime_one_right_iff Nat.coprime_one_right_iff

theorem gcd_mul_of_coprime_of_dvd {a b c : ℕ} (hac : coprime a c) (b_dvd_c : b ∣ c) :
    gcd (a * b) c = b := by
  rcases exists_eq_mul_left_of_dvd b_dvd_c with ⟨d, rfl⟩
  -- ⊢ gcd (a * b) (d * b) = b
  rw [gcd_mul_right]
  -- ⊢ gcd a d * b = b
  convert one_mul b
  -- ⊢ gcd a d = 1
  exact coprime.coprime_mul_right_right hac
  -- 🎉 no goals
#align nat.gcd_mul_of_coprime_of_dvd Nat.gcd_mul_of_coprime_of_dvd

theorem coprime.eq_of_mul_eq_zero {m n : ℕ} (h : m.coprime n) (hmn : m * n = 0) :
    m = 0 ∧ n = 1 ∨ m = 1 ∧ n = 0 :=
  (Nat.eq_zero_of_mul_eq_zero hmn).imp (fun hm => ⟨hm, n.coprime_zero_left.mp <| hm ▸ h⟩) fun hn =>
    let eq := hn ▸ h.symm
    ⟨m.coprime_zero_left.mp <| eq, hn⟩
#align nat.coprime.eq_of_mul_eq_zero Nat.coprime.eq_of_mul_eq_zero

/-- Represent a divisor of `m * n` as a product of a divisor of `m` and a divisor of `n`.

See `exists_dvd_and_dvd_of_dvd_mul` for the more general but less constructive version for other
`GCDMonoid`s. -/
def prodDvdAndDvdOfDvdProd {m n k : ℕ} (H : k ∣ m * n) :
    { d : { m' // m' ∣ m } × { n' // n' ∣ n } // k = d.1 * d.2 } := by
  cases h0 : gcd k m
  -- ⊢ { d // k = ↑d.fst * ↑d.snd }
  case zero =>
    obtain rfl : k = 0 := eq_zero_of_gcd_eq_zero_left h0
    obtain rfl : m = 0 := eq_zero_of_gcd_eq_zero_right h0
    exact ⟨⟨⟨0, dvd_refl 0⟩, ⟨n, dvd_refl n⟩⟩, (zero_mul n).symm⟩
  case succ tmp =>
    have hpos : 0 < gcd k m := h0.symm ▸ Nat.zero_lt_succ _; clear h0 tmp
    have hd : gcd k m * (k / gcd k m) = k := Nat.mul_div_cancel' (gcd_dvd_left k m)
    refine' ⟨⟨⟨gcd k m, gcd_dvd_right k m⟩, ⟨k / gcd k m, _⟩⟩, hd.symm⟩
    apply Nat.dvd_of_mul_dvd_mul_left hpos
    rw [hd, ← gcd_mul_right]
    exact dvd_gcd (dvd_mul_right _ _) H
#align nat.prod_dvd_and_dvd_of_dvd_prod Nat.prodDvdAndDvdOfDvdProd

theorem dvd_mul {x m n : ℕ} : x ∣ m * n ↔ ∃ y z, y ∣ m ∧ z ∣ n ∧ y * z = x := by
  constructor
  -- ⊢ x ∣ m * n → ∃ y z, y ∣ m ∧ z ∣ n ∧ y * z = x
  · intro h
    -- ⊢ ∃ y z, y ∣ m ∧ z ∣ n ∧ y * z = x
    obtain ⟨⟨⟨y, hy⟩, ⟨z, hz⟩⟩, rfl⟩ := prod_dvd_and_dvd_of_dvd_prod h
    -- ⊢ ∃ y_1 z_1, y_1 ∣ m ∧ z_1 ∣ n ∧ y_1 * z_1 = ↑({ val := y, property := hy }, { …
    exact ⟨y, z, hy, hz, rfl⟩
    -- 🎉 no goals
  · rintro ⟨y, z, hy, hz, rfl⟩
    -- ⊢ y * z ∣ m * n
    exact mul_dvd_mul hy hz
    -- 🎉 no goals
#align nat.dvd_mul Nat.dvd_mul

theorem pow_dvd_pow_iff {a b n : ℕ} (n0 : 0 < n) : a ^ n ∣ b ^ n ↔ a ∣ b := by
  refine' ⟨fun h => _, fun h => pow_dvd_pow_of_dvd h _⟩
  -- ⊢ a ∣ b
  cases' Nat.eq_zero_or_pos (gcd a b) with g0 g0
  -- ⊢ a ∣ b
  · simp [eq_zero_of_gcd_eq_zero_right g0]
    -- 🎉 no goals
  rcases exists_coprime' g0 with ⟨g, a', b', g0', co, rfl, rfl⟩
  -- ⊢ a' * g ∣ b' * g
  rw [mul_pow, mul_pow] at h
  -- ⊢ a' * g ∣ b' * g
  replace h := Nat.dvd_of_mul_dvd_mul_right (pow_pos g0' _) h
  -- ⊢ a' * g ∣ b' * g
  have := pow_dvd_pow a' n0
  -- ⊢ a' * g ∣ b' * g
  rw [pow_one, (co.pow n n).eq_one_of_dvd h] at this
  -- ⊢ a' * g ∣ b' * g
  simp [eq_one_of_dvd_one this]
  -- 🎉 no goals
#align nat.pow_dvd_pow_iff Nat.pow_dvd_pow_iff

/-- If `k:ℕ` divides coprime `a` and `b` then `k = 1` -/
theorem eq_one_of_dvd_coprimes {a b k : ℕ} (h_ab_coprime : coprime a b) (hka : k ∣ a)
    (hkb : k ∣ b) : k = 1 := by
  rw [coprime_iff_gcd_eq_one] at h_ab_coprime
  -- ⊢ k = 1
  have h1 := dvd_gcd hka hkb
  -- ⊢ k = 1
  rw [h_ab_coprime] at h1
  -- ⊢ k = 1
  exact Nat.dvd_one.mp h1
  -- 🎉 no goals
#align nat.eq_one_of_dvd_coprimes Nat.eq_one_of_dvd_coprimes

theorem coprime.mul_add_mul_ne_mul {m n a b : ℕ} (cop : coprime m n) (ha : a ≠ 0) (hb : b ≠ 0) :
    a * m + b * n ≠ m * n := by
  intro h
  -- ⊢ False
  obtain ⟨x, rfl⟩ : n ∣ a :=
    cop.symm.dvd_of_dvd_mul_right
      ((Nat.dvd_add_iff_left (Nat.dvd_mul_left n b)).mpr
        ((congr_arg _ h).mpr (Nat.dvd_mul_left n m)))
  obtain ⟨y, rfl⟩ : m ∣ b :=
    cop.dvd_of_dvd_mul_right
      ((Nat.dvd_add_iff_right (Nat.dvd_mul_left m (n * x))).mpr
        ((congr_arg _ h).mpr (Nat.dvd_mul_right m n)))
  rw [mul_comm, mul_ne_zero_iff, ← one_le_iff_ne_zero] at ha hb
  -- ⊢ False
  refine' mul_ne_zero hb.2 ha.2 (eq_zero_of_mul_eq_self_left (ne_of_gt (add_le_add ha.1 hb.1)) _)
  -- ⊢ (x + y) * (m * n) = m * n
  rw [← mul_assoc, ← h, add_mul, add_mul, mul_comm _ n, ← mul_assoc, mul_comm y]
  -- 🎉 no goals
#align nat.coprime.mul_add_mul_ne_mul Nat.coprime.mul_add_mul_ne_mul

end Nat
