/-
Copyright (c) 2020 Paul van Wamelen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul van Wamelen
-/
import Mathlib.Algebra.Field.Basic
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Int.NatPrime
import Mathlib.Data.ZMod.Basic

#align_import number_theory.pythagorean_triples from "leanprover-community/mathlib"@"e8638a0fcaf73e4500469f368ef9494e495099b3"

/-!
# Pythagorean Triples

The main result is the classification of Pythagorean triples. The final result is for general
Pythagorean triples. It follows from the more interesting relatively prime case. We use the
"rational parametrization of the circle" method for the proof. The parametrization maps the point
`(x / z, y / z)` to the slope of the line through `(-1 , 0)` and `(x / z, y / z)`. This quickly
shows that `(x / z, y / z) = (2 * m * n / (m ^ 2 + n ^ 2), (m ^ 2 - n ^ 2) / (m ^ 2 + n ^ 2))` where
`m / n` is the slope. In order to identify numerators and denominators we now need results showing
that these are coprime. This is easy except for the prime 2. In order to deal with that we have to
analyze the parity of `x`, `y`, `m` and `n` and eliminate all the impossible cases. This takes up
the bulk of the proof below.
-/


theorem sq_ne_two_fin_zmod_four (z : ZMod 4) : z * z ≠ 2 := by
  change Fin 4 at z
  -- ⊢ z * z ≠ 2
  fin_cases z <;> norm_num [Fin.ext_iff]
                  -- 🎉 no goals
                  -- 🎉 no goals
                  -- 🎉 no goals
                  -- 🎉 no goals
#align sq_ne_two_fin_zmod_four sq_ne_two_fin_zmod_four

theorem Int.sq_ne_two_mod_four (z : ℤ) : z * z % 4 ≠ 2 := by
  suffices ¬z * z % (4 : ℕ) = 2 % (4 : ℕ) by exact this
  -- ⊢ ¬z * z % ↑4 = 2 % ↑4
  rw [← ZMod.int_cast_eq_int_cast_iff']
  -- ⊢ ¬↑(z * z) = ↑2
  simpa using sq_ne_two_fin_zmod_four _
  -- 🎉 no goals
#align int.sq_ne_two_mod_four Int.sq_ne_two_mod_four

noncomputable section

open Classical

/-- Three integers `x`, `y`, and `z` form a Pythagorean triple if `x * x + y * y = z * z`. -/
def PythagoreanTriple (x y z : ℤ) : Prop :=
  x * x + y * y = z * z
#align pythagorean_triple PythagoreanTriple

/-- Pythagorean triples are interchangeable, i.e `x * x + y * y = y * y + x * x = z * z`.
This comes from additive commutativity. -/
theorem pythagoreanTriple_comm {x y z : ℤ} : PythagoreanTriple x y z ↔ PythagoreanTriple y x z := by
  delta PythagoreanTriple
  -- ⊢ x * x + y * y = z * z ↔ y * y + x * x = z * z
  rw [add_comm]
  -- 🎉 no goals
#align pythagorean_triple_comm pythagoreanTriple_comm

/-- The zeroth Pythagorean triple is all zeros. -/
theorem PythagoreanTriple.zero : PythagoreanTriple 0 0 0 := by
  simp only [PythagoreanTriple, zero_mul, zero_add]
  -- 🎉 no goals
#align pythagorean_triple.zero PythagoreanTriple.zero

namespace PythagoreanTriple

variable {x y z : ℤ} (h : PythagoreanTriple x y z)

theorem eq : x * x + y * y = z * z :=
  h
#align pythagorean_triple.eq PythagoreanTriple.eq

@[symm]
theorem symm : PythagoreanTriple y x z := by rwa [pythagoreanTriple_comm]
                                             -- 🎉 no goals
#align pythagorean_triple.symm PythagoreanTriple.symm

/-- A triple is still a triple if you multiply `x`, `y` and `z`
by a constant `k`. -/
theorem mul (k : ℤ) : PythagoreanTriple (k * x) (k * y) (k * z) :=
  calc
    k * x * (k * x) + k * y * (k * y) = k ^ 2 * (x * x + y * y) := by ring
                                                                      -- 🎉 no goals
    _ = k ^ 2 * (z * z) := by rw [h.eq]
                              -- 🎉 no goals
    _ = k * z * (k * z) := by ring
                              -- 🎉 no goals
#align pythagorean_triple.mul PythagoreanTriple.mul

/-- `(k*x, k*y, k*z)` is a Pythagorean triple if and only if
`(x, y, z)` is also a triple. -/
theorem mul_iff (k : ℤ) (hk : k ≠ 0) :
    PythagoreanTriple (k * x) (k * y) (k * z) ↔ PythagoreanTriple x y z := by
  refine' ⟨_, fun h => h.mul k⟩
  -- ⊢ PythagoreanTriple (k * x) (k * y) (k * z) → PythagoreanTriple x y z
  simp only [PythagoreanTriple]
  -- ⊢ k * x * (k * x) + k * y * (k * y) = k * z * (k * z) → x * x + y * y = z * z
  intro h
  -- ⊢ x * x + y * y = z * z
  rw [← mul_left_inj' (mul_ne_zero hk hk)]
  -- ⊢ (x * x + y * y) * (k * k) = z * z * (k * k)
  convert h using 1 <;> ring
  -- ⊢ (x * x + y * y) * (k * k) = k * x * (k * x) + k * y * (k * y)
                        -- 🎉 no goals
                        -- 🎉 no goals
#align pythagorean_triple.mul_iff PythagoreanTriple.mul_iff

/-- A Pythagorean triple `x, y, z` is “classified” if there exist integers `k, m, n` such that
either
 * `x = k * (m ^ 2 - n ^ 2)` and `y = k * (2 * m * n)`, or
 * `x = k * (2 * m * n)` and `y = k * (m ^ 2 - n ^ 2)`. -/
@[nolint unusedArguments]
def IsClassified (_ : PythagoreanTriple x y z) :=
  ∃ k m n : ℤ,
    (x = k * (m ^ 2 - n ^ 2) ∧ y = k * (2 * m * n) ∨
        x = k * (2 * m * n) ∧ y = k * (m ^ 2 - n ^ 2)) ∧
      Int.gcd m n = 1
#align pythagorean_triple.is_classified PythagoreanTriple.IsClassified

/-- A primitive Pythagorean triple `x, y, z` is a Pythagorean triple with `x` and `y` coprime.
 Such a triple is “primitively classified” if there exist coprime integers `m, n` such that either
 * `x = m ^ 2 - n ^ 2` and `y = 2 * m * n`, or
 * `x = 2 * m * n` and `y = m ^ 2 - n ^ 2`.
-/
@[nolint unusedArguments]
def IsPrimitiveClassified (_ : PythagoreanTriple x y z) :=
  ∃ m n : ℤ,
    (x = m ^ 2 - n ^ 2 ∧ y = 2 * m * n ∨ x = 2 * m * n ∧ y = m ^ 2 - n ^ 2) ∧
      Int.gcd m n = 1 ∧ (m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0)
#align pythagorean_triple.is_primitive_classified PythagoreanTriple.IsPrimitiveClassified

theorem mul_isClassified (k : ℤ) (hc : h.IsClassified) : (h.mul k).IsClassified := by
  obtain ⟨l, m, n, ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, co⟩⟩ := hc
  -- ⊢ IsClassified (_ : PythagoreanTriple (k * (l * (m ^ 2 - n ^ 2))) (k * (l * (2 …
  · use k * l, m, n
    -- ⊢ (k * (l * (m ^ 2 - n ^ 2)) = k * l * (m ^ 2 - n ^ 2) ∧ k * (l * (2 * m * n)) …
    apply And.intro _ co
    -- ⊢ k * (l * (m ^ 2 - n ^ 2)) = k * l * (m ^ 2 - n ^ 2) ∧ k * (l * (2 * m * n))  …
    left
    -- ⊢ k * (l * (m ^ 2 - n ^ 2)) = k * l * (m ^ 2 - n ^ 2) ∧ k * (l * (2 * m * n))  …
    constructor <;> ring
    -- ⊢ k * (l * (m ^ 2 - n ^ 2)) = k * l * (m ^ 2 - n ^ 2)
                    -- 🎉 no goals
                    -- 🎉 no goals
  · use k * l, m, n
    -- ⊢ (k * (l * (2 * m * n)) = k * l * (m ^ 2 - n ^ 2) ∧ k * (l * (m ^ 2 - n ^ 2)) …
    apply And.intro _ co
    -- ⊢ k * (l * (2 * m * n)) = k * l * (m ^ 2 - n ^ 2) ∧ k * (l * (m ^ 2 - n ^ 2))  …
    right
    -- ⊢ k * (l * (2 * m * n)) = k * l * (2 * m * n) ∧ k * (l * (m ^ 2 - n ^ 2)) = k  …
    constructor <;> ring
    -- ⊢ k * (l * (2 * m * n)) = k * l * (2 * m * n)
                    -- 🎉 no goals
                    -- 🎉 no goals
#align pythagorean_triple.mul_is_classified PythagoreanTriple.mul_isClassified

theorem even_odd_of_coprime (hc : Int.gcd x y = 1) :
    x % 2 = 0 ∧ y % 2 = 1 ∨ x % 2 = 1 ∧ y % 2 = 0 := by
  cases' Int.emod_two_eq_zero_or_one x with hx hx <;>
  -- ⊢ x % 2 = 0 ∧ y % 2 = 1 ∨ x % 2 = 1 ∧ y % 2 = 0
    cases' Int.emod_two_eq_zero_or_one y with hy hy
    -- ⊢ x % 2 = 0 ∧ y % 2 = 1 ∨ x % 2 = 1 ∧ y % 2 = 0
    -- ⊢ x % 2 = 0 ∧ y % 2 = 1 ∨ x % 2 = 1 ∧ y % 2 = 0
  -- x even, y even
  · exfalso
    -- ⊢ False
    apply Nat.not_coprime_of_dvd_of_dvd (by decide : 1 < 2) _ _ hc
    -- ⊢ 2 ∣ Int.natAbs x
    · apply Int.coe_nat_dvd_left.1
      -- ⊢ ↑2 ∣ x
      apply Int.dvd_of_emod_eq_zero hx
      -- 🎉 no goals
    · apply Int.coe_nat_dvd_left.1
      -- ⊢ ↑2 ∣ y
      apply Int.dvd_of_emod_eq_zero hy
      -- 🎉 no goals
  -- x even, y odd
  · left
    -- ⊢ x % 2 = 0 ∧ y % 2 = 1
    exact ⟨hx, hy⟩
    -- 🎉 no goals
  -- x odd, y even
  · right
    -- ⊢ x % 2 = 1 ∧ y % 2 = 0
    exact ⟨hx, hy⟩
    -- 🎉 no goals
  -- x odd, y odd
  · exfalso
    -- ⊢ False
    obtain ⟨x0, y0, rfl, rfl⟩ : ∃ x0 y0, x = x0 * 2 + 1 ∧ y = y0 * 2 + 1 := by
      cases' exists_eq_mul_left_of_dvd (Int.dvd_sub_of_emod_eq hx) with x0 hx2
      cases' exists_eq_mul_left_of_dvd (Int.dvd_sub_of_emod_eq hy) with y0 hy2
      rw [sub_eq_iff_eq_add] at hx2 hy2
      exact ⟨x0, y0, hx2, hy2⟩
    apply Int.sq_ne_two_mod_four z
    -- ⊢ z * z % 4 = 2
    rw [show z * z = 4 * (x0 * x0 + x0 + y0 * y0 + y0) + 2 by
        rw [← h.eq]
        ring]
    norm_num [Int.add_emod]
    -- 🎉 no goals
#align pythagorean_triple.even_odd_of_coprime PythagoreanTriple.even_odd_of_coprime

theorem gcd_dvd : (Int.gcd x y : ℤ) ∣ z := by
  by_cases h0 : Int.gcd x y = 0
  -- ⊢ ↑(Int.gcd x y) ∣ z
  · have hx : x = 0 := by
      apply Int.natAbs_eq_zero.mp
      apply Nat.eq_zero_of_gcd_eq_zero_left h0
    have hy : y = 0 := by
      apply Int.natAbs_eq_zero.mp
      apply Nat.eq_zero_of_gcd_eq_zero_right h0
    have hz : z = 0 := by
      simpa only [PythagoreanTriple, hx, hy, add_zero, zero_eq_mul, mul_zero,
        or_self_iff] using h
    simp only [hz, dvd_zero]
    -- 🎉 no goals
  obtain ⟨k, x0, y0, _, h2, rfl, rfl⟩ :
    ∃ (k : ℕ) (x0 y0 : _), 0 < k ∧ Int.gcd x0 y0 = 1 ∧ x = x0 * k ∧ y = y0 * k :=
    Int.exists_gcd_one' (Nat.pos_of_ne_zero h0)
  rw [Int.gcd_mul_right, h2, Int.natAbs_ofNat, one_mul]
  -- ⊢ ↑k ∣ z
  rw [← Int.pow_dvd_pow_iff zero_lt_two, sq z, ← h.eq]
  -- ⊢ ↑k ^ 2 ∣ x0 * ↑k * (x0 * ↑k) + y0 * ↑k * (y0 * ↑k)
  rw [(by ring : x0 * k * (x0 * k) + y0 * k * (y0 * k) = (k : ℤ) ^ 2 * (x0 * x0 + y0 * y0))]
  -- ⊢ ↑k ^ 2 ∣ ↑k ^ 2 * (x0 * x0 + y0 * y0)
  exact dvd_mul_right _ _
  -- 🎉 no goals
#align pythagorean_triple.gcd_dvd PythagoreanTriple.gcd_dvd

theorem normalize : PythagoreanTriple (x / Int.gcd x y) (y / Int.gcd x y) (z / Int.gcd x y) := by
  by_cases h0 : Int.gcd x y = 0
  -- ⊢ PythagoreanTriple (x / ↑(Int.gcd x y)) (y / ↑(Int.gcd x y)) (z / ↑(Int.gcd x …
  · have hx : x = 0 := by
      apply Int.natAbs_eq_zero.mp
      apply Nat.eq_zero_of_gcd_eq_zero_left h0
    have hy : y = 0 := by
      apply Int.natAbs_eq_zero.mp
      apply Nat.eq_zero_of_gcd_eq_zero_right h0
    have hz : z = 0 := by
      simpa only [PythagoreanTriple, hx, hy, add_zero, zero_eq_mul, mul_zero,
        or_self_iff] using h
    simp only [hx, hy, hz, Int.zero_div]
    -- ⊢ PythagoreanTriple (0 / ↑(Int.gcd 0 0)) (0 / ↑(Int.gcd 0 0)) (0 / ↑(Int.gcd 0 …
    exact zero
    -- 🎉 no goals
  rcases h.gcd_dvd with ⟨z0, rfl⟩
  -- ⊢ PythagoreanTriple (x / ↑(Int.gcd x y)) (y / ↑(Int.gcd x y)) (↑(Int.gcd x y)  …
  obtain ⟨k, x0, y0, k0, h2, rfl, rfl⟩ :
    ∃ (k : ℕ) (x0 y0 : _), 0 < k ∧ Int.gcd x0 y0 = 1 ∧ x = x0 * k ∧ y = y0 * k :=
    Int.exists_gcd_one' (Nat.pos_of_ne_zero h0)
  have hk : (k : ℤ) ≠ 0 := by
    norm_cast
    rwa [pos_iff_ne_zero] at k0
  rw [Int.gcd_mul_right, h2, Int.natAbs_ofNat, one_mul] at h ⊢
  -- ⊢ PythagoreanTriple (x0 * ↑k / ↑k) (y0 * ↑k / ↑k) (↑k * z0 / ↑k)
  rw [mul_comm x0, mul_comm y0, mul_iff k hk] at h
  -- ⊢ PythagoreanTriple (x0 * ↑k / ↑k) (y0 * ↑k / ↑k) (↑k * z0 / ↑k)
  rwa [Int.mul_ediv_cancel _ hk, Int.mul_ediv_cancel _ hk, Int.mul_ediv_cancel_left _ hk]
  -- 🎉 no goals
#align pythagorean_triple.normalize PythagoreanTriple.normalize

theorem isClassified_of_isPrimitiveClassified (hp : h.IsPrimitiveClassified) : h.IsClassified := by
  obtain ⟨m, n, H⟩ := hp
  -- ⊢ IsClassified h
  use 1, m, n
  -- ⊢ (x = 1 * (m ^ 2 - n ^ 2) ∧ y = 1 * (2 * m * n) ∨ x = 1 * (2 * m * n) ∧ y = 1 …
  rcases H with ⟨t, co, _⟩
  -- ⊢ (x = 1 * (m ^ 2 - n ^ 2) ∧ y = 1 * (2 * m * n) ∨ x = 1 * (2 * m * n) ∧ y = 1 …
  rw [one_mul, one_mul]
  -- ⊢ (x = m ^ 2 - n ^ 2 ∧ y = 2 * m * n ∨ x = 2 * m * n ∧ y = m ^ 2 - n ^ 2) ∧ In …
  exact ⟨t, co⟩
  -- 🎉 no goals
#align pythagorean_triple.is_classified_of_is_primitive_classified PythagoreanTriple.isClassified_of_isPrimitiveClassified

theorem isClassified_of_normalize_isPrimitiveClassified (hc : h.normalize.IsPrimitiveClassified) :
    h.IsClassified := by
  convert h.normalize.mul_isClassified (Int.gcd x y)
        (isClassified_of_isPrimitiveClassified h.normalize hc) <;>
    rw [Int.mul_ediv_cancel']
    -- ⊢ ↑(Int.gcd x y) ∣ x
    -- ⊢ ↑(Int.gcd x y) ∣ y
    -- ⊢ ↑(Int.gcd x y) ∣ z
  · exact Int.gcd_dvd_left x y
    -- 🎉 no goals
  · exact Int.gcd_dvd_right x y
    -- 🎉 no goals
  · exact h.gcd_dvd
    -- 🎉 no goals
#align pythagorean_triple.is_classified_of_normalize_is_primitive_classified PythagoreanTriple.isClassified_of_normalize_isPrimitiveClassified

theorem ne_zero_of_coprime (hc : Int.gcd x y = 1) : z ≠ 0 := by
  suffices 0 < z * z by
    rintro rfl
    norm_num at this
  rw [← h.eq, ← sq, ← sq]
  -- ⊢ 0 < x ^ 2 + y ^ 2
  have hc' : Int.gcd x y ≠ 0 := by
    rw [hc]
    exact one_ne_zero
  cases' Int.ne_zero_of_gcd hc' with hxz hyz
  -- ⊢ 0 < x ^ 2 + y ^ 2
  · apply lt_add_of_pos_of_le (sq_pos_of_ne_zero x hxz) (sq_nonneg y)
    -- 🎉 no goals
  · apply lt_add_of_le_of_pos (sq_nonneg x) (sq_pos_of_ne_zero y hyz)
    -- 🎉 no goals
#align pythagorean_triple.ne_zero_of_coprime PythagoreanTriple.ne_zero_of_coprime

theorem isPrimitiveClassified_of_coprime_of_zero_left (hc : Int.gcd x y = 1) (hx : x = 0) :
    h.IsPrimitiveClassified := by
  subst x
  -- ⊢ IsPrimitiveClassified h
  change Nat.gcd 0 (Int.natAbs y) = 1 at hc
  -- ⊢ IsPrimitiveClassified h
  rw [Nat.gcd_zero_left (Int.natAbs y)] at hc
  -- ⊢ IsPrimitiveClassified h
  cases' Int.natAbs_eq y with hy hy
  -- ⊢ IsPrimitiveClassified h
  · use 1, 0
    -- ⊢ (0 = 1 ^ 2 - 0 ^ 2 ∧ y = 2 * 1 * 0 ∨ 0 = 2 * 1 * 0 ∧ y = 1 ^ 2 - 0 ^ 2) ∧ In …
    rw [hy, hc, Int.gcd_zero_right]
    -- ⊢ (0 = 1 ^ 2 - 0 ^ 2 ∧ ↑1 = 2 * 1 * 0 ∨ 0 = 2 * 1 * 0 ∧ ↑1 = 1 ^ 2 - 0 ^ 2) ∧  …
    norm_num
    -- 🎉 no goals
  · use 0, 1
    -- ⊢ (0 = 0 ^ 2 - 1 ^ 2 ∧ y = 2 * 0 * 1 ∨ 0 = 2 * 0 * 1 ∧ y = 0 ^ 2 - 1 ^ 2) ∧ In …
    rw [hy, hc, Int.gcd_zero_left]
    -- ⊢ (0 = 0 ^ 2 - 1 ^ 2 ∧ -↑1 = 2 * 0 * 1 ∨ 0 = 2 * 0 * 1 ∧ -↑1 = 0 ^ 2 - 1 ^ 2)  …
    norm_num
    -- 🎉 no goals
#align pythagorean_triple.is_primitive_classified_of_coprime_of_zero_left PythagoreanTriple.isPrimitiveClassified_of_coprime_of_zero_left

theorem coprime_of_coprime (hc : Int.gcd x y = 1) : Int.gcd y z = 1 := by
  by_contra H
  -- ⊢ False
  obtain ⟨p, hp, hpy, hpz⟩ := Nat.Prime.not_coprime_iff_dvd.mp H
  -- ⊢ False
  apply hp.not_dvd_one
  -- ⊢ p ∣ 1
  rw [← hc]
  -- ⊢ p ∣ Int.gcd x y
  apply Nat.dvd_gcd (Int.Prime.dvd_natAbs_of_coe_dvd_sq hp _ _) hpy
  -- ⊢ ↑p ∣ x ^ 2
  rw [sq, eq_sub_of_add_eq h]
  -- ⊢ ↑p ∣ z * z - y * y
  rw [← Int.coe_nat_dvd_left] at hpy hpz
  -- ⊢ ↑p ∣ z * z - y * y
  exact dvd_sub (hpz.mul_right _) (hpy.mul_right _)
  -- 🎉 no goals
#align pythagorean_triple.coprime_of_coprime PythagoreanTriple.coprime_of_coprime

end PythagoreanTriple

section circleEquivGen

/-!
### A parametrization of the unit circle

For the classification of Pythagorean triples, we will use a parametrization of the unit circle.
-/


variable {K : Type*} [Field K]

/-- A parameterization of the unit circle that is useful for classifying Pythagorean triples.
 (To be applied in the case where `K = ℚ`.) -/
def circleEquivGen (hk : ∀ x : K, 1 + x ^ 2 ≠ 0) :
    K ≃ { p : K × K // p.1 ^ 2 + p.2 ^ 2 = 1 ∧ p.2 ≠ -1 } where
  toFun x :=
    ⟨⟨2 * x / (1 + x ^ 2), (1 - x ^ 2) / (1 + x ^ 2)⟩, by
      field_simp [hk x, div_pow]
      -- ⊢ (2 * x) ^ 2 + (1 - x ^ 2) ^ 2 = (1 + x ^ 2) ^ 2
      ring, by
      -- 🎉 no goals
      simp only [Ne.def, div_eq_iff (hk x), neg_mul, one_mul, neg_add, sub_eq_add_neg, add_left_inj]
      -- ⊢ ¬1 = -1
      simpa only [eq_neg_iff_add_eq_zero, one_pow] using hk 1⟩
      -- 🎉 no goals
  invFun p := (p : K × K).1 / ((p : K × K).2 + 1)
  left_inv x := by
    have h2 : (1 + 1 : K) = 2 := by norm_num -- Porting note: rfl is not enough to close this
    -- ⊢ (fun p => (↑p).fst / ((↑p).snd + 1)) ((fun x => { val := (2 * x / (1 + x ^ 2 …
    have h3 : (2 : K) ≠ 0 := by
      convert hk 1
      rw [one_pow 2, h2]
    field_simp [hk x, h2, add_assoc, add_comm, add_sub_cancel'_right, mul_comm]
    -- 🎉 no goals
  right_inv := fun ⟨⟨x, y⟩, hxy, hy⟩ => by
    change x ^ 2 + y ^ 2 = 1 at hxy
    -- ⊢ (fun x => { val := (2 * x / (1 + x ^ 2), (1 - x ^ 2) / (1 + x ^ 2)), propert …
    have h2 : y + 1 ≠ 0 := mt eq_neg_of_add_eq_zero_left hy
    -- ⊢ (fun x => { val := (2 * x / (1 + x ^ 2), (1 - x ^ 2) / (1 + x ^ 2)), propert …
    have h3 : (y + 1) ^ 2 + x ^ 2 = 2 * (y + 1) := by
      rw [(add_neg_eq_iff_eq_add.mpr hxy.symm).symm]
      ring
    have h4 : (2 : K) ≠ 0 := by
      convert hk 1
      rw [one_pow 2]
      ring -- Porting note: rfl is not enough to close this
    simp only [Prod.mk.inj_iff, Subtype.mk_eq_mk]
    -- ⊢ 2 * (x / (y + 1)) / (1 + (x / (y + 1)) ^ 2) = x ∧ (1 - (x / (y + 1)) ^ 2) /  …
    constructor
    -- ⊢ 2 * (x / (y + 1)) / (1 + (x / (y + 1)) ^ 2) = x
    · field_simp [h3]
      -- ⊢ 2 * x * (y + 1) ^ 2 = x * ((y + 1) * (2 * (y + 1)))
      ring
      -- 🎉 no goals
    · field_simp [h3]
      -- ⊢ (y + 1) ^ 2 - x ^ 2 = y * (2 * (y + 1))
      rw [← add_neg_eq_iff_eq_add.mpr hxy.symm]
      -- ⊢ (y + 1) ^ 2 - (1 + -y ^ 2) = y * (2 * (y + 1))
      ring
      -- 🎉 no goals
#align circle_equiv_gen circleEquivGen

@[simp]
theorem circleEquivGen_apply (hk : ∀ x : K, 1 + x ^ 2 ≠ 0) (x : K) :
    (circleEquivGen hk x : K × K) = ⟨2 * x / (1 + x ^ 2), (1 - x ^ 2) / (1 + x ^ 2)⟩ :=
  rfl
#align circle_equiv_apply circleEquivGen_apply

@[simp]
theorem circleEquivGen_symm_apply (hk : ∀ x : K, 1 + x ^ 2 ≠ 0)
    (v : { p : K × K // p.1 ^ 2 + p.2 ^ 2 = 1 ∧ p.2 ≠ -1 }) :
    (circleEquivGen hk).symm v = (v : K × K).1 / ((v : K × K).2 + 1) :=
  rfl
#align circle_equiv_symm_apply circleEquivGen_symm_apply

end circleEquivGen

private theorem coprime_sq_sub_sq_add_of_even_odd {m n : ℤ} (h : Int.gcd m n = 1) (hm : m % 2 = 0)
    (hn : n % 2 = 1) : Int.gcd (m ^ 2 - n ^ 2) (m ^ 2 + n ^ 2) = 1 := by
  by_contra H
  -- ⊢ False
  obtain ⟨p, hp, hp1, hp2⟩ := Nat.Prime.not_coprime_iff_dvd.mp H
  -- ⊢ False
  rw [← Int.coe_nat_dvd_left] at hp1 hp2
  -- ⊢ False
  have h2m : (p : ℤ) ∣ 2 * m ^ 2 := by
    convert dvd_add hp2 hp1 using 1
    ring
  have h2n : (p : ℤ) ∣ 2 * n ^ 2 := by
    convert dvd_sub hp2 hp1 using 1
    ring
  have hmc : p = 2 ∨ p ∣ Int.natAbs m := prime_two_or_dvd_of_dvd_two_mul_pow_self_two hp h2m
  -- ⊢ False
  have hnc : p = 2 ∨ p ∣ Int.natAbs n := prime_two_or_dvd_of_dvd_two_mul_pow_self_two hp h2n
  -- ⊢ False
  by_cases h2 : p = 2
  -- ⊢ False
  -- Porting note: norm_num is not enough to close h3
  · have h3 : (m ^ 2 + n ^ 2) % 2 = 1 := by field_simp [sq, Int.add_emod, Int.mul_emod, hm, hn]
    -- ⊢ False
    have h4 : (m ^ 2 + n ^ 2) % 2 = 0 := by
      apply Int.emod_eq_zero_of_dvd
      rwa [h2] at hp2
    rw [h4] at h3
    -- ⊢ False
    exact zero_ne_one h3
    -- 🎉 no goals
  · apply hp.not_dvd_one
    -- ⊢ p ∣ 1
    rw [← h]
    -- ⊢ p ∣ Int.gcd m n
    exact Nat.dvd_gcd (Or.resolve_left hmc h2) (Or.resolve_left hnc h2)
    -- 🎉 no goals

private theorem coprime_sq_sub_sq_add_of_odd_even {m n : ℤ} (h : Int.gcd m n = 1) (hm : m % 2 = 1)
    (hn : n % 2 = 0) : Int.gcd (m ^ 2 - n ^ 2) (m ^ 2 + n ^ 2) = 1 := by
  rw [Int.gcd, ← Int.natAbs_neg (m ^ 2 - n ^ 2)]
  -- ⊢ Nat.gcd (Int.natAbs (-(m ^ 2 - n ^ 2))) (Int.natAbs (m ^ 2 + n ^ 2)) = 1
  rw [(by ring : -(m ^ 2 - n ^ 2) = n ^ 2 - m ^ 2), add_comm]
  -- ⊢ Nat.gcd (Int.natAbs (n ^ 2 - m ^ 2)) (Int.natAbs (n ^ 2 + m ^ 2)) = 1
  apply coprime_sq_sub_sq_add_of_even_odd _ hn hm; rwa [Int.gcd_comm]
  -- ⊢ Int.gcd n m = 1
                                                   -- 🎉 no goals

private theorem coprime_sq_sub_mul_of_even_odd {m n : ℤ} (h : Int.gcd m n = 1) (hm : m % 2 = 0)
    (hn : n % 2 = 1) : Int.gcd (m ^ 2 - n ^ 2) (2 * m * n) = 1 := by
  by_contra H
  -- ⊢ False
  obtain ⟨p, hp, hp1, hp2⟩ := Nat.Prime.not_coprime_iff_dvd.mp H
  -- ⊢ False
  rw [← Int.coe_nat_dvd_left] at hp1 hp2
  -- ⊢ False
  have hnp : ¬(p : ℤ) ∣ Int.gcd m n := by
    rw [h]
    norm_cast
    exact mt Nat.dvd_one.mp (Nat.Prime.ne_one hp)
  cases' Int.Prime.dvd_mul hp hp2 with hp2m hpn
  -- ⊢ False
  · rw [Int.natAbs_mul] at hp2m
    -- ⊢ False
    cases' (Nat.Prime.dvd_mul hp).mp hp2m with hp2 hpm
    -- ⊢ False
    · have hp2' : p = 2 := (Nat.le_of_dvd zero_lt_two hp2).antisymm hp.two_le
      -- ⊢ False
      revert hp1
      -- ⊢ ↑p ∣ m ^ 2 - n ^ 2 → False
      rw [hp2']
      -- ⊢ ↑2 ∣ m ^ 2 - n ^ 2 → False
      apply mt Int.emod_eq_zero_of_dvd
      -- ⊢ ¬(m ^ 2 - n ^ 2) % ↑2 = 0
      -- Porting note: norm_num is not enough to close this
      field_simp [sq, Int.sub_emod, Int.mul_emod, hm, hn]
      -- 🎉 no goals
    apply mt (Int.dvd_gcd (Int.coe_nat_dvd_left.mpr hpm)) hnp
    -- ⊢ ↑p ∣ n
    apply (or_self_iff _).mp
    -- ⊢ ↑p ∣ n ∨ ↑p ∣ n
    apply Int.Prime.dvd_mul' hp
    -- ⊢ ↑p ∣ n * n
    rw [(by ring : n * n = -(m ^ 2 - n ^ 2) + m * m)]
    -- ⊢ ↑p ∣ -(m ^ 2 - n ^ 2) + m * m
    exact hp1.neg_right.add ((Int.coe_nat_dvd_left.2 hpm).mul_right _)
    -- 🎉 no goals
  rw [Int.gcd_comm] at hnp
  -- ⊢ False
  apply mt (Int.dvd_gcd (Int.coe_nat_dvd_left.mpr hpn)) hnp
  -- ⊢ ↑p ∣ m
  apply (or_self_iff _).mp
  -- ⊢ ↑p ∣ m ∨ ↑p ∣ m
  apply Int.Prime.dvd_mul' hp
  -- ⊢ ↑p ∣ m * m
  rw [(by ring : m * m = m ^ 2 - n ^ 2 + n * n)]
  -- ⊢ ↑p ∣ m ^ 2 - n ^ 2 + n * n
  apply dvd_add hp1
  -- ⊢ ↑p ∣ n * n
  exact (Int.coe_nat_dvd_left.mpr hpn).mul_right n
  -- 🎉 no goals

private theorem coprime_sq_sub_mul_of_odd_even {m n : ℤ} (h : Int.gcd m n = 1) (hm : m % 2 = 1)
    (hn : n % 2 = 0) : Int.gcd (m ^ 2 - n ^ 2) (2 * m * n) = 1 := by
  rw [Int.gcd, ← Int.natAbs_neg (m ^ 2 - n ^ 2)]
  -- ⊢ Nat.gcd (Int.natAbs (-(m ^ 2 - n ^ 2))) (Int.natAbs (2 * m * n)) = 1
  rw [(by ring : 2 * m * n = 2 * n * m), (by ring : -(m ^ 2 - n ^ 2) = n ^ 2 - m ^ 2)]
  -- ⊢ Nat.gcd (Int.natAbs (n ^ 2 - m ^ 2)) (Int.natAbs (2 * n * m)) = 1
  apply coprime_sq_sub_mul_of_even_odd _ hn hm; rwa [Int.gcd_comm]
  -- ⊢ Int.gcd n m = 1
                                                -- 🎉 no goals

private theorem coprime_sq_sub_mul {m n : ℤ} (h : Int.gcd m n = 1)
    (hmn : m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0) :
    Int.gcd (m ^ 2 - n ^ 2) (2 * m * n) = 1 := by
  cases' hmn with h1 h2
  -- ⊢ Int.gcd (m ^ 2 - n ^ 2) (2 * m * n) = 1
  · exact coprime_sq_sub_mul_of_even_odd h h1.left h1.right
    -- 🎉 no goals
  · exact coprime_sq_sub_mul_of_odd_even h h2.left h2.right
    -- 🎉 no goals

private theorem coprime_sq_sub_sq_sum_of_odd_odd {m n : ℤ} (h : Int.gcd m n = 1) (hm : m % 2 = 1)
    (hn : n % 2 = 1) :
    2 ∣ m ^ 2 + n ^ 2 ∧
      2 ∣ m ^ 2 - n ^ 2 ∧
        (m ^ 2 - n ^ 2) / 2 % 2 = 0 ∧ Int.gcd ((m ^ 2 - n ^ 2) / 2) ((m ^ 2 + n ^ 2) / 2) = 1 := by
  cases' exists_eq_mul_left_of_dvd (Int.dvd_sub_of_emod_eq hm) with m0 hm2
  -- ⊢ 2 ∣ m ^ 2 + n ^ 2 ∧ 2 ∣ m ^ 2 - n ^ 2 ∧ (m ^ 2 - n ^ 2) / 2 % 2 = 0 ∧ Int.gc …
  cases' exists_eq_mul_left_of_dvd (Int.dvd_sub_of_emod_eq hn) with n0 hn2
  -- ⊢ 2 ∣ m ^ 2 + n ^ 2 ∧ 2 ∣ m ^ 2 - n ^ 2 ∧ (m ^ 2 - n ^ 2) / 2 % 2 = 0 ∧ Int.gc …
  rw [sub_eq_iff_eq_add] at hm2 hn2
  -- ⊢ 2 ∣ m ^ 2 + n ^ 2 ∧ 2 ∣ m ^ 2 - n ^ 2 ∧ (m ^ 2 - n ^ 2) / 2 % 2 = 0 ∧ Int.gc …
  subst m
  -- ⊢ 2 ∣ (m0 * 2 + 1) ^ 2 + n ^ 2 ∧ 2 ∣ (m0 * 2 + 1) ^ 2 - n ^ 2 ∧ ((m0 * 2 + 1)  …
  subst n
  -- ⊢ 2 ∣ (m0 * 2 + 1) ^ 2 + (n0 * 2 + 1) ^ 2 ∧ 2 ∣ (m0 * 2 + 1) ^ 2 - (n0 * 2 + 1 …
  have h1 : (m0 * 2 + 1) ^ 2 + (n0 * 2 + 1) ^ 2 = 2 * (2 * (m0 ^ 2 + n0 ^ 2 + m0 + n0) + 1) := by
    ring
  have h2 : (m0 * 2 + 1) ^ 2 - (n0 * 2 + 1) ^ 2 = 2 * (2 * (m0 ^ 2 - n0 ^ 2 + m0 - n0)) := by ring
  -- ⊢ 2 ∣ (m0 * 2 + 1) ^ 2 + (n0 * 2 + 1) ^ 2 ∧ 2 ∣ (m0 * 2 + 1) ^ 2 - (n0 * 2 + 1 …
  have h3 : ((m0 * 2 + 1) ^ 2 - (n0 * 2 + 1) ^ 2) / 2 % 2 = 0 := by
    rw [h2, Int.mul_ediv_cancel_left, Int.mul_emod_right]
    exact by decide
  refine' ⟨⟨_, h1⟩, ⟨_, h2⟩, h3, _⟩
  -- ⊢ Int.gcd (((m0 * 2 + 1) ^ 2 - (n0 * 2 + 1) ^ 2) / 2) (((m0 * 2 + 1) ^ 2 + (n0 …
  have h20 : (2 : ℤ) ≠ 0 := by decide
  -- ⊢ Int.gcd (((m0 * 2 + 1) ^ 2 - (n0 * 2 + 1) ^ 2) / 2) (((m0 * 2 + 1) ^ 2 + (n0 …
  rw [h1, h2, Int.mul_ediv_cancel_left _ h20, Int.mul_ediv_cancel_left _ h20]
  -- ⊢ Int.gcd (2 * (m0 ^ 2 - n0 ^ 2 + m0 - n0)) (2 * (m0 ^ 2 + n0 ^ 2 + m0 + n0) + …
  by_contra h4
  -- ⊢ False
  obtain ⟨p, hp, hp1, hp2⟩ := Nat.Prime.not_coprime_iff_dvd.mp h4
  -- ⊢ False
  apply hp.not_dvd_one
  -- ⊢ p ∣ 1
  rw [← h]
  -- ⊢ p ∣ Int.gcd (m0 * 2 + 1) (n0 * 2 + 1)
  rw [← Int.coe_nat_dvd_left] at hp1 hp2
  -- ⊢ p ∣ Int.gcd (m0 * 2 + 1) (n0 * 2 + 1)
  apply Nat.dvd_gcd
  -- ⊢ p ∣ Int.natAbs (m0 * 2 + 1)
  · apply Int.Prime.dvd_natAbs_of_coe_dvd_sq hp
    -- ⊢ ↑p ∣ (m0 * 2 + 1) ^ 2
    convert dvd_add hp1 hp2
    -- ⊢ (m0 * 2 + 1) ^ 2 = 2 * (m0 ^ 2 - n0 ^ 2 + m0 - n0) + (2 * (m0 ^ 2 + n0 ^ 2 + …
    ring
    -- 🎉 no goals
  · apply Int.Prime.dvd_natAbs_of_coe_dvd_sq hp
    -- ⊢ ↑p ∣ (n0 * 2 + 1) ^ 2
    convert dvd_sub hp2 hp1
    -- ⊢ (n0 * 2 + 1) ^ 2 = 2 * (m0 ^ 2 + n0 ^ 2 + m0 + n0) + 1 - 2 * (m0 ^ 2 - n0 ^  …
    ring
    -- 🎉 no goals

namespace PythagoreanTriple

variable {x y z : ℤ} (h : PythagoreanTriple x y z)

theorem isPrimitiveClassified_aux (hc : x.gcd y = 1) (hzpos : 0 < z) {m n : ℤ}
    (hm2n2 : 0 < m ^ 2 + n ^ 2) (hv2 : (x : ℚ) / z = 2 * m * n / ((m : ℚ) ^ 2 + (n : ℚ) ^ 2))
    (hw2 : (y : ℚ) / z = ((m : ℚ) ^ 2 - (n : ℚ) ^ 2) / ((m : ℚ) ^ 2 + (n : ℚ) ^ 2))
    (H : Int.gcd (m ^ 2 - n ^ 2) (m ^ 2 + n ^ 2) = 1) (co : Int.gcd m n = 1)
    (pp : m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0) : h.IsPrimitiveClassified := by
  have hz : z ≠ 0
  -- ⊢ z ≠ 0
  apply ne_of_gt hzpos
  -- ⊢ IsPrimitiveClassified h
  have h2 : y = m ^ 2 - n ^ 2 ∧ z = m ^ 2 + n ^ 2 := by
    apply Rat.div_int_inj hzpos hm2n2 (h.coprime_of_coprime hc) H
    rw [hw2]
    norm_cast
  use m, n
  -- ⊢ (x = m ^ 2 - n ^ 2 ∧ y = 2 * m * n ∨ x = 2 * m * n ∧ y = m ^ 2 - n ^ 2) ∧ In …
  apply And.intro _ (And.intro co pp)
  -- ⊢ x = m ^ 2 - n ^ 2 ∧ y = 2 * m * n ∨ x = 2 * m * n ∧ y = m ^ 2 - n ^ 2
  right
  -- ⊢ x = 2 * m * n ∧ y = m ^ 2 - n ^ 2
  refine' ⟨_, h2.left⟩
  -- ⊢ x = 2 * m * n
  rw [← Rat.coe_int_inj _ _, ← div_left_inj' ((mt (Rat.coe_int_inj z 0).mp) hz), hv2, h2.right]
  -- ⊢ 2 * ↑m * ↑n / (↑m ^ 2 + ↑n ^ 2) = ↑(2 * m * n) / ↑(m ^ 2 + n ^ 2)
  norm_cast
  -- 🎉 no goals
#align pythagorean_triple.is_primitive_classified_aux PythagoreanTriple.isPrimitiveClassified_aux

theorem isPrimitiveClassified_of_coprime_of_odd_of_pos (hc : Int.gcd x y = 1) (hyo : y % 2 = 1)
    (hzpos : 0 < z) : h.IsPrimitiveClassified := by
  by_cases h0 : x = 0
  -- ⊢ IsPrimitiveClassified h
  · exact h.isPrimitiveClassified_of_coprime_of_zero_left hc h0
    -- 🎉 no goals
  let v := (x : ℚ) / z
  -- ⊢ IsPrimitiveClassified h
  let w := (y : ℚ) / z
  -- ⊢ IsPrimitiveClassified h
  have hq : v ^ 2 + w ^ 2 = 1 := by
    field_simp [sq]
    norm_cast
  have hvz : v ≠ 0 := by
    field_simp
    exact h0
  have hw1 : w ≠ -1 := by
    contrapose! hvz with hw1
    -- porting note: `contrapose` unfolds local names, refold them
    replace hw1 : w = -1 := hw1; show v = 0
    rw [hw1, neg_sq, one_pow, add_left_eq_self] at hq
    exact pow_eq_zero hq
  have hQ : ∀ x : ℚ, 1 + x ^ 2 ≠ 0 := by
    intro q
    apply ne_of_gt
    exact lt_add_of_pos_of_le zero_lt_one (sq_nonneg q)
  have hp : (⟨v, w⟩ : ℚ × ℚ) ∈ { p : ℚ × ℚ | p.1 ^ 2 + p.2 ^ 2 = 1 ∧ p.2 ≠ -1 } := ⟨hq, hw1⟩
  -- ⊢ IsPrimitiveClassified h
  let q := (circleEquivGen hQ).symm ⟨⟨v, w⟩, hp⟩
  -- ⊢ IsPrimitiveClassified h
  have ht4 : v = 2 * q / (1 + q ^ 2) ∧ w = (1 - q ^ 2) / (1 + q ^ 2) := by
    apply Prod.mk.inj
    have := ((circleEquivGen hQ).apply_symm_apply ⟨⟨v, w⟩, hp⟩).symm
    exact congr_arg Subtype.val this
  let m := (q.den : ℤ)
  -- ⊢ IsPrimitiveClassified h
  let n := q.num
  -- ⊢ IsPrimitiveClassified h
  have hm0 : m ≠ 0 := by
    norm_cast
    apply Rat.den_nz q
  have hq2 : q = n / m := (Rat.num_div_den q).symm
  -- ⊢ IsPrimitiveClassified h
  have hm2n2 : 0 < m ^ 2 + n ^ 2 := by
    apply lt_add_of_pos_of_le _ (sq_nonneg n)
    exact lt_of_le_of_ne (sq_nonneg m) (Ne.symm (pow_ne_zero 2 hm0))
  have hm2n20 : (m : ℚ) ^ 2 + (n : ℚ) ^ 2 ≠ 0 := by
    norm_cast
    simpa only [Int.coe_nat_pow] using ne_of_gt hm2n2
  have hx1 {j k : ℚ} (h₁ : k ≠ 0) (h₂ : k ^ 2 + j ^ 2 ≠ 0) :
      (1 - (j / k) ^ 2) / (1 + (j / k) ^ 2) = (k ^ 2 - j ^ 2) / (k ^ 2 + j ^ 2) :=
    by field_simp
  have hw2 : w = ((m : ℚ) ^ 2 - (n : ℚ) ^ 2) / ((m : ℚ) ^ 2 + (n : ℚ) ^ 2) := by
    calc
      w = (1 - q ^ 2) / (1 + q ^ 2) := by apply ht4.2
      _ = (1 - (↑n / ↑m) ^ 2) / (1 + (↑n / ↑m) ^ 2) := by rw [hq2]
      _ = _ := by exact hx1 (Int.cast_ne_zero.mpr hm0) hm2n20
  have hx2 {j k : ℚ} (h₁ : k ≠ 0) (h₂ : k ^ 2 + j ^ 2 ≠ 0) :
      2 * (j / k) / (1 + (j / k) ^ 2) = 2 * k * j / (k ^ 2 + j ^ 2) :=
    have h₃ : k * (k ^ 2 + j ^ 2) ≠ 0 := mul_ne_zero h₁ h₂
    by field_simp; ring
  have hv2 : v = 2 * m * n / ((m : ℚ) ^ 2 + (n : ℚ) ^ 2) := by
    calc
      v = 2 * q / (1 + q ^ 2) := by apply ht4.1
      _ = 2 * (n / m) / (1 + (↑n / ↑m) ^ 2) := by rw [hq2]
      _ = _ := by exact hx2 (Int.cast_ne_zero.mpr hm0) hm2n20
  have hnmcp : Int.gcd n m = 1 := q.reduced
  -- ⊢ IsPrimitiveClassified h
  have hmncp : Int.gcd m n = 1 := by
    rw [Int.gcd_comm]
    exact hnmcp
  cases' Int.emod_two_eq_zero_or_one m with hm2 hm2 <;>
  -- ⊢ IsPrimitiveClassified h
    cases' Int.emod_two_eq_zero_or_one n with hn2 hn2
    -- ⊢ IsPrimitiveClassified h
    -- ⊢ IsPrimitiveClassified h
  · -- m even, n even
    exfalso
    -- ⊢ False
    have h1 : 2 ∣ (Int.gcd n m : ℤ) :=
      Int.dvd_gcd (Int.dvd_of_emod_eq_zero hn2) (Int.dvd_of_emod_eq_zero hm2)
    rw [hnmcp] at h1
    -- ⊢ False
    revert h1
    -- ⊢ 2 ∣ ↑1 → False
    norm_num
    -- 🎉 no goals
  · -- m even, n odd
    apply h.isPrimitiveClassified_aux hc hzpos hm2n2 hv2 hw2 _ hmncp
    -- ⊢ m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0
    · apply Or.intro_left
      -- ⊢ m % 2 = 0 ∧ n % 2 = 1
      exact And.intro hm2 hn2
      -- 🎉 no goals
    · apply coprime_sq_sub_sq_add_of_even_odd hmncp hm2 hn2
      -- 🎉 no goals
  · -- m odd, n even
    apply h.isPrimitiveClassified_aux hc hzpos hm2n2 hv2 hw2 _ hmncp
    -- ⊢ m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0
    · apply Or.intro_right
      -- ⊢ m % 2 = 1 ∧ n % 2 = 0
      exact And.intro hm2 hn2
      -- 🎉 no goals
    apply coprime_sq_sub_sq_add_of_odd_even hmncp hm2 hn2
    -- 🎉 no goals
  · -- m odd, n odd
    exfalso
    -- ⊢ False
    have h1 :
      2 ∣ m ^ 2 + n ^ 2 ∧
        2 ∣ m ^ 2 - n ^ 2 ∧
          (m ^ 2 - n ^ 2) / 2 % 2 = 0 ∧ Int.gcd ((m ^ 2 - n ^ 2) / 2) ((m ^ 2 + n ^ 2) / 2) = 1 :=
      coprime_sq_sub_sq_sum_of_odd_odd hmncp hm2 hn2
    have h2 : y = (m ^ 2 - n ^ 2) / 2 ∧ z = (m ^ 2 + n ^ 2) / 2 := by
      apply Rat.div_int_inj hzpos _ (h.coprime_of_coprime hc) h1.2.2.2
      · show w = _
        rw [← Rat.divInt_eq_div, ← Rat.divInt_mul_right (by norm_num : (2 : ℤ) ≠ 0)]
        rw [Int.ediv_mul_cancel h1.1, Int.ediv_mul_cancel h1.2.1, hw2]
        norm_cast
      · apply (mul_lt_mul_right (by norm_num : 0 < (2 : ℤ))).mp
        rw [Int.ediv_mul_cancel h1.1, zero_mul]
        exact hm2n2
    rw [h2.1, h1.2.2.1] at hyo
    -- ⊢ False
    revert hyo
    -- ⊢ 0 = 1 → False
    norm_num
    -- 🎉 no goals
#align pythagorean_triple.is_primitive_classified_of_coprime_of_odd_of_pos PythagoreanTriple.isPrimitiveClassified_of_coprime_of_odd_of_pos

theorem isPrimitiveClassified_of_coprime_of_pos (hc : Int.gcd x y = 1) (hzpos : 0 < z) :
    h.IsPrimitiveClassified := by
  cases' h.even_odd_of_coprime hc with h1 h2
  -- ⊢ IsPrimitiveClassified h
  · exact h.isPrimitiveClassified_of_coprime_of_odd_of_pos hc h1.right hzpos
    -- 🎉 no goals
  rw [Int.gcd_comm] at hc
  -- ⊢ IsPrimitiveClassified h
  obtain ⟨m, n, H⟩ := h.symm.isPrimitiveClassified_of_coprime_of_odd_of_pos hc h2.left hzpos
  -- ⊢ IsPrimitiveClassified h
  use m, n; tauto
  -- ⊢ (x = m ^ 2 - n ^ 2 ∧ y = 2 * m * n ∨ x = 2 * m * n ∧ y = m ^ 2 - n ^ 2) ∧ In …
            -- 🎉 no goals
#align pythagorean_triple.is_primitive_classified_of_coprime_of_pos PythagoreanTriple.isPrimitiveClassified_of_coprime_of_pos

theorem isPrimitiveClassified_of_coprime (hc : Int.gcd x y = 1) : h.IsPrimitiveClassified := by
  by_cases hz : 0 < z
  -- ⊢ IsPrimitiveClassified h
  · exact h.isPrimitiveClassified_of_coprime_of_pos hc hz
    -- 🎉 no goals
  have h' : PythagoreanTriple x y (-z) := by simpa [PythagoreanTriple, neg_mul_neg] using h.eq
  -- ⊢ IsPrimitiveClassified h
  apply h'.isPrimitiveClassified_of_coprime_of_pos hc
  -- ⊢ 0 < -z
  apply lt_of_le_of_ne _ (h'.ne_zero_of_coprime hc).symm
  -- ⊢ 0 ≤ -z
  exact le_neg.mp (not_lt.mp hz)
  -- 🎉 no goals
#align pythagorean_triple.is_primitive_classified_of_coprime PythagoreanTriple.isPrimitiveClassified_of_coprime

theorem classified : h.IsClassified := by
  by_cases h0 : Int.gcd x y = 0
  -- ⊢ IsClassified h
  · have hx : x = 0 := by
      apply Int.natAbs_eq_zero.mp
      apply Nat.eq_zero_of_gcd_eq_zero_left h0
    have hy : y = 0 := by
      apply Int.natAbs_eq_zero.mp
      apply Nat.eq_zero_of_gcd_eq_zero_right h0
    use 0, 1, 0
    -- ⊢ (x = 0 * (1 ^ 2 - 0 ^ 2) ∧ y = 0 * (2 * 1 * 0) ∨ x = 0 * (2 * 1 * 0) ∧ y = 0 …
    field_simp [hx, hy]
    -- 🎉 no goals
  apply h.isClassified_of_normalize_isPrimitiveClassified
  -- ⊢ IsPrimitiveClassified (_ : PythagoreanTriple (x / ↑(Int.gcd x y)) (y / ↑(Int …
  apply h.normalize.isPrimitiveClassified_of_coprime
  -- ⊢ Int.gcd (x / ↑(Int.gcd x y)) (y / ↑(Int.gcd x y)) = 1
  apply Int.gcd_div_gcd_div_gcd (Nat.pos_of_ne_zero h0)
  -- 🎉 no goals
#align pythagorean_triple.classified PythagoreanTriple.classified

theorem coprime_classification :
    PythagoreanTriple x y z ∧ Int.gcd x y = 1 ↔
      ∃ m n,
        (x = m ^ 2 - n ^ 2 ∧ y = 2 * m * n ∨ x = 2 * m * n ∧ y = m ^ 2 - n ^ 2) ∧
          (z = m ^ 2 + n ^ 2 ∨ z = -(m ^ 2 + n ^ 2)) ∧
            Int.gcd m n = 1 ∧ (m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0) := by
  clear h -- porting note: don't want this variable, but can't use `include` / `omit`
  -- ⊢ PythagoreanTriple x y z ∧ Int.gcd x y = 1 ↔ ∃ m n, (x = m ^ 2 - n ^ 2 ∧ y =  …
  constructor
  -- ⊢ PythagoreanTriple x y z ∧ Int.gcd x y = 1 → ∃ m n, (x = m ^ 2 - n ^ 2 ∧ y =  …
  · intro h
    -- ⊢ ∃ m n, (x = m ^ 2 - n ^ 2 ∧ y = 2 * m * n ∨ x = 2 * m * n ∧ y = m ^ 2 - n ^  …
    obtain ⟨m, n, H⟩ := h.left.isPrimitiveClassified_of_coprime h.right
    -- ⊢ ∃ m n, (x = m ^ 2 - n ^ 2 ∧ y = 2 * m * n ∨ x = 2 * m * n ∧ y = m ^ 2 - n ^  …
    use m, n
    -- ⊢ (x = m ^ 2 - n ^ 2 ∧ y = 2 * m * n ∨ x = 2 * m * n ∧ y = m ^ 2 - n ^ 2) ∧ (z …
    rcases H with ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, co, pp⟩
    -- ⊢ (m ^ 2 - n ^ 2 = m ^ 2 - n ^ 2 ∧ 2 * m * n = 2 * m * n ∨ m ^ 2 - n ^ 2 = 2 * …
    · refine' ⟨Or.inl ⟨rfl, rfl⟩, _, co, pp⟩
      -- ⊢ z = m ^ 2 + n ^ 2 ∨ z = -(m ^ 2 + n ^ 2)
      have : z ^ 2 = (m ^ 2 + n ^ 2) ^ 2 := by
        rw [sq, ← h.left.eq]
        ring
      simpa using eq_or_eq_neg_of_sq_eq_sq _ _ this
      -- 🎉 no goals
    · refine' ⟨Or.inr ⟨rfl, rfl⟩, _, co, pp⟩
      -- ⊢ z = m ^ 2 + n ^ 2 ∨ z = -(m ^ 2 + n ^ 2)
      have : z ^ 2 = (m ^ 2 + n ^ 2) ^ 2 := by
        rw [sq, ← h.left.eq]
        ring
      simpa using eq_or_eq_neg_of_sq_eq_sq _ _ this
      -- 🎉 no goals
  · delta PythagoreanTriple
    -- ⊢ (∃ m n, (x = m ^ 2 - n ^ 2 ∧ y = 2 * m * n ∨ x = 2 * m * n ∧ y = m ^ 2 - n ^ …
    rintro ⟨m, n, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, rfl | rfl, co, pp⟩ <;>
      first
      | constructor; ring; exact coprime_sq_sub_mul co pp
      | constructor; ring; rw [Int.gcd_comm]; exact coprime_sq_sub_mul co pp
#align pythagorean_triple.coprime_classification PythagoreanTriple.coprime_classification

/-- by assuming `x` is odd and `z` is positive we get a slightly more precise classification of
the Pythagorean triple `x ^ 2 + y ^ 2 = z ^ 2`-/
theorem coprime_classification' {x y z : ℤ} (h : PythagoreanTriple x y z)
    (h_coprime : Int.gcd x y = 1) (h_parity : x % 2 = 1) (h_pos : 0 < z) :
    ∃ m n,
      x = m ^ 2 - n ^ 2 ∧
        y = 2 * m * n ∧
          z = m ^ 2 + n ^ 2 ∧
            Int.gcd m n = 1 ∧ (m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0) ∧ 0 ≤ m := by
  obtain ⟨m, n, ht1, ht2, ht3, ht4⟩ :=
    PythagoreanTriple.coprime_classification.mp (And.intro h h_coprime)
  cases' le_or_lt 0 m with hm hm
  -- ⊢ ∃ m n, x = m ^ 2 - n ^ 2 ∧ y = 2 * m * n ∧ z = m ^ 2 + n ^ 2 ∧ Int.gcd m n = …
  · use m, n
    -- ⊢ x = m ^ 2 - n ^ 2 ∧ y = 2 * m * n ∧ z = m ^ 2 + n ^ 2 ∧ Int.gcd m n = 1 ∧ (m …
    cases' ht1 with h_odd h_even
    -- ⊢ x = m ^ 2 - n ^ 2 ∧ y = 2 * m * n ∧ z = m ^ 2 + n ^ 2 ∧ Int.gcd m n = 1 ∧ (m …
    · apply And.intro h_odd.1
      -- ⊢ y = 2 * m * n ∧ z = m ^ 2 + n ^ 2 ∧ Int.gcd m n = 1 ∧ (m % 2 = 0 ∧ n % 2 = 1 …
      apply And.intro h_odd.2
      -- ⊢ z = m ^ 2 + n ^ 2 ∧ Int.gcd m n = 1 ∧ (m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n …
      cases' ht2 with h_pos h_neg
      -- ⊢ z = m ^ 2 + n ^ 2 ∧ Int.gcd m n = 1 ∧ (m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n …
      · apply And.intro h_pos (And.intro ht3 (And.intro ht4 hm))
        -- 🎉 no goals
      · exfalso
        -- ⊢ False
        revert h_pos
        -- ⊢ 0 < z → False
        rw [h_neg]
        -- ⊢ 0 < -(m ^ 2 + n ^ 2) → False
        exact imp_false.mpr (not_lt.mpr (neg_nonpos.mpr (add_nonneg (sq_nonneg m) (sq_nonneg n))))
        -- 🎉 no goals
    exfalso
    -- ⊢ False
    rcases h_even with ⟨rfl, -⟩
    -- ⊢ False
    rw [mul_assoc, Int.mul_emod_right] at h_parity
    -- ⊢ False
    exact zero_ne_one h_parity
    -- 🎉 no goals
  · use -m, -n
    -- ⊢ x = (-m) ^ 2 - (-n) ^ 2 ∧ y = 2 * -m * -n ∧ z = (-m) ^ 2 + (-n) ^ 2 ∧ Int.gc …
    cases' ht1 with h_odd h_even
    -- ⊢ x = (-m) ^ 2 - (-n) ^ 2 ∧ y = 2 * -m * -n ∧ z = (-m) ^ 2 + (-n) ^ 2 ∧ Int.gc …
    · rw [neg_sq m]
      -- ⊢ x = m ^ 2 - (-n) ^ 2 ∧ y = 2 * -m * -n ∧ z = m ^ 2 + (-n) ^ 2 ∧ Int.gcd (-m) …
      rw [neg_sq n]
      -- ⊢ x = m ^ 2 - n ^ 2 ∧ y = 2 * -m * -n ∧ z = m ^ 2 + n ^ 2 ∧ Int.gcd (-m) (-n)  …
      apply And.intro h_odd.1
      -- ⊢ y = 2 * -m * -n ∧ z = m ^ 2 + n ^ 2 ∧ Int.gcd (-m) (-n) = 1 ∧ (-m % 2 = 0 ∧  …
      constructor
      -- ⊢ y = 2 * -m * -n
      · rw [h_odd.2]
        -- ⊢ 2 * m * n = 2 * -m * -n
        ring
        -- 🎉 no goals
      cases' ht2 with h_pos h_neg
      -- ⊢ z = m ^ 2 + n ^ 2 ∧ Int.gcd (-m) (-n) = 1 ∧ (-m % 2 = 0 ∧ -n % 2 = 1 ∨ -m %  …
      · apply And.intro h_pos
        -- ⊢ Int.gcd (-m) (-n) = 1 ∧ (-m % 2 = 0 ∧ -n % 2 = 1 ∨ -m % 2 = 1 ∧ -n % 2 = 0)  …
        constructor
        -- ⊢ Int.gcd (-m) (-n) = 1
        · delta Int.gcd
          -- ⊢ Nat.gcd (Int.natAbs (-m)) (Int.natAbs (-n)) = 1
          rw [Int.natAbs_neg, Int.natAbs_neg]
          -- ⊢ Nat.gcd (Int.natAbs m) (Int.natAbs n) = 1
          exact ht3
          -- 🎉 no goals
        · rw [Int.neg_emod_two, Int.neg_emod_two]
          -- ⊢ (m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0) ∧ 0 ≤ -m
          apply And.intro ht4
          -- ⊢ 0 ≤ -m
          linarith
          -- 🎉 no goals
      · exfalso
        -- ⊢ False
        revert h_pos
        -- ⊢ 0 < z → False
        rw [h_neg]
        -- ⊢ 0 < -(m ^ 2 + n ^ 2) → False
        exact imp_false.mpr (not_lt.mpr (neg_nonpos.mpr (add_nonneg (sq_nonneg m) (sq_nonneg n))))
        -- 🎉 no goals
    exfalso
    -- ⊢ False
    rcases h_even with ⟨rfl, -⟩
    -- ⊢ False
    rw [mul_assoc, Int.mul_emod_right] at h_parity
    -- ⊢ False
    exact zero_ne_one h_parity
    -- 🎉 no goals
#align pythagorean_triple.coprime_classification' PythagoreanTriple.coprime_classification'

/-- **Formula for Pythagorean Triples** -/
theorem classification :
    PythagoreanTriple x y z ↔
      ∃ k m n,
        (x = k * (m ^ 2 - n ^ 2) ∧ y = k * (2 * m * n) ∨
            x = k * (2 * m * n) ∧ y = k * (m ^ 2 - n ^ 2)) ∧
          (z = k * (m ^ 2 + n ^ 2) ∨ z = -k * (m ^ 2 + n ^ 2)) := by
  clear h
  -- ⊢ PythagoreanTriple x y z ↔ ∃ k m n, (x = k * (m ^ 2 - n ^ 2) ∧ y = k * (2 * m …
  constructor
  -- ⊢ PythagoreanTriple x y z → ∃ k m n, (x = k * (m ^ 2 - n ^ 2) ∧ y = k * (2 * m …
  · intro h
    -- ⊢ ∃ k m n, (x = k * (m ^ 2 - n ^ 2) ∧ y = k * (2 * m * n) ∨ x = k * (2 * m * n …
    obtain ⟨k, m, n, H⟩ := h.classified
    -- ⊢ ∃ k m n, (x = k * (m ^ 2 - n ^ 2) ∧ y = k * (2 * m * n) ∨ x = k * (2 * m * n …
    use k, m, n
    -- ⊢ (x = k * (m ^ 2 - n ^ 2) ∧ y = k * (2 * m * n) ∨ x = k * (2 * m * n) ∧ y = k …
    rcases H with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    -- ⊢ (k * (m ^ 2 - n ^ 2) = k * (m ^ 2 - n ^ 2) ∧ k * (2 * m * n) = k * (2 * m *  …
    · refine' ⟨Or.inl ⟨rfl, rfl⟩, _⟩
      -- ⊢ z = k * (m ^ 2 + n ^ 2) ∨ z = -k * (m ^ 2 + n ^ 2)
      have : z ^ 2 = (k * (m ^ 2 + n ^ 2)) ^ 2 := by
        rw [sq, ← h.eq]
        ring
      simpa using eq_or_eq_neg_of_sq_eq_sq _ _ this
      -- 🎉 no goals
    · refine' ⟨Or.inr ⟨rfl, rfl⟩, _⟩
      -- ⊢ z = k * (m ^ 2 + n ^ 2) ∨ z = -k * (m ^ 2 + n ^ 2)
      have : z ^ 2 = (k * (m ^ 2 + n ^ 2)) ^ 2 := by
        rw [sq, ← h.eq]
        ring
      simpa using eq_or_eq_neg_of_sq_eq_sq _ _ this
      -- 🎉 no goals
  · rintro ⟨k, m, n, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, rfl | rfl⟩ <;> delta PythagoreanTriple <;> ring
                                                             -- ⊢ k * (m ^ 2 - n ^ 2) * (k * (m ^ 2 - n ^ 2)) + k * (2 * m * n) * (k * (2 * m  …
                                                             -- ⊢ k * (m ^ 2 - n ^ 2) * (k * (m ^ 2 - n ^ 2)) + k * (2 * m * n) * (k * (2 * m  …
                                                             -- ⊢ k * (2 * m * n) * (k * (2 * m * n)) + k * (m ^ 2 - n ^ 2) * (k * (m ^ 2 - n  …
                                                             -- ⊢ k * (2 * m * n) * (k * (2 * m * n)) + k * (m ^ 2 - n ^ 2) * (k * (m ^ 2 - n  …
                                                                                         -- 🎉 no goals
                                                                                         -- 🎉 no goals
                                                                                         -- 🎉 no goals
                                                                                         -- 🎉 no goals
#align pythagorean_triple.classification PythagoreanTriple.classification

end PythagoreanTriple
