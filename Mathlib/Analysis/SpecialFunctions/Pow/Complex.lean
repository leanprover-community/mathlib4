/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Sébastien Gouëzel,
  Rémy Degenne, David Loeffler
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Log

#align_import analysis.special_functions.pow.complex from "leanprover-community/mathlib"@"4fa54b337f7d52805480306db1b1439c741848c8"

/-! # Power function on `ℂ`

We construct the power functions `x ^ y`, where `x` and `y` are complex numbers.
-/

local macro_rules | `($x ^ $y)   => `(HPow.hPow $x $y) -- Porting note: See issue #2220

open Classical Real Topology Filter ComplexConjugate Finset Set

namespace Complex

/-- The complex power function `x ^ y`, given by `x ^ y = exp(y log x)` (where `log` is the
principal determination of the logarithm), unless `x = 0` where one sets `0 ^ 0 = 1` and
`0 ^ y = 0` for `y ≠ 0`. -/
noncomputable def cpow (x y : ℂ) : ℂ :=
  if x = 0 then if y = 0 then 1 else 0 else exp (log x * y)
#align complex.cpow Complex.cpow

noncomputable instance : Pow ℂ ℂ :=
  ⟨cpow⟩

@[simp]
theorem cpow_eq_pow (x y : ℂ) : cpow x y = x ^ y :=
  rfl
#align complex.cpow_eq_pow Complex.cpow_eq_pow

theorem cpow_def (x y : ℂ) : x ^ y = if x = 0 then if y = 0 then 1 else 0 else exp (log x * y) :=
  rfl
#align complex.cpow_def Complex.cpow_def

theorem cpow_def_of_ne_zero {x : ℂ} (hx : x ≠ 0) (y : ℂ) : x ^ y = exp (log x * y) :=
  if_neg hx
#align complex.cpow_def_of_ne_zero Complex.cpow_def_of_ne_zero

@[simp]
theorem cpow_zero (x : ℂ) : x ^ (0 : ℂ) = 1 := by simp [cpow_def]
                                                  -- 🎉 no goals
#align complex.cpow_zero Complex.cpow_zero

@[simp]
theorem cpow_eq_zero_iff (x y : ℂ) : x ^ y = 0 ↔ x = 0 ∧ y ≠ 0 := by
  simp only [cpow_def]
  -- ⊢ (if x = 0 then if y = 0 then 1 else 0 else exp (log x * y)) = 0 ↔ x = 0 ∧ y  …
  split_ifs <;> simp [*, exp_ne_zero]
                -- 🎉 no goals
                -- 🎉 no goals
                -- 🎉 no goals
#align complex.cpow_eq_zero_iff Complex.cpow_eq_zero_iff

@[simp]
theorem zero_cpow {x : ℂ} (h : x ≠ 0) : (0 : ℂ) ^ x = 0 := by simp [cpow_def, *]
                                                              -- 🎉 no goals
#align complex.zero_cpow Complex.zero_cpow

theorem zero_cpow_eq_iff {x : ℂ} {a : ℂ} : (0 : ℂ) ^ x = a ↔ x ≠ 0 ∧ a = 0 ∨ x = 0 ∧ a = 1 := by
  constructor
  -- ⊢ 0 ^ x = a → x ≠ 0 ∧ a = 0 ∨ x = 0 ∧ a = 1
  · intro hyp
    -- ⊢ x ≠ 0 ∧ a = 0 ∨ x = 0 ∧ a = 1
    simp only [cpow_def, eq_self_iff_true, if_true] at hyp
    -- ⊢ x ≠ 0 ∧ a = 0 ∨ x = 0 ∧ a = 1
    by_cases x = 0
    -- ⊢ x ≠ 0 ∧ a = 0 ∨ x = 0 ∧ a = 1
    -- ⊢ x ≠ 0 ∧ a = 0 ∨ x = 0 ∧ a = 1
    · subst h
      -- ⊢ 0 ≠ 0 ∧ a = 0 ∨ 0 = 0 ∧ a = 1
      simp only [if_true, eq_self_iff_true] at hyp
      -- ⊢ 0 ≠ 0 ∧ a = 0 ∨ 0 = 0 ∧ a = 1
      right
      -- ⊢ 0 = 0 ∧ a = 1
      exact ⟨rfl, hyp.symm⟩
      -- 🎉 no goals
    · rw [if_neg h] at hyp
      -- ⊢ x ≠ 0 ∧ a = 0 ∨ x = 0 ∧ a = 1
      left
      -- ⊢ x ≠ 0 ∧ a = 0
      exact ⟨h, hyp.symm⟩
      -- 🎉 no goals
  · rintro (⟨h, rfl⟩ | ⟨rfl, rfl⟩)
    -- ⊢ 0 ^ x = 0
    · exact zero_cpow h
      -- 🎉 no goals
    · exact cpow_zero _
      -- 🎉 no goals
#align complex.zero_cpow_eq_iff Complex.zero_cpow_eq_iff

theorem eq_zero_cpow_iff {x : ℂ} {a : ℂ} : a = (0 : ℂ) ^ x ↔ x ≠ 0 ∧ a = 0 ∨ x = 0 ∧ a = 1 := by
  rw [← zero_cpow_eq_iff, eq_comm]
  -- 🎉 no goals
#align complex.eq_zero_cpow_iff Complex.eq_zero_cpow_iff

@[simp]
theorem cpow_one (x : ℂ) : x ^ (1 : ℂ) = x :=
  if hx : x = 0 then by simp [hx, cpow_def]
                        -- 🎉 no goals
  else by rw [cpow_def, if_neg (one_ne_zero : (1 : ℂ) ≠ 0), if_neg hx, mul_one, exp_log hx]
          -- 🎉 no goals
#align complex.cpow_one Complex.cpow_one

@[simp]
theorem one_cpow (x : ℂ) : (1 : ℂ) ^ x = 1 := by
  rw [cpow_def]
  -- ⊢ (if 1 = 0 then if x = 0 then 1 else 0 else exp (log 1 * x)) = 1
  split_ifs <;> simp_all [one_ne_zero]
                -- 🎉 no goals
                -- 🎉 no goals
                -- 🎉 no goals
#align complex.one_cpow Complex.one_cpow

theorem cpow_add {x : ℂ} (y z : ℂ) (hx : x ≠ 0) : x ^ (y + z) = x ^ y * x ^ z := by
  simp only [cpow_def, ite_mul, boole_mul, mul_ite, mul_boole]
  -- ⊢ (if x = 0 then if y + z = 0 then 1 else 0 else exp (log x * (y + z))) = if x …
  simp_all [exp_add, mul_add]
  -- 🎉 no goals
#align complex.cpow_add Complex.cpow_add

theorem cpow_mul {x y : ℂ} (z : ℂ) (h₁ : -π < (log x * y).im) (h₂ : (log x * y).im ≤ π) :
    x ^ (y * z) = (x ^ y) ^ z := by
  simp only [cpow_def]
  -- ⊢ (if x = 0 then if y * z = 0 then 1 else 0 else exp (log x * (y * z))) = if ( …
  split_ifs <;> simp_all [exp_ne_zero, log_exp h₁ h₂, mul_assoc]
                -- 🎉 no goals
                -- 🎉 no goals
                -- 🎉 no goals
                -- 🎉 no goals
                -- 🎉 no goals
                -- 🎉 no goals
                -- 🎉 no goals
                -- 🎉 no goals
                -- 🎉 no goals
                -- 🎉 no goals
                -- 🎉 no goals
                -- 🎉 no goals
                -- 🎉 no goals
                -- 🎉 no goals
                -- 🎉 no goals
#align complex.cpow_mul Complex.cpow_mul

theorem cpow_neg (x y : ℂ) : x ^ (-y) = (x ^ y)⁻¹ := by
  simp only [cpow_def, neg_eq_zero, mul_neg]
  -- ⊢ (if x = 0 then if y = 0 then 1 else 0 else exp (-(log x * y))) = (if x = 0 t …
  split_ifs <;> simp [exp_neg]
                -- 🎉 no goals
                -- 🎉 no goals
                -- 🎉 no goals
#align complex.cpow_neg Complex.cpow_neg

theorem cpow_sub {x : ℂ} (y z : ℂ) (hx : x ≠ 0) : x ^ (y - z) = x ^ y / x ^ z := by
  rw [sub_eq_add_neg, cpow_add _ _ hx, cpow_neg, div_eq_mul_inv]
  -- 🎉 no goals
#align complex.cpow_sub Complex.cpow_sub

theorem cpow_neg_one (x : ℂ) : x ^ (-1 : ℂ) = x⁻¹ := by simpa using cpow_neg x 1
                                                        -- 🎉 no goals
#align complex.cpow_neg_one Complex.cpow_neg_one

@[simp, norm_cast]
theorem cpow_nat_cast (x : ℂ) : ∀ n : ℕ, x ^ (n : ℂ) = x ^ n
  | 0 => by simp
            -- 🎉 no goals
  | n + 1 =>
    if hx : x = 0 then by
      simp only [hx, pow_succ, Complex.zero_cpow (Nat.cast_ne_zero.2 (Nat.succ_ne_zero _)),
        zero_mul]
    else by simp [cpow_add, hx, pow_add, cpow_nat_cast x n]
            -- 🎉 no goals
#align complex.cpow_nat_cast Complex.cpow_nat_cast

@[simp]
theorem cpow_two (x : ℂ) : x ^ (2 : ℂ) = x ^ (2 : ℕ) := by
  rw [← cpow_nat_cast]
  -- ⊢ x ^ 2 = x ^ ↑2
  simp only [Nat.cast_ofNat]
  -- 🎉 no goals
#align complex.cpow_two Complex.cpow_two

open Int in
@[simp, norm_cast]
theorem cpow_int_cast (x : ℂ) : ∀ n : ℤ, x ^ (n : ℂ) = x ^ n
  | (n : ℕ) => by simp
                  -- 🎉 no goals
  | -[n+1] => by
    rw [zpow_negSucc]
    -- ⊢ x ^ ↑-[n+1] = (x ^ (n + 1))⁻¹
    simp only [Int.negSucc_coe, Int.cast_neg, Complex.cpow_neg, inv_eq_one_div, Int.cast_ofNat,
      cpow_nat_cast]
#align complex.cpow_int_cast Complex.cpow_int_cast

theorem cpow_nat_inv_pow (x : ℂ) {n : ℕ} (hn : n ≠ 0) : (x ^ (n⁻¹ : ℂ)) ^ n = x := by
  suffices im (log x * (n⁻¹ : ℂ)) ∈ Ioc (-π) π by
    rw [← cpow_nat_cast, ← cpow_mul _ this.1 this.2, inv_mul_cancel, cpow_one]
    exact_mod_cast hn
  rw [mul_comm, ← ofReal_nat_cast, ← ofReal_inv, ofReal_mul_im, ← div_eq_inv_mul]
  -- ⊢ (log x).im / ↑n ∈ Set.Ioc (-π) π
  rw [← pos_iff_ne_zero] at hn
  -- ⊢ (log x).im / ↑n ∈ Set.Ioc (-π) π
  have hn' : 0 < (n : ℝ) := by assumption_mod_cast
  -- ⊢ (log x).im / ↑n ∈ Set.Ioc (-π) π
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast Nat.succ_le_iff.2 hn
  -- ⊢ (log x).im / ↑n ∈ Set.Ioc (-π) π
  constructor
  -- ⊢ -π < (log x).im / ↑n
  · rw [lt_div_iff hn']
    -- ⊢ -π * ↑n < (log x).im
    calc
      -π * n ≤ -π * 1 := mul_le_mul_of_nonpos_left hn1 (neg_nonpos.2 Real.pi_pos.le)
      _ = -π := (mul_one _)
      _ < im (log x) := neg_pi_lt_log_im _

  · rw [div_le_iff hn']
    -- ⊢ (log x).im ≤ π * ↑n
    calc
      im (log x) ≤ π := log_im_le_pi _
      _ = π * 1 := (mul_one π).symm
      _ ≤ π * n := mul_le_mul_of_nonneg_left hn1 Real.pi_pos.le

#align complex.cpow_nat_inv_pow Complex.cpow_nat_inv_pow

theorem mul_cpow_ofReal_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (r : ℂ) :
    ((a : ℂ) * (b : ℂ)) ^ r = (a : ℂ) ^ r * (b : ℂ) ^ r := by
  rcases eq_or_ne r 0 with (rfl | hr)
  -- ⊢ (↑a * ↑b) ^ 0 = ↑a ^ 0 * ↑b ^ 0
  · simp only [cpow_zero, mul_one]
    -- 🎉 no goals
  rcases eq_or_lt_of_le ha with (rfl | ha')
  -- ⊢ (↑0 * ↑b) ^ r = ↑0 ^ r * ↑b ^ r
  · rw [ofReal_zero, zero_mul, zero_cpow hr, zero_mul]
    -- 🎉 no goals
  rcases eq_or_lt_of_le hb with (rfl | hb')
  -- ⊢ (↑a * ↑0) ^ r = ↑a ^ r * ↑0 ^ r
  · rw [ofReal_zero, mul_zero, zero_cpow hr, mul_zero]
    -- 🎉 no goals
  have ha'' : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr ha'.ne'
  -- ⊢ (↑a * ↑b) ^ r = ↑a ^ r * ↑b ^ r
  have hb'' : (b : ℂ) ≠ 0 := ofReal_ne_zero.mpr hb'.ne'
  -- ⊢ (↑a * ↑b) ^ r = ↑a ^ r * ↑b ^ r
  rw [cpow_def_of_ne_zero (mul_ne_zero ha'' hb''), log_ofReal_mul ha' hb'', ofReal_log ha,
    add_mul, exp_add, ← cpow_def_of_ne_zero ha'', ← cpow_def_of_ne_zero hb'']
#align complex.mul_cpow_of_real_nonneg Complex.mul_cpow_ofReal_nonneg

theorem inv_cpow_eq_ite (x : ℂ) (n : ℂ) :
    x⁻¹ ^ n = if x.arg = π then conj (x ^ conj n)⁻¹ else (x ^ n)⁻¹ := by
  simp_rw [Complex.cpow_def, log_inv_eq_ite, inv_eq_zero, map_eq_zero, ite_mul, neg_mul,
    IsROrC.conj_inv, apply_ite conj, apply_ite exp, apply_ite Inv.inv, map_zero, map_one, exp_neg,
    inv_one, inv_zero, ← exp_conj, map_mul, conj_conj]
  split_ifs with hx hn ha ha <;> rfl
                                 -- 🎉 no goals
                                 -- 🎉 no goals
                                 -- 🎉 no goals
                                 -- 🎉 no goals
                                 -- 🎉 no goals
                                 -- 🎉 no goals
#align complex.inv_cpow_eq_ite Complex.inv_cpow_eq_ite

theorem inv_cpow (x : ℂ) (n : ℂ) (hx : x.arg ≠ π) : x⁻¹ ^ n = (x ^ n)⁻¹ := by
  rw [inv_cpow_eq_ite, if_neg hx]
  -- 🎉 no goals
#align complex.inv_cpow Complex.inv_cpow

/-- `Complex.inv_cpow_eq_ite` with the `ite` on the other side. -/
theorem inv_cpow_eq_ite' (x : ℂ) (n : ℂ) :
    (x ^ n)⁻¹ = if x.arg = π then conj (x⁻¹ ^ conj n) else x⁻¹ ^ n := by
  rw [inv_cpow_eq_ite, apply_ite conj, conj_conj, conj_conj]
  -- ⊢ (x ^ n)⁻¹ = if arg x = π then if arg x = π then (x ^ n)⁻¹ else ↑(starRingEnd …
  split_ifs with h
  -- ⊢ (x ^ n)⁻¹ = (x ^ n)⁻¹
  · rfl
    -- 🎉 no goals
  · rw [inv_cpow _ _ h]
    -- 🎉 no goals
#align complex.inv_cpow_eq_ite' Complex.inv_cpow_eq_ite'

theorem conj_cpow_eq_ite (x : ℂ) (n : ℂ) :
    conj x ^ n = if x.arg = π then x ^ n else conj (x ^ conj n) := by
  simp_rw [cpow_def, map_eq_zero, apply_ite conj, map_one, map_zero, ← exp_conj, map_mul, conj_conj,
    log_conj_eq_ite]
  split_ifs with hcx hn hx <;> rfl
                               -- 🎉 no goals
                               -- 🎉 no goals
                               -- 🎉 no goals
                               -- 🎉 no goals
                               -- 🎉 no goals
                               -- 🎉 no goals
#align complex.conj_cpow_eq_ite Complex.conj_cpow_eq_ite

theorem conj_cpow (x : ℂ) (n : ℂ) (hx : x.arg ≠ π) : conj x ^ n = conj (x ^ conj n) := by
  rw [conj_cpow_eq_ite, if_neg hx]
  -- 🎉 no goals
#align complex.conj_cpow Complex.conj_cpow

theorem cpow_conj (x : ℂ) (n : ℂ) (hx : x.arg ≠ π) : x ^ conj n = conj (conj x ^ n) := by
  rw [conj_cpow _ _ hx, conj_conj]
  -- 🎉 no goals
#align complex.cpow_conj Complex.cpow_conj

end Complex

-- section Tactics

-- /-!
-- ## Tactic extensions for complex powers
-- -/


-- namespace NormNum

-- theorem cpow_pos (a b : ℂ) (b' : ℕ) (c : ℂ) (hb : b = b') (h : a ^ b' = c) : a ^ b = c := by
--   rw [← h, hb, Complex.cpow_nat_cast]
-- #align norm_num.cpow_pos NormNum.cpow_pos

-- theorem cpow_neg (a b : ℂ) (b' : ℕ) (c c' : ℂ) (hb : b = b') (h : a ^ b' = c) (hc : c⁻¹ = c') :
--     a ^ (-b) = c' := by rw [← hc, ← h, hb, Complex.cpow_neg, Complex.cpow_nat_cast]
-- #align norm_num.cpow_neg NormNum.cpow_neg

-- open Tactic

-- /-- Generalized version of `prove_cpow`, `prove_nnrpow`, `prove_ennrpow`. -/
-- unsafe def prove_rpow' (pos neg zero : Name) (α β one a b : expr) : tactic (expr × expr) := do
--   let na ← a.to_rat
--   let icα ← mk_instance_cache α
--   let icβ ← mk_instance_cache β
--   match match_sign b with
--     | Sum.inl b => do
--       let nc ← mk_instance_cache q(ℕ)
--       let (icβ, nc, b', hb) ← prove_nat_uncast icβ nc b
--       let (icα, c, h) ← prove_pow a na icα b'
--       let cr ← c
--       let (icα, c', hc) ← prove_inv icα c cr
--       pure (c', (expr.const neg []).mk_app [a, b, b', c, c', hb, h, hc])
--     | Sum.inr ff => pure (one, expr.const zero [] a)
--     | Sum.inr tt => do
--       let nc ← mk_instance_cache q(ℕ)
--       let (icβ, nc, b', hb) ← prove_nat_uncast icβ nc b
--       let (icα, c, h) ← prove_pow a na icα b'
--       pure (c, (expr.const Pos []).mk_app [a, b, b', c, hb, h])
-- #align norm_num.prove_rpow' norm_num.prove_rpow'

-- /-- Evaluate `Complex.cpow a b` where `a` is a rational numeral and `b` is an integer. -/
-- unsafe def prove_cpow : expr → expr → tactic (expr × expr) :=
--   prove_rpow' `` cpow_pos `` cpow_neg `` Complex.cpow_zero q(ℂ) q(ℂ) q((1 : ℂ))
-- #align norm_num.prove_cpow norm_num.prove_cpow

-- /-- Evaluates expressions of the form `cpow a b` and `a ^ b` in the special case where
-- `b` is an integer and `a` is a positive rational (so it's really just a rational power). -/
-- @[norm_num]
-- unsafe def eval_cpow : expr → tactic (expr × expr)
--   | q(@Pow.pow _ _ Complex.hasPow $(a) $(b)) => b.to_int >> prove_cpow a b
--   | q(Complex.cpow $(a) $(b)) => b.to_int >> prove_cpow a b
--   | _ => tactic.failed
-- #align norm_num.eval_cpow norm_num.eval_cpow

-- end NormNum

-- end Tactics
