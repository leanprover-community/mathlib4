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

open scoped Classical
open Real Topology Filter ComplexConjugate Finset Set

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
#align complex.cpow_zero Complex.cpow_zero

@[simp]
theorem cpow_eq_zero_iff (x y : ℂ) : x ^ y = 0 ↔ x = 0 ∧ y ≠ 0 := by
  simp only [cpow_def]
  split_ifs <;> simp [*, exp_ne_zero]
#align complex.cpow_eq_zero_iff Complex.cpow_eq_zero_iff

@[simp]
theorem zero_cpow {x : ℂ} (h : x ≠ 0) : (0 : ℂ) ^ x = 0 := by simp [cpow_def, *]
#align complex.zero_cpow Complex.zero_cpow

theorem zero_cpow_eq_iff {x : ℂ} {a : ℂ} : (0 : ℂ) ^ x = a ↔ x ≠ 0 ∧ a = 0 ∨ x = 0 ∧ a = 1 := by
  constructor
  · intro hyp
    simp only [cpow_def, eq_self_iff_true, if_true] at hyp
    by_cases h : x = 0
    · subst h
      simp only [if_true, eq_self_iff_true] at hyp
      right
      exact ⟨rfl, hyp.symm⟩
    · rw [if_neg h] at hyp
      left
      exact ⟨h, hyp.symm⟩
  · rintro (⟨h, rfl⟩ | ⟨rfl, rfl⟩)
    · exact zero_cpow h
    · exact cpow_zero _
#align complex.zero_cpow_eq_iff Complex.zero_cpow_eq_iff

theorem eq_zero_cpow_iff {x : ℂ} {a : ℂ} : a = (0 : ℂ) ^ x ↔ x ≠ 0 ∧ a = 0 ∨ x = 0 ∧ a = 1 := by
  rw [← zero_cpow_eq_iff, eq_comm]
#align complex.eq_zero_cpow_iff Complex.eq_zero_cpow_iff

@[simp]
theorem cpow_one (x : ℂ) : x ^ (1 : ℂ) = x :=
  if hx : x = 0 then by simp [hx, cpow_def]
  else by rw [cpow_def, if_neg (one_ne_zero : (1 : ℂ) ≠ 0), if_neg hx, mul_one, exp_log hx]
#align complex.cpow_one Complex.cpow_one

@[simp]
theorem one_cpow (x : ℂ) : (1 : ℂ) ^ x = 1 := by
  rw [cpow_def]
  split_ifs <;> simp_all [one_ne_zero]
#align complex.one_cpow Complex.one_cpow

theorem cpow_add {x : ℂ} (y z : ℂ) (hx : x ≠ 0) : x ^ (y + z) = x ^ y * x ^ z := by
  simp only [cpow_def, ite_mul, boole_mul, mul_ite, mul_boole]
  simp_all [exp_add, mul_add]
#align complex.cpow_add Complex.cpow_add

theorem cpow_mul {x y : ℂ} (z : ℂ) (h₁ : -π < (log x * y).im) (h₂ : (log x * y).im ≤ π) :
    x ^ (y * z) = (x ^ y) ^ z := by
  simp only [cpow_def]
  split_ifs <;> simp_all [exp_ne_zero, log_exp h₁ h₂, mul_assoc]
#align complex.cpow_mul Complex.cpow_mul

theorem cpow_neg (x y : ℂ) : x ^ (-y) = (x ^ y)⁻¹ := by
  simp only [cpow_def, neg_eq_zero, mul_neg]
  split_ifs <;> simp [exp_neg]
#align complex.cpow_neg Complex.cpow_neg

theorem cpow_sub {x : ℂ} (y z : ℂ) (hx : x ≠ 0) : x ^ (y - z) = x ^ y / x ^ z := by
  rw [sub_eq_add_neg, cpow_add _ _ hx, cpow_neg, div_eq_mul_inv]
#align complex.cpow_sub Complex.cpow_sub

theorem cpow_neg_one (x : ℂ) : x ^ (-1 : ℂ) = x⁻¹ := by simpa using cpow_neg x 1
#align complex.cpow_neg_one Complex.cpow_neg_one

/-- See also `Complex.cpow_int_mul'`. -/
lemma cpow_int_mul (x : ℂ) (n : ℤ) (y : ℂ) : x ^ (n * y) = (x ^ y) ^ n := by
  rcases eq_or_ne x 0 with rfl | hx
  · rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rcases eq_or_ne y 0 with rfl | hy <;> simp [*, zero_zpow]
  · rw [cpow_def_of_ne_zero hx, cpow_def_of_ne_zero hx, mul_left_comm, exp_int_mul]

lemma cpow_mul_int (x y : ℂ) (n : ℤ) : x ^ (y * n) = (x ^ y) ^ n := by rw [mul_comm, cpow_int_mul]

lemma cpow_nat_mul (x : ℂ) (n : ℕ) (y : ℂ) : x ^ (n * y) = (x ^ y) ^ n :=
  mod_cast cpow_int_mul x n y

/-- See Note [no_index around OfNat.ofNat] -/
lemma cpow_ofNat_mul (x : ℂ) (n : ℕ) [n.AtLeastTwo] (y : ℂ) :
    x ^ (no_index (OfNat.ofNat n) * y) = (x ^ y) ^ (OfNat.ofNat n : ℕ) :=
  cpow_nat_mul x n y

lemma cpow_mul_nat (x y : ℂ) (n : ℕ) : x ^ (y * n) = (x ^ y) ^ n := by
  rw [mul_comm, cpow_nat_mul]

/-- See Note [no_index around OfNat.ofNat] -/
lemma cpow_mul_ofNat (x y : ℂ) (n : ℕ) [n.AtLeastTwo] :
    x ^ (y * no_index (OfNat.ofNat n)) = (x ^ y) ^ (OfNat.ofNat n : ℕ) :=
  cpow_mul_nat x y n

@[simp, norm_cast]
theorem cpow_natCast (x : ℂ) (n : ℕ) : x ^ (n : ℂ) = x ^ n := by simpa using cpow_nat_mul x n 1
#align complex.cpow_nat_cast Complex.cpow_natCast

@[deprecated (since := "2024-04-17")]
alias cpow_nat_cast := cpow_natCast

/-- See Note [no_index around OfNat.ofNat] -/
@[simp]
lemma cpow_ofNat (x : ℂ) (n : ℕ) [n.AtLeastTwo] :
    x ^ (no_index (OfNat.ofNat n) : ℂ) = x ^ (OfNat.ofNat n : ℕ) :=
  cpow_natCast x n

theorem cpow_two (x : ℂ) : x ^ (2 : ℂ) = x ^ (2 : ℕ) := cpow_ofNat x 2
#align complex.cpow_two Complex.cpow_two

@[simp, norm_cast]
theorem cpow_intCast (x : ℂ) (n : ℤ) : x ^ (n : ℂ) = x ^ n := by simpa using cpow_int_mul x n 1
#align complex.cpow_int_cast Complex.cpow_intCast

@[deprecated (since := "2024-04-17")]
alias cpow_int_cast := cpow_intCast

@[simp]
theorem cpow_nat_inv_pow (x : ℂ) {n : ℕ} (hn : n ≠ 0) : (x ^ (n⁻¹ : ℂ)) ^ n = x := by
  rw [← cpow_nat_mul, mul_inv_cancel, cpow_one]
  assumption_mod_cast
#align complex.cpow_nat_inv_pow Complex.cpow_nat_inv_pow

/-- See Note [no_index around OfNat.ofNat] -/
@[simp]
lemma cpow_ofNat_inv_pow (x : ℂ) (n : ℕ) [n.AtLeastTwo] :
    (x ^ ((no_index (OfNat.ofNat n) : ℂ)⁻¹)) ^ (no_index (OfNat.ofNat n) : ℕ) = x :=
  cpow_nat_inv_pow _ (NeZero.ne n)

/-- A version of `Complex.cpow_int_mul` with RHS that matches `Complex.cpow_mul`.

The assumptions on the arguments are needed
because the equality fails, e.g., for `x = -I`, `n = 2`, `y = 1/2`. -/
lemma cpow_int_mul' {x : ℂ} {n : ℤ} (hlt : -π < n * x.arg) (hle : n * x.arg ≤ π) (y : ℂ) :
    x ^ (n * y) = (x ^ n) ^ y := by
  rw [mul_comm] at hlt hle
  rw [cpow_mul, cpow_intCast] <;> simpa [log_im]

/-- A version of `Complex.cpow_nat_mul` with RHS that matches `Complex.cpow_mul`.

The assumptions on the arguments are needed
because the equality fails, e.g., for `x = -I`, `n = 2`, `y = 1/2`. -/
lemma cpow_nat_mul' {x : ℂ} {n : ℕ} (hlt : -π < n * x.arg) (hle : n * x.arg ≤ π) (y : ℂ) :
    x ^ (n * y) = (x ^ n) ^ y :=
  cpow_int_mul' hlt hle y

lemma cpow_ofNat_mul' {x : ℂ} {n : ℕ} [n.AtLeastTwo] (hlt : -π < OfNat.ofNat n * x.arg)
    (hle : OfNat.ofNat n * x.arg ≤ π) (y : ℂ) :
    x ^ (OfNat.ofNat n * y) = (x ^ (OfNat.ofNat n : ℕ)) ^ y :=
  cpow_nat_mul' hlt hle y

lemma pow_cpow_nat_inv {x : ℂ} {n : ℕ} (h₀ : n ≠ 0) (hlt : -(π / n) < x.arg) (hle : x.arg ≤ π / n) :
    (x ^ n) ^ (n⁻¹ : ℂ) = x := by
  rw [← cpow_nat_mul', mul_inv_cancel (Nat.cast_ne_zero.2 h₀), cpow_one]
  · rwa [← div_lt_iff' (Nat.cast_pos.2 h₀.bot_lt), neg_div]
  · rwa [← le_div_iff' (Nat.cast_pos.2 h₀.bot_lt)]

lemma pow_cpow_ofNat_inv {x : ℂ} {n : ℕ} [n.AtLeastTwo] (hlt : -(π / OfNat.ofNat n) < x.arg)
    (hle : x.arg ≤ π / OfNat.ofNat n) :
    (x ^ (OfNat.ofNat n : ℕ)) ^ ((OfNat.ofNat n : ℂ)⁻¹) = x :=
  pow_cpow_nat_inv (NeZero.ne n) hlt hle

/-- See also `Complex.pow_cpow_ofNat_inv` for a version that also works for `x * I`, `0 ≤ x`. -/
lemma sq_cpow_two_inv {x : ℂ} (hx : 0 < x.re) : (x ^ (2 : ℕ)) ^ (2⁻¹ : ℂ) = x :=
  pow_cpow_ofNat_inv (neg_pi_div_two_lt_arg_iff.2 <| .inl hx)
    (arg_le_pi_div_two_iff.2 <| .inl hx.le)

theorem mul_cpow_ofReal_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (r : ℂ) :
    ((a : ℂ) * (b : ℂ)) ^ r = (a : ℂ) ^ r * (b : ℂ) ^ r := by
  rcases eq_or_ne r 0 with (rfl | hr)
  · simp only [cpow_zero, mul_one]
  rcases eq_or_lt_of_le ha with (rfl | ha')
  · rw [ofReal_zero, zero_mul, zero_cpow hr, zero_mul]
  rcases eq_or_lt_of_le hb with (rfl | hb')
  · rw [ofReal_zero, mul_zero, zero_cpow hr, mul_zero]
  have ha'' : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr ha'.ne'
  have hb'' : (b : ℂ) ≠ 0 := ofReal_ne_zero.mpr hb'.ne'
  rw [cpow_def_of_ne_zero (mul_ne_zero ha'' hb''), log_ofReal_mul ha' hb'', ofReal_log ha,
    add_mul, exp_add, ← cpow_def_of_ne_zero ha'', ← cpow_def_of_ne_zero hb'']
#align complex.mul_cpow_of_real_nonneg Complex.mul_cpow_ofReal_nonneg

lemma natCast_mul_natCast_cpow (m n : ℕ) (s : ℂ) : (m * n : ℂ) ^ s = m ^ s * n ^ s :=
  ofReal_natCast m ▸ ofReal_natCast n ▸ mul_cpow_ofReal_nonneg m.cast_nonneg n.cast_nonneg s

lemma natCast_cpow_natCast_mul (n m : ℕ) (z : ℂ) : (n : ℂ) ^ (m * z) = ((n : ℂ) ^ m) ^ z := by
  refine cpow_nat_mul' (x := n) (n := m) ?_ ?_ z
  · simp only [natCast_arg, mul_zero, Left.neg_neg_iff, pi_pos]
  · simp only [natCast_arg, mul_zero, pi_pos.le]

theorem inv_cpow_eq_ite (x : ℂ) (n : ℂ) :
    x⁻¹ ^ n = if x.arg = π then conj (x ^ conj n)⁻¹ else (x ^ n)⁻¹ := by
  simp_rw [Complex.cpow_def, log_inv_eq_ite, inv_eq_zero, map_eq_zero, ite_mul, neg_mul,
    RCLike.conj_inv, apply_ite conj, apply_ite exp, apply_ite Inv.inv, map_zero, map_one, exp_neg,
    inv_one, inv_zero, ← exp_conj, map_mul, conj_conj]
  split_ifs with hx hn ha ha <;> rfl
#align complex.inv_cpow_eq_ite Complex.inv_cpow_eq_ite

theorem inv_cpow (x : ℂ) (n : ℂ) (hx : x.arg ≠ π) : x⁻¹ ^ n = (x ^ n)⁻¹ := by
  rw [inv_cpow_eq_ite, if_neg hx]
#align complex.inv_cpow Complex.inv_cpow

/-- `Complex.inv_cpow_eq_ite` with the `ite` on the other side. -/
theorem inv_cpow_eq_ite' (x : ℂ) (n : ℂ) :
    (x ^ n)⁻¹ = if x.arg = π then conj (x⁻¹ ^ conj n) else x⁻¹ ^ n := by
  rw [inv_cpow_eq_ite, apply_ite conj, conj_conj, conj_conj]
  split_ifs with h
  · rfl
  · rw [inv_cpow _ _ h]
#align complex.inv_cpow_eq_ite' Complex.inv_cpow_eq_ite'

theorem conj_cpow_eq_ite (x : ℂ) (n : ℂ) :
    conj x ^ n = if x.arg = π then x ^ n else conj (x ^ conj n) := by
  simp_rw [cpow_def, map_eq_zero, apply_ite conj, map_one, map_zero, ← exp_conj, map_mul, conj_conj,
    log_conj_eq_ite]
  split_ifs with hcx hn hx <;> rfl
#align complex.conj_cpow_eq_ite Complex.conj_cpow_eq_ite

theorem conj_cpow (x : ℂ) (n : ℂ) (hx : x.arg ≠ π) : conj x ^ n = conj (x ^ conj n) := by
  rw [conj_cpow_eq_ite, if_neg hx]
#align complex.conj_cpow Complex.conj_cpow

theorem cpow_conj (x : ℂ) (n : ℂ) (hx : x.arg ≠ π) : x ^ conj n = conj (conj x ^ n) := by
  rw [conj_cpow _ _ hx, conj_conj]
#align complex.cpow_conj Complex.cpow_conj

end Complex

-- section Tactics

-- /-!
-- ## Tactic extensions for complex powers
-- -/


-- namespace NormNum

-- theorem cpow_pos (a b : ℂ) (b' : ℕ) (c : ℂ) (hb : b = b') (h : a ^ b' = c) : a ^ b = c := by
--   rw [← h, hb, Complex.cpow_natCast]
-- #align norm_num.cpow_pos NormNum.cpow_pos

-- theorem cpow_neg (a b : ℂ) (b' : ℕ) (c c' : ℂ) (hb : b = b') (h : a ^ b' = c) (hc : c⁻¹ = c') :
--     a ^ (-b) = c' := by rw [← hc, ← h, hb, Complex.cpow_neg, Complex.cpow_natCast]
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
