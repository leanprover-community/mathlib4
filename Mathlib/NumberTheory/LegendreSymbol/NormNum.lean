/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll

! This file was ported from Lean 3 source module number_theory.legendre_symbol.norm_num
! leanprover-community/mathlib commit e2621d935895abe70071ab828a4ee6e26a52afe4
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-!
# A `norm_num` extension for Jacobi and Legendre symbols

We extend the `norm_num` tactic so that it can be used to provably compute
the value of the Jacobi symbol `J(a | b)` or the Legendre symbol `legendreSym p a` when
the arguments are numerals.

## Implementation notes

We use the Law of Quadratic Reciprocity for the Jacobi symbol to compute the value of `J(a | b)`
efficiently, roughly comparable in effort with the euclidean algorithm for the computation
of the gcd of `a` and `b`. More precisely, the computation is done in the following steps.

* Use `J(a | 0) = 1` (an artifact of the definition) and `J(a | 1) = 1` to deal
  with corner cases.

* Use `J(a | b) = J(a % b | b)` to reduce to the case that `a` is a natural number.
  We define a version of the Jacobi symbol restricted to natural numbers for use in
  the following steps; see `NormNum.jacobiSymNat`. (But we'll continue to write `J(a | b)`
  in this description.)

* Remove powers of two from `b`. This is done via `J(2a | 2b) = 0` and
  `J(2a+1 | 2b) = J(2a+1 | b)` (another artifact of the definition).

* Now `0 ≤ a < b` and `b` is odd. If `b = 1`, then the value is `1`.
  If `a = 0` (and `b > 1`), then the value is `0`. Otherwise, we remove powers of two from `a`
  via `J(4a | b) = J(a | b)` and `J(2a | b) = ±J(a | b)`, where the sign is determined
  by the residue class of `b` mod 8, to reduce to `a` odd.

* Once `a` is odd, we use Quadratic Reciprocity (QR) in the form
  `J(a | b) = ±J(b % a | a)`, where the sign is determined by the residue classes
  of `a` and `b` mod 4. We are then back in the previous case.

We provide customized versions of these results for the various reduction steps,
where we encode the residue classes mod 2, mod 4, or mod 8 by using hypotheses like
`a % n = b`. In this way, the only divisions we have to compute and prove
are the ones occurring in the use of QR above.
-/


section Lemmas

namespace NormNum

/-- The Jacobi symbol restricted to natural numbers in both arguments. -/
def jacobiSymNat (a b : ℕ) : ℤ :=
  jacobiSym a b
#align norm_num.jacobi_sym_nat NormNum.jacobiSymNat

/-!
### API Lemmas

We repeat part of the API for `jacobiSym` with `NormNum.jacobiSymNat` and without implicit
arguments, in a form that is suitable for constructing proofs in `norm_num`.
-/


/-- Base cases: `b = 0`, `b = 1`, `a = 0`, `a = 1`. -/
theorem jacobiSymNat.zero_right (a : ℕ) : jacobiSymNat a 0 = 1 := by
  rw [jacobiSymNat, jacobiSym.zero_right]
#align norm_num.jacobi_sym_nat.zero_right NormNum.jacobiSymNat.zero_right

theorem jacobiSymNat.one_right (a : ℕ) : jacobiSymNat a 1 = 1 := by
  rw [jacobiSymNat, jacobiSym.one_right]
#align norm_num.jacobi_sym_nat.one_right NormNum.jacobiSymNat.one_right

theorem jacobiSymNat.zero_left (b : ℕ) (hb : Nat.beq (b / 2) 0 = false) : jacobiSymNat 0 b = 0 := by
  rw [jacobiSymNat, Nat.cast_zero, jacobiSym.zero_left ?_]
  · calc
      1 < 2 * 1       := by decide
      _ ≤ 2 * (b / 2) :=
        Nat.mul_le_mul_of_nonneg_left
          (Nat.succ_le.mpr (Nat.pos_of_ne_zero (Nat.ne_of_beq_eq_false hb)))
      _ ≤ b           := Nat.mul_div_le b 2
#align norm_num.jacobi_sym_nat.zero_left_even NormNum.jacobiSymNat.zero_left
#align norm_num.jacobi_sym_nat.zero_left_odd NormNum.jacobiSymNat.zero_left

theorem jacobiSymNat.one_left (b : ℕ) : jacobiSymNat 1 b = 1 := by
  rw [jacobiSymNat, Nat.cast_one, jacobiSym.one_left]
#align norm_num.jacobi_sym_nat.one_left_even NormNum.jacobiSymNat.one_left
#align norm_num.jacobi_sym_nat.one_left_odd NormNum.jacobiSymNat.one_left

/-- Turn a Legendre symbol into a Jacobi symbol. -/
theorem LegendreSym.to_jacobiSym (p : ℕ) (pp : Fact p.Prime) (a r : ℤ) (hr : jacobiSym a p = r) :
    legendreSym p a = r := by rwa [@jacobiSym.legendreSym.to_jacobiSym p pp a]
#align norm_num.legendre_sym.to_jacobi_sym NormNum.LegendreSym.to_jacobiSym

/-- The value depends only on the residue class of `a` mod `b`. -/
theorem JacobiSym.mod_left (a : ℤ) (b ab' : ℕ) (ab r b' : ℤ) (hb' : (b : ℤ) = b')
    (hab : a % b' = ab) (h : (ab' : ℤ) = ab) (hr : jacobiSymNat ab' b = r) : jacobiSym a b = r := by
  rw [← hr, jacobiSymNat, jacobiSym.mod_left, hb', hab, ← h]
#align norm_num.jacobi_sym.mod_left NormNum.JacobiSym.mod_left

theorem jacobiSymNat.mod_left (a b ab : ℕ) (r : ℤ) (hab : a % b = ab) (hr : jacobiSymNat ab b = r) :
    jacobiSymNat a b = r := by
  rw [← hr, jacobiSymNat, jacobiSymNat, _root_.jacobiSym.mod_left a b, ← hab]; rfl
#align norm_num.jacobi_sym_nat.mod_left NormNum.jacobiSymNat.mod_left

/-- The symbol vanishes when both entries are even (and `b / 2 ≠ 0`). -/
theorem jacobiSymNat.even_even (a b : ℕ) (hb₀ : Nat.beq (b / 2) 0 = false) (ha : a % 2 = 0)
    (hb₁ : b % 2 = 0) : jacobiSymNat a b = 0 := by
  refine' jacobiSym.eq_zero_iff.mpr
    ⟨ne_of_gt ((Nat.pos_of_ne_zero (Nat.ne_of_beq_eq_false hb₀)).trans_le (Nat.div_le_self b 2)),
      fun hf => _⟩
  have h : 2 ∣ a.gcd b := Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero ha) (Nat.dvd_of_mod_eq_zero hb₁)
  change 2 ∣ (a : ℤ).gcd b at h
  rw [hf, ← even_iff_two_dvd] at h
  exact Nat.not_even_one h
#align norm_num.jacobi_sym_nat.even_even NormNum.jacobiSymNat.even_even

/-- When `a` is odd and `b` is even, we can replace `b` by `b / 2`. -/
theorem jacobiSymNat.odd_even (a b c : ℕ) (r : ℤ) (ha : a % 2 = 1) (hb : b % 2 = 0) (hc : b / 2 = c)
    (hr : jacobiSymNat a c = r) :
    jacobiSymNat a b = r := by
  have ha' : legendreSym 2 a = 1 := by
    simp only [legendreSym.mod 2 a, Int.ofNat_mod_ofNat, ha]
  rcases eq_or_ne c 0 with (rfl | hc')
  · rw [← hr, Nat.eq_zero_of_dvd_of_div_eq_zero (Nat.dvd_of_mod_eq_zero hb) hc]
  · haveI : NeZero c := ⟨hc'⟩
    -- for `jacobiSym.mul_right`
    rwa [← Nat.mod_add_div b 2, hb, hc, Nat.zero_add, jacobiSymNat, jacobiSym.mul_right,
      ← jacobiSym.legendreSym.to_jacobiSym, ha', one_mul]
#align norm_num.jacobi_sym_nat.odd_even NormNum.jacobiSymNat.odd_even

/-- If `a` is divisible by `4` and `b` is odd, then we can remove the factor `4` from `a`. -/
theorem jacobiSymNat.double_even (a b c : ℕ) (r : ℤ) (ha : a % 4 = 0) (hb : b % 2 = 1)
    (hc : a / 4 = c) (hr : jacobiSymNat c b = r) : jacobiSymNat a b = r := by
  have : ((2 : ℕ) : ℤ).gcd b = 1 := by
    rw [Int.coe_nat_gcd, ← Nat.mod_add_div b 2, hb, Nat.gcd_add_mul_left_right, Nat.gcd_one_right]
  rwa [← Nat.mod_add_div a 4, ha, hc, Nat.zero_add, (by decide : 4 = 2 ^ 2), jacobiSymNat,
    Nat.cast_mul, Nat.cast_pow, jacobiSym.mul_left, jacobiSym.sq_one' this, one_mul]
#align norm_num.jacobi_sym_nat.double_even NormNum.jacobiSymNat.double_even

/-- If `a` is even and `b` is odd, then we can remove a factor `2` from `a`,
but we may have to change the sign, depending on `b % 8`.
We give one version for each of the four odd residue classes mod `8`. -/
theorem jacobiSymNat.even_odd₁ (a b c : ℕ) (r : ℤ) (ha : a % 2 = 0) (hb : b % 8 = 1)
    (hc : a / 2 = c) (hr : jacobiSymNat c b = r) : jacobiSymNat a b = r := by
  have hb' : Odd b := by
    rw [← Nat.div_add_mod b 8, hb, Odd]
    use 4 * (b / 8); rw [← Nat.mul_assoc]; congr
  rw [jacobiSymNat, ← Nat.mod_add_div a 2, ha, hc, Nat.zero_add, Nat.cast_mul, jacobiSym.mul_left,
    Nat.cast_two, jacobiSym.at_two hb', ZMod.χ₈_nat_mod_eight, hb]
  norm_num
  exact hr
#align norm_num.jacobi_sym_nat.even_odd₁ NormNum.jacobiSymNat.even_odd₁

theorem jacobiSymNat.even_odd₇ (a b c : ℕ) (r : ℤ) (ha : a % 2 = 0) (hb : b % 8 = 7)
    (hc : a / 2 = c) (hr : jacobiSymNat c b = r) : jacobiSymNat a b = r := by
  have hb' : Odd b := by
    rw [← Nat.div_add_mod b 8, hb, Odd]
    use 4 * (b / 8) + 3; rw [Nat.mul_add, ← Nat.mul_assoc, Nat.add_assoc]; congr
  rw [jacobiSymNat, ← Nat.mod_add_div a 2, ha, hc, Nat.zero_add, Nat.cast_mul, jacobiSym.mul_left,
    Nat.cast_two, jacobiSym.at_two hb', ZMod.χ₈_nat_mod_eight, hb,
    (by decide : ZMod.χ₈ (7 : ℕ) = 1)]
  norm_num
  exact hr
#align norm_num.jacobi_sym_nat.even_odd₇ NormNum.jacobiSymNat.even_odd₇

theorem jacobiSymNat.even_odd₃ (a b c : ℕ) (r : ℤ) (ha : a % 2 = 0) (hb : b % 8 = 3)
    (hc : a / 2 = c) (hr : jacobiSymNat c b = r) : jacobiSymNat a b = -r := by
  have hb' : Odd b := by
    rw [← Nat.div_add_mod b 8, hb, Odd]
    use 4 * (b / 8) + 1; rw [Nat.mul_add, ← Nat.mul_assoc, Nat.add_assoc]; congr
  rw [jacobiSymNat, ← Nat.mod_add_div a 2, ha, hc, Nat.zero_add, Nat.cast_mul, jacobiSym.mul_left,
    Nat.cast_two, jacobiSym.at_two hb', ZMod.χ₈_nat_mod_eight, hb,
    (by decide : ZMod.χ₈ (3 : ℕ) = -1)]
  norm_num
  exact hr
#align norm_num.jacobi_sym_nat.even_odd₃ NormNum.jacobiSymNat.even_odd₃

theorem jacobiSymNat.even_odd₅ (a b c : ℕ) (r : ℤ) (ha : a % 2 = 0) (hb : b % 8 = 5)
    (hc : a / 2 = c) (hr : jacobiSymNat c b = r) : jacobiSymNat a b = -r := by
  have hb' : Odd b := by
    rw [← Nat.div_add_mod b 8, hb, Odd]
    use 4 * (b / 8) + 2; rw [Nat.mul_add, ← Nat.mul_assoc, Nat.add_assoc]; congr
  rw [jacobiSymNat, ← Nat.mod_add_div a 2, ha, hc, Nat.zero_add, Nat.cast_mul, jacobiSym.mul_left,
    Nat.cast_two, jacobiSym.at_two hb', ZMod.χ₈_nat_mod_eight, hb,
    (by decide : ZMod.χ₈ (5 : ℕ) = -1)]
  norm_num
  exact hr
#align norm_num.jacobi_sym_nat.even_odd₅ NormNum.jacobiSymNat.even_odd₅

/-- Use quadratic reciproity to reduce to smaller `b`. -/
theorem jacobiSymNat.qr₁ (a b : ℕ) (r : ℤ) (ha : a % 4 = 1) (hb : b % 2 = 1)
    (hr : jacobiSymNat b a = r) : jacobiSymNat a b = r := by
  rwa [jacobiSymNat, jacobiSym.quadratic_reciprocity_one_mod_four ha (Nat.odd_iff.mpr hb)]
#align norm_num.jacobi_sym_nat.qr₁ NormNum.jacobiSymNat.qr₁

theorem jacobiSymNat.qr₁_mod (a b ab : ℕ) (r : ℤ) (ha : a % 4 = 1) (hb : b % 2 = 1)
    (hab : b % a = ab) (hr : jacobiSymNat ab a = r) : jacobiSymNat a b = r :=
  jacobiSymNat.qr₁ _ _ _ ha hb <| jacobiSymNat.mod_left _ _ ab r hab hr
#align norm_num.jacobi_sym_nat.qr₁_mod NormNum.jacobiSymNat.qr₁_mod

theorem jacobiSymNat.qr₁' (a b : ℕ) (r : ℤ) (ha : a % 2 = 1) (hb : b % 4 = 1)
    (hr : jacobiSymNat b a = r) : jacobiSymNat a b = r := by
  rwa [jacobiSymNat, ← jacobiSym.quadratic_reciprocity_one_mod_four hb (Nat.odd_iff.mpr ha)]
#align norm_num.jacobi_sym_nat.qr₁' NormNum.jacobiSymNat.qr₁'

theorem jacobiSymNat.qr₁'_mod (a b ab : ℕ) (r : ℤ) (ha : a % 2 = 1) (hb : b % 4 = 1)
    (hab : b % a = ab) (hr : jacobiSymNat ab a = r) : jacobiSymNat a b = r :=
  jacobiSymNat.qr₁' _ _ _ ha hb <| jacobiSymNat.mod_left _ _ ab r hab hr
#align norm_num.jacobi_sym_nat.qr₁'_mod NormNum.jacobiSymNat.qr₁'_mod

theorem jacobiSymNat.qr₃ (a b : ℕ) (r : ℤ) (ha : a % 4 = 3) (hb : b % 4 = 3)
    (hr : jacobiSymNat b a = r) : jacobiSymNat a b = -r := by
  rwa [jacobiSymNat, jacobiSym.quadratic_reciprocity_three_mod_four ha hb, neg_inj]
#align norm_num.jacobi_sym_nat.qr₃ NormNum.jacobiSymNat.qr₃

theorem jacobiSymNat.qr₃_mod (a b ab : ℕ) (r : ℤ) (ha : a % 4 = 3) (hb : b % 4 = 3)
    (hab : b % a = ab) (hr : jacobiSymNat ab a = r) : jacobiSymNat a b = -r :=
  jacobiSymNat.qr₃ _ _ _ ha hb <| jacobiSymNat.mod_left _ _ ab r hab hr
#align norm_num.jacobi_sym_nat.qr₃_mod NormNum.jacobiSymNat.qr₃_mod

end NormNum

end Lemmas

section Evaluation

/-!
### Certified evaluation of the Jacobi symbol

The following functions recursively evaluate a Jacobi symbol and construct the
corresponding proof term.
-/


namespace NormNum

open Lean Elab Tactic Qq Mathlib.Meta.NormNum

/-- This evaluates `r := jacobiSymNat a b` recursively using quadratic reciprocity
and produces a proof term for the equality, assuming that `a < b` and `b` is odd. -/
partial def prove_jacobiSym_odd (ea eb : Q(ℕ)) : ((er : Q(ℤ)) × Q(jacobiSymNat $ea $eb = $er)) :=
  match eb.natLit! with
  | 1 =>
    show (er : Q(ℤ)) × Q(jacobiSymNat $ea 1 = $er) from
      ⟨mkRawIntLit 1, q(jacobiSymNat.one_right $ea)⟩
  | b =>
    match ea.natLit! with
    | 0 =>
      have hb : Q(Nat.beq ($eb / 2) 0 = false) := (q(Eq.refl false) : Expr)
      show (er : Q(ℤ)) × Q(jacobiSymNat 0 $eb = $er) from
        ⟨mkRawIntLit 0, q(jacobiSymNat.zero_left $eb $hb)⟩
    | 1 =>
      show (er : Q(ℤ)) × Q(jacobiSymNat 1 $eb = $er) from
        ⟨mkRawIntLit 1, q(jacobiSymNat.one_left $eb)⟩
    | a =>
      match a % 2 with
      | 0 =>
        match a % 4 with
        | 0 =>
          have ha : Q(Nat.mod $ea 4 = 0) := (q(Eq.refl 0) : Expr)
          have hb : Q(Nat.mod $eb 2 = 1) := (q(Eq.refl 1) : Expr)
          have c := a / 4
          have ec : Q(ℕ) := mkRawNatLit c
          have hc : Q(Nat.div $ea 4 = $ec) := (q(Eq.refl $ec) : Expr)
          let ⟨er, p⟩ := prove_jacobiSym_odd ec eb
          ⟨er, q(jacobiSymNat.double_even $ea $eb $ec $er $ha $hb $hc $p)⟩
        | _ =>
          have ha : Q(Nat.mod $ea 2 = 0) := (q(Eq.refl 0) : Expr)
          have c := a / 2
          have ec : Q(ℕ) := mkRawNatLit c
          have hc : Q(Nat.div $ea 2 = $ec) := (q(Eq.refl $ec) : Expr)
          let ⟨er, p⟩ := prove_jacobiSym_odd ec eb
          match b % 8 with
          | 1 =>
            have hb : Q(Nat.mod $eb 8 = 1) := (q(Eq.refl 1) : Expr)
            ⟨er, q(jacobiSymNat.even_odd₁ $ea $eb $ec $er $ha $hb $hc $p)⟩
          | 3 =>
            have r' := er.intLit!
            have er' := mkRawIntLit r'
            have hb : Q(Nat.mod $eb 8 = 3) := (q(Eq.refl 3) : Expr)
            show (_ : Q(ℤ)) × Q(jacobiSymNat $ea $eb = -$er) from
            ⟨er', q(jacobiSymNat.even_odd₃ $ea $eb $ec $er $ha $hb $hc $p)⟩
          | 5 =>
            have r' := er.intLit!
            have er' := mkRawIntLit r'
            have hb : Q(Nat.mod $eb 8 = 5) := (q(Eq.refl 5) : Expr)
            show (_ : Q(ℤ)) × Q(jacobiSymNat $ea $eb = -$er) from
            ⟨er', q(jacobiSymNat.even_odd₅ $ea $eb $ec $er $ha $hb $hc $p)⟩
          | _ =>
            have hb : Q(Nat.mod $eb 8 = 7) := (q(Eq.refl 7) : Expr)
            ⟨er, q(jacobiSymNat.even_odd₇ $ea $eb $ec $er $ha $hb $hc $p)⟩
      | _ => default
/-
| zc nc ea eb := do
  match match_numeral eb with
  | match_numeral_result.one :=  -- `b = 1`, result is `1`
    pure (zc, nc, `(1 : ℤ), `(jacobi_sym_nat.one_right).mk_app [ea])
  | match_numeral_result.bit1 eb₁ := do -- `b > 1` (recall that `b` is odd)
    match match_numeral ea with
    | match_numeral_result.zero := do -- `a = 0`, result is `0`
      b ← eb₁.to_nat,
      (nc, phb₀) ← prove_ne nc eb₁ `(0 : ℕ) b 0, -- proof of `b ≠ 0`
      pure (zc, nc, `(0 : ℤ), `(jacobi_sym_nat.zero_left_odd).mk_app [eb₁, phb₀])
    | match_numeral_result.one := do -- `a = 1`, result is `1`
      pure (zc, nc, `(1 : ℤ), `(jacobi_sym_nat.one_left_odd).mk_app [eb₁])
    | match_numeral_result.bit0 ea₁ := do -- `a` is even; check if divisible by `4`
      match match_numeral ea₁ with
      | match_numeral_result.bit0 ea₂ := do
        (zc, nc, er, p) ← prove_jacobi_sym_odd zc nc ea₂ eb, -- compute `jacobi_sym_nat (a / 4) b`
        pure (zc, nc, er, `(jacobi_sym_nat.double_even).mk_app [ea₂, eb₁, er, p])
      | _ := do -- reduce to `a / 2`; need to consider `b % 8`
        (zc, nc, er, p) ← prove_jacobi_sym_odd zc nc ea₁ eb, -- compute `jacobi_sym_nat (a / 2) b`
        match match_numeral eb₁ with
        -- | match_numeral_result.zero := -- `b = 1`, not reached
        | match_numeral_result.one := do -- `b = 3`
          r ← er.to_int,
          (zc, er') ← zc.of_int (- r),
          pure (zc, nc, er', `(jacobi_sym_nat.even_odd₃).mk_app [ea₁, `(0 : ℕ), er, p])
        | match_numeral_result.bit0 eb₂ := do -- `b % 4 = 1`
          match match_numeral eb₂ with
          -- | match_numeral_result.zero := -- not reached
          | match_numeral_result.one := do -- `b = 5`
            r ← er.to_int,
            (zc, er') ← zc.of_int (- r),
            pure (zc, nc, er', `(jacobi_sym_nat.even_odd₅).mk_app [ea₁, `(0 : ℕ), er, p])
          | match_numeral_result.bit0 eb₃ := do -- `b % 8 = 1`
            pure (zc, nc, er, `(jacobi_sym_nat.even_odd₁).mk_app [ea₁, eb₃, er, p])
          | match_numeral_result.bit1 eb₃ := do -- `b % 8 = 5`
            r ← er.to_int,
            (zc, er') ← zc.of_int (- r),
            pure (zc, nc, er', `(jacobi_sym_nat.even_odd₅).mk_app [ea₁, eb₃, er, p])
          | _ := failed
          end
        | match_numeral_result.bit1 eb₂ := do -- `b % 4 = 3`
          match match_numeral eb₂ with
          -- | match_numeral_result.zero := -- not reached
          | match_numeral_result.one := do -- `b = 7`
            pure (zc, nc, er, `(jacobi_sym_nat.even_odd₇).mk_app [ea₁, `(0 : ℕ), er, p])
          | match_numeral_result.bit0 eb₃ := do -- `b % 8 = 3`
            r ← er.to_int,
            (zc, er') ← zc.of_int (- r),
            pure (zc, nc, er', `(jacobi_sym_nat.even_odd₃).mk_app [ea₁, eb₃, er, p])
          | match_numeral_result.bit1 eb₃ := do -- `b % 8 = 7`
            pure (zc, nc, er, `(jacobi_sym_nat.even_odd₇).mk_app [ea₁, eb₃, er, p])
          | _ := failed
          end
        | _ := failed
        end
      end
    | match_numeral_result.bit1 ea₁ := do -- `a` is odd
      -- use Quadratic Reciprocity; look at `a` and `b` mod `4`
      (nc, bma, phab) ← prove_div_mod nc eb ea tt, -- compute `b % a`
      (zc, nc, er, p) ← prove_jacobi_sym_odd zc nc bma ea, -- compute `jacobi_sym_nat (b % a) a`
      match match_numeral ea₁ with
      -- | match_numeral_result.zero :=  -- `a = 1`, not reached
      | match_numeral_result.one := do -- `a = 3`; need to consider `b`
        match match_numeral eb₁ with
        -- | match_numeral_result.zero := -- `b = 1`, not reached
        -- | match_numeral_result.one := -- `b = 3`, not reached, since `a < b`
        | match_numeral_result.bit0 eb₂ := do -- `b % 4 = 1`
          pure (zc, nc, er, `(jacobi_sym_nat.qr₁'_mod).mk_app [ea₁, eb₂, bma, er, phab, p])
        | match_numeral_result.bit1 eb₂ := do -- `b % 4 = 3`
          r ← er.to_int,
          (zc, er') ← zc.of_int (- r),
          pure (zc, nc, er', `(jacobi_sym_nat.qr₃_mod).mk_app [`(0 : ℕ), eb₂, bma, er, phab, p])
        | _ := failed
        end
      | match_numeral_result.bit0 ea₂ := do -- `a % 4 = 1`
        pure (zc, nc, er, `(jacobi_sym_nat.qr₁_mod).mk_app [ea₂, eb₁, bma, er, phab, p])
      | match_numeral_result.bit1 ea₂ := do -- `a % 4 = 3`; need to consider `b`
        match match_numeral eb₁ with
        -- | match_numeral_result.zero := do -- `b = 1`, not reached
        -- | match_numeral_result.one := do -- `b = 3`, not reached, since `a < b`
        | match_numeral_result.bit0 eb₂ := do -- `b % 4 = 1`
          pure (zc, nc, er, `(jacobi_sym_nat.qr₁'_mod).mk_app [ea₁, eb₂, bma, er, phab, p])
        | match_numeral_result.bit1 eb₂ := do -- `b % 4 = 3`
          r ← er.to_int,
          (zc, er') ← zc.of_int (- r),
          pure (zc, nc, er', `(jacobi_sym_nat.qr₃_mod).mk_app [ea₂, eb₂, bma, er, phab, p])
        | _ := failed
        end
      | _ := failed
      end
    | _ := failed
    end
  | _ := failed
  end
-/
#align norm_num.prove_jacobi_sym_odd NormNum.prove_jacobiSym_odd

/-- This evaluates `r := jacobi_sym_nat a b` and produces a proof term for the equality
by removing powers of `2` from `b` and then calling `prove_jacobi_sym_odd`. -/
unsafe def prove_jacobi_sym_nat :
    instance_cache →
      instance_cache → expr → expr → tactic (instance_cache × instance_cache × expr × expr)
  | zc, nc, ea, eb => do
    match match_numeral eb with
      |
      match_numeral_result.zero =>-- `b = 0`, result is `1`
          pure
          (zc, nc, q((1 : ℤ)), q(jacobiSymNat.zero_right).mk_app [ea])
      |
      match_numeral_result.one =>-- `b = 1`, result is `1`
          pure
          (zc, nc, q((1 : ℤ)), q(jacobiSymNat.one_right).mk_app [ea])
      |
      match_numeral_result.bit0 eb₁ =>-- `b` is even and nonzero
        match match_numeral ea with
        | match_numeral_result.zero => do
          let b
            ←-- `a = 0`, result is `0`
              eb₁
          let (nc, phb₀) ← prove_ne nc eb₁ q((0 : ℕ)) b 0
          -- proof of `b ≠ 0`
              pure
              (zc, nc, q((0 : ℤ)), q(jacobiSymNat.zero_left_even).mk_app [eb₁, phb₀])
        | match_numeral_result.one => do
          -- `a = 1`, result is `1`
              pure
              (zc, nc, q((1 : ℤ)), q(jacobiSymNat.one_left_even).mk_app [eb₁])
        | match_numeral_result.bit0 ea₁ => do
          let b
            ←-- `a` is even, result is `0`
              eb₁
          let (nc, phb₀) ← prove_ne nc eb₁ q((0 : ℕ)) b 0
          let-- proof of `b ≠ 0`
          er : expr := q((0 : ℤ))
          pure (zc, nc, er, q(jacobiSymNat.even_even).mk_app [ea₁, eb₁, phb₀])
        | match_numeral_result.bit1 ea₁ => do
          let-- `a` is odd, reduce to `b / 2`
            (zc, nc, er, p)
            ← prove_jacobi_sym_nat zc nc ea eb₁
          pure (zc, nc, er, q(jacobiSymNat.odd_even).mk_app [ea₁, eb₁, er, p])
        | _ => failed
      | match_numeral_result.bit1 eb₁ => do
        let a
          ←-- `b` is odd
            ea
        let b ← eb
        if b ≤ a then do
            let-- reduce to `jacobi_sym_nat (a % b) b`
              (nc, amb, phab)
              ← prove_div_mod nc ea eb tt
            let-- compute `a % b`
              (zc, nc, er, p)
              ← prove_jacobi_sym_odd zc nc amb eb
            -- compute `jacobi_sym_nat (a % b) b`
                pure
                (zc, nc, er, q(jacobiSymNat.mod_left).mk_app [ea, eb, amb, er, phab, p])
          else prove_jacobi_sym_odd zc nc ea eb
      | _ => failed
#align norm_num.prove_jacobi_sym_nat norm_num.prove_jacobi_sym_nat

/-- This evaluates `r := jacobi_sym a b` and produces a proof term for the equality.
This is done by reducing to `r := jacobi_sym_nat (a % b) b`. -/
unsafe def prove_jacobi_sym :
    instance_cache →
      instance_cache → expr → expr → tactic (instance_cache × instance_cache × expr × expr)
  | zc, nc, ea, eb => do
    match match_numeral eb with
      |-- deal with simple cases right away
        match_numeral_result.zero =>
        pure (zc, nc, q((1 : ℤ)), q(jacobiSym.zero_right).mk_app [ea])
      | match_numeral_result.one => pure (zc, nc, q((1 : ℤ)), q(jacobiSym.one_right).mk_app [ea])
      | _ => do
        let b
          ←-- Now `1 < b`. Compute `jacobi_sym_nat (a % b) b` instead.
            eb
        let (zc, eb') ← zc (b : ℤ)
        let-- Get the proof that `(b : ℤ) = b'` (where `eb'` is the numeral representing `b'`).
          -- This is important to avoid inefficient matching between the two.
          (zc, nc, eb₁, pb')
          ← prove_nat_uncast zc nc eb'
        let (zc, amb, phab) ← prove_div_mod zc ea eb' tt
        let-- compute `a % b`
          (zc, nc, amb', phab')
          ← prove_nat_uncast zc nc amb
        let-- `a % b` as a natural number
          (zc, nc, er, p)
          ← prove_jacobi_sym_nat zc nc amb' eb₁
        -- compute `jacobi_sym_nat (a % b) b`
            pure
            (zc, nc, er,
              q(JacobiSym.mod_left).mk_app [ea, eb₁, amb', amb, er, eb', pb', phab, phab', p])
#align norm_num.prove_jacobi_sym norm_num.prove_jacobi_sym

end NormNum

end Evaluation

section Tactic

/-!
### The `norm_num` plug-in
-/


namespace Tactic

namespace NormNum

/-- This is the `norm_num` plug-in that evaluates Jacobi and Legendre symbols. -/
@[norm_num]
unsafe def eval_jacobi_sym : expr → tactic (expr × expr)
  | q(jacobiSym $(ea) $(eb)) => do
    let zc
      ←-- Jacobi symbol
          mk_instance_cache
          q(ℤ)
    let nc ← mk_instance_cache q(ℕ)
    (Prod.snd ∘ Prod.snd) <$> norm_num.prove_jacobi_sym zc nc ea eb
  | q(NormNum.jacobiSymNat $(ea) $(eb)) => do
    let zc
      ←-- Jacobi symbol on natural numbers
          mk_instance_cache
          q(ℤ)
    let nc ← mk_instance_cache q(ℕ)
    (Prod.snd ∘ Prod.snd) <$> norm_num.prove_jacobi_sym_nat zc nc ea eb
  | q(@legendreSym $(ep) $(inst) $(ea)) => do
    let zc
      ←-- Legendre symbol
          mk_instance_cache
          q(ℤ)
    let nc ← mk_instance_cache q(ℕ)
    let (zc, nc, er, pf) ← norm_num.prove_jacobi_sym zc nc ea ep
    pure (er, q(NormNum.LegendreSym.to_jacobiSym).mk_app [ep, inst, ea, er, pf])
  | _ => failed
#align tactic.norm_num.eval_jacobi_sym tactic.norm_num.eval_jacobi_sym

end NormNum

end Tactic

end Tactic
