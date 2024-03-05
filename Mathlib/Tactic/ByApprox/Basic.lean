import Mathlib.Data.Rat.Order
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.Rewrites
import Mathlib.Tactic.GRW
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Nat.Sqrt
import Mathlib.Util.Qq

import Mathlib.Tactic.ByApprox.Core
import Mathlib.Tactic.ByApprox.Util
import Mathlib.Tactic.ByApprox.Lemmas

namespace Mathlib.Tactic.ByApprox

open Lean hiding Rat
open Qq Meta

section Sqrt

private lemma lower_bound_sqrt (t : ℝ) (lb t_lb : ℚ)
    (h : lb * lb ≤ t_lb) (p_lb : t ≥ t_lb) : Real.sqrt t ≥ lb := by
  apply Real.le_sqrt_of_sq_le
  trans ↑t_lb
  . rwa [← Rat.cast_pow, Rat.cast_le, pow_two]
  . exact p_lb

private lemma upper_bound_sqrt (t : ℝ) (ub t_ub : ℚ) (ub_pos : ub ≥ 0)
    (h : ub * ub ≥ t_ub) (p_ub : t ≤ t_ub) : Real.sqrt t ≤ ub := by
  refine (Real.sqrt_le_left (Rat.cast_nonneg.mpr ub_pos)).mpr ?_
  trans ↑t_ub
  . exact p_ub
  . rwa [← Rat.cast_pow, Rat.cast_le, pow_two]

/-- `by_approx` extension for `Real.sqrt` --/
@[by_approx Real.sqrt _] def approxSqrt : ByApproxExt where approximate precision proofs e := do
  let .app (_ : Q(ℝ → ℝ)) (a : Q(ℝ)) ← withReducible (whnf e) | throwError "not Real.sqrt"

  trace[ByApprox] "Approx sqrt with arg {a}"

  let ⟨lb, lb_prf, ub, ub_prf⟩ ← approximate precision proofs a

  -- todo these bounds are bad
  let multiplier := 4 ^ precision

  let new_lb := if lb < 0 then 0 else
    ((lb.num.toNat * multiplier).sqrt : ℚ) / ((lb.den * multiplier).sqrt + 1)

  -- todo consider upper bound
  let new_ub := ((ub.num.toNat * multiplier).sqrt + 1 : ℚ) / (ub.den * multiplier).sqrt

  if proofs then
    let (new_lb_prf) ← if lb < 0 then
      pure q(Real.sqrt_nonneg (0 : ℚ))
    else
      mkAppNormNum ``lower_bound_sqrt
        #[a, mkRatExpr new_lb, mkRatExpr lb, none, lb_prf]

    let new_ub_prf ← mkAppNormNum ``upper_bound_sqrt
        #[a, mkRatExpr new_ub, mkRatExpr ub, none, none, ub_prf]

    return ⟨new_lb, new_lb_prf, new_ub, new_ub_prf⟩
  else
    return ⟨new_lb, none, new_ub, none⟩


end Sqrt

section Add

private lemma lower_bound_add (a b : ℝ) (a_l b_l l : ℚ)
  (ha : a ≥ a_l) (hb : b ≥ b_l) (hl : l = a_l + b_l) : a + b ≥ l := by
  rw [hl, Rat.cast_add]
  exact add_le_add ha hb

private lemma upper_bound_add (a b : ℝ) (a_u b_u u : ℚ)
  (ha : a ≤ a_u) (hb : b ≤ b_u) (hl : u = a_u + b_u) : a + b ≤ u := by
  rw [hl, Rat.cast_add]
  exact add_le_add ha hb

/-- `by_approx` extension for `+` --/
@[by_approx _ + _] def approxAdd : ByApproxExt where approximate precision proofs e := do
  let .app (.app (_ : Q(ℝ → ℝ → ℝ)) (a : Q(ℝ))) (b : Q(ℝ)) ← withReducible (whnf e)
    | throwError "not add"

  let ⟨a_lb, a_lb_prf, a_ub, a_ub_prf⟩ ← approximate precision proofs a
  let ⟨b_lb, b_lb_prf, b_ub, b_ub_prf⟩ ← approximate precision proofs b

  let new_lb := a_lb + b_lb
  let new_ub := a_ub + b_ub

  if proofs then
    let new_lb_prf ← mkAppNormNum ``lower_bound_add #[a, b, mkRatExpr a_lb, mkRatExpr b_lb,
      mkRatExpr new_lb, a_lb_prf, b_lb_prf, none]
    let new_ub_prf ← mkAppNormNum ``upper_bound_add #[a, b, mkRatExpr a_ub, mkRatExpr b_ub,
      mkRatExpr new_ub, a_ub_prf, b_ub_prf, none]

    return ⟨new_lb, new_lb_prf, new_ub, new_ub_prf⟩
  else
    return ⟨new_lb, none, new_ub, none⟩

end Add

section Neg

private lemma lower_bound_neg (a : ℝ) (a_u : ℚ) (l : ℚ) (h : a ≤ a_u) (hl : l = - a_u) :
  - a ≥ l := by simpa [neg_div, hl]

private lemma upper_bound_neg (a : ℝ) (a_l : ℚ) (u : ℚ) (h : a ≥ a_l) (hu : u = - a_l) :
  - a ≤ u := by
  simpa [neg_div, hu]


/-- `by_approx` extension for `Neg.neg` --/
@[by_approx Neg.neg _] def approxNeg : ByApproxExt where approximate precision proofs e := do
  let .app (_ : Q(ℝ → ℝ)) (a : Q(ℝ)) ← withReducible (whnf e) | throwError "not Neg.neg"

  let ⟨lb, lb_prf, ub, ub_prf⟩ ← approximate precision proofs a

  if proofs then
    let new_lb_prf ← mkAppNormNum ``lower_bound_neg #[a, mkRatExpr ub, mkRatExpr (-ub),
      ub_prf.get!, none]
    let new_ub_prf ← mkAppNormNum ``upper_bound_neg #[a, mkRatExpr lb, mkRatExpr (-lb),
      lb_prf.get!, none]
    return ⟨-ub, new_lb_prf, -lb, new_ub_prf⟩
  else
    return ⟨-ub, none, -lb, none⟩

end Neg

/-- `by_approx` extension for `-` --/
@[by_approx _ - _] def approxSub : ByApproxExt where approximate precision proofs e := do
  let .app (.app (_ : Q(ℝ → ℝ → ℝ)) (a : Q(ℝ))) (b : Q(ℝ)) ← withReducible (whnf e)
    | throwError "not sub"
  approximate precision proofs q($a + (- $b))

section Inv

private lemma lower_bound_pos_inv (a : ℝ) (a_l a_u l : ℚ)
    (hal : a_l ≤ a) (hau : a_u ≥ a) (hl : l = a_u⁻¹) (al_pos : 0 < a_l) : a⁻¹ ≥ l := by
  refine (le_inv ?_ ?_).mp ?_
  . exact lt_of_lt_of_le (b := ↑a_l) (Rat.cast_pos.mpr al_pos) hal
  . rw [hl, Rat.cast_inv, inv_pos]
    exact lt_of_lt_of_le (Rat.cast_pos.mpr al_pos) (le_trans hal hau)
  . rwa [hl, Rat.cast_inv, inv_inv]

private lemma upper_bound_pos_inv (a : ℝ) (a_l a_u u : ℚ)
    (hal : a_l ≤ a) (_ : a_u ≥ a) (hu : u = a_l⁻¹) (al_pos : 0 < a_l) : a⁻¹ ≤ u := by
  have a_pos : 0 < a := lt_of_lt_of_le (Rat.cast_pos.mpr al_pos) hal
  refine (inv_le a_pos ?_).mpr ?_
  . rwa [hu, Rat.cast_inv, inv_pos, Rat.cast_pos]
  . rwa [hu, Rat.cast_inv, inv_inv]

private lemma lower_bound_neg_inv (a : ℝ) (a_l a_u l : ℚ)
    (_ : a_l ≤ a) (hau : a_u ≥ a) (hl : l = a_u⁻¹) (au_neg : 0 > a_u) : a⁻¹ ≥ l := by
  refine (le_inv_of_neg ?_ ?_).mp ?_
  . exact lt_of_le_of_lt (b := ↑a_u) hau (Rat.cast_lt_zero.mpr au_neg)
  . rwa [hl, Rat.cast_inv, inv_lt_zero, Rat.cast_lt_zero]
  . rwa [hl, Rat.cast_inv, inv_inv]

private lemma upper_bound_neg_inv (a : ℝ) (a_l a_u u : ℚ)
    (hal : a_l ≤ a) (hau : a_u ≥ a) (hu : u = a_l⁻¹) (au_neg : 0 > a_u) : a⁻¹ ≤ u := by
  have a_neg : 0 > a := lt_of_le_of_lt hau (Rat.cast_lt_zero.mpr au_neg)
  refine (inv_le_of_neg a_neg ?_).mpr ?_
  . rw [hu, Rat.cast_inv, inv_lt_zero]
    exact lt_of_le_of_lt hal a_neg
  . rwa [hu, Rat.cast_inv, inv_inv]

/-- `by_approx` extension for `Real.inv` --/
@[by_approx Inv.inv _] def approxInv : ByApproxExt where approximate precision proofs e := do
  let .app (_ : Q(ℝ → ℝ)) (a : Q(ℝ)) ← withReducible (whnf e) | throwError "not Inv.inv"

  let ⟨lb, lb_prf, ub, ub_prf⟩ ← approximate precision proofs a

  let new_lb := ub⁻¹
  let new_ub := lb⁻¹
  if proofs then
    let lb_args : Array (Option Expr) := #[a, mkRatExpr lb, mkRatExpr ub, mkRatExpr new_lb,
      lb_prf, ub_prf, none, none]
    let ub_args : Array (Option Expr) := #[a, mkRatExpr lb, mkRatExpr ub, mkRatExpr new_ub,
      lb_prf, ub_prf, none, none]

    if lb > 0 then
      let new_lb_prf ← mkAppNormNum ``lower_bound_pos_inv lb_args
      let new_ub_prf ←  mkAppNormNum ``upper_bound_pos_inv ub_args
      return ⟨new_lb, new_lb_prf, new_ub, new_ub_prf⟩

    if ub < 0 then
      let new_lb_prf ← mkAppNormNum ``lower_bound_neg_inv lb_args
      let new_ub_prf ← mkAppNormNum ``upper_bound_neg_inv ub_args
      return ⟨new_lb, new_lb_prf, new_ub, new_ub_prf⟩
  else
    return ⟨new_lb, none, new_ub, none⟩

  -- todo what to do?
  throwError "Inv.inv: Need more precision"
end Inv

section Mul

private lemma mul_lower_bound (a b : ℝ) (a_l a_u b_l b_u : ℚ)
    (pa_l : a_l ≤ a) (pa_u : a_u ≥ a) (pb_l : b_l ≤ b) (pb_u : b_u ≥ b)
    (lb : ℚ) (hll : lb ≤ a_l * b_l) (hlu : lb ≤ a_l * b_u)
    (hul : lb ≤ a_u * b_l) (huu : lb ≤ a_u * b_u): a * b ≥ lb := by
  by_cases a_sign : a ≥ 0
  . trans a * b_l
    exact mul_le_mul_of_nonneg_left pb_l a_sign
    by_cases b_l_sign : b_l ≥ 0
    . trans a_l * b_l
      exact mul_le_mul_of_nonneg_right pa_l (Rat.cast_nonneg.mpr b_l_sign)
      rw [← Rat.cast_mul]
      apply Rat.cast_le.mpr hll
    . trans a_u * b_l
      simp at b_l_sign
      exact mul_le_mul_of_nonpos_right pa_u (Rat.cast_nonpos.mpr b_l_sign.le)
      rw [← Rat.cast_mul]
      apply Rat.cast_le.mpr hul
  . simp at a_sign
    trans a * b_u
    exact mul_le_mul_of_nonpos_left pb_u a_sign.le
    by_cases b_u_sign : b_u ≥ 0
    . trans a_l * b_u
      exact mul_le_mul_of_nonneg_right pa_l (Rat.cast_nonneg.mpr b_u_sign)
      rw [← Rat.cast_mul]
      apply Rat.cast_le.mpr hlu
    . trans a_u * b_u
      simp at b_u_sign
      exact mul_le_mul_of_nonpos_right pa_u (Rat.cast_nonpos.mpr b_u_sign.le)
      rw [← Rat.cast_mul]
      apply Rat.cast_le.mpr huu

private lemma mul_upper_bound (a b : ℝ) (a_l a_u b_l b_u : ℚ)
    (pa_l : a_l ≤ a) (pa_u : a_u ≥ a) (pb_l : b_l ≤ b) (pb_u : b_u ≥ b)
    (ub : ℚ) (hll : ub ≥ a_l * b_l) (hlu : ub ≥ a_l * b_u)
    (hul : ub ≥ a_u * b_l) (huu : ub ≥ a_u * b_u): a * b ≤ ub := by
  suffices : a * (- b) ≥ ((- ub) : ℚ)
  . simp at this
    exact this
  apply mul_lower_bound a (-b) a_l a_u (-b_u) (-b_l) pa_l pa_u
  repeat { simp ; assumption }

/-- `by_approx` extension for `*` --/
@[by_approx _ * _] def approxMul : ByApproxExt where approximate precision proofs e := do
  let .app (.app (_ : Q(ℝ → ℝ → ℝ)) (a : Q(ℝ))) (b : Q(ℝ)) ← withReducible (whnf e)
    | throwError "not mul"

  let ⟨a_l, a_l_prf, a_u, a_u_prf⟩ ← approximate precision proofs a
  let ⟨b_l, b_l_prf, b_u, b_u_prf⟩ ← approximate precision proofs b

  let terms := [a_l * b_l, a_l * b_u, a_u * b_l, a_u * b_u]

  let new_lb := terms.minimum.get!
  let new_ub := terms.maximum.get!

  if proofs then
    let new_lb_prf ← mkAppNormNum ``mul_lower_bound #[a, b, none, none, none, none,
      a_l_prf, a_u_prf, b_l_prf, b_u_prf, mkRatExpr new_lb, none, none, none, none]
    let new_ub_prf ← mkAppNormNum ``mul_upper_bound #[a, b, none, none, none, none,
      a_l_prf, a_u_prf, b_l_prf, b_u_prf, mkRatExpr new_ub, none, none, none, none]

    return ⟨new_lb, new_lb_prf, new_ub, new_ub_prf⟩
  else
    return ⟨new_lb, none, new_ub, none⟩

end Mul

@[by_approx _ / _] def approxDiv : ByApproxExt where approximate precision proofs e := do
  let .app (.app (_ : Q(ℝ → ℝ → ℝ)) (a : Q(ℝ))) (b : Q(ℝ)) ← withReducible (whnf e)
    | throwError "not div"

  approximate precision proofs q($a * ($b)⁻¹)

section Abs

private lemma abs_lower_bound_pos (a : ℝ) (a_l : ℚ) (a_lb : a ≥ a_l) :
    |a| ≥ a_l := by grw [← le_abs_self, a_lb]

private lemma abs_lower_bound_neg (a : ℝ) (a_u l : ℚ) (a_ub : a ≤ a_u)
    (a_u_neg : a_u ≤ 0) (h : l = - a_u) : |a| ≥ l := by
  grw [abs_of_nonpos, a_ub, h]
  simp
  grw [a_ub, Rat.cast_nonpos.mpr]
  exact a_u_neg

private lemma abs_lower_bound_zero (a : ℝ) (l : ℚ) (h : l = 0) : |a| ≥ l := by simp [h]

private lemma abs_upper_bound (a : ℝ) (a_l a_u u : ℚ) (a_lb : a ≥ a_l) (a_ub : a ≤ a_u)
    (hln : -a_l ≤ u) (hu : a_u ≤ u) : |a| ≤ u := by
  by_cases a_sign : a ≥ 0
  . grw [← Rat.cast_le.mpr hu, abs_of_nonneg a_sign, a_ub]
  . have a_neg := not_le.mp a_sign
    grw [← Rat.cast_le.mpr hln, abs_of_neg a_neg, a_lb]
    simp


@[by_approx abs _] def approxAbs : ByApproxExt where approximate precision proofs e := do
  let .app (_ : Q(ℝ → ℝ → ℝ)) (a : Q(ℝ)) ← withReducible (whnf e)
    | throwError "not abs"

  let ⟨a_l, a_l_prf, a_u, a_u_prf⟩ ← approximate precision proofs a

  let lb := if (a_l ≥ 0) ≠ (a_u ≥ 0) then 0 else min |a_l| |a_u|
  let ub := max |a_l| |a_u|

  if proofs then
    let lb_prf ← if lb ≥ 0 then
      mkAppNormNum ``abs_lower_bound_pos #[a, mkRatExpr a_l, a_l_prf]
    else if ub ≤ 0 then
      mkAppNormNum ``abs_lower_bound_neg #[a, mkRatExpr a_l, mkRatExpr lb, a_u_prf, none, none]
    else
      mkAppNormNum ``abs_lower_bound_zero #[a, mkRatExpr 0, none]

    let ub_prf ← mkAppNormNum ``abs_upper_bound #[a, mkRatExpr a_l, mkRatExpr a_u, mkRatExpr ub,
      a_l_prf, a_u_prf, none, none]
    return ⟨lb, lb_prf, ub, ub_prf⟩
  else
    return ⟨lb, none, ub, none⟩

end Abs
