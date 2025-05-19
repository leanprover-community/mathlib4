/-
Copyright (c) 2025 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Draft
-/

namespace Mathlib
open Lean
open Meta

namespace Meta.NormNum
open Qq

/-- hack, this should be constructed inline -/
def mkRatQ (q : ℚ) : MetaM Q(ℝ) := do
  have m'n : Q(ℕ) := Mathlib.Meta.NormNum.mkRawIntLit q.num
  have m'd : Q(ℕ) := mkRawNatLit q.den
  have r : Result q(0 : ℝ) := .isRat' q(inferInstance) q (m'n) (m'd) q(sorry)
  let ⟨(m' : Q(ℝ)), hm', _⟩ ← r.toSimpResult
  return m'

open Real in
/-- cos_mul_pi_div -/
simproc cos_mul_pi_div (cos (_ * π / _)) := .ofQ fun u α e => do
  match u, α, e with
  | 1, ~q(ℝ), ~q(cos ($m * π / $n)) =>
    let rm ← derive q($m)
    let rn ← derive q($n)
    let qm := rm.toRat.get!
    let qn := rn.toRat.get!
    if qm ∈ Set.Ico 0 (qn / 2) then
      -- already normalized
      return .continue
    let c1 := qm / (2 * qn)
    Lean.logInfo m!"c1: {c1}"
    if Int.fract c1 <= 0.25 then
      let offset : ℤ := Int.floor c1
      let qm' : ℚ := qm - offset * 2 * qn
      let m' ← mkRatQ qm'
      return .continue <| some <| .mk q(cos ($m' * π / $n)) <| some q(sorry)
    else if Int.fract c1 <= 0.5 then
      let offset : ℤ := Int.ceil c1
      let qm' : ℚ := (offset * 2 - 1) * qn - qm
      let m' ← mkRatQ qm'
      return .continue <| some <| .mk q(-cos ($m' * π / $n)) <| some q(sorry)
    else if Int.fract c1 <= 0.75 then
      let offset : ℤ := Int.floor c1
      let qm' : ℚ := qm - (offset * 2 + 1) * qn
      let m' ← mkRatQ qm'
      return .continue <| some <| .mk q(-cos ($m' * π / $n)) <| some q(sorry)
    else
      let offset : ℤ := Int.ceil c1
      let qm' : ℚ := (offset * 2 - 1) * qn - qm
      let m' ← mkRatQ qm'
      return .continue <| some <| .mk q(cos ($m' * π / $n)) <| some q(sorry)
  | _, _, _ => return .continue


end NormNum

end Meta

end Mathlib
