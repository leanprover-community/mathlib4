/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Tactic.ComputeAsymptotics.Multiseries
public import Mathlib.Tactic.ComputeAsymptotics.Meta.MS
public import Mathlib.Tactic.ComputeAsymptotics.Meta.Normalization
public import Mathlib.Tactic.ComputeAsymptotics.Meta.ZeroOracle
public import Qq

/-!
# Trimming a multiseries

TODO: write about what is trimming and why it is needed
-/

public meta section

open Filter Asymptotics Stream' Seq ComputeAsymptotics Normalization

open Lean Elab Meta Tactic Qq

namespace ComputeAsymptotics

section Trimming

/-- Result of the `checkZero` function. -/
inductive CheckZeroResult {basis : Q(Basis)} (ms : Q(MultiseriesExpansion $basis))
| neq (h_ne_zero : Q(¬ MultiseriesExpansion.IsZero $ms))
| eq (h_eq_zero : Q(MultiseriesExpansion.IsZero $ms))

theorem const_not_zero_not_IsZero {ms : MultiseriesExpansion []} (h : ms.toReal ≠ 0) :
  ¬ MultiseriesExpansion.IsZero ms := by
  simpa

/-- Checks if a multiseries is zero. -/
def checkZero {basis : Q(Basis)} (ms : Q(MultiseriesExpansion $basis)) :
    TacticM (CheckZeroResult ms) := do
  match basis with
  | ~q(List.nil) =>
    match ← CompareReal.checkZero q(($ms).toReal) with
    | .eq h => return .eq q(MultiseriesExpansion.IsZero.const $h)
    | .neq h => return .neq q(const_not_zero_not_IsZero $h)
  | ~q(List.cons $basis_hd $basis_tl) =>
    match ms with
    | ~q(MultiseriesExpansion.mk .nil $f) => return .eq q(MultiseriesExpansion.IsZero.nil $f)
    | ~q(MultiseriesExpansion.mk (.cons $exp $coef $tl) $f) =>
      return .neq q(MultiseriesExpansion.cons_not_IsZero)
    | _ => throwError "checkZero: unexpected ms"

theorem approx_cons_zero {basis_hd : ℝ → ℝ} {basis_tl : Basis} {f : ℝ → ℝ} {exp : ℝ}
    {coef coef' : MultiseriesExpansion basis_tl}
    {tl : MultiseriesExpansion.Multiseries basis_hd basis_tl}
    (h_approx : (MultiseriesExpansion.mk (.cons exp coef tl) f).Approximates)
    (h_coef'_approx : coef'.Approximates)
    (h_coef_fun : coef'.toFun = coef.toFun)
    (h_zero : coef'.IsZero) :
    (MultiseriesExpansion.mk tl f).Approximates := by
  obtain ⟨h_coef, h_maj, h_tl⟩ := MultiseriesExpansion.Approximates_cons h_approx
  convert MultiseriesExpansion.replaceFun_Approximates _ h_tl
  replace h_zero := MultiseriesExpansion.IsZero_Approximates_zero h_zero h_coef'_approx
  rw [h_coef_fun] at h_zero
  simp only [MultiseriesExpansion.mk_toFun]
  grw [h_zero]
  simp

-- TODO: rename
theorem approx_cons_aux {basis_hd : ℝ → ℝ} {basis_tl : Basis} (f : ℝ → ℝ) {exp : ℝ}
    {coef coef' : MultiseriesExpansion basis_tl}
    {tl : MultiseriesExpansion.Multiseries basis_hd basis_tl}
    (h_approx : (MultiseriesExpansion.mk (.cons exp coef tl) f).Approximates)
    (h_coef'_approx : coef'.Approximates)
    (h_coef_fun : coef'.toFun = coef.toFun) :
    (MultiseriesExpansion.mk (.cons exp coef' tl) f).Approximates := by
  obtain ⟨h_coef, h_maj, h_tl⟩ := MultiseriesExpansion.Approximates_cons h_approx
  apply MultiseriesExpansion.Approximates.cons h_coef'_approx h_maj
  convert h_tl

/-- Result of the `trim` function. -/
structure TrimmingResult {basis : Q(Basis)} (ms : Q(MultiseriesExpansion $basis)) where
  /-- Trimmed multiseries. -/
  val : Q(MultiseriesExpansion $basis)
  /-- Proof of its well-orderedness. -/
  h_wo : Q(MultiseriesExpansion.Sorted $val)
  /-- Proof that it has the same function. -/
  h_fun : Q(MultiseriesExpansion.toFun $val = MultiseriesExpansion.toFun $ms)
  /-- Proof that it approximates the same function. -/
  h_approx : Q(MultiseriesExpansion.Approximates $val)
  /-- Proof that it is trimmed. -/
  h_trimmed : Option Q(MultiseriesExpansion.Trimmed $val)

mutual

/-- Trims a multiseries without using the zero oracle. -/
partial def trimWithoutOracle {basis : Q(Basis)} (ms : Q(MultiseriesExpansion $basis))
    (h_wo : Q(MultiseriesExpansion.Sorted $ms))
    (h_approx : Q(MultiseriesExpansion.Approximates $ms))
    (h_basis : Q(WellFormedBasis $basis))
    (allZero : Bool)
    (destructStepsLeft := 5) :
    TacticM (Option <| TrimmingResult ms) := do
  let destructStepsLeftNext + 1 := destructStepsLeft
    | return none
  match basis with
  | ~q(List.nil) =>
    return some {
      val := q($ms)
      h_wo := q($h_wo)
      h_approx := q($h_approx)
      h_trimmed := some q(MultiseriesExpansion.Trimmed.const)
      h_fun := q(rfl)
    }
  | ~q(List.cons $basis_hd $basis_tl) =>
    let ⟨ms_extracted, h_eq_extracted⟩ ← normalizeMultiseriesExpansion ms
    let h_extracted_wo : Q(MultiseriesExpansion.Sorted $ms_extracted) := q($h_eq_extracted ▸ $h_wo)
    match ms_extracted with
    | ~q(MultiseriesExpansion.mk .nil $f) =>
      return some {
        val := q($ms_extracted)
        h_wo := q($h_extracted_wo)
        h_approx := q($h_eq_extracted ▸ $h_approx)
        h_trimmed := some q(MultiseriesExpansion.Trimmed.nil)
        h_fun := q($h_eq_extracted ▸ rfl)
      }
    | ~q(MultiseriesExpansion.mk (.cons $exp $coef $tl) $f) =>
      let mut allZeroNew := allZero
      if allZero then
        match ← compareReal q($exp) with
        | .neg _ =>
          return some {
            val := q($ms_extracted)
            h_wo := q($h_extracted_wo)
            h_approx := q($h_eq_extracted ▸ $h_approx)
            h_trimmed := .none
            h_fun := q($h_eq_extracted ▸ rfl)
          }
        | .pos _ => allZeroNew := false
        | .zero _ => pure ()

      let h_coef_wo : Q(($coef).Sorted) :=
        q((MultiseriesExpansion.Sorted_cons $h_extracted_wo).left)
      let h_comp : Q(($tl).leadingExp < $exp) :=
        q((MultiseriesExpansion.Sorted_cons $h_extracted_wo).right.left)
      let h_tl_wo : Q(($tl).Sorted) :=
        q((MultiseriesExpansion.Sorted_cons $h_extracted_wo).right.right)
      let h_coef_approx : Q(MultiseriesExpansion.Approximates $coef) :=
        q((MultiseriesExpansion.Approximates_cons ($h_eq_extracted ▸ $h_approx)).left)

      let coef_trimmed ← trim q($coef) q($h_coef_wo) q($h_coef_approx)
        q(WellFormedBasis.tail $h_basis) allZeroNew
      match ← checkZero coef_trimmed.val with
      | .neq h_coef_ne_zero =>
        return some {
          val := q(MultiseriesExpansion.mk (.cons $exp $coef_trimmed.val $tl) $f)
          h_wo := q(MultiseriesExpansion.Sorted.cons $coef_trimmed.h_wo $h_comp $h_tl_wo)
          h_approx :=
            q(approx_cons_aux $f ($h_eq_extracted ▸ $h_approx) $coef_trimmed.h_approx
              $coef_trimmed.h_fun)
          h_trimmed := coef_trimmed.h_trimmed.map fun h_coef_trimmed ↦
            q(MultiseriesExpansion.Trimmed.cons $h_coef_trimmed $h_coef_ne_zero)
          h_fun := q(MultiseriesExpansion.mk_toFun.trans ($h_eq_extracted ▸ rfl))
        }
      | .eq h_coef_eq_zero =>
        let h_tl_approx : Q(MultiseriesExpansion.Approximates (.mk $tl $f)) :=
          q(approx_cons_zero ($h_eq_extracted ▸ $h_approx) $coef_trimmed.h_approx
            $coef_trimmed.h_fun $h_coef_eq_zero)
        let .some tl_trimmed ← trimWithoutOracle q(.mk $tl $f)
          q(MultiseriesExpansion.Sorted_iff_Seq_Sorted.mpr $h_tl_wo)
          q($h_tl_approx) q($h_basis) allZero destructStepsLeftNext | return none
        return some {
          val := q($tl_trimmed.val)
          h_wo := q($tl_trimmed.h_wo)
          h_approx := q($tl_trimmed.h_approx)
          h_trimmed := tl_trimmed.h_trimmed
          h_fun := q($tl_trimmed.h_fun ▸
            (MultiseriesExpansion.mk_toFun.trans ($h_eq_extracted ▸ rfl)))
        }

/-- Trims a multiseries. -/
partial def trim {basis : Q(Basis)} (ms : Q(MultiseriesExpansion $basis))
    (h_wo : Q(MultiseriesExpansion.Sorted $ms))
    (h_approx : Q(MultiseriesExpansion.Approximates $ms))
    (h_basis : Q(WellFormedBasis $basis))
    (allZero : Bool) :
    TacticM (TrimmingResult ms) := do
  match ← trimWithoutOracle q($ms) q($h_wo) q($h_approx) q($h_basis) allZero with
  | some result => return result
  | none =>
    let ~q($basis_hd :: $basis_tl) := basis | panic! "Unexpected basis in trimAnnotated"
    -- TODO: we do normalization twice
    let ⟨ms_extracted, h_eq_extracted⟩ ← normalizeMultiseriesExpansion ms
    let ~q(MultiseriesExpansion.mk $s $f) := ms_extracted | panic! "Unexpected ms in trim"
    let hf ← proveFunEqZero q($f)
    return {
      val := q(MultiseriesExpansion.mk .nil $f)
      h_wo := q(MultiseriesExpansion.Sorted.nil $f)
      h_approx := q(MultiseriesExpansion.Approximates.nil $hf)
      h_trimmed := some q(MultiseriesExpansion.Trimmed.nil)
      h_fun := q($h_eq_extracted ▸ rfl)
    }

end

/-- Trims a multiseries. -/
def trimMS (ms : MS) :
    TacticM ((ms' : MS) × Q(($ms'.val).toFun = ($ms.val).toFun) ×
      Q(MultiseriesExpansion.Trimmed $ms'.val)) := do
  let res ← trim ms.val ms.h_wo ms.h_approx ms.h_basis false
  let newMs : MS := {
    basis := q($ms.basis)
    logBasis := q($ms.logBasis)
    val := q($res.val)
    h_wo := q($res.h_wo)
    h_approx := q($res.h_approx)
    h_basis := q($ms.h_basis)
    h_logBasis := q($ms.h_logBasis)
  }
  return ⟨newMs, q($res.h_fun), res.h_trimmed.get!⟩

/-- Same as `trimMS` but stops when it is clear that `FirstIsNeg ms.leadingTerm.exps` is true.
In such case one can prove that the limit is zero without the `ms.Trimmed` assumption. -/
def trimPartialMS (ms : MS) :
    TacticM ((ms' : MS) × Q(($ms'.val).toFun = ($ms.val).toFun) ×
      Option Q(MultiseriesExpansion.Trimmed $ms'.val)) := do
  let res ← trim ms.val ms.h_wo ms.h_approx ms.h_basis true
  let newMs : MS := {
    basis := q($ms.basis)
    logBasis := q($ms.logBasis)
    val := q($res.val)
    h_wo := q($res.h_wo)
    h_approx := q($res.h_approx)
    h_basis := q($ms.h_basis)
    h_logBasis := q($ms.h_logBasis)
  }
  return ⟨newMs, q($res.h_fun), res.h_trimmed⟩

end Trimming

end ComputeAsymptotics
