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


inductive CheckZeroResult {basis : Q(Basis)} (ms : Q(PreMS $basis))
| neq (h_ne_zero : Q(¬ PreMS.IsZero $ms))
| eq (h_eq_zero : Q(PreMS.IsZero $ms))

theorem const_not_zero_not_IsZero {ms : PreMS []} (h : ms.toReal ≠ 0) :
  ¬ PreMS.IsZero ms := by
  simpa

def checkZero {basis : Q(Basis)} (ms : Q(PreMS $basis)) : TacticM (CheckZeroResult ms) := do
  match basis with
  | ~q(List.nil) =>
    match ← CompareReal.checkZero q(($ms).toReal) with
    | .eq h => return .eq q(PreMS.IsZero.const $h) --q($h)
    | .neq h => return .neq q(const_not_zero_not_IsZero $h) --q($h)
  | ~q(List.cons $basis_hd $basis_tl) =>
    match ms with
    | ~q(PreMS.mk .nil $f) => return .eq q(PreMS.IsZero.nil $f)
    | ~q(PreMS.mk (.cons $exp $coef $tl) $f) => return .neq q(PreMS.cons_not_IsZero)
    | _ => throwError "checkZero: unexpected ms"


-- theorem Approximates_sub_zero {basis : Basis} {ms : PreMS basis} {f fC : ℝ → ℝ}
--     (h_approx : ms.Approximates (f - fC)) (hC : fC =ᶠ[Filter.atTop] 0) :
--     ms.Approximates f := by
--   apply PreMS.Approximates_of_EventuallyEq _ h_approx
--   have := Filter.EventuallyEq.sub (Filter.EventuallyEq.refl _ f) hC
--   simpa using this

theorem approx_cons_zero {basis_hd : ℝ → ℝ} {basis_tl : Basis} {f : ℝ → ℝ} {exp : ℝ}
    {coef coef' : PreMS basis_tl} {tl : PreMS.SeqMS basis_hd basis_tl}
    (h_approx : (PreMS.mk (.cons exp coef tl) f).Approximates)
    (h_coef'_approx : coef'.Approximates)
    (h_coef_fun : coef'.toFun = coef.toFun)
    (h_zero : coef'.IsZero) :
    (PreMS.mk tl f).Approximates := by
  obtain ⟨h_coef, h_maj, h_tl⟩ := PreMS.Approximates_cons h_approx
  convert PreMS.replaceFun_Approximates _ h_tl
  replace h_zero := PreMS.IsZero_Approximates_zero h_zero h_coef'_approx
  rw [h_coef_fun] at h_zero
  simp
  grw [h_zero]
  simp

-- theorem approx_cons_zero' {basis_hd : ℝ → ℝ} {basis_tl : Basis} {f : ℝ → ℝ} {exp : ℝ}
--     {coef : PreMS basis_tl} {tl : PreMS (basis_hd :: basis_tl)}
--     (h_approx : (PreMS.cons exp coef tl).Approximates f)
--     (h_coef_approx : coef.Approximates 0) :
--     tl.Approximates f := by
--   apply PreMS.Approximates_erase_head h_approx h_coef_approx

-- theorem approx_cons_zero'' {basis_hd : ℝ → ℝ} {basis_tl : Basis} {f : ℝ → ℝ} {exp : ℝ}
--     {coef coef' : PreMS basis_tl} {tl : PreMS (basis_hd :: basis_tl)}
--     (h_approx : (PreMS.cons exp coef tl).Approximates f)
--     (h_coef_approx : ∀ fC, coef.Approximates fC → coef'.Approximates fC)
--     (h_coef : coef' = PreMS.zero _) :
--     tl.Approximates f := by
--   apply approx_cons_zero h_approx
--   exact h_coef ▸ h_coef_approx

-- TODO: rename
theorem approx_cons_aux {basis_hd : ℝ → ℝ} {basis_tl : Basis} (f : ℝ → ℝ) {exp : ℝ}
    {coef coef' : PreMS basis_tl} {tl : PreMS.SeqMS basis_hd basis_tl}
    (h_approx : (PreMS.mk (.cons exp coef tl) f).Approximates)
    (h_coef'_approx : coef'.Approximates)
    (h_coef_fun : coef'.toFun = coef.toFun) :
    (PreMS.mk (.cons exp coef' tl) f).Approximates := by
  obtain ⟨h_coef, h_maj, h_tl⟩ := PreMS.Approximates_cons h_approx
  apply PreMS.Approximates.cons h_coef'_approx h_maj
  convert h_tl

-- def proveApproximatesZero {basis : Q(Basis)} (ms : Q(PreMS $basis))
--     (h_basis : Q(WellFormedBasis $basis)) :
--     TacticM Q(($ms).Approximates 0) := do
--   let ⟨f, _, h_approx⟩ ← toFun ms q($h_basis)
--   let hf ← proveFunEqZero f
--   pure q(PreMS.Approximates_of_EventuallyEq $hf $h_approx)

-- theorem Approximates_sub_zero {basis : Basis} {ms : PreMS basis} {f fC : ℝ → ℝ}
--     (h_approx : ms.Approximates (f - fC)) (hC : fC =ᶠ[Filter.atTop] 0) :
--     ms.Approximates f := by
--   apply PreMS.Approximates_of_EventuallyEq _ h_approx
--   have := Filter.EventuallyEq.sub (Filter.EventuallyEq.refl _ f) hC
--   simpa using this

-- -- TODO: rename
-- theorem approx_cons_zero {basis_hd : ℝ → ℝ} {f : ℝ → ℝ} {exp : ℝ}
--     {coef : PreMS []} {tl : PreMS [basis_hd]}
--     (h_zero : coef = 0)
--     (h_approx : (PreMS.cons exp coef tl).Approximates f) :
--     tl.Approximates f := by
--   obtain ⟨fC, h_coef, h_maj, h_tl⟩ := PreMS.Approximates_cons h_approx
--   simp only [PreMS.Approximates_const_iff, h_zero] at h_coef
--   apply Approximates_sub_zero h_tl
--   rw [eventuallyEq_iff_sub]
--   eta_expand
--   simp only [Pi.zero_apply, Pi.sub_apply, sub_zero]
--   rw [show (fun a ↦ 0) = fun a ↦ (basis_hd a ^ exp * 0) by simp]
--   apply EventuallyEq.mul (by rfl) h_coef

-- -- TODO: rename
-- theorem approx_cons_nil {basis_hd basis_tl_hd : ℝ → ℝ} {basis_tl_tl : Basis} {f : ℝ → ℝ} {exp : ℝ}
--     {coef : PreMS (basis_tl_hd :: basis_tl_tl)}
--     {tl : PreMS (basis_hd :: basis_tl_hd :: basis_tl_tl)}
--     (h_approx : (PreMS.cons exp coef tl).Approximates f)
--     (h_coef_approx : ∀ fC, coef.Approximates fC →
--       PreMS.Approximates (@PreMS.nil basis_tl_hd basis_tl_tl) fC) :
--     tl.Approximates f := by
--   obtain ⟨fC, h_coef, h_maj, h_tl⟩ := PreMS.Approximates_cons h_approx
--   specialize h_coef_approx fC h_coef
--   apply PreMS.Approximates_nil at h_coef_approx
--   apply Approximates_sub_zero h_tl
--   rw [eventuallyEq_iff_sub]
--   eta_expand
--   simp only [Pi.zero_apply, Pi.sub_apply, sub_zero]
--   rw [show (fun a ↦ 0) = fun a ↦ (basis_hd a ^ exp * 0) by simp]
--   exact EventuallyEq.mul (by rfl) h_coef_approx

-- -- TODO: rename
-- theorem approx_cons_aux {basis_hd : ℝ → ℝ} {basis_tl : Basis} (f : ℝ → ℝ) {exp : ℝ}
--     {coef coef' : PreMS basis_tl} {tl : PreMS (basis_hd :: basis_tl)}
--     (h_approx : (PreMS.cons exp coef tl).Approximates f)
--     (h_coef_approx : ∀ fC, coef.Approximates fC → coef'.Approximates fC) :
--     (PreMS.cons exp coef' tl).Approximates f := by
--   obtain ⟨fC, h_coef, h_maj, h_tl⟩ := PreMS.Approximates_cons h_approx
--   apply PreMS.Approximates.cons fC _ h_maj h_tl
--   exact h_coef_approx _ h_coef

/-- Result of the `trim` function. -/
structure TrimmingResult {basis : Q(Basis)} (ms : Q(PreMS $basis)) where
  /-- Trimmed multiseries. -/
  val : Q(PreMS $basis)
  /-- Proof of its well-orderedness. -/
  h_wo : Q(PreMS.WellOrdered $val)
  /-- Proof that it approximates the same function. -/
  h_fun : Q(PreMS.toFun $val = PreMS.toFun $ms)
  h_approx : Q(PreMS.Approximates $val)
  /-- Proof that it is trimmed. -/
  h_trimmed : Option Q(PreMS.Trimmed $val)

mutual

/-- Trims a multiseries. -/
partial def trimWithoutOracle {basis : Q(Basis)} (ms : Q(PreMS $basis))
    (h_wo : Q(PreMS.WellOrdered $ms)) (h_approx : Q(PreMS.Approximates $ms))
    (h_basis : Q(WellFormedBasis $basis))
    (allZero : Bool)
    (destructStepsLeft := 5) :
    TacticM (Option <| TrimmingResult ms) := do
  let destructStepsLeftNext + 1 := destructStepsLeft
    | return none
  match basis with
  | ~q(List.nil) => -- const; TODO: do we need it?
    return some {
      val := q($ms)
      h_wo := q($h_wo)
      h_approx := q($h_approx)
      h_trimmed := some q(PreMS.Trimmed.const)
      h_fun := q(rfl)
    }
  | ~q(List.cons $basis_hd $basis_tl) =>
    let ⟨ms_extracted, h_eq_extracted⟩ ← normalizePreMS ms
    -- dbg_trace f!"Normalized ms: {← ppExpr ms_extracted}"
    let h_extracted_wo : Q(PreMS.WellOrdered $ms_extracted) := q($h_eq_extracted ▸ $h_wo)
    match ms_extracted with
    | ~q(PreMS.mk .nil $f) =>
      return some {
        val := q($ms_extracted)
        h_wo := q($h_extracted_wo)
        h_approx := q($h_eq_extracted ▸ $h_approx)
        h_trimmed := some q(PreMS.Trimmed.nil)
        h_fun := q($h_eq_extracted ▸ rfl)
      }
    | ~q(PreMS.mk (.cons $exp $coef $tl) $f) =>
      let mut allZeroNew := allZero
      if allZero then
        match ← compareReal exp with
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

      let h_coef_wo : Q(($coef).WellOrdered) :=
        q((PreMS.WellOrdered_cons $h_extracted_wo).left)
      let h_comp : Q(($tl).leadingExp < $exp) :=
        q((PreMS.WellOrdered_cons $h_extracted_wo).right.left)
      let h_tl_wo : Q(($tl).WellOrdered) :=
        q((PreMS.WellOrdered_cons $h_extracted_wo).right.right)
      let h_coef_approx : Q(PreMS.Approximates $coef) :=
        q((PreMS.Approximates_cons ($h_eq_extracted ▸ $h_approx)).left)

      let coef_trimmed ← trim q($coef) q($h_coef_wo) q($h_coef_approx) q(WellFormedBasis.tail $h_basis) allZeroNew
      match ← checkZero coef_trimmed.val with
      | .neq h_coef_ne_zero =>
        return some {
          val := q(PreMS.mk (.cons $exp $coef_trimmed.val $tl) $f)
          h_wo := q(PreMS.WellOrdered.cons $coef_trimmed.h_wo $h_comp $h_tl_wo)
          h_approx :=
            q(approx_cons_aux $f ($h_eq_extracted ▸ $h_approx) $coef_trimmed.h_approx $coef_trimmed.h_fun)
          h_trimmed := coef_trimmed.h_trimmed.map fun h_coef_trimmed ↦
            q(PreMS.Trimmed.cons $h_coef_trimmed $h_coef_ne_zero)
          h_fun := q(PreMS.mk_toFun.trans ($h_eq_extracted ▸ rfl))
        }
      | .eq h_coef_eq_zero =>
        let h_tl_approx : Q(PreMS.Approximates (.mk $tl $f)) :=
          q(approx_cons_zero ($h_eq_extracted ▸ $h_approx) $coef_trimmed.h_approx $coef_trimmed.h_fun $h_coef_eq_zero)
        let .some tl_trimmed ← trimWithoutOracle q(.mk $tl $f) q(PreMS.WellOrdered_iff_Seq_WellOrdered.mpr $h_tl_wo) --q($h_tl_wo)
          q($h_tl_approx) q($h_basis) allZero destructStepsLeftNext | return none
        return some {
          val := q($tl_trimmed.val)
          h_wo := q($tl_trimmed.h_wo)
          h_approx := q($tl_trimmed.h_approx)
          h_trimmed := tl_trimmed.h_trimmed
          h_fun := q($tl_trimmed.h_fun ▸ (PreMS.mk_toFun.trans ($h_eq_extracted ▸ rfl)))
        }

partial def trim {basis : Q(Basis)} (ms : Q(PreMS $basis))
    (h_wo : Q(PreMS.WellOrdered $ms)) (h_approx : Q(PreMS.Approximates $ms))
    (h_basis : Q(WellFormedBasis $basis))
    (allZero : Bool) :
    TacticM (TrimmingResult ms) := do
  match ← trimWithoutOracle q($ms) q($h_wo) q($h_approx) q($h_basis) allZero with
  | some result => return result
  | none =>
    let ~q($basis_hd :: $basis_tl) := basis | panic! "Unexpected basis in trimAnnotated"
    -- TODO: we do normalization twice
    let ⟨ms_extracted, h_eq_extracted⟩ ← normalizePreMS ms
    let ~q(PreMS.mk $s $f) := ms_extracted | panic! "Unexpected ms in trim"
    let hf ← proveFunEqZero q($f)
    return {
      val := q(PreMS.mk .nil $f)
      h_wo := q(PreMS.WellOrdered.nil $f)
      h_approx := q(PreMS.Approximates.nil $hf)
      h_trimmed := some q(PreMS.Trimmed.nil)
      h_fun := q($h_eq_extracted ▸ rfl)
    }

end

/-- Trims a multiseries. -/
def trimMS (ms : MS) : TacticM ((ms' : MS) × Q(PreMS.Trimmed $ms'.val)) := do
  let res ← trim ms.val ms.h_wo ms.h_approx ms.h_basis false
  let newMs : MS := {
    basis := ms.basis
    logBasis := ms.logBasis
    val := res.val
    h_wo := res.h_wo
    h_approx := q($res.h_approx)
    h_basis := ms.h_basis
    h_logBasis := ms.h_logBasis
  }
  return ⟨newMs, res.h_trimmed.get!⟩

/-- Same as `trimMS` but stops when it is clear that `FirstIsNeg ms.leadingTerm.exps` is true.
In such case one can prove that the limit is zero without the `ms.Trimmed` assumption. -/
def trimPartialMS (ms : MS) : TacticM ((ms' : MS) × Option Q(PreMS.Trimmed $ms'.val)) := do
  let res ← trim ms.val ms.h_wo ms.h_approx ms.h_basis true
  let newMs : MS := {
    basis := ms.basis
    logBasis := ms.logBasis
    val := res.val
    h_wo := res.h_wo
    h_approx := q($res.h_approx)
    h_basis := ms.h_basis
    h_logBasis := ms.h_logBasis
  }
  return ⟨newMs, res.h_trimmed⟩

end Trimming

end ComputeAsymptotics
