import Mathlib.Tactic.Tendsto.Multiseries.Main
import Mathlib.Tactic.Tendsto.Meta.MS
import Mathlib.Tactic.Tendsto.Meta.ElimDestruct
import Mathlib.Tactic.Tendsto.Meta.CompareReal
import Qq

open Filter Asymptotics TendstoTactic Stream' Seq

open Lean Elab Meta Tactic Qq

def extract' {basis : Basis} (ms : PreMS basis) : PreMS basis :=
  match basis with
  | [] => ms
  | List.cons _ _ =>
    match destruct ms with
    | .none => .nil
    | .some (hd, tl) => .cons hd tl

theorem extract'_eq {basis : Basis} {ms : PreMS basis} : ms = extract' ms := by
  cases basis with
  | nil => simp [extract']
  | cons =>
    cases ms with
    | nil => simp [extract']
    | cons => simp [extract']

theorem nil_of_destruct {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : PreMS (basis_hd :: basis_tl)}
    (h_destruct : destruct ms = .none) :
    ms = PreMS.nil :=
  Stream'.Seq.destruct_eq_nil h_destruct

theorem cons_of_destruct {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : PreMS (basis_hd :: basis_tl)}
    {hd : ℝ × PreMS basis_tl} {tl : PreMS (basis_hd :: basis_tl)}
    (h_destruct : destruct ms = .some (hd, tl)) :
    ms = PreMS.cons hd tl :=
  Stream'.Seq.destruct_eq_cons h_destruct

namespace Test

example : ms_cons = PreMS.cons (1, 1) PreMS.nil := by
  have h_destruct : destruct ms_cons = ?_ := by
    unfold ms_cons
    elim_destruct
    exact Eq.refl _
  exact cons_of_destruct h_destruct

end Test

-- brings `ms` to normal form: `const`, `nil`, or `cons` with proof of equality
def extractMS (basis : Q(Basis)) (ms : Q(PreMS $basis)) : TacticM (Q(PreMS $basis) × Expr) := do
  match basis with
  | ~q(List.nil) => return (ms, ← mkAppM ``Eq.refl #[ms]) -- const
  | ~q(List.cons $basis_hd $basis_tl) =>
    let h_eq_expr ← mkFreshExprMVar (← mkEq (← mkAppM ``destruct #[ms]) (← mkFreshExprMVar q(Option (Seq1 (ℝ × PreMS $basis_tl)))))
    let res ← evalTacticAt (← `(tactic| elim_destruct; exact Eq.refl _)) h_eq_expr.mvarId!
    if !res.isEmpty then
      throwError "elim_destruct can't prove the goal"
    let res_type ← instantiateMVars (← h_eq_expr.mvarId!.getType)
    let some (_, _, rhs) := res_type.eq? | throwError "should be Eq"
    match rhs.consumeMData.getAppFnArgs with
    | (``Option.none, _) =>
      return (← mkAppOptM ``PreMS.nil #[basis_hd, basis_tl], ← mkAppM ``nil_of_destruct #[h_eq_expr])
    | (``Option.some, #[_, val]) =>
      match val.getAppFnArgs with
      | (``Prod.mk, #[_, _, hd, tl]) =>
        return (
          ← mkAppOptM ``PreMS.cons #[basis_hd, basis_tl, hd, tl],
          ← mkAppM ``cons_of_destruct #[h_eq_expr]
        )
      | _ => throwError "strange Prod"
    | _ =>
      throwError f!"Strange Option:\n{← ppExpr rhs.consumeMData}"
  | _ => throwError "strage basis"

elab "kek" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let ctx ← Lean.MonadLCtx.getLCtx -- get the local context.
    let ms_decl := (ctx.getAt? 1).get!
    -- dbg_trace ms_decl.type
    match ms_decl.type.getAppFnArgs with
    | (``PreMS, #[basis]) =>
      let (rhs, proof) ← extractMS basis ms_decl.value
      liftMetaTactic fun mvarId => do
        let mvarIdNew ← mvarId.assert `h_eq (← mkEq ms_decl.toExpr rhs) proof
        let (fvar, mvarIdNew) ← mvarIdNew.intro1P
        return [mvarIdNew]
    | _ => throwError "strange ms type"

example :
    let ms_nil : PreMS [id] := PreMS.mul PreMS.nil PreMS.nil;
    ms_nil = PreMS.nil := by
  intro ms_nil
  kek
  exact h_eq

example :
    let ms_cons : PreMS [id] := PreMS.add (PreMS.cons (1, 1) PreMS.nil) (PreMS.cons (1, 1) PreMS.nil);
    ms_cons = PreMS.cons (1, 2) PreMS.nil := by
  intro ms_nil
  kek
  convert h_eq
  sorry -- It's ok, we don't need tail

section Trimming

lemma PreMS.pos_ne_zero {x : PreMS []} (h_pos : 0 < x) : ¬ PreMS.FlatZero x := by
  intro h_zero
  cases h_zero
  linarith

lemma PreMS.neg_ne_zero {x : PreMS []} (h_neg : x < 0) : ¬ PreMS.FlatZero x := by
  intro h_zero
  cases h_zero
  linarith

-- TODO: rename
lemma approx_cons_zero {basis_hd : ℝ → ℝ}  {F : ℝ → ℝ} {exp : ℝ}
    {coef : PreMS []} {tl : PreMS [basis_hd]}
    (h_zero : coef = 0)
    (h_approx : (PreMS.cons (exp, coef) tl).Approximates F) :
    tl.Approximates F := by
  obtain ⟨C, h_coef, h_maj, h_tl⟩ := PreMS.Approximates_cons h_approx
  simp [PreMS.Approximates, h_zero] at h_coef
  apply PreMS.Approximates_of_EventuallyEq _ h_tl
  rw [eventuallyEq_iff_sub]
  eta_expand
  simp
  rw [show (fun a ↦ 0) = fun a ↦ -(basis_hd a ^ exp * 0) by simp]
  apply EventuallyEq.neg
  apply EventuallyEq.mul (by rfl) h_coef

-- TODO: rename
lemma approx_cons_nil {basis_hd basis_tl_hd : ℝ → ℝ} {basis_tl_tl : Basis} {F : ℝ → ℝ} {exp : ℝ}
    {coef : PreMS (basis_tl_hd :: basis_tl_tl)}
    {tl : PreMS (basis_hd :: basis_tl_hd :: basis_tl_tl)}
    (h_approx : (PreMS.cons (exp, coef) tl).Approximates F)
    (h_coef_approx : ∀ C, coef.Approximates C →
      PreMS.Approximates (@PreMS.nil basis_tl_hd basis_tl_tl) C) :
    tl.Approximates F := by
  obtain ⟨C, h_coef, h_maj, h_tl⟩ := PreMS.Approximates_cons h_approx
  specialize h_coef_approx C h_coef
  apply PreMS.Approximates_nil at h_coef_approx
  apply PreMS.Approximates_of_EventuallyEq _ h_tl
  rw [eventuallyEq_iff_sub]
  eta_expand
  simp
  rw [show (fun a ↦ 0) = fun a ↦ -(basis_hd a ^ exp * 0) by simp]
  apply EventuallyEq.neg
  exact EventuallyEq.mul (by rfl) h_coef_approx

-- TODO: rename
lemma approx_cons_aux {basis_hd : ℝ → ℝ} {basis_tl : Basis} (F : ℝ → ℝ) {exp : ℝ}
    {coef coef' : PreMS basis_tl} {tl : PreMS (basis_hd :: basis_tl)}
    (h_approx : (PreMS.cons (exp, coef) tl).Approximates F)
    (h_coef_approx : ∀ C, coef.Approximates C → coef'.Approximates C) :
    (PreMS.cons (exp, coef') tl).Approximates F := by
  obtain ⟨C, h_coef, h_maj, h_tl⟩ := PreMS.Approximates_cons h_approx
  apply PreMS.Approximates.cons C _ h_maj h_tl
  exact h_coef_approx _ h_coef

structure TrimmingResult {basis : Q(Basis)} (ms : Q(PreMS $basis)) where
  result : Q(PreMS $basis) -- TODO: rename to val
  h_wo : Q(PreMS.WellOrdered $result)
  h_approx : Q(∀ F, PreMS.Approximates $ms F → PreMS.Approximates $result F)
  h_trimmed : Q(PreMS.Trimmed $result)

def trim {basis : Q(Basis)} (ms : Q(PreMS $basis))
    (h_wo : Q(PreMS.WellOrdered $ms))
    (destructStepsLeft := 20)
    : TacticM (TrimmingResult ms) := do
  match destructStepsLeft with
  | 0 => throwError "no destruction steps left"
  | destructStepsLeftNext + 1 =>
  match basis with
  | ~q(List.nil) => -- const
    return {
      result := ms
      h_wo := h_wo
      h_approx := q(fun _ h ↦ h)
      h_trimmed := ← mkAppOptM ``PreMS.Trimmed.const #[ms]
    }
  | ~q(List.cons $basis_hd $basis_tl) =>
    let (ms_extracted, h_eq_extracted) ← extractMS basis ms
    let h_eq_extracted : Q($ms = $ms_extracted) := h_eq_extracted -- TODO

    let h_extracted_wo : Q(PreMS.WellOrdered $ms_extracted) := q(Eq.subst $h_eq_extracted $h_wo)

    match ms_extracted with
    | ~q(PreMS.nil) =>
      return {
        result := ms_extracted
        h_wo := h_extracted_wo
        h_approx := q(fun F h ↦ Eq.subst (motive := fun x ↦ PreMS.Approximates x F) $h_eq_extracted h)
        h_trimmed := ← mkAppOptM ``PreMS.Trimmed.nil #[basis_hd, basis_tl]
      }
    | ~q(PreMS.cons $hd $tl) =>
      match hd with
      | ~q( ($exp, $coef) ) =>
        let h_coef_wo : Q(PreMS.WellOrdered $coef) :=
          q((PreMS.WellOrdered_cons $h_extracted_wo).left)
        let h_comp : Q(PreMS.leadingExp $tl < $exp) :=
          q((PreMS.WellOrdered_cons $h_extracted_wo).right.left)
        let h_tl_wo : Q(PreMS.WellOrdered $tl) :=
          q((PreMS.WellOrdered_cons $h_extracted_wo).right.right)

        match basis_tl with
        | ~q(List.nil) =>
          let comp_result ← compareReal coef
          match comp_result with
          | .pos pf =>
            let h_coef_trimmed : Q(PreMS.Trimmed $coef) := q(PreMS.Trimmed.const)
            let h_coef_ne_zero : Q(¬ PreMS.FlatZero $coef) := q(PreMS.pos_ne_zero $pf)
            return {
              result := ms_extracted
              h_wo := h_extracted_wo
              h_approx := q(fun F h ↦ Eq.subst (motive := fun x ↦ PreMS.Approximates x F) $h_eq_extracted h)
              h_trimmed := q(PreMS.Trimmed.cons $h_coef_trimmed $h_coef_ne_zero)
            }
          | .neg pf =>
            let h_coef_trimmed : Q(PreMS.Trimmed $coef) := q(PreMS.Trimmed.const)
            let h_coef_ne_zero : Q(¬ PreMS.FlatZero $coef) := q(PreMS.neg_ne_zero $pf)
            return {
              result := ms_extracted
              h_wo := h_extracted_wo
              h_approx := q(fun F h ↦ Eq.subst (motive := fun x ↦ PreMS.Approximates x F) $h_eq_extracted h)
              h_trimmed := q(PreMS.Trimmed.cons $h_coef_trimmed $h_coef_ne_zero)
            }
          | .zero pf =>
            -- TODO : tl_trimmed -> tl_result
            -- let h_coef_zero : Q(PreMS.FlatZero $coef) := q(PreMS.FlatZero.const $pf)
            let tl_trimmed ← trim tl h_tl_wo destructStepsLeftNext
            return {
              result := tl_trimmed.result
              h_wo := tl_trimmed.h_wo
              h_approx :=
                q(fun F h ↦ $tl_trimmed.h_approx F
                  (approx_cons_zero $pf (Eq.subst (motive := fun x ↦ PreMS.Approximates x F) $h_eq_extracted h)))
              h_trimmed := tl_trimmed.h_trimmed
            }
        | ~q(List.cons $basis_tl_hd $basis_tl_tl) =>
          let coef_result ← trim coef h_coef_wo destructStepsLeftNext
          match coef_result.result with
          | ~q(PreMS.nil) =>
            let tl_trimmed ← trim tl h_tl_wo destructStepsLeftNext
            return {
              result := tl_trimmed.result
              h_wo := tl_trimmed.h_wo
              h_approx := q(fun F h ↦ $tl_trimmed.h_approx F
                (approx_cons_nil (Eq.subst (motive := fun x ↦ PreMS.Approximates x F) $h_eq_extracted h) $coef_result.h_approx))
              h_trimmed := tl_trimmed.h_trimmed
            }
          | ~q(PreMS.cons $coef_hd $coef_tl) =>
            let h_coef_ne_zero : Q(¬ PreMS.FlatZero $coef_result.result) := q(PreMS.FlatZero_cons)
            return {
              result := q(PreMS.cons ($exp, $coef_result.result) $tl)
              h_wo := q(PreMS.WellOrdered.cons $coef_result.h_wo $h_comp $h_tl_wo)
              h_approx :=
                q(fun F h ↦ approx_cons_aux F (Eq.subst (motive := fun x ↦ PreMS.Approximates x F) $h_eq_extracted h) $coef_result.h_approx)
              h_trimmed := q(PreMS.Trimmed.cons $coef_result.h_trimmed $h_coef_ne_zero)
            }
          | _ => throwError "trim returned wrong ms"
        | _ => throwError "strange basis_tl"
      | _ => throwError "strange Prod"
    | _ => throwError "extractMS returned wrong ms"

def trimMS (ms : MS) : TacticM (MS × Expr) := do
  let res ← trim ms.val ms.h_wo
  let newMs : MS := {
    basis := ms.basis
    val := res.result
    F := ms.F
    h_wo := res.h_wo
    h_approx := q($res.h_approx _ $ms.h_approx)
    h_basis := ms.h_basis
  }
  return (newMs, res.h_trimmed)

end Trimming
