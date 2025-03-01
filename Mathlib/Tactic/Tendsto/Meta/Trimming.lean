/-
Copyright (c) 2024 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
import Mathlib.Tactic.Tendsto.Multiseries
import Mathlib.Tactic.Tendsto.Meta.MS
import Mathlib.Tactic.Tendsto.Meta.ElimDestruct
import Mathlib.Tactic.Tendsto.Meta.CompareReal
import Qq

/-!
# TODO
-/

open Filter Asymptotics Stream' Seq TendstoTactic ElimDestruct

open Lean Elab Meta Tactic Qq

namespace TendstoTactic

/-- brings `ms` to normal form: `const`, `nil`, or `cons` with proof of equality. -/
def extractMS (basis : Q(Basis)) (ms : Q(PreMS $basis)) :
    TacticM ((ms' : Q(PreMS $basis)) × Q($ms = $ms')) := do
  match basis with
  | ~q(List.nil) => return ⟨ms, q(Eq.refl $ms)⟩ -- const
  | ~q(List.cons $basis_hd $basis_tl) =>
    let destruct_res ← mkFreshExprMVarQ q(Option (Seq1 (ℝ × PreMS $basis_tl)))
    let h_eq ← mkFreshExprMVarQ q(Stream'.Seq.destruct $ms = $destruct_res)
    try
      let _ ← evalTacticAt (← `(tactic| elim_destruct; exact Eq.refl _)) h_eq.mvarId!
    catch _ =>
      throwError "elim_destruct cannot solve the goal"
    let destruct_res' ← instantiateMVarsQ destruct_res
    haveI' : $destruct_res' =Q $destruct_res := ⟨⟩
    match destruct_res with
    | ~q(Option.none) =>
      return ⟨q(@PreMS.nil $basis_hd $basis_tl), q(PreMS.nil_of_destruct $h_eq)⟩
    | ~q(@Option.some ((Seq1 (ℝ × PreMS «$basis_tl»))) ($hd, $tl)) =>
      -- why do i need explicitly put the type?
      return ⟨q(PreMS.cons $hd $tl), q(PreMS.cons_of_destruct $h_eq)⟩
    | _ =>
      throwError f!"Unexpected destruct_res in extractMS:\n{← ppExpr destruct_res.consumeMData}"
  | _ => throwError "Unexpected basis in extractMS"

section Trimming

theorem Approximates_sub_zero {basis : Basis} {ms : PreMS basis} {f fC : ℝ → ℝ}
    (h_approx : ms.Approximates (f - fC)) (hC : fC =ᶠ[Filter.atTop] 0) :
    ms.Approximates f := by
  apply PreMS.Approximates_of_EventuallyEq _ h_approx
  have := Filter.EventuallyEq.sub (Filter.EventuallyEq.refl _ f) hC
  simpa using this

-- TODO: rename
theorem approx_cons_zero {basis_hd : ℝ → ℝ}  {f : ℝ → ℝ} {exp : ℝ}
    {coef : PreMS []} {tl : PreMS [basis_hd]}
    (h_zero : coef = 0)
    (h_approx : (PreMS.cons (exp, coef) tl).Approximates f) :
    tl.Approximates f := by
  obtain ⟨fC, h_coef, h_maj, h_tl⟩ := PreMS.Approximates_cons h_approx
  simp [PreMS.Approximates, h_zero] at h_coef
  apply Approximates_sub_zero h_tl
  rw [eventuallyEq_iff_sub]
  eta_expand
  simp
  rw [show (fun a ↦ 0) = fun a ↦ (basis_hd a ^ exp * 0) by simp]
  apply EventuallyEq.mul (by rfl) h_coef

-- TODO: rename
theorem approx_cons_nil {basis_hd basis_tl_hd : ℝ → ℝ} {basis_tl_tl : Basis} {f : ℝ → ℝ} {exp : ℝ}
    {coef : PreMS (basis_tl_hd :: basis_tl_tl)}
    {tl : PreMS (basis_hd :: basis_tl_hd :: basis_tl_tl)}
    (h_approx : (PreMS.cons (exp, coef) tl).Approximates f)
    (h_coef_approx : ∀ fC, coef.Approximates fC →
      PreMS.Approximates (@PreMS.nil basis_tl_hd basis_tl_tl) fC) :
    tl.Approximates f := by
  obtain ⟨fC, h_coef, h_maj, h_tl⟩ := PreMS.Approximates_cons h_approx
  specialize h_coef_approx fC h_coef
  apply PreMS.Approximates_nil at h_coef_approx
  apply Approximates_sub_zero h_tl
  rw [eventuallyEq_iff_sub]
  eta_expand
  simp
  rw [show (fun a ↦ 0) = fun a ↦ (basis_hd a ^ exp * 0) by simp]
  exact EventuallyEq.mul (by rfl) h_coef_approx

-- TODO: rename
theorem approx_cons_aux {basis_hd : ℝ → ℝ} {basis_tl : Basis} (f : ℝ → ℝ) {exp : ℝ}
    {coef coef' : PreMS basis_tl} {tl : PreMS (basis_hd :: basis_tl)}
    (h_approx : (PreMS.cons (exp, coef) tl).Approximates f)
    (h_coef_approx : ∀ fC, coef.Approximates fC → coef'.Approximates fC) :
    (PreMS.cons (exp, coef') tl).Approximates f := by
  obtain ⟨fC, h_coef, h_maj, h_tl⟩ := PreMS.Approximates_cons h_approx
  apply PreMS.Approximates.cons fC _ h_maj h_tl
  exact h_coef_approx _ h_coef

structure TrimmingResult {basis : Q(Basis)} (ms : Q(PreMS $basis)) where
  val : Q(PreMS $basis)
  h_wo : Q(PreMS.WellOrdered $val)
  h_approx : Q(∀ f, PreMS.Approximates $ms f → PreMS.Approximates $val f)
  h_trimmed : Q(PreMS.Trimmed $val)

def trim {basis : Q(Basis)} (ms : Q(PreMS $basis))
    (h_wo : Q(PreMS.WellOrdered $ms))
    (destructStepsLeft := 20)
    : TacticM (TrimmingResult ms) := do
  match destructStepsLeft with
  | 0 => throwError "No destruction steps left"
  | destructStepsLeftNext + 1 =>
  match basis with
  | ~q(List.nil) => -- const
    return {
      val := ms
      h_wo := h_wo
      h_approx := q(fun _ h ↦ h)
      h_trimmed := q(@PreMS.Trimmed.const $ms)
    }
  | ~q(List.cons $basis_hd $basis_tl) =>
    let ⟨ms_extracted, h_eq_extracted⟩ ← extractMS basis ms
    let h_extracted_wo : Q(PreMS.WellOrdered $ms_extracted) := q(Eq.subst $h_eq_extracted $h_wo)

    match ms_extracted with
    | ~q(PreMS.nil) =>
      return {
        val := ms_extracted
        h_wo := h_extracted_wo
        h_approx :=
          q(fun f h ↦ Eq.subst (motive := fun x ↦ PreMS.Approximates x f) $h_eq_extracted h)
        h_trimmed := q(@PreMS.Trimmed.nil $basis_hd $basis_tl)
      }
    | ~q(PreMS.cons ($exp, $coef) $tl) =>
      let h_coef_wo : Q(PreMS.WellOrdered $coef) :=
        q((PreMS.WellOrdered_cons $h_extracted_wo).left)
      let h_comp : Q(PreMS.leadingExp $tl < $exp) :=
        q((PreMS.WellOrdered_cons $h_extracted_wo).right.left)
      let h_tl_wo : Q(PreMS.WellOrdered $tl) :=
        q((PreMS.WellOrdered_cons $h_extracted_wo).right.right)

      match basis_tl with
      | ~q(List.nil) =>
        match ← compareReal coef with
        | .pos pf =>
          let h_coef_trimmed : Q(PreMS.Trimmed $coef) := q(PreMS.Trimmed.const)
          let h_coef_ne_zero : Q($coef ≠ PreMS.zero _) := q(Ne.symm (ne_of_lt $pf))
          return {
            val := ms_extracted
            h_wo := h_extracted_wo
            h_approx :=
              q(fun f h ↦ Eq.subst (motive := fun x ↦ PreMS.Approximates x f) $h_eq_extracted h)
            h_trimmed := q(PreMS.Trimmed.cons $h_coef_trimmed $h_coef_ne_zero)
          }
        | .neg pf =>
          let h_coef_trimmed : Q(PreMS.Trimmed $coef) := q(PreMS.Trimmed.const)
          let h_coef_ne_zero : Q($coef ≠ PreMS.zero _) := q(Ne.symm (ne_of_gt $pf))
          return {
            val := ms_extracted
            h_wo := h_extracted_wo
            h_approx :=
              q(fun f h ↦ Eq.subst (motive := fun x ↦ PreMS.Approximates x f) $h_eq_extracted h)
            h_trimmed := q(PreMS.Trimmed.cons $h_coef_trimmed $h_coef_ne_zero)
          }
        | .zero pf =>
          let tl_trimmed ← trim tl h_tl_wo destructStepsLeftNext
          return {
            val := tl_trimmed.val
            h_wo := tl_trimmed.h_wo
            h_approx :=
              q(fun f h ↦ $tl_trimmed.h_approx f
                (approx_cons_zero $pf
                  (Eq.subst (motive := fun x ↦ PreMS.Approximates x f) $h_eq_extracted h)))
            h_trimmed := tl_trimmed.h_trimmed
          }
      | ~q(List.cons $basis_tl_hd $basis_tl_tl) =>
        let coef_trimmed ← trim coef h_coef_wo destructStepsLeftNext
        match coef_trimmed.val with
        | ~q(PreMS.nil) =>
          let tl_trimmed ← trim tl h_tl_wo destructStepsLeftNext
          return {
            val := tl_trimmed.val
            h_wo := tl_trimmed.h_wo
            h_approx := q(fun f h ↦ $tl_trimmed.h_approx f
              (approx_cons_nil
                (Eq.subst (motive := fun x ↦ PreMS.Approximates x f) $h_eq_extracted h)
                $coef_trimmed.h_approx))
            h_trimmed := tl_trimmed.h_trimmed
          }
        | ~q(PreMS.cons $coef_hd $coef_tl) =>
          let h_coef_ne_zero : Q($coef_trimmed.val ≠ PreMS.zero _) := q(PreMS.noConfusion_zero)
          return {
            val := q(PreMS.cons ($exp, $coef_trimmed.val) $tl)
            h_wo := q(PreMS.WellOrdered.cons $coef_trimmed.h_wo $h_comp $h_tl_wo)
            h_approx :=
              q(fun f h ↦ approx_cons_aux f
                (Eq.subst (motive := fun x ↦ PreMS.Approximates x f) $h_eq_extracted h)
                $coef_trimmed.h_approx)
            h_trimmed := q(PreMS.Trimmed.cons $coef_trimmed.h_trimmed $h_coef_ne_zero)
          }
        | _ => throwError "trim returned wrong ms"
      | _ => throwError "Unexpected basis_tl in trim"
    | _ => throwError "extractMS returned wrong ms"


structure PartialTrimmingResult {basis : Q(Basis)} (ms : Q(PreMS $basis)) where
  val : Q(PreMS $basis)
  h_wo : Q(PreMS.WellOrdered $val)
  h_approx : Q(∀ f, PreMS.Approximates $ms f → PreMS.Approximates $val f)
  h_trimmed : Option Q(PreMS.Trimmed $val)

/-- Same as `trim` but stops when it is clear that `FirstIsNeg ms.leadingTerm.exps` is true. In such
case we can prove that the limit is zero without `ms.Trimmed`. -/
def trimPartial {basis : Q(Basis)} (ms : Q(PreMS $basis))
    (h_wo : Q(PreMS.WellOrdered $ms))
    (allZero := true)
    (destructStepsLeft := 20)
    : TacticM (PartialTrimmingResult ms) := do
  match destructStepsLeft with
  | 0 => throwError "No destruction steps left"
  | destructStepsLeftNext + 1 =>
  match basis with
  | ~q(List.nil) => -- const
    return {
      val := ms
      h_wo := h_wo
      h_approx := q(fun _ h ↦ h)
      h_trimmed := .some q(@PreMS.Trimmed.const $ms)
    }
  | ~q(List.cons $basis_hd $basis_tl) =>
    let ⟨ms_extracted, h_eq_extracted⟩ ← extractMS basis ms
    let h_extracted_wo : Q(PreMS.WellOrdered $ms_extracted) := q(Eq.subst $h_eq_extracted $h_wo)

    match ms_extracted with
    | ~q(PreMS.nil) =>
      return {
        val := ms_extracted
        h_wo := h_extracted_wo
        h_approx :=
          q(fun f h ↦ Eq.subst (motive := fun x ↦ PreMS.Approximates x f) $h_eq_extracted h)
        h_trimmed := .some q(@PreMS.Trimmed.nil $basis_hd $basis_tl)
      }
    | ~q(PreMS.cons ($exp, $coef) $tl) =>
      let mut allZeroNew := allZero
      if allZero then
        match ← compareReal exp with
        | .neg _ =>
          return {
            val := ms_extracted
            h_wo := h_extracted_wo
            h_approx :=
              q(fun f h ↦ Eq.subst (motive := fun x ↦ PreMS.Approximates x f) $h_eq_extracted h)
            h_trimmed := .none
          }
        | .pos _ =>
          allZeroNew := false
        | .zero _ => pure ()

      let h_coef_wo : Q(PreMS.WellOrdered $coef) :=
        q((PreMS.WellOrdered_cons $h_extracted_wo).left)
      let h_comp : Q(PreMS.leadingExp $tl < $exp) :=
        q((PreMS.WellOrdered_cons $h_extracted_wo).right.left)
      let h_tl_wo : Q(PreMS.WellOrdered $tl) :=
        q((PreMS.WellOrdered_cons $h_extracted_wo).right.right)

      match basis_tl with
      | ~q(List.nil) =>
        match ← compareReal coef with
        | .pos pf =>
          let h_coef_trimmed : Q(PreMS.Trimmed $coef) := q(PreMS.Trimmed.const)
          let h_coef_ne_zero : Q($coef ≠ PreMS.zero _) := q(Ne.symm (ne_of_lt $pf))
          return {
            val := ms_extracted
            h_wo := h_extracted_wo
            h_approx :=
              q(fun f h ↦ Eq.subst (motive := fun x ↦ PreMS.Approximates x f) $h_eq_extracted h)
            h_trimmed := .some q(PreMS.Trimmed.cons $h_coef_trimmed $h_coef_ne_zero)
          }
        | .neg pf =>
          let h_coef_trimmed : Q(PreMS.Trimmed $coef) := q(PreMS.Trimmed.const)
          let h_coef_ne_zero : Q($coef ≠ PreMS.zero _) := q(Ne.symm (ne_of_gt $pf))
          return {
            val := ms_extracted
            h_wo := h_extracted_wo
            h_approx :=
              q(fun f h ↦ Eq.subst (motive := fun x ↦ PreMS.Approximates x f) $h_eq_extracted h)
            h_trimmed := .some q(PreMS.Trimmed.cons $h_coef_trimmed $h_coef_ne_zero)
          }
        | .zero pf =>
          let tl_trimmed ← trimPartial tl h_tl_wo allZero destructStepsLeftNext
          return {
            val := tl_trimmed.val
            h_wo := tl_trimmed.h_wo
            h_approx :=
              q(fun f h ↦ $tl_trimmed.h_approx f
                (approx_cons_zero $pf
                  (Eq.subst (motive := fun x ↦ PreMS.Approximates x f) $h_eq_extracted h)))
            h_trimmed := tl_trimmed.h_trimmed
          }
      | ~q(List.cons $basis_tl_hd $basis_tl_tl) =>
        let coef_trimmed ← trimPartial coef h_coef_wo allZeroNew destructStepsLeftNext
        match coef_trimmed.val with
        | ~q(PreMS.nil) =>
          let tl_trimmed ← trimPartial tl h_tl_wo allZero destructStepsLeftNext
          return {
            val := tl_trimmed.val
            h_wo := tl_trimmed.h_wo
            h_approx := q(fun f h ↦ $tl_trimmed.h_approx f
              (approx_cons_nil
                (Eq.subst (motive := fun x ↦ PreMS.Approximates x f) $h_eq_extracted h)
                $coef_trimmed.h_approx))
            h_trimmed := tl_trimmed.h_trimmed
          }
        | ~q(PreMS.cons $coef_hd $coef_tl) =>
          let h_coef_ne_zero : Q($coef_trimmed.val ≠ PreMS.zero _) := q(PreMS.noConfusion_zero)
          return {
            val := q(PreMS.cons ($exp, $coef_trimmed.val) $tl)
            h_wo := q(PreMS.WellOrdered.cons $coef_trimmed.h_wo $h_comp $h_tl_wo)
            h_approx :=
              q(fun f h ↦ approx_cons_aux f
                (Eq.subst (motive := fun x ↦ PreMS.Approximates x f) $h_eq_extracted h)
                $coef_trimmed.h_approx)
            h_trimmed := coef_trimmed.h_trimmed.map fun h_trimmed ↦
              q(PreMS.Trimmed.cons $h_trimmed $h_coef_ne_zero)
          }
        | _ => throwError "trim returned wrong ms"
      | _ => throwError "Unexpected basis_tl in trim"
    | _ => throwError "extractMS returned wrong ms"

def trimMS (ms : MS) : TacticM ((ms' : MS) × Q(PreMS.Trimmed $ms'.val)) := do
  let res ← trim ms.val ms.h_wo
  let newMs : MS := {
    basis := ms.basis
    val := res.val
    f := ms.f
    h_wo := res.h_wo
    h_approx := q($res.h_approx _ $ms.h_approx)
    h_basis := ms.h_basis
  }
  return ⟨newMs, res.h_trimmed⟩

def trimPartialMS (ms : MS) : TacticM ((ms' : MS) × Option Q(PreMS.Trimmed $ms'.val)) := do
  let res ← trimPartial ms.val ms.h_wo
  let newMs : MS := {
    basis := ms.basis
    val := res.val
    f := ms.f
    h_wo := res.h_wo
    h_approx := q($res.h_approx _ $ms.h_approx)
    h_basis := ms.h_basis
  }
  return ⟨newMs, res.h_trimmed⟩

end Trimming

end TendstoTactic
