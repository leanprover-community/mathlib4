/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Tactic.ComputeAsymptotics.Multiseries
public import Mathlib.Tactic.ComputeAsymptotics.Meta.MS
public import Mathlib.Tactic.ComputeAsymptotics.Meta.Normalization
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

theorem Approximates_sub_zero {basis : Basis} {ms : PreMS basis} {f fC : ℝ → ℝ}
    (h_approx : ms.Approximates (f - fC)) (hC : fC =ᶠ[Filter.atTop] 0) :
    ms.Approximates f := by
  apply PreMS.Approximates_of_EventuallyEq _ h_approx
  have := Filter.EventuallyEq.sub (Filter.EventuallyEq.refl _ f) hC
  simpa using this

-- TODO: rename
theorem approx_cons_zero {basis_hd : ℝ → ℝ} {f : ℝ → ℝ} {exp : ℝ}
    {coef : PreMS []} {tl : PreMS [basis_hd]}
    (h_zero : coef = 0)
    (h_approx : (PreMS.cons exp coef tl).Approximates f) :
    tl.Approximates f := by
  obtain ⟨fC, h_coef, h_maj, h_tl⟩ := PreMS.Approximates_cons h_approx
  simp only [PreMS.Approximates_const_iff, h_zero] at h_coef
  apply Approximates_sub_zero h_tl
  rw [eventuallyEq_iff_sub]
  eta_expand
  simp only [Pi.zero_apply, Pi.sub_apply, sub_zero]
  rw [show (fun a ↦ 0) = fun a ↦ (basis_hd a ^ exp * 0) by simp]
  apply EventuallyEq.mul (by rfl) h_coef

-- TODO: rename
theorem approx_cons_nil {basis_hd basis_tl_hd : ℝ → ℝ} {basis_tl_tl : Basis} {f : ℝ → ℝ} {exp : ℝ}
    {coef : PreMS (basis_tl_hd :: basis_tl_tl)}
    {tl : PreMS (basis_hd :: basis_tl_hd :: basis_tl_tl)}
    (h_approx : (PreMS.cons exp coef tl).Approximates f)
    (h_coef_approx : ∀ fC, coef.Approximates fC →
      PreMS.Approximates (@PreMS.nil basis_tl_hd basis_tl_tl) fC) :
    tl.Approximates f := by
  obtain ⟨fC, h_coef, h_maj, h_tl⟩ := PreMS.Approximates_cons h_approx
  specialize h_coef_approx fC h_coef
  apply PreMS.Approximates_nil at h_coef_approx
  apply Approximates_sub_zero h_tl
  rw [eventuallyEq_iff_sub]
  eta_expand
  simp only [Pi.zero_apply, Pi.sub_apply, sub_zero]
  rw [show (fun a ↦ 0) = fun a ↦ (basis_hd a ^ exp * 0) by simp]
  exact EventuallyEq.mul (by rfl) h_coef_approx

-- TODO: rename
theorem approx_cons_aux {basis_hd : ℝ → ℝ} {basis_tl : Basis} (f : ℝ → ℝ) {exp : ℝ}
    {coef coef' : PreMS basis_tl} {tl : PreMS (basis_hd :: basis_tl)}
    (h_approx : (PreMS.cons exp coef tl).Approximates f)
    (h_coef_approx : ∀ fC, coef.Approximates fC → coef'.Approximates fC) :
    (PreMS.cons exp coef' tl).Approximates f := by
  obtain ⟨fC, h_coef, h_maj, h_tl⟩ := PreMS.Approximates_cons h_approx
  apply PreMS.Approximates.cons fC _ h_maj h_tl
  exact h_coef_approx _ h_coef

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
  h_trimmed : Q(PreMS.Trimmed $val)

/-- Trims a multiseries. -/
def trim {basis : Q(Basis)} (ms : Q(PreMS $basis)) (h_wo : Q(PreMS.WellOrdered $ms))
    (destructStepsLeft := 20) : TacticM (TrimmingResult ms) := do
  let destructStepsLeftNext + 1 := destructStepsLeft
    | throwError "trim: no destruction steps left"
  match basis with
  | ~q(List.nil) => -- const
    return {
      val := q($ms)
      h_wo := q($h_wo)
      h_approx := q(fun _ h ↦ h)
      h_trimmed := q(@PreMS.Trimmed.const $ms)
    }
  | ~q(List.cons $basis_hd $basis_tl) =>
    let ⟨ms_extracted, h_eq_extracted⟩ ← normalizePreMS ms
    let h_extracted_wo : Q(PreMS.WellOrdered $ms_extracted) := q(Eq.subst $h_eq_extracted $h_wo)

    match ms_extracted with
    | ~q(PreMS.nil) =>
      return {
        val := q($ms_extracted)
        h_wo := q($h_extracted_wo)
        h_approx :=
          q(fun f h ↦ Eq.subst (motive := fun x ↦ PreMS.Approximates x f) $h_eq_extracted h)
        h_trimmed := q(@PreMS.Trimmed.nil $basis_hd $basis_tl)
      }
    | ~q(PreMS.cons $exp $coef $tl) =>
      let h_coef_wo : Q(PreMS.WellOrdered $coef) :=
        q((PreMS.WellOrdered_cons $h_extracted_wo).left)
      let h_comp : Q(PreMS.leadingExp $tl < $exp) :=
        q((PreMS.WellOrdered_cons $h_extracted_wo).right.left)
      let h_tl_wo : Q(PreMS.WellOrdered $tl) :=
        q((PreMS.WellOrdered_cons $h_extracted_wo).right.right)

      match basis_tl with
      | ~q(List.nil) =>
        match ← checkZero coef with
        | .neq h_coef_ne_zero =>
          let h_coef_trimmed : Q(PreMS.Trimmed $coef) := q(PreMS.Trimmed.const)
          return {
            val := q($ms_extracted)
            h_wo := q($h_extracted_wo)
            h_approx :=
              q(fun f h ↦ Eq.subst (motive := fun x ↦ PreMS.Approximates x f) $h_eq_extracted h)
            h_trimmed := q(PreMS.Trimmed.cons $h_coef_trimmed $h_coef_ne_zero)
          }
        | .eq h_coef_eq_zero =>
          let tl_trimmed ← trim tl h_tl_wo destructStepsLeftNext
          return {
            val := q($tl_trimmed.val)
            h_wo := q($tl_trimmed.h_wo)
            h_approx :=
              q(fun f h ↦ $tl_trimmed.h_approx f
                (approx_cons_zero $h_coef_eq_zero
                  (Eq.subst (motive := fun x ↦ PreMS.Approximates x f) $h_eq_extracted h)))
            h_trimmed := q($tl_trimmed.h_trimmed)
          }
      | ~q(List.cons $basis_tl_hd $basis_tl_tl) =>
        let coef_trimmed ← trim coef h_coef_wo destructStepsLeftNext
        match coef_trimmed.val with
        | ~q(PreMS.nil) =>
          let tl_trimmed ← trim tl h_tl_wo destructStepsLeftNext
          return {
            val := q($tl_trimmed.val)
            h_wo := q($tl_trimmed.h_wo)
            h_approx := q(fun f h ↦ $tl_trimmed.h_approx f
              (approx_cons_nil
                (Eq.subst (motive := fun x ↦ PreMS.Approximates x f) $h_eq_extracted h)
                $coef_trimmed.h_approx))
            h_trimmed := q($tl_trimmed.h_trimmed)
          }
        | ~q(PreMS.cons $coef_exp $coef_coef $coef_tl) =>
          let h_coef_ne_zero : Q($coef_trimmed.val ≠ PreMS.zero _) := q(PreMS.cons_ne_zero)
          return {
            val := q(PreMS.cons $exp $coef_trimmed.val $tl)
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


/-- Result of the `trimPartial` function. -/
structure PartialTrimmingResult {basis : Q(Basis)} (ms : Q(PreMS $basis)) where
  /-- Trimmed multiseries. -/
  val : Q(PreMS $basis)
  /-- Proof that it is well-ordered. -/
  h_wo : Q(PreMS.WellOrdered $val)
  /-- Proof that it approximates the same function. -/
  h_approx : Q(∀ f, PreMS.Approximates $ms f → PreMS.Approximates $val f)
  /-- Optional proof that it is trimmed. It it's not present, then it can be proved that
  `FirstIsNeg ms.leadingTerm.exps` is true by the `getFirstIs` function. -/
  h_trimmed : Option Q(PreMS.Trimmed $val)

/-- Same as `trim` but stops when it is clear that `FirstIsNeg ms.leadingTerm.exps` is true. In such
case one can prove that the limit is zero without the `ms.Trimmed` assumption. -/
def trimPartial {basis : Q(Basis)} (ms : Q(PreMS $basis))
    (h_wo : Q(PreMS.WellOrdered $ms)) (allZero := true) (destructStepsLeft := 20) :
    TacticM (PartialTrimmingResult ms) := do
  let destructStepsLeftNext + 1 := destructStepsLeft
    | throwError "trimPartial: no destruction steps left"
  match basis with
  | ~q(List.nil) => -- const
    return {
      val := q($ms)
      h_wo := q($h_wo)
      h_approx := q(fun _ h ↦ h)
      h_trimmed := .some q(@PreMS.Trimmed.const $ms)
    }
  | ~q(List.cons $basis_hd $basis_tl) =>
    let ⟨ms_extracted, h_eq_extracted⟩ ← normalizePreMS ms
    let h_extracted_wo : Q(PreMS.WellOrdered $ms_extracted) := q(Eq.subst $h_eq_extracted $h_wo)

    match ms_extracted with
    | ~q(PreMS.nil) =>
      return {
        val := q($ms_extracted)
        h_wo := q($h_extracted_wo)
        h_approx :=
          q(fun f h ↦ Eq.subst (motive := fun x ↦ PreMS.Approximates x f) $h_eq_extracted h)
        h_trimmed := .some q(@PreMS.Trimmed.nil $basis_hd $basis_tl)
      }
    | ~q(PreMS.cons $exp $coef $tl) =>
      let mut allZeroNew := allZero
      if allZero then
        match ← compareReal exp with
        | .neg _ =>
          return {
            val := q($ms_extracted)
            h_wo := q($h_extracted_wo)
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
        match ← checkZero coef with
        | .neq h_coef_ne_zero =>
          let h_coef_trimmed : Q(PreMS.Trimmed $coef) := q(PreMS.Trimmed.const)
          return {
            val := q($ms_extracted)
            h_wo := q($h_extracted_wo)
            h_approx :=
              q(fun f h ↦ Eq.subst (motive := fun x ↦ PreMS.Approximates x f) $h_eq_extracted h)
            h_trimmed := .some q(PreMS.Trimmed.cons $h_coef_trimmed $h_coef_ne_zero)
          }
        | .eq h_coef_eq_zero =>
          let tl_trimmed ← trimPartial tl h_tl_wo allZero destructStepsLeftNext
          return {
            val := q($tl_trimmed.val)
            h_wo := q($tl_trimmed.h_wo)
            h_approx :=
              q(fun f h ↦ $tl_trimmed.h_approx f
                (approx_cons_zero $h_coef_eq_zero
                  (Eq.subst (motive := fun x ↦ PreMS.Approximates x f) $h_eq_extracted h)))
            h_trimmed := tl_trimmed.h_trimmed
          }
      | ~q(List.cons $basis_tl_hd $basis_tl_tl) =>
        let coef_trimmed ← trimPartial coef h_coef_wo allZeroNew destructStepsLeftNext
        match coef_trimmed.val with
        | ~q(PreMS.nil) =>
          let tl_trimmed ← trimPartial tl h_tl_wo allZero destructStepsLeftNext
          return {
            val := q($tl_trimmed.val)
            h_wo := q($tl_trimmed.h_wo)
            h_approx := q(fun f h ↦ $tl_trimmed.h_approx f
              (approx_cons_nil
                (Eq.subst (motive := fun x ↦ PreMS.Approximates x f) $h_eq_extracted h)
                $coef_trimmed.h_approx))
            h_trimmed := tl_trimmed.h_trimmed
          }
        | ~q(PreMS.cons $coef_exp $coef_coef $coef_tl) =>
          let h_coef_ne_zero : Q($coef_trimmed.val ≠ PreMS.zero _) := q(PreMS.cons_ne_zero)
          return {
            val := q(PreMS.cons $exp $coef_trimmed.val $tl)
            h_wo := q(PreMS.WellOrdered.cons $coef_trimmed.h_wo $h_comp $h_tl_wo)
            h_approx :=
              q(fun f h ↦ approx_cons_aux f
                (Eq.subst (motive := fun x ↦ PreMS.Approximates x f) $h_eq_extracted h)
                $coef_trimmed.h_approx)
            h_trimmed := coef_trimmed.h_trimmed.map fun h_trimmed ↦
              q(PreMS.Trimmed.cons $h_trimmed $h_coef_ne_zero)
          }
        | _ => throwError "trimPartial returned wrong ms"
      | _ => throwError "Unexpected basis_tl in trim"
    | _ => throwError "extractMS returned wrong ms"

/-- Trims a multiseries. -/
def trimMS (ms : MS) : TacticM ((ms' : MS) × Q(PreMS.Trimmed $ms'.val)) := do
  let res ← trim ms.val ms.h_wo
  let newMs : MS := {
    basis := ms.basis
    logBasis := ms.logBasis
    val := res.val
    f := ms.f
    h_wo := res.h_wo
    h_approx := q($res.h_approx _ $ms.h_approx)
    h_basis := ms.h_basis
    h_logBasis := ms.h_logBasis
  }
  return ⟨newMs, res.h_trimmed⟩

/-- Same as `trimMS` but stops when it is clear that `FirstIsNeg ms.leadingTerm.exps` is true.
In such case one can prove that the limit is zero without the `ms.Trimmed` assumption. -/
def trimPartialMS (ms : MS) : TacticM ((ms' : MS) × Option Q(PreMS.Trimmed $ms'.val)) := do
  let res ← trimPartial ms.val ms.h_wo
  let newMs : MS := {
    basis := ms.basis
    logBasis := ms.logBasis
    val := res.val
    f := ms.f
    h_wo := res.h_wo
    h_approx := q($res.h_approx _ $ms.h_approx)
    h_basis := ms.h_basis
    h_logBasis := ms.h_logBasis
  }
  return ⟨newMs, res.h_trimmed⟩

end Trimming

end ComputeAsymptotics
