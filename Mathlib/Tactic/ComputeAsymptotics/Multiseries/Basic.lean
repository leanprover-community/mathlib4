/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Tactic.ComputeAsymptotics.Multiseries.Defs
public import Mathlib.Tactic.ComputeAsymptotics.Multiseries.Basis

/-!
# TODO
-/

set_option linter.style.multiGoal false

@[expose] public section

namespace ComputeAsymptotics

namespace PreMS

open Filter

/-- Multiseries representing constant. -/
def const (basis : Basis) (c : ℝ) : PreMS basis :=
  match basis with
  | [] => c
  | List.cons _ basis_tl =>
    cons 0 (const basis_tl c) nil

/-- Neutral element for addition. It is `0 : ℝ` for empty basis and `[]` otherwise. -/
def zero (basis) : PreMS basis :=
  match basis with
  | [] => (0 : ℝ)
  | List.cons _ _ => .nil

/-- This instance is needed to create instance for `AddCommMonoid (PreMS basis)`, which is
necessary for using `abel` tactic in our proofs. -/
instance instZero {basis : Basis} : Zero (PreMS basis) where
  zero := zero basis

@[simp]
theorem cons_ne_zero {basis_hd : ℝ → ℝ} {basis_tl : Basis} {exp : ℝ} {coef : PreMS basis_tl}
    {tl : PreMS (basis_hd :: basis_tl)} :
    cons exp coef tl ≠ (0 : PreMS (basis_hd :: basis_tl)) := by
  rw [show (0 : PreMS (basis_hd :: basis_tl)) = nil by rfl]
  simp

@[simp]
theorem zero_ne_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {exp : ℝ} {coef : PreMS basis_tl}
    {tl : PreMS (basis_hd :: basis_tl)} :
    (0 : PreMS (basis_hd :: basis_tl)) ≠ cons exp coef tl :=
  cons_ne_zero.symm

/-- Neutral element for multiplication. -/
def one (basis : Basis) : PreMS basis :=
  const basis 1

/-- Multiseries representing `basis[n] ^ r`. -/
def monomial_rpow (basis : Basis) (n : ℕ) (r : ℝ) : PreMS basis :=
  match n, basis with
  | 0, [] => default
  | 0, List.cons _ _ => cons r (one _) nil
  | _ + 1, [] => default
  | m + 1, List.cons _ basis_tl => cons 0 (monomial_rpow basis_tl m r) nil

/-- Multiseries representing `basis[n]`. -/
def monomial (basis : Basis) (n : ℕ) : PreMS basis :=
  monomial_rpow basis n 1

/-- Constants are well-ordered. -/
theorem const_WellOrdered {c : ℝ} {basis : Basis} :
    (const basis c).WellOrdered := by
  cases basis with
  | nil => constructor
  | cons basis_hd basis_tl =>
    simp only [const]
    apply WellOrdered.cons
    · exact const_WellOrdered
    · simp [leadingExp, Ne.bot_lt] -- may be `Ne.bot_lt` should be simp lemma?
    · apply WellOrdered.nil

/-- Zero is well-ordered. -/
theorem zero_WellOrdered {basis : Basis} : (0 : PreMS basis).WellOrdered := by
  cases basis with
  | nil => constructor
  | cons => exact WellOrdered.nil

/-- `one` is wellOrdered. -/
theorem one_WellOrdered {basis : Basis} : (one basis).WellOrdered := by
  simp only [one]
  apply const_WellOrdered

-- TODO : move it
/-- Constant multiseries approximates constant function. -/
theorem const_Approximates {c : ℝ} {basis : Basis} (h_basis : WellFormedBasis basis) :
    (const basis c).Approximates (fun _ ↦ c) := by
  cases basis with
  | nil => simp [const]
  | cons basis_hd basis_tl =>
    simp only [const]
    have ih : (const basis_tl c).Approximates (fun _ ↦ c) := by
      apply const_Approximates h_basis.tail
    apply Approximates.cons _ ih
    · apply const_majorated
      apply basis_tendsto_top h_basis
      simp
    · apply Approximates.nil
      simp
      rfl

-- TODO : move it
/-- `zero` approximates zero functions. -/
theorem zero_Approximates {basis : Basis} :
    (zero basis).Approximates (fun _ ↦ 0) := by
  cases basis with
  | nil => simp [zero]
  | cons => exact Approximates.nil (by rfl)

theorem zero_Approximates_iff {basis : Basis} {f : ℝ → ℝ} :
    (zero basis).Approximates f ↔ (f =ᶠ[atTop] 0) where
  mp h := by
    cases basis with
    | nil =>
      simpa [zero] using h
    | cons basis_hd basis_tl =>
      simp only [zero] at h
      exact Approximates_nil h
  mpr h := Approximates_of_EventuallyEq h.symm zero_Approximates

/-- `one` approximates unit function. -/
theorem one_Approximates {basis : Basis} (h_wo : WellFormedBasis basis) :
    (one basis).Approximates (fun _ ↦ 1) :=
  const_Approximates h_wo

/-- `monomial` is well-ordered. -/
theorem monomial_rpow_WellOrdered {basis : Basis} {n : ℕ} {r : ℝ} :
    (monomial_rpow basis n r).WellOrdered := by
  cases basis with
  | nil =>
    cases n with
    | zero =>
      constructor
    | succ m =>
      apply zero_WellOrdered
  | cons basis_hd basis_tl =>
    cases n with
    | zero =>
      apply WellOrdered.cons
      · exact const_WellOrdered
      · simp [leadingExp, Ne.bot_lt]
      · exact WellOrdered.nil
    | succ m =>
      apply WellOrdered.cons
      · exact monomial_rpow_WellOrdered
      · simp [leadingExp, Ne.bot_lt]
      · exact WellOrdered.nil

/-- `monomial_rpow` approximates monomial function. -/
theorem monomial_rpow_Approximates {basis : Basis} {n : Fin (List.length basis)} {r : ℝ}
    (h_basis : WellFormedBasis basis) :
    (monomial_rpow basis n r).Approximates (fun x ↦ (basis[n] x)^r) := by
  cases basis with
  | nil => grind
  | cons basis_hd basis_tl =>
    cases n using Fin.cases with
    | zero =>
      apply Approximates.cons (fun _ ↦ 1)
      · exact one_Approximates h_basis.tail
      · apply PreMS.majorated_self
        apply basis_tendsto_top h_basis
        simp
      · simp only [List.length_cons, Fin.getElem_fin, Fin.val_zero, List.getElem_cons_zero,
          mul_one, sub_self]
        apply Approximates.nil
        rfl
    | succ m =>
      apply Approximates.cons
      · exact monomial_rpow_Approximates h_basis.tail
      · apply basis_tail_pow_majorated_head h_basis
        apply List.getElem_mem
      · simp only [List.length_cons, Fin.getElem_fin, Fin.val_succ, List.getElem_cons_succ,
          Real.rpow_zero, one_mul, sub_self]
        apply Approximates.nil
        rfl

/-- `monomial` is well-ordered. -/
theorem monomial_WellOrdered {basis : Basis} {n : ℕ} : (monomial basis n).WellOrdered :=
  monomial_rpow_WellOrdered

/-- `monomial` approximates monomial function. -/
theorem monomial_Approximates {basis : Basis} {n : Fin (List.length basis)}
    (h_basis : WellFormedBasis basis) : (monomial basis n).Approximates basis[n] := by
  cases basis with
  | nil => grind
  | cons basis_hd basis_tl =>
    cases n using Fin.cases with
    | zero =>
      simp only [monomial, List.length_cons, Fin.val_zero, Fin.getElem_fin, List.getElem_cons_zero]
      apply Approximates.cons (fun _ ↦ 1)
      · exact one_Approximates h_basis.tail
      · nth_rw 1 [show basis_hd = fun x ↦ (basis_hd x)^(1 : ℝ) by ext x; simp]
        apply PreMS.majorated_self
        apply basis_tendsto_top h_basis
        simp
      · simp only [Real.rpow_one, mul_one, sub_self]
        apply Approximates.nil
        rfl
    | succ m =>
      simp only [monomial, List.length_cons, Fin.val_succ, Fin.getElem_fin, List.getElem_cons_succ]
      apply Approximates.cons
      · exact monomial_Approximates h_basis.tail
      · apply basis_tail_majorated_head h_basis
        apply List.getElem_mem
      · simp only [Real.rpow_zero, Fin.getElem_fin, one_mul, sub_self]
        apply Approximates.nil
        rfl

section BasisOperations

/-- Extends basis with `f` in the middle. -/
def extendBasisMiddle {left right : Basis} (f : ℝ → ℝ) (ms : PreMS (left ++ right)) :
    PreMS (left ++ f :: right) :=
  match left with
  | [] => cons 0 ms nil
  | List.cons _ _ => ms.map id (fun coef => extendBasisMiddle f coef)

theorem extendBasisMiddle_WellOrdered {left right : Basis} {b : ℝ → ℝ} {ms : PreMS (left ++ right)}
    (h_wo : ms.WellOrdered) : (ms.extendBasisMiddle b).WellOrdered := by
  cases left with
  | nil =>
    simp only [List.nil_append, extendBasisMiddle]
    apply WellOrdered.cons_nil
    assumption
  | cons left_hd left_tl =>
  simp only [List.cons_append, extendBasisMiddle, List.append_eq]
  let motive (ms' : PreMS (left_hd :: left_tl ++ b :: right)) : Prop :=
    ∃ ms : PreMS (left_hd :: left_tl ++ right),
      ms' = ms.map id (fun coef => extendBasisMiddle b coef) ∧
      ms.WellOrdered
  apply WellOrdered.coind motive
  · use ms
  intro exp' coef' tl' ih
  simp only [List.cons_append, List.append_eq, motive] at ih
  obtain ⟨ms, h_eq, h_wo⟩ := ih
  cases ms with
  | nil => simp at h_eq
  | cons exp coef tl =>
  obtain ⟨h_coef, h_comp, h_tl⟩ := WellOrdered_cons h_wo
  simp at h_eq
  constructor
  · simp [h_eq]
    exact extendBasisMiddle_WellOrdered h_coef
  constructor
  · cases tl with
    | nil =>
      simp [h_eq]
    | cons tl_exp tl_coef tl_tl =>
      simpa [h_eq] using h_comp
  simp only [List.cons_append, motive]
  use tl
  simpa [h_eq]

theorem extendBasisMiddle_Approximates {left right : Basis} {f b : ℝ → ℝ}
    {ms : PreMS (left ++ right)}
    (h_basis : WellFormedBasis (left ++ b :: right))
    (h_approx : ms.Approximates f) : (ms.extendBasisMiddle b).Approximates f := by
  cases left with
  | nil =>
    simp only [List.nil_append, extendBasisMiddle]
    apply Approximates.cons _ h_approx
    · exact PreMS.Approximates_coef_majorated_head h_approx h_basis
    · apply Approximates.nil
      simp only [Real.rpow_zero, one_mul, sub_self]
      rfl
  | cons left_hd left_tl =>
  simp only [List.cons_append, extendBasisMiddle, List.append_eq]
  let motive (ms' : PreMS (left_hd :: left_tl ++ b :: right)) (f' : ℝ → ℝ) : Prop :=
    ∃ ms : PreMS (left_hd :: left_tl ++ right),
      ms' = ms.map id (fun coef => extendBasisMiddle b coef) ∧
      ms.Approximates f'
  apply Approximates.coind motive
  · use ms
  intro ms' f' ih
  simp only [List.cons_append, motive] at ih
  obtain ⟨ms, h_eq, h_approx⟩ := ih
  subst h_eq
  cases ms with
  | nil => simpa using Approximates_nil h_approx
  | cons exp coef tl =>
  right
  obtain ⟨fC, h_coef, h_majorated, h_tl⟩ := Approximates_cons h_approx
  simp
  use fC
  constructor
  · exact extendBasisMiddle_Approximates h_basis.tail h_coef
  constructor
  · exact h_majorated
  simp only [List.cons_append, motive]
  use tl

/-- Extends basis with `f` at right end. -/
-- TODO: it's just extendMiddle with right = [].
def extendBasisEnd {basis : Basis} (f : ℝ → ℝ) (ms : PreMS basis) : PreMS (basis ++ [f]) :=
  match basis with
  | [] => const [f] ms
  | List.cons _ _ => ms.map id (fun coef => extendBasisEnd f coef)

theorem extendBasisEnd_WellOrdered {basis : Basis} {b : ℝ → ℝ} {ms : PreMS basis}
    (h_wo : ms.WellOrdered) : (ms.extendBasisEnd b).WellOrdered := by
  cases basis with
  | nil => simpa [extendBasisEnd] using const_WellOrdered
  | cons basis_hd basis_tl =>
  simp only [List.cons_append, extendBasisEnd, List.append_eq]
  let motive (ms' : PreMS (basis_hd :: basis_tl ++ [b])) : Prop :=
    ∃ ms : PreMS (basis_hd :: basis_tl),
      ms' = ms.map id (fun coef => extendBasisEnd b coef) ∧
      ms.WellOrdered
  apply WellOrdered.coind motive
  · use ms
  intro exp' coef' tl' ih
  simp only [List.cons_append, List.append_eq, motive] at ih
  obtain ⟨ms, h_eq, h_wo⟩ := ih
  cases ms with
  | nil => simp at h_eq
  | cons exp coef tl =>
  simp at h_eq
  simp [h_eq]
  obtain ⟨h_coef, h_comp, h_tl⟩ := WellOrdered_cons h_wo
  constructor
  · exact extendBasisEnd_WellOrdered h_coef
  constructor
  · cases tl
    · simp
    · simpa using h_comp
  simp only [List.cons_append, motive]
  use tl

theorem extendBasisEnd_Approximates {basis : Basis} {f b : ℝ → ℝ} {ms : PreMS basis}
    (h_basis : WellFormedBasis (basis ++ [b]))
    (h_approx : ms.Approximates f) : (ms.extendBasisEnd b).Approximates f := by
  cases basis with
  | nil =>
    simp only [List.nil_append, extendBasisEnd]
    apply Approximates_of_EventuallyEq (Approximates_const_iff.mp h_approx).symm
    exact const_Approximates h_basis
  | cons basis_hd basis_tl =>
  simp only [List.cons_append, extendBasisEnd, List.append_eq]
  let motive (ms' : PreMS (basis_hd :: basis_tl ++ [b])) (f' : ℝ → ℝ) : Prop :=
    ∃ ms : PreMS (basis_hd :: basis_tl),
      ms' = ms.map id (fun coef => extendBasisEnd b coef) ∧
      ms.Approximates f'
  apply Approximates.coind motive
  · use ms
  intro ms' f' ih
  simp only [List.cons_append, motive] at ih
  obtain ⟨ms, h_eq, h_approx⟩ := ih
  subst h_eq
  cases ms with
  | nil => simpa using Approximates_nil h_approx
  | cons exp coef tl =>
  right
  obtain ⟨fC, h_coef, h_majorated, h_tl⟩ := Approximates_cons h_approx
  simp
  use fC
  constructor
  · exact extendBasisEnd_Approximates h_basis.tail h_coef
  constructor
  · exact h_majorated
  simp only [List.cons_append, motive]
  use tl

/-- Given a basis extension `ex`, and a multiseries `ms`, immerses `ms` into the
basis `ex.getBasis`. -/
def updateBasis {basis : Basis} (ex : BasisExtension basis) (ms : PreMS basis) :
    PreMS ex.getBasis :=
  match ex with
  | .nil => ms
  | .keep basis_hd ex_tl => ms.map id (fun coef => updateBasis ex_tl coef)
  | .insert _ ex_tl => cons 0 (ms.updateBasis ex_tl) nil

theorem updateBasis_WellOrdered {basis : Basis} {ex : BasisExtension basis} {ms : PreMS basis}
    (h_wo : ms.WellOrdered) :
    (ms.updateBasis ex).WellOrdered := by
  cases ex with
  | nil => simpa [updateBasis]
  | insert f ex_tl =>
    simp only [updateBasis]
    apply WellOrdered.cons_nil
    exact updateBasis_WellOrdered h_wo
  | keep basis_hd ex_tl =>
    simp only [updateBasis]
    let motive (ms' : PreMS (BasisExtension.keep basis_hd ex_tl).getBasis) : Prop :=
      ∃ ms : PreMS (basis_hd :: _),
        ms' = ms.map id (fun coef => updateBasis ex_tl coef) ∧
        ms.WellOrdered
    apply WellOrdered.coind motive
    · use ms
    intro exp' coef' tl' ih
    simp only [motive] at ih
    obtain ⟨ms, h_eq, h_wo⟩ := ih
    cases ms with
    | nil => simp [BasisExtension.getBasis] at h_eq
    | cons exp coef tl =>
    obtain ⟨h_coef, h_comp, h_tl⟩ := WellOrdered_cons h_wo
    simp [BasisExtension.getBasis] at h_eq
    constructor
    · simp [h_eq]
      exact updateBasis_WellOrdered h_coef
    constructor
    · cases tl
      · simp [h_eq]
      · simpa [h_eq] using h_comp
    simp only [motive]
    use tl
    grind

theorem updateBasis_Approximates {basis : Basis} {ex : BasisExtension basis} {ms : PreMS basis}
    {f : ℝ → ℝ}
    (h_basis : WellFormedBasis ex.getBasis)
    (h_wo : ms.WellOrdered)
    (h_approx : ms.Approximates f) :
    (ms.updateBasis ex).Approximates f := by
  cases ex with
  | nil => simpa [updateBasis] using h_approx
  | keep basis_hd ex_tl =>
    simp only [updateBasis]
    let motive (ms' : PreMS (BasisExtension.keep basis_hd ex_tl).getBasis) (f' : ℝ → ℝ) : Prop :=
      ∃ ms : PreMS (basis_hd :: _),
        ms' = ms.map id (fun coef => updateBasis ex_tl coef) ∧
        ms.WellOrdered ∧
        ms.Approximates f'
    apply Approximates.coind motive
    · use ms
    intro f' ms' ih
    simp only [motive] at ih
    obtain ⟨ms, h_eq, h_wo, h_approx⟩ := ih
    subst h_eq
    cases ms with
    | nil => simpa using Approximates_nil h_approx
    | cons exp coef tl =>
    right
    obtain ⟨fC, h_coef, h_majorated, h_tl⟩ := Approximates_cons h_approx
    obtain ⟨h_coef_wo, h_coef_comp, h_coef_approx⟩ := WellOrdered_cons h_wo
    simp
    use fC
    constructor
    · exact updateBasis_Approximates h_basis.tail h_coef_wo h_coef
    constructor
    · exact h_majorated
    simp only [motive]
    use tl
  | insert g ex_tl =>
    simp only [updateBasis]
    apply Approximates.cons f
    · apply updateBasis_Approximates _ h_wo h_approx
      exact BasisExtension.insert_WellFormedBasis_tail h_basis
    · refine PreMS.Approximates_coef_majorated_head
        (updateBasis_Approximates ?_ h_wo h_approx) h_basis
      exact BasisExtension.insert_WellFormedBasis_tail h_basis
    · apply Approximates.nil
      simp
      rfl

end BasisOperations

end PreMS

end ComputeAsymptotics
