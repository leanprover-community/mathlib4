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

open Filter Stream'

lemma nil_tendsto_zero {basis_hd : ℝ → ℝ} {basis_tl : Basis} {f : ℝ → ℝ}
    (h : PreMS.Approximates (basis := basis_hd :: basis_tl) (mk .nil f)) : Tendsto f atTop (nhds 0) := by
  apply PreMS.Approximates_nil at h
  exact h.tendsto

instance (basis : Basis) : Inhabited (PreMS basis) :=
  match basis with
  | [] => ⟨(default : ℝ)⟩
  | List.cons _ _ => ⟨(default : Seq (ℝ × PreMS _) × (ℝ → ℝ))⟩

/-- Multiseries representing constant. -/
def const (basis : Basis) (c : ℝ) : PreMS basis :=
  match basis with
  | [] => ofReal c
  | List.cons _ _ => mk (.cons (0, const _ c) .nil) (fun _ ↦ c)

@[simp]
theorem const_toFun' {basis : Basis} (c : ℝ) : (const basis c).toFun = fun _ ↦ c := by
  match basis with
  | [] => rfl
  | List.cons _ _ => rfl

/-- Neutral element for addition. It is `0 : ℝ` for empty basis and `[]` otherwise. -/
def zero {basis : Basis} : PreMS basis :=
  match basis with
  | [] => ofReal 0
  | List.cons _ _ => mk .nil (fun _ ↦ 0)

@[simp]
theorem zero_toFun {basis : Basis} : (@zero basis).toFun = 0 := by
  match basis with
  | [] => rfl
  | List.cons _ _ => rfl

/-- This instance is needed to create instance for `AddCommMonoid (PreMS basis)`, which is
necessary for using `abel` tactic in our proofs. -/
instance instZero {basis : Basis} : Zero (PreMS basis) where
  zero := zero

theorem zero_def {basis_hd basis_tl} : (0 : PreMS (basis_hd :: basis_tl)) = mk .nil (fun _ ↦ 0) :=
  rfl

@[simp]
theorem cons_ne_zero {basis_hd : ℝ → ℝ} {basis_tl : Basis} {exp : ℝ} {coef : PreMS basis_tl}
    {tl : Seq (ℝ × PreMS basis_tl)} {f : ℝ → ℝ} :
    mk (basis_hd := basis_hd) (.cons (exp, coef) tl) f ≠ 0 := by
  simp [zero_def]

@[simp]
theorem zero_ne_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {exp : ℝ} {coef : PreMS basis_tl}
    {tl : Seq (ℝ × PreMS basis_tl)} {f : ℝ → ℝ} :
    0 ≠ mk (basis_hd := basis_hd) (.cons (exp, coef) tl) f :=
  cons_ne_zero.symm

/-- Neutral element for multiplication. -/
def one {basis : Basis} : PreMS basis :=
  const basis 1

@[simp]
theorem one_toFun {basis : Basis} : (@one basis).toFun = 1 := by
  simp [one]
  rfl

/-- Multiseries representing `basis[n] ^ r`. -/
noncomputable def monomial_rpow {basis : Basis} (n : ℕ) (r : ℝ) : PreMS basis :=
  match n, basis with
  -- | 0, [] => default
  | 0, List.cons basis_hd _ => mk (.cons (r, one) .nil) (basis_hd ^ r)
  -- | _ + 1, [] => default
  | m + 1, List.cons _ basis_tl => mk (.cons (0, monomial_rpow m r) .nil) (basis_tl[m]! ^ r)
  | _, _ => default

/-- Multiseries representing `basis[n]`. -/
noncomputable def monomial {basis : Basis} (n : ℕ) : PreMS basis :=
  monomial_rpow n 1

/-- Constants are well-ordered. -/
theorem const_WellOrdered {basis : Basis} {c : ℝ} :
    (const basis c).WellOrdered := by
  cases basis with
  | nil => constructor
  | cons basis_hd basis_tl =>
    simp only [const]
    apply WellOrdered.cons_nil
    exact const_WellOrdered

/-- Zero is well-ordered. -/
theorem zero_WellOrdered {basis : Basis} : (0 : PreMS basis).WellOrdered := by
  cases basis with
  | nil => constructor
  | cons => apply WellOrdered.nil

/-- `one` is wellOrdered. -/
theorem one_WellOrdered {basis : Basis} : one.WellOrdered (basis := basis) := by
  simp only [one]
  apply const_WellOrdered

-- TODO: move it
@[simp]
theorem real_real_rpow_zero (f : ℝ → ℝ) : f ^ (0 : ℝ) = 1 := by ext; simp

-- TODO : move it
/-- Constant multiseries approximates constant function. -/
theorem const_Approximates {c : ℝ} {basis : Basis} (h_basis : WellFormedBasis basis) :
    (const basis c).Approximates := by
  cases basis with
  | nil => simp
  | cons basis_hd basis_tl =>
    simp only [const]
    have ih : (const basis_tl c).Approximates := by
      apply const_Approximates h_basis.tail
    apply Approximates.cons ih
    · apply const_majorated
      apply basis_tendsto_top h_basis
      simp
    · simp

-- TODO : move it
/-- `zero` approximates zero functions. -/
theorem zero_Approximates {basis : Basis} :
    (@zero basis).Approximates := by
  cases basis with
  | nil => simp [zero]
  | cons => exact Approximates.nil (by rfl)

-- theorem zero_Approximates_iff {basis : Basis} {f : ℝ → ℝ} :
--     (@zero basis).Approximates f ↔ (f =ᶠ[atTop] 0) where
--   mp h := by
--     cases basis with
--     | nil =>
--       simpa [zero] using h
--     | cons basis_hd basis_tl =>
--       simp only [zero] at h
--       exact Approximates_nil h
--   mpr h := Approximates_of_EventuallyEq h.symm zero_Approximates

/-- `one` approximates unit function. -/
theorem one_Approximates {basis : Basis} (h_basis : WellFormedBasis basis) :
    (@one basis).Approximates :=
  const_Approximates h_basis

/-- `monomial` is well-ordered. -/
theorem monomial_rpow_WellOrdered {basis : Basis} {n : ℕ} {r : ℝ} :
    (@monomial_rpow basis n r).WellOrdered := by
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
      apply WellOrdered.cons_nil
      exact const_WellOrdered
    | succ m =>
      apply WellOrdered.cons_nil
      exact monomial_rpow_WellOrdered

@[simp]
theorem monomial_rpow_toFun {basis : Basis} {n : Fin (List.length basis)} {r : ℝ} :
    (@monomial_rpow basis n r).toFun = basis[n] ^ r := by
  cases basis with
  | nil => grind
  | cons basis_hd basis_tl => cases n using Fin.cases <;> simp [monomial_rpow]

/-- `monomial_rpow` approximates monomial function. -/
theorem monomial_rpow_Approximates {basis : Basis} {n : Fin (List.length basis)} {r : ℝ}
    (h_basis : WellFormedBasis basis) :
    (@monomial_rpow basis n r).Approximates := by
  cases basis with
  | nil => grind
  | cons basis_hd basis_tl =>
    cases n using Fin.cases with
    | zero =>
      apply Approximates.cons
      · exact one_Approximates h_basis.tail
      · apply PreMS.majorated_self
        apply basis_tendsto_top h_basis
        simp
      · simp
    | succ m =>
      apply Approximates.cons
      · exact monomial_rpow_Approximates h_basis.tail
      · apply basis_tail_pow_majorated_head h_basis
        simp
      · simp

/-- `monomial` is well-ordered. -/
theorem monomial_WellOrdered {basis : Basis} {n : ℕ} : (@monomial basis n).WellOrdered :=
  monomial_rpow_WellOrdered

/-- `monomial` approximates monomial function. -/
theorem monomial_Approximates {basis : Basis} {n : Fin (List.length basis)}
    (h_basis : WellFormedBasis basis) : (@monomial basis n).Approximates :=
  monomial_rpow_Approximates h_basis

section BasisOperations

-- /-- Extends basis with `f` in the middle. -/
-- def extendBasisMiddle {left right : Basis} (f : ℝ → ℝ) (ms : PreMS (left ++ right)) :
--     PreMS (left ++ f :: right) :=
--   match left with
--   | [] => cons 0 ms nil
--   | List.cons _ _ => ms.map id (fun coef => extendBasisMiddle f coef)

-- theorem extendBasisMiddle_WellOrdered {left right : Basis} {b : ℝ → ℝ} {ms : PreMS (left ++ right)}
--     (h_wo : ms.WellOrdered) : (ms.extendBasisMiddle b).WellOrdered := by
--   cases left with
--   | nil =>
--     simp only [List.nil_append, extendBasisMiddle]
--     apply WellOrdered.cons_nil
--     assumption
--   | cons left_hd left_tl =>
--   simp only [List.cons_append, extendBasisMiddle, List.append_eq]
--   let motive (ms' : PreMS (left_hd :: left_tl ++ b :: right)) : Prop :=
--     ∃ ms : PreMS (left_hd :: left_tl ++ right),
--       ms' = ms.map id (fun coef => extendBasisMiddle b coef) ∧
--       ms.WellOrdered
--   apply WellOrdered.coind motive
--   · use ms
--   intro exp' coef' tl' ih
--   simp only [List.cons_append, List.append_eq, motive] at ih
--   obtain ⟨ms, h_eq, h_wo⟩ := ih
--   cases ms with
--   | nil => simp at h_eq
--   | cons exp coef tl =>
--   obtain ⟨h_coef, h_comp, h_tl⟩ := WellOrdered_cons h_wo
--   simp only [map_cons, id_eq, cons_eq_cons] at h_eq
--   constructor
--   · simp only [List.append_eq, h_eq]
--     exact extendBasisMiddle_WellOrdered h_coef
--   constructor
--   · cases tl with
--     | nil =>
--       simp [h_eq]
--     | cons tl_exp tl_coef tl_tl =>
--       simpa [h_eq] using h_comp
--   simp only [List.cons_append, motive]
--   use tl
--   simpa [h_eq]

-- theorem extendBasisMiddle_Approximates {left right : Basis} {f b : ℝ → ℝ}
--     {ms : PreMS (left ++ right)}
--     (h_basis : WellFormedBasis (left ++ b :: right))
--     (h_approx : ms.Approximates f) : (ms.extendBasisMiddle b).Approximates f := by
--   cases left with
--   | nil =>
--     simp only [List.nil_append, extendBasisMiddle]
--     apply Approximates.cons _ h_approx
--     · exact PreMS.Approximates_coef_majorated_head h_approx h_basis
--     · apply Approximates.nil
--       simp only [Real.rpow_zero, one_mul, sub_self]
--       rfl
--   | cons left_hd left_tl =>
--   simp only [List.cons_append, extendBasisMiddle, List.append_eq]
--   let motive (ms' : PreMS (left_hd :: left_tl ++ b :: right)) (f' : ℝ → ℝ) : Prop :=
--     ∃ ms : PreMS (left_hd :: left_tl ++ right),
--       ms' = ms.map id (fun coef => extendBasisMiddle b coef) ∧
--       ms.Approximates f'
--   apply Approximates.coind motive
--   · use ms
--   intro ms' f' ih
--   simp only [List.cons_append, motive] at ih
--   obtain ⟨ms, h_eq, h_approx⟩ := ih
--   subst h_eq
--   cases ms with
--   | nil => simpa using Approximates_nil h_approx
--   | cons exp coef tl =>
--   right
--   obtain ⟨fC, h_coef, h_majorated, h_tl⟩ := Approximates_cons h_approx
--   simp only [List.append_eq, map_cons, id_eq, cons_eq_cons, exists_and_left, ↓existsAndEq, and_true,
--     exists_eq_left']
--   use fC
--   constructor
--   · exact extendBasisMiddle_Approximates h_basis.tail h_coef
--   constructor
--   · exact h_majorated
--   simp only [List.cons_append, motive]
--   use tl

-- /-- Extends basis with `f` at right end. -/
-- -- TODO: it's just extendMiddle with right = [].
-- def extendBasisEnd {basis : Basis} (f : ℝ → ℝ) (ms : PreMS basis) : PreMS (basis ++ [f]) :=
--   match basis with
--   | [] => const [f] ms
--   | List.cons _ _ => ms.map id (fun coef => extendBasisEnd f coef)

-- theorem extendBasisEnd_WellOrdered {basis : Basis} {b : ℝ → ℝ} {ms : PreMS basis}
--     (h_wo : ms.WellOrdered) : (ms.extendBasisEnd b).WellOrdered := by
--   cases basis with
--   | nil => simpa [extendBasisEnd] using const_WellOrdered
--   | cons basis_hd basis_tl =>
--   simp only [List.cons_append, extendBasisEnd, List.append_eq]
--   let motive (ms' : PreMS (basis_hd :: basis_tl ++ [b])) : Prop :=
--     ∃ ms : PreMS (basis_hd :: basis_tl),
--       ms' = ms.map id (fun coef => extendBasisEnd b coef) ∧
--       ms.WellOrdered
--   apply WellOrdered.coind motive
--   · use ms
--   intro exp' coef' tl' ih
--   simp only [List.cons_append, List.append_eq, motive] at ih
--   obtain ⟨ms, h_eq, h_wo⟩ := ih
--   cases ms with
--   | nil => simp at h_eq
--   | cons exp coef tl =>
--   simp only [map_cons, id_eq, cons_eq_cons] at h_eq
--   simp only [List.append_eq, h_eq]
--   obtain ⟨h_coef, h_comp, h_tl⟩ := WellOrdered_cons h_wo
--   constructor
--   · exact extendBasisEnd_WellOrdered h_coef
--   constructor
--   · cases tl
--     · simp
--     · simpa using h_comp
--   simp only [List.cons_append, motive]
--   use tl

-- theorem extendBasisEnd_Approximates {basis : Basis} {f b : ℝ → ℝ} {ms : PreMS basis}
--     (h_basis : WellFormedBasis (basis ++ [b]))
--     (h_approx : ms.Approximates f) : (ms.extendBasisEnd b).Approximates f := by
--   cases basis with
--   | nil =>
--     simp only [List.nil_append, extendBasisEnd]
--     apply Approximates_of_EventuallyEq (Approximates_const_iff.mp h_approx).symm
--     exact const_Approximates h_basis
--   | cons basis_hd basis_tl =>
--   simp only [List.cons_append, extendBasisEnd, List.append_eq]
--   let motive (ms' : PreMS (basis_hd :: basis_tl ++ [b])) (f' : ℝ → ℝ) : Prop :=
--     ∃ ms : PreMS (basis_hd :: basis_tl),
--       ms' = ms.map id (fun coef => extendBasisEnd b coef) ∧
--       ms.Approximates f'
--   apply Approximates.coind motive
--   · use ms
--   intro ms' f' ih
--   simp only [List.cons_append, motive] at ih
--   obtain ⟨ms, h_eq, h_approx⟩ := ih
--   subst h_eq
--   cases ms with
--   | nil => simpa using Approximates_nil h_approx
--   | cons exp coef tl =>
--   right
--   obtain ⟨fC, h_coef, h_majorated, h_tl⟩ := Approximates_cons h_approx
--   simp only [List.append_eq, map_cons, id_eq, cons_eq_cons, exists_and_left, ↓existsAndEq, and_true,
--     exists_eq_left']
--   use fC
--   constructor
--   · exact extendBasisEnd_Approximates h_basis.tail h_coef
--   constructor
--   · exact h_majorated
--   simp only [List.cons_append, motive]
--   use tl

-- /-- Given a basis extension `ex`, and a multiseries `ms`, immerses `ms` into the
-- basis `ex.getBasis`. -/
-- def updateBasis {basis : Basis} (ex : BasisExtension basis) (ms : PreMS basis) :
--     PreMS ex.getBasis :=
--   match ex with
--   | .nil => ms
--   | .keep basis_hd ex_tl => ms.map id (fun coef => updateBasis ex_tl coef)
--   | .insert _ ex_tl => cons 0 (ms.updateBasis ex_tl) nil

-- theorem updateBasis_WellOrdered {basis : Basis} {ex : BasisExtension basis} {ms : PreMS basis}
--     (h_wo : ms.WellOrdered) :
--     (ms.updateBasis ex).WellOrdered := by
--   cases ex with
--   | nil => simpa [updateBasis]
--   | insert f ex_tl =>
--     simp only [updateBasis]
--     apply WellOrdered.cons_nil
--     exact updateBasis_WellOrdered h_wo
--   | keep basis_hd ex_tl =>
--     simp only [updateBasis]
--     let motive (ms' : PreMS (BasisExtension.keep basis_hd ex_tl).getBasis) : Prop :=
--       ∃ ms : PreMS (basis_hd :: _),
--         ms' = ms.map id (fun coef => updateBasis ex_tl coef) ∧
--         ms.WellOrdered
--     apply WellOrdered.coind motive
--     · use ms
--     intro exp' coef' tl' ih
--     simp only [motive] at ih
--     obtain ⟨ms, h_eq, h_wo⟩ := ih
--     cases ms with
--     | nil => simp [BasisExtension.getBasis] at h_eq
--     | cons exp coef tl =>
--     obtain ⟨h_coef, h_comp, h_tl⟩ := WellOrdered_cons h_wo
--     simp [BasisExtension.getBasis] at h_eq
--     constructor
--     · simp only [h_eq]
--       exact updateBasis_WellOrdered h_coef
--     constructor
--     · cases tl
--       · simp [h_eq]
--       · simpa [h_eq] using h_comp
--     simp only [motive]
--     use tl
--     grind

-- theorem updateBasis_Approximates {basis : Basis} {ex : BasisExtension basis} {ms : PreMS basis}
--     {f : ℝ → ℝ}
--     (h_basis : WellFormedBasis ex.getBasis)
--     (h_wo : ms.WellOrdered)
--     (h_approx : ms.Approximates f) :
--     (ms.updateBasis ex).Approximates f := by
--   cases ex with
--   | nil => simpa [updateBasis] using h_approx
--   | keep basis_hd ex_tl =>
--     simp only [updateBasis]
--     let motive (ms' : PreMS (BasisExtension.keep basis_hd ex_tl).getBasis) (f' : ℝ → ℝ) : Prop :=
--       ∃ ms : PreMS (basis_hd :: _),
--         ms' = ms.map id (fun coef => updateBasis ex_tl coef) ∧
--         ms.WellOrdered ∧
--         ms.Approximates f'
--     apply Approximates.coind motive
--     · use ms
--     intro f' ms' ih
--     simp only [motive] at ih
--     obtain ⟨ms, h_eq, h_wo, h_approx⟩ := ih
--     subst h_eq
--     cases ms with
--     | nil => simpa using Approximates_nil h_approx
--     | cons exp coef tl =>
--     right
--     obtain ⟨fC, h_coef, h_majorated, h_tl⟩ := Approximates_cons h_approx
--     obtain ⟨h_coef_wo, h_coef_comp, h_coef_approx⟩ := WellOrdered_cons h_wo
--     simp only [map_cons, id_eq, cons_eq_cons, exists_and_left, ↓existsAndEq, and_true,
--       exists_eq_left']
--     use fC
--     constructor
--     · exact updateBasis_Approximates h_basis.tail h_coef_wo h_coef
--     constructor
--     · exact h_majorated
--     simp only [motive]
--     use tl
--   | insert g ex_tl =>
--     simp only [updateBasis]
--     apply Approximates.cons f
--     · apply updateBasis_Approximates _ h_wo h_approx
--       exact BasisExtension.insert_WellFormedBasis_tail h_basis
--     · refine PreMS.Approximates_coef_majorated_head
--         (updateBasis_Approximates ?_ h_wo h_approx) h_basis
--       exact BasisExtension.insert_WellFormedBasis_tail h_basis
--     · apply Approximates.nil
--       simp
--       rfl

end BasisOperations

end PreMS

end ComputeAsymptotics
