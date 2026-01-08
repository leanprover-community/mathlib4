/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Tactic.ComputeAsymptotics.Multiseries.Basic
public import Mathlib.Tactic.ComputeAsymptotics.Multiseries.Basis
public import Mathlib.Tactic.ComputeAsymptotics.Multiseries.LeadingTerm

/-!
# Basic operations for multiseries: multiplication by constant and negation

-/

@[expose] public section

namespace ComputeAsymptotics

namespace PreMS

/-- Multiplies all coefficient of the multiseries to `c`. -/
def mulConst {basis : Basis} (c : ℝ) (ms : PreMS basis) : PreMS basis :=
  match basis with
  | [] => ofReal (c * ms.toReal)
  | List.cons _ _ =>
    mk (ms.seq.map (fun (exp, coef) => (exp, coef.mulConst c))) (c • ms.toFun)

/-- Negates all coefficient of the multiseries. -/
def neg {basis : Basis} (ms : PreMS basis) : PreMS basis :=
  ms.mulConst (-1)

/-- This instance is needed to create instance for `AddCommMonoid (PreMS basis)`, which is
necessary for using `abel` tactic in our proofs. -/
instance instNeg {basis : Basis} : Neg (PreMS basis) where
  neg := neg

-------------------- theorems

open Filter Asymptotics Stream'

@[simp]
theorem mulConst_toFun {basis : Basis} {ms : PreMS basis} {c : ℝ} :
    (ms.mulConst c).toFun = c • ms.toFun := by
  cases basis with
  | nil => rfl
  | cons => rfl

@[simp]
theorem mulConst_replaceFun_seq {basis_hd basis_tl} {c : ℝ}
    {ms : PreMS (basis_hd :: basis_tl)} {f : ℝ → ℝ} :
    (ms.replaceFun f).mulConst c = (ms.mulConst c).replaceFun (c • f) := by
  rfl

@[simp]
theorem mulConst_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {c : ℝ} {f : ℝ → ℝ} :
  @mulConst (basis_hd :: basis_tl) c (mk .nil f) = mk .nil (c • f) := by
  simp [mulConst]

@[simp]
theorem mulConst_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {c exp : ℝ}
    {coef : PreMS basis_tl} {tl : Seq (ℝ × PreMS basis_tl)} {f : ℝ → ℝ} :
    (mk (.cons (exp, coef) tl) f).mulConst c =
    mk (basis_hd := basis_hd) (.cons (exp, coef.mulConst c)
      ((mk (basis_hd := basis_hd) tl 0).mulConst c).seq) (c • f) := by
  simp [mulConst]

@[simp]
theorem mulConst_leadingExp {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {ms : PreMS (basis_hd :: basis_tl)} {c : ℝ} :
    Seq.leadingExp (ms.mulConst c).seq = ms.leadingExp := by
  cases ms <;> simp [mulConst]

@[simp]
theorem const_mulConst {basis : Basis} {x y : ℝ} :
    (const basis x).mulConst y = const basis (y * x) := by
  cases basis with
  | nil => simp [mulConst, const]
  | cons =>
    simp [mulConst, const, Seq.map_cons, Seq.map_nil, const_mulConst]
    rfl

@[simp]
theorem mulConst_one {basis : Basis} {ms : PreMS basis} : ms.mulConst 1 = ms := by
  cases basis with
  | nil => simp [mulConst]
  | cons basis_hd basis_tl =>
    simp [mulConst]
    symm
    convert Seq.map_id _
    apply mulConst_one

@[simp]
theorem mulConst_mulConst {basis : Basis} {ms : PreMS basis} {x y : ℝ} :
    (ms.mulConst x).mulConst y = ms.mulConst (x * y) := by
  cases basis with
  | nil => simp [mulConst, ofReal, toReal]; ring_nf
  | cons =>
    simp [mulConst, ← Seq.map_comp]
    constructor
    · congr 1
      ext1
      simp [mulConst_mulConst]
    · ext
      simp
      ring_nf

/-- Multiplication by constant preserves well-orderedness. -/
theorem mulConst_WellOrdered {basis : Basis} {ms : PreMS basis} {c : ℝ}
    (h_wo : ms.WellOrdered) : (ms.mulConst c).WellOrdered := by
  cases basis with
  | nil => constructor
  | cons basis_hd basis_tl =>
    simp at h_wo ⊢
    let motive (s : Seq (ℝ × PreMS basis_tl)) : Prop :=
      ∃ (X : PreMS (basis_hd :: basis_tl)), s = (X.mulConst c).seq ∧ Seq.WellOrdered X.seq
    apply Seq.WellOrdered.coind motive
    · simp only [motive]
      use ms
    · rintro exp' coef' tl' ⟨X, h_ms_eq, hX_wo⟩
      cases X with
      | nil => simp at h_ms_eq
      | cons exp coef tl f =>
        obtain ⟨hX_coef_wo, hX_comp, hX_tl_wo⟩ := WellOrdered_cons hX_wo
        simp at h_ms_eq
        constructor
        · simp only [h_ms_eq]
          exact mulConst_WellOrdered hX_coef_wo
        constructor
        · simpa [h_ms_eq]
        use mk tl 0
        simpa [h_ms_eq]

/-- If `ms` approximates `f`, then `ms.mulConst c` approximates `f * c`. -/
theorem mulConst_Approximates {basis : Basis} {ms : PreMS basis} {c : ℝ}
    (h_approx : ms.Approximates) :
    (ms.mulConst c).Approximates := by
  cases basis with
  | nil => simp
  | cons basis_hd basis_tl =>
    let motive (ms : PreMS (basis_hd :: basis_tl)) : Prop :=
      ∃ (X : PreMS (basis_hd :: basis_tl)),
        ms = X.mulConst c ∧ ms.toFun = c • X.toFun ∧
        X.Approximates
    apply Approximates.coind motive
    · simp only [motive]
      use ms
      simp [h_approx]
    · rintro ms ⟨X, rfl, hf_eq, hX_approx⟩
      cases X with
      | nil =>
        left
        apply Approximates_nil at hX_approx
        simp
        grw [hX_approx]
        simp
      | cons X_exp X_coef X_tl fX =>
        obtain ⟨hX_coef, hX_maj, hX_tl⟩ := Approximates_cons hX_approx
        right
        simp [mulConst_Approximates hX_coef, smul_majorated hX_maj]
        use (mk X_tl (fX - basis_hd ^ X_exp * X_coef.toFun))
        simp [mulConst, hX_tl]
        ext t
        simp
        ring

-- /-- If `ms` approximates `f`, then `ms.mulConst c` approximates `f * c`. -/
-- theorem mulConst_Approximates' {basis : Basis} {ms : PreMS basis} {c : ℝ} {f : ℝ → ℝ}
--     (h_approx : ms.Approximates f) :
--     (ms.mulConst c).Approximates (fun t ↦ f t * c) := by
--   cases basis with
--   | nil =>
--     simp only [Approximates_const_iff] at *
--     apply EventuallyEq.mul h_approx
--     rfl
--   | cons basis_hd basis_tl =>
--     let motive (ms' : PreMS (basis_hd :: basis_tl)) (f : ℝ → ℝ) : Prop :=
--       ∃ (X : PreMS (basis_hd :: basis_tl)) (fX : ℝ → ℝ),
--         ms' = X.mulConst c ∧ f =ᶠ[atTop] (fun t ↦ fX t * c) ∧
--         X.Approximates fX
--     apply Approximates.coind motive
--     · simp only [motive]
--       use ms, f
--     · intro ms f ih
--       simp only [motive] at ih
--       obtain ⟨X, fX, h_ms_eq, hf_eq, hX_approx⟩ := ih
--       cases X with
--       | nil =>
--         left
--         apply Approximates_nil at hX_approx
--         simp only [mulConst, map_nil] at h_ms_eq
--         constructor
--         · exact h_ms_eq
--         trans
--         · exact hf_eq
--         conv =>
--           rhs
--           ext
--           rw [Pi.zero_apply, ← zero_mul c]
--         apply EventuallyEq.mul hX_approx
--         rfl
--       | cons X_exp X_coef X_tl =>
--         obtain ⟨fXC, hX_coef, hX_maj, hX_tl⟩ := Approximates_cons hX_approx
--         right
--         simp only [mulConst, map_cons] at h_ms_eq
--         use ?_, ?_, ?_, fun t ↦ fXC t * c
--         constructor
--         · exact h_ms_eq
--         constructor
--         · exact mulConst_Approximates' hX_coef
--         constructor
--         · apply majorated_of_EventuallyEq hf_eq
--           exact mul_const_majorated hX_maj
--         simp only [motive]
--         use X_tl, fun t ↦ fX t - basis_hd t ^ X_exp * fXC t
--         constructor
--         · rfl
--         constructor
--         · apply eventuallyEq_iff_sub.mpr
--           eta_expand
--           simp only [Pi.sub_apply, Pi.zero_apply]
--           ring_nf!
--           apply eventuallyEq_iff_sub.mp
--           conv_rhs => ext; rw [mul_comm]
--           exact hf_eq
--         · exact hX_tl

theorem mulConst_not_zero {basis : Basis} {ms : PreMS basis} {c : ℝ} (h_ne_zero : ¬ IsZero ms)
    (hc : c ≠ 0) : ¬ IsZero (ms.mulConst c) := by
  contrapose! h_ne_zero
  generalize h_ms' : ms.mulConst c = ms' at h_ne_zero
  cases h_ne_zero with
  | const hc =>
    simp_all [mulConst, ofReal, toReal]
    grind
  | nil f =>
    cases ms
    · simp
    · simp at h_ms'

theorem mulConst_Trimmed {basis : Basis} {ms : PreMS basis} {c : ℝ} (h_trimmed : ms.Trimmed)
    (hc : c ≠ 0) :
    (ms.mulConst c).Trimmed := by
  cases basis with
  | nil => constructor
  | cons basis_hd basis_tl =>
    cases ms with
    | nil => constructor
    | cons exp coef tl =>
    simp only [mulConst_cons]
    apply Trimmed_cons at h_trimmed
    constructor
    · exact mulConst_Trimmed h_trimmed.left hc
    · exact mulConst_not_zero h_trimmed.right hc

theorem mulConst_leadingTerm {basis : Basis} {ms : PreMS basis} {c : ℝ} :
    (ms.mulConst c).leadingTerm = ⟨ms.leadingTerm.coef * c, ms.leadingTerm.exps⟩ := by
  cases basis with
  | nil =>
    simp [mulConst, leadingTerm]
    ring
  | cons basis_hd basis_tl =>
    cases ms
    · simp [leadingTerm]
    · simp [leadingTerm, mulConst_leadingTerm]

@[simp]
theorem neg_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {f : ℝ → ℝ} :
    neg (basis := basis_hd :: basis_tl) (mk .nil f) = mk .nil (-f) := by
  simp [neg]

@[simp]
theorem neg_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {exp : ℝ}
    {coef : PreMS basis_tl} {tl : Seq (ℝ × PreMS basis_tl)} {f : ℝ → ℝ} :
    (mk (basis_hd := basis_hd) (.cons (exp, coef) tl) f).neg =
    mk (.cons (exp, coef.neg) ((mk (basis_hd := basis_hd) tl 0).neg).seq) (-f) := by
  simp [neg]

@[simp]
theorem neg_leadingExp {basis_hd : ℝ → ℝ} {basis_tl : Basis} {X : PreMS (basis_hd :: basis_tl)} :
    X.neg.leadingExp = X.leadingExp := by
  simp [neg]

@[simp]
theorem neg_neg {basis : Basis} {ms : PreMS basis} : ms.neg.neg = ms := by
  cases basis <;> simp [neg]

theorem neg_WellOrdered {basis : Basis} {ms : PreMS basis}
    (h_wo : ms.WellOrdered) : ms.neg.WellOrdered :=
  mulConst_WellOrdered h_wo

theorem neg_Approximates {basis : Basis} {ms : PreMS basis}
    (h_approx : ms.Approximates) : ms.neg.Approximates :=
  mulConst_Approximates h_approx

theorem neg_Trimmed {basis : Basis} {ms : PreMS basis} (h_trimmed : ms.Trimmed) :
    ms.neg.Trimmed :=
  mulConst_Trimmed h_trimmed (by simp)

theorem neg_leadingTerm {basis : Basis} {ms : PreMS basis} :
    ms.neg.leadingTerm = ⟨-ms.leadingTerm.coef, ms.leadingTerm.exps⟩ := by
  simp [neg, mulConst_leadingTerm]

end PreMS

end ComputeAsymptotics
