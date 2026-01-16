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
    mk (ms.seq.map id (fun coef => coef.mulConst c)) (c • ms.toFun)

/-- Negates all coefficient of the multiseries. -/
def neg {basis : Basis} (ms : PreMS basis) : PreMS basis :=
  ms.mulConst (-1)

/-- This instance is needed to create instance for `AddCommMonoid (PreMS basis)`, which is
necessary for using `abel` tactic in our proofs. -/
instance {basis : Basis} : Neg (PreMS basis) where
  neg := neg

def SeqMS.mulConst {basis_hd basis_tl} (c : ℝ) (ms : SeqMS basis_hd basis_tl) :
    SeqMS basis_hd basis_tl :=
  ms.map id (fun coef => coef.mulConst c)

def SeqMS.neg {basis_hd basis_tl} (ms : SeqMS basis_hd basis_tl) : SeqMS basis_hd basis_tl :=
  ms.mulConst (-1)

instance {basis_hd basis_tl} : Neg (SeqMS basis_hd basis_tl) where
  neg := SeqMS.neg

-------------------- theorems

open Filter Asymptotics

@[simp]
theorem mulConst_toFun {basis : Basis} {ms : PreMS basis} {c : ℝ} :
    (ms.mulConst c).toFun = c • ms.toFun := by
  cases basis with
  | nil => rfl
  | cons => rfl

@[simp]
theorem mulConst_seq {basis_hd basis_tl} {ms : PreMS (basis_hd :: basis_tl)} {c : ℝ} :
    (ms.mulConst c).seq = ms.seq.mulConst c :=
  rfl

-- @[simp]
-- theorem mulConst_replaceFun_seq {basis_hd basis_tl} {c : ℝ}
--     {ms : PreMS (basis_hd :: basis_tl)} {f : ℝ → ℝ} :
--     (ms.replaceFun f).mulConst c = (ms.mulConst c).replaceFun (c • f) := by
--   rfl

@[simp]
theorem SeqMS.mulConst_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {c : ℝ} :
  @mulConst basis_hd basis_tl c nil = nil := by
  simp [mulConst]

@[simp]
theorem SeqMS.mulConst_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {c exp : ℝ}
    {coef : PreMS basis_tl} {tl : SeqMS basis_hd basis_tl} :
    (cons exp coef tl).mulConst c =
    cons exp (coef.mulConst c) (tl.mulConst c) := by
  simp [mulConst]

@[simp]
theorem SeqMS.mulConst_leadingExp {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {ms : SeqMS basis_hd basis_tl} {c : ℝ} :
    (ms.mulConst c).leadingExp = ms.leadingExp := by
  cases ms <;> simp [mulConst]

mutual

@[simp]
theorem SeqMS.const_mulConst {basis_hd : ℝ → ℝ} {basis_tl : Basis} {x y : ℝ} :
    (SeqMS.const basis_hd basis_tl x).mulConst y = SeqMS.const _ _ (y * x) := by
  simp [SeqMS.const]
  rw [const_mulConst]

@[simp]
theorem const_mulConst {basis : Basis} {x y : ℝ} :
    (const basis x).mulConst y = const basis (y * x) := by
  cases basis with
  | nil => simp [mulConst, const, ofReal, toReal]
  | cons =>
    rw [ms_eq_ms_iff_mk_eq_mk]
    simp
    refine ⟨?_, rfl⟩
    apply SeqMS.const_mulConst

end

mutual

@[simp]
theorem SeqMS.mulConst_one {basis_hd basis_tl} {ms : SeqMS basis_hd basis_tl} :
    ms.mulConst 1 = ms := by
  simp only [SeqMS.mulConst]
  convert SeqMS.map_id _
  apply mulConst_one

@[simp]
theorem mulConst_one {basis} {ms : PreMS basis} :
    ms.mulConst 1 = ms := by
  cases basis with
  | nil => simp [mulConst, ofReal, toReal]
  | cons =>
    simp [ms_eq_ms_iff_mk_eq_mk]
    rw [SeqMS.mulConst_one]

end

mutual

@[simp]
theorem SeqMS.mulConst_mulConst {basis_hd basis_tl} {ms : SeqMS basis_hd basis_tl} {x y : ℝ} :
    (ms.mulConst x).mulConst y = ms.mulConst (x * y) := by
  simp only [SeqMS.mulConst, ← SeqMS.map_comp, CompTriple.comp_eq]
  congr 1
  ext1
  simp [mulConst_mulConst (basis := basis_tl)]

@[simp]
theorem mulConst_mulConst {basis : Basis} {ms : PreMS basis} {x y : ℝ} :
    (ms.mulConst x).mulConst y = ms.mulConst (x * y) := by
  cases basis with
  | nil =>
    simp [mulConst, ofReal, toReal]
    ring_nf
  | cons =>
    simp [ms_eq_ms_iff_mk_eq_mk]
    constructor
    · rw [SeqMS.mulConst_mulConst]
    · ext1
      simp
      ring_nf

end

mutual

theorem SeqMS.mulConst_WellOrdered {basis_hd basis_tl} {ms : SeqMS basis_hd basis_tl} {c : ℝ}
    (h_wo : ms.WellOrdered) : (ms.mulConst c).WellOrdered := by
  let motive (ms : SeqMS basis_hd basis_tl) : Prop :=
    ∃ (X : SeqMS basis_hd basis_tl), ms = X.mulConst c ∧ X.WellOrdered
  apply SeqMS.WellOrdered.coind motive
  · simp only [motive]
    use ms
  · intro exp' coef' tl' ih
    simp only [motive] at ih
    obtain ⟨X, h_ms_eq, hX_wo⟩ := ih
    cases X with
    | nil => simp at h_ms_eq
    | cons exp coef tl =>
      obtain ⟨hX_coef_wo, hX_comp, hX_tl_wo⟩ := WellOrdered_cons hX_wo
      simp at h_ms_eq
      constructor
      · simp only [h_ms_eq]
        exact mulConst_WellOrdered hX_coef_wo
      constructor
      · simpa [h_ms_eq]
      simp only [motive]
      use tl
      simpa [h_ms_eq]

/-- Multiplication by constant preserves well-orderedness. -/
theorem mulConst_WellOrdered {basis : Basis} {ms : PreMS basis} {c : ℝ}
    (h_wo : ms.WellOrdered) : (ms.mulConst c).WellOrdered := by
  cases basis with
  | nil => constructor
  | cons basis_hd basis_tl =>
    simp
    apply SeqMS.mulConst_WellOrdered
    simpa using h_wo

end

/-- If `ms` approximates `f`, then `ms.mulConst c` approximates `f * c`. -/
theorem mulConst_Approximates {basis : Basis} {ms : PreMS basis} {c : ℝ}
    (h_approx : ms.Approximates) :
    (ms.mulConst c).Approximates:= by
  cases basis with
  | nil => simp
  | cons basis_hd basis_tl =>
  let motive (ms' : PreMS (basis_hd :: basis_tl)) : Prop :=
    ∃ (X : PreMS (basis_hd :: basis_tl)),
      ms' = X.mulConst c ∧ X.Approximates
  apply Approximates.coind motive
  · simp only [motive]
    use ms
  · rintro _ ⟨X, rfl, hX_approx⟩
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
      refine ⟨_, ?_, hX_tl⟩
      simp
      ext t
      simp
      ring

-- theorem mulConst_Approximates' {basis : Basis} {ms : PreMS basis} {c : ℝ} {f : ℝ → ℝ}
--     (h_approx : ms.Approximates) :
--     (ms.mulConst c).Approximates (fun t ↦ f t * c) := by
--   sorry

theorem mulConst_not_zero {basis : Basis} {ms : PreMS basis} {c : ℝ} (h_ne_zero : ¬ IsZero ms)
    (hc : c ≠ 0) : ¬ IsZero (ms.mulConst c) := by
  contrapose! h_ne_zero
  cases basis with
  | nil =>
    simp [mulConst, ofReal, toReal] at h_ne_zero ⊢
    grind
  | cons =>
    cases ms
    · simp
    · simp at h_ne_zero

theorem mulConst_Trimmed {basis : Basis} {ms : PreMS basis} {c : ℝ} (h_trimmed : ms.Trimmed)
    (hc : c ≠ 0) :
    (ms.mulConst c).Trimmed := by
  cases basis with
  | nil => constructor
  | cons basis_hd basis_tl =>
    cases ms with
    | nil => constructor
    | cons exp coef tl =>
    simp [Trimmed_iff_seq_Trimmed] at h_trimmed ⊢
    apply SeqMS.Trimmed_cons at h_trimmed
    apply SeqMS.Trimmed.cons
    · exact mulConst_Trimmed h_trimmed.left hc
    · exact mulConst_not_zero h_trimmed.right hc

theorem mulConst_realCoef {basis : Basis} {ms : PreMS basis} {c : ℝ} :
    (ms.mulConst c).realCoef = c * ms.realCoef := by
  cases basis with
  | nil => simp [mulConst, ofReal, toReal]
  | cons basis_hd basis_tl =>
    cases ms with
    | nil => simp [mulConst, realCoef]
    | cons exp coef tl =>
      simp [mulConst, realCoef]
      rw [mulConst_realCoef]

mutual

@[simp]
theorem SeqMS.mulConst_exps {basis_hd basis_tl} {ms : SeqMS basis_hd basis_tl} {c : ℝ} :
    (ms.mulConst c).exps = ms.exps := by
  cases ms with
  | nil => simp
  | cons exp coef tl =>
  simp [SeqMS.mulConst, SeqMS.exps]
  rw [mulConst_exps]

@[simp]
theorem mulConst_exps {basis : Basis} {ms : PreMS basis} {c : ℝ} :
    (ms.mulConst c).exps = ms.exps := by
  cases basis with
  | nil => simp [mulConst, ofReal, toReal]
  | cons basis_hd basis_tl =>
    simp [exps]
    rw [SeqMS.mulConst_exps]

end

theorem mulConst_leadingTerm {basis : Basis} {ms : PreMS basis} {c : ℝ} :
    (ms.mulConst c).leadingTerm = ⟨c * ms.leadingTerm.coef, ms.leadingTerm.exps⟩ := by
  simp [leadingTerm, mulConst_realCoef, mulConst_exps]

@[simp]
theorem neg_toFun {basis : Basis} {ms : PreMS basis} :
    ms.neg.toFun = -ms.toFun := by
  convert mulConst_toFun
  ext
  simp

@[simp]
theorem neg_seq {basis_hd basis_tl} {ms : PreMS (basis_hd :: basis_tl)} :
    ms.neg.seq = ms.seq.neg :=
  rfl

@[simp]
theorem SeqMS.neg_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} :
    @SeqMS.neg basis_hd basis_tl .nil = .nil := by
  simp [SeqMS.neg]

@[simp]
theorem SeqMS.neg_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {exp : ℝ}
    {coef : PreMS basis_tl} {tl : SeqMS basis_hd basis_tl} :
    (cons exp coef tl).neg =
    cons exp (coef.neg) (tl.neg) := by
  simp [neg]
  rfl

@[simp]
theorem SeqMS.neg_leadingExp {basis_hd : ℝ → ℝ} {basis_tl : Basis} {X : SeqMS basis_hd basis_tl} :
    X.neg.leadingExp = X.leadingExp := by
  simp [neg]

@[simp]
theorem neg_leadingExp {basis_hd : ℝ → ℝ} {basis_tl : Basis} {X : PreMS (basis_hd :: basis_tl)} :
    X.neg.leadingExp = X.leadingExp := by
  simp

@[simp]
theorem SeqMS.neg_neg {basis_hd basis_tl} {ms : SeqMS basis_hd basis_tl} : ms.neg.neg = ms := by
  simp [SeqMS.neg]

@[simp]
theorem neg_neg {basis : Basis} {ms : PreMS basis} : ms.neg.neg = ms := by
  cases basis <;> simp [neg]

theorem SeqMS.neg_WellOrdered {basis_hd basis_tl} {ms : SeqMS basis_hd basis_tl}
    (h_wo : ms.WellOrdered) : ms.neg.WellOrdered :=
  SeqMS.mulConst_WellOrdered h_wo

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
