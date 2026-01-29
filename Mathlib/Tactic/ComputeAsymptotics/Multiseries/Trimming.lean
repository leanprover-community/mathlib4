/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Tactic.ComputeAsymptotics.Multiseries.Basic

/-!
# Trimming of multiseries
-/

@[expose] public section

namespace ComputeAsymptotics

namespace PreMS

open Filter Topology Stream'

/-- A multiseries is zero if it is constant zero or `[]`. -/
inductive IsZero : {basis : Basis} → PreMS basis → Prop
| const {c : PreMS []} (hc : c.toReal = 0) : IsZero c
| nil {basis_hd} {basis_tl} (f) : @IsZero (basis_hd :: basis_tl) (mk .nil f)

@[simp]
theorem const_IsZero_iff {c : PreMS []} : IsZero c ↔ c.toReal = 0 := by
  constructor <;> grind [IsZero]

@[simp]
theorem IsZero_iff_seq_nil {basis_hd basis_tl} {ms : PreMS (basis_hd :: basis_tl)} :
    IsZero ms ↔ ms.seq = .nil where
  mp h := by
    cases h
    rfl
  mpr h := by
    convert IsZero.nil ms.toFun
    simp [h]

-- TODO: move
theorem IsZero_Approximates_zero {basis : Basis} {ms : PreMS basis} (h_zero : IsZero ms)
    (h_approx : ms.Approximates) :
    ms.toFun =ᶠ[atTop] 0 := by
  cases h_zero with
  | const hc =>
    simp [hc]
    rfl
  | nil =>
    simpa using h_approx

theorem cons_not_IsZero {basis_hd} {basis_tl} {exp : ℝ} {coef : PreMS basis_tl}
    {tl : SeqMS basis_hd basis_tl} {f : ℝ → ℝ} :
    ¬ @IsZero (basis_hd :: basis_tl) (mk (.cons exp coef tl) f) := by
  simp

/-- We call multiseries `Trimmed` if it is either constant, `[]` or `cons (exp, coef) tl` where
coef is trimmed and is not zero. Intuitively, when multiseries is trimmed, it guarantees that
leading term of multiseries is main asymptotics of the function, approximated by multiseries. -/
inductive Trimmed : {basis : Basis} → PreMS basis → Prop
| const {c : ℝ} : @Trimmed [] c
| nil {basis_hd} {basis_tl} {f} : @Trimmed (basis_hd :: basis_tl) (mk .nil f)
| cons {basis_hd} {basis_tl} {exp : ℝ} {coef : PreMS basis_tl}
  {tl : SeqMS basis_hd basis_tl} {f : ℝ → ℝ} (h_trimmed : coef.Trimmed)
  (h_ne_zero : ¬ IsZero coef) :
  @Trimmed (basis_hd :: basis_tl) (mk (.cons exp coef tl) f)

/-- We call multiseries `Trimmed` if it is either constant, `[]` or `cons (exp, coef) tl` where
coef is trimmed and is not zero. Intuitively, when multiseries is trimmed, it guarantees that
leading term of multiseries is main asymptotics of the function, approximated by multiseries. -/
def SeqMS.Trimmed {basis_hd : ℝ → ℝ} {basis_tl : Basis} (ms : SeqMS basis_hd basis_tl) : Prop :=
  (mk ms 0).Trimmed

theorem Trimmed_iff_seq_Trimmed {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    (ms : PreMS (basis_hd :: basis_tl)) :
    ms.Trimmed ↔ ms.seq.Trimmed where
  mp h := by
    cases h <;> constructor <;> grind
  mpr h := by
    generalize hs : ms.seq = s at h
    cases h with
    | nil =>
      convert Trimmed.nil (f := ms.toFun)
      simp [hs]
    | cons h_trimmed h_ne_zero =>
      convert Trimmed.cons h_trimmed h_ne_zero (f := ms.toFun)
      · simp only [ms_eq_mk_iff, hs, SeqMS.cons_eq_cons, true_and, and_true]
        exact ⟨rfl, rfl⟩

@[simp]
theorem SeqMS.Trimmed.nil {basis_hd} {basis_tl} : @SeqMS.Trimmed basis_hd basis_tl .nil := by
  constructor

theorem SeqMS.Trimmed.cons {basis_hd} {basis_tl} {exp : ℝ} {coef : PreMS basis_tl}
    {tl : SeqMS basis_hd basis_tl}
    (h_coef : coef.Trimmed) (h_ne_zero : ¬ IsZero coef) :
    SeqMS.Trimmed (cons exp coef tl) := by
  constructor
  · exact h_coef
  · exact h_ne_zero

/-- `cons (exp, coef) tl` means that `coef` is trimmed and is not zero. -/
theorem SeqMS.Trimmed_cons {basis_hd} {basis_tl} {exp : ℝ} {coef : PreMS basis_tl}
    {tl : SeqMS basis_hd basis_tl}
    (h : SeqMS.Trimmed (.cons exp coef tl)) :
    coef.Trimmed ∧ ¬ IsZero coef := by
  generalize h_ms : SeqMS.cons exp coef tl = ms at h
  cases h with
  | nil => simp at h_ms
  | cons h_trimmed h_ne_zero =>
    simp at h_ms
    grind

/-- `cons (exp, coef) tl` means that `coef` is trimmed and is not zero. -/
theorem Trimmed_cons {basis_hd} {basis_tl} {exp : ℝ} {coef : PreMS basis_tl}
    {tl : SeqMS basis_hd basis_tl} {f : ℝ → ℝ}
    (h : Trimmed (mk (.cons exp coef tl) f)) :
    coef.Trimmed ∧ ¬ IsZero coef := by
  simp only [Trimmed_iff_seq_Trimmed, mk_seq] at h
  exact SeqMS.Trimmed_cons h

mutual

theorem SeqMS.const_Trimmed {basis_hd : ℝ → ℝ} {basis_tl : Basis} {c : ℝ} (hc : c ≠ 0) :
    (SeqMS.const basis_hd basis_tl c).Trimmed := by
  simp only [SeqMS.const]
  constructor
  · exact const_Trimmed hc
  cases basis_tl <;> simp [const, SeqMS.const, ofReal, toReal, hc]

theorem const_Trimmed {basis : Basis} {c : ℝ} (hc : c ≠ 0) : (const basis c).Trimmed := by
  obtain _ | ⟨basis_hd, basis_tl⟩ := basis
  · constructor
  simp only [const, Trimmed_iff_seq_Trimmed, mk_seq]
  apply SeqMS.const_Trimmed hc

end

mutual

theorem SeqMS.monomialRpow_Trimmed {basis_hd : ℝ → ℝ} {basis_tl : Basis} {n : ℕ}
    (h : n < (basis_hd :: basis_tl).length) {r : ℝ} :
    (@SeqMS.monomialRpow basis_hd basis_tl n r).Trimmed := by
  cases n with
  | zero =>
    simp only [SeqMS.monomialRpow]
    apply SeqMS.Trimmed.cons
    · simp only [one]
      apply PreMS.const_Trimmed (by simp)
    · cases basis_tl <;> simp [PreMS.one, PreMS.const, PreMS.ofReal, PreMS.toReal, SeqMS.const]
  | succ m =>
    simp only [SeqMS.monomialRpow]
    apply SeqMS.Trimmed.cons
    · apply monomialRpow_Trimmed (by simpa using h)
    · cases basis_tl
      · simp at h
      cases m <;> simp [PreMS.monomialRpow, SeqMS.monomialRpow]

theorem monomialRpow_Trimmed {basis : Basis} {n : ℕ} (h : n < basis.length) {r : ℝ} :
    (@monomialRpow basis n r).Trimmed := by
  obtain _ | ⟨basis_hd, basis_tl⟩ := basis
  · constructor
  simp only [monomialRpow, List.getElem!_eq_getElem?_getD, Pi.default_def, Trimmed_iff_seq_Trimmed,
    mk_seq]
  exact SeqMS.monomialRpow_Trimmed h

end

theorem SeqMS.monomial_Trimmed {basis_hd : ℝ → ℝ} {basis_tl : Basis} {n : ℕ}
    (h : n < (basis_hd :: basis_tl).length) :
    (@SeqMS.monomial basis_hd basis_tl n).Trimmed :=
  SeqMS.monomialRpow_Trimmed h

theorem monomial_Trimmed {basis : Basis} {n : ℕ} (h : n < basis.length) :
    (@monomial basis n).Trimmed :=
  monomialRpow_Trimmed h

theorem extendBasisEnd_ne_zero {basis : Basis} {b : ℝ → ℝ} {ms : PreMS basis}
    (h : ¬ IsZero ms) : ¬ IsZero (ms.extendBasisEnd b) := by
  obtain _ | ⟨basis_hd, basis_tl⟩ := basis
  · simp [extendBasisEnd, const, SeqMS.const]
  cases ms
  · simp at h
  simp [extendBasisEnd, SeqMS.extendBasisEnd]

mutual

theorem SeqMS.extendBasisEnd_Trimmed {basis_hd : ℝ → ℝ} {basis_tl : Basis} {b : ℝ → ℝ}
    {ms : SeqMS basis_hd basis_tl} (h_trimmed : ms.Trimmed) :
    (ms.extendBasisEnd b).Trimmed := by
  cases ms with
  | nil => simp [SeqMS.extendBasisEnd]
  | cons exp coef tl =>
  simp only [SeqMS.extendBasisEnd, SeqMS.map_cons, id_eq]
  constructor
  · cases basis_tl with
    | nil =>
      simp only [List.nil_append, extendBasisEnd]
      apply const_Trimmed
      simpa using (Trimmed_cons h_trimmed).right
    | cons basis_tl_hd basis_tl_tl => exact extendBasisEnd_Trimmed (Trimmed_cons h_trimmed).left
  · obtain _ | ⟨basis_tl_hd, basis_tl_tl⟩ := basis_tl
    · simp [extendBasisEnd, const, SeqMS.const]
    · exact extendBasisEnd_ne_zero (Trimmed_cons h_trimmed).right

theorem extendBasisEnd_Trimmed {basis_hd : ℝ → ℝ} {basis_tl : Basis} {b : ℝ → ℝ}
    {ms : PreMS (basis_hd :: basis_tl)}
    (h_trimmed : ms.Trimmed) : (ms.extendBasisEnd b).Trimmed := by
  simp only [Trimmed_iff_seq_Trimmed, List.cons_append, List.append_eq, extendBasisEnd_seq] at *
  apply SeqMS.extendBasisEnd_Trimmed h_trimmed

end

theorem extendBasisMiddle_Trimmed {left right_tl : Basis} {right_hd b : ℝ → ℝ}
    {ms : PreMS (left ++ right_hd :: right_tl)}
    (h_trimmed : ms.Trimmed) (h_ne_zero : ¬ IsZero ms) : (ms.extendBasisMiddle b).Trimmed := by
  obtain _ | ⟨left_hd, left_tl⟩ := left
  · cases ms with
    | nil => simp at h_ne_zero
    | cons exp coef tl =>
    simp only [List.nil_append, extendBasisMiddle]
    constructor
    · exact h_trimmed
    · simp
  · cases ms with
    | nil => simp at h_ne_zero
    | cons exp coef tl =>
    simp only [List.cons_append, extendBasisMiddle, List.append_eq, mk_seq, SeqMS.map_cons, id_eq,
      mk_toFun]
    apply Trimmed_cons at h_trimmed
    constructor
    · exact extendBasisMiddle_Trimmed h_trimmed.left h_trimmed.right
    · obtain _ | ⟨left_tl_hd, left_tl_tl⟩ := left_tl
      · simp [extendBasisMiddle]
      · cases coef
        · simp at h_trimmed
        simp [extendBasisMiddle]

-- -- TODO: Where should I put it? Trimming is not needed here.
-- /-- If `f` can be approximated by multiseries with negative leading exponent, then
-- it tends to zero. -/
theorem neg_leadingExp_tendsto_zero {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {ms : PreMS (basis_hd :: basis_tl)}
    (h_neg : ms.leadingExp < 0) (h_approx : ms.Approximates) :
    Tendsto ms.toFun atTop (𝓝 0) := by
    cases ms
    · apply Approximates_nil at h_approx
      apply Tendsto.congr' h_approx.symm
      apply tendsto_const_nhds
    · obtain ⟨h_coef, h_maj, h_tl⟩ := Approximates_cons h_approx
      simp only [leadingExp_def, mk_seq, SeqMS.leadingExp_cons, WithBot.coe_lt_zero] at h_neg
      apply majorated_tendsto_zero_of_neg h_neg h_maj

end PreMS

end ComputeAsymptotics
