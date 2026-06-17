/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Tactic.ComputeAsymptotics.Multiseries.Basic

/-!
# Trimming of multiseries

A multiseries is *trimmed* when its leading coefficient (the head of its expansion) is itself
trimmed and non-zero. For a trimmed multiseries, the leading monomial captures the main
asymptotic behavior of the approximated function.

## Main definitions

* `IsZero`: a multiseries represents the zero function — it is either the real number `0`
  (for the empty basis) or has an empty underlying sequence (`.nil`).
* `Trimmed` and `Multiseries.Trimmed`: a multiseries is trimmed in the sense above. The former
  is defined inductively for `MultiseriesExpansion`, and the latter for `Multiseries` is
  derived from it.

We also prove structural lemmas relating these predicates to `seq` and to the `cons`/`nil`
constructors.

-/

@[expose] public section

namespace Mathlib.Tactic.ComputeAsymptotics

namespace MultiseriesExpansion

open Filter Topology Stream'

/-- A multiseries is zero if it is the real constant `0` or has an empty sequence. -/
inductive IsZero : {basis : Basis} → MultiseriesExpansion basis → Prop
| const {c : MultiseriesExpansion []} (hc : c.toReal = 0) : IsZero c
| nil {basis_hd} {basis_tl} (f) : @IsZero (basis_hd :: basis_tl) (mk .nil f)

namespace IsZero

@[simp]
theorem const_iff {c : MultiseriesExpansion []} : IsZero c ↔ c.toReal = 0 := by
  constructor <;> grind [IsZero]

@[simp]
theorem iff_seq_eq_nil {basis_hd basis_tl} {ms : MultiseriesExpansion (basis_hd :: basis_tl)} :
    IsZero ms ↔ ms.seq = .nil where
  mp h := by cases h; rw [mk_seq]
  mpr h := by
    convert IsZero.nil ms.toFun
    simp [h]

theorem approximates_zero {basis : Basis} {ms : MultiseriesExpansion basis}
    (h_zero : IsZero ms) (h_approx : ms.Approximates) :
    ms.toFun =ᶠ[atTop] 0 := by
  cases h_zero with
  | const hc => simp [hc, Pi.zero_def]
  | nil => simpa using h_approx

theorem not_cons {basis_hd} {basis_tl} {exp : ℝ} {coef : MultiseriesExpansion basis_tl}
    {tl : Multiseries basis_hd basis_tl} {f : ℝ → ℝ} :
    ¬ @IsZero (basis_hd :: basis_tl) (mk (.cons exp coef tl) f) := by
  simp

end IsZero

/-- We call a multiseries `Trimmed` if it is either a constant, `.nil`, or `cons (exp, coef) tl`
where `coef` is trimmed and is not zero. Intuitively, when a multiseries is trimmed, its leading
monomial gives the main asymptotic behavior of the approximated function. -/
inductive Trimmed : {basis : Basis} → MultiseriesExpansion basis → Prop
| const {c : ℝ} : @Trimmed [] c
| nil {basis_hd} {basis_tl} {f} : @Trimmed (basis_hd :: basis_tl) (mk .nil f)
| cons {basis_hd} {basis_tl} {exp : ℝ} {coef : MultiseriesExpansion basis_tl}
  {tl : Multiseries basis_hd basis_tl} {f : ℝ → ℝ} (h_trimmed : coef.Trimmed)
  (h_ne_zero : ¬ IsZero coef) :
  @Trimmed (basis_hd :: basis_tl) (mk (.cons exp coef tl) f)

/-- We call a `Multiseries` `Trimmed` if it is either `.nil` or `cons (exp, coef) tl` where `coef`
is trimmed and is not zero. -/
def Multiseries.Trimmed {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    (ms : Multiseries basis_hd basis_tl) : Prop :=
  (mk ms 0).Trimmed

theorem trimmed_iff_seq_trimmed {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    (ms : MultiseriesExpansion (basis_hd :: basis_tl)) :
    ms.Trimmed ↔ ms.seq.Trimmed where
  mp h := by
    cases h <;> constructor <;> grind
  mpr h := by
    generalize hs : ms.seq = s at h
    cases h with
    | nil =>
      convert Trimmed.nil (f := ms.toFun)
      simp [hs]
    | @cons _ _ exp coef tl _ h_trimmed h_ne_zero =>
      convert Trimmed.cons h_trimmed h_ne_zero (exp := exp) (tl := tl) (f := ms.toFun)
      simp only [ms_eq_mk_iff, hs, and_true]

namespace Multiseries.Trimmed

@[simp]
theorem nil {basis_hd} {basis_tl} :
    @Multiseries.Trimmed basis_hd basis_tl .nil := by
  constructor

theorem cons {basis_hd} {basis_tl} {exp : ℝ}
    {coef : MultiseriesExpansion basis_tl} {tl : Multiseries basis_hd basis_tl}
    (h_coef : coef.Trimmed) (h_ne_zero : ¬ IsZero coef) :
    Multiseries.Trimmed (cons exp coef tl) :=
  MultiseriesExpansion.Trimmed.cons h_coef h_ne_zero

/-- If `cons (exp, coef) tl` is trimmed, then `coef` is trimmed and is not zero. -/
theorem elim_cons {basis_hd} {basis_tl} {exp : ℝ}
    {coef : MultiseriesExpansion basis_tl} {tl : Multiseries basis_hd basis_tl}
    (h : Multiseries.Trimmed (.cons exp coef tl)) :
    coef.Trimmed ∧ ¬ IsZero coef := by
  generalize h_ms : Multiseries.cons exp coef tl = ms at h
  cases h with
  | nil => simp at h_ms
  | cons h_trimmed h_ne_zero =>
    simp at h_ms
    grind

end Multiseries.Trimmed

-- /-- If `cons (exp, coef) tl` is trimmed, then `coef` is trimmed and is not zero. -/
-- theorem Trimmed.elim_cons {basis_hd} {basis_tl} {exp : ℝ} {coef : MultiseriesExpansion basis_tl}
--     {tl : Multiseries basis_hd basis_tl} {f : ℝ → ℝ}
--     (h : Trimmed (mk (.cons exp coef tl) f)) :
--     coef.Trimmed ∧ ¬ IsZero coef := by
--   simp only [trimmed_iff_seq_trimmed, mk_seq] at h
--   exact h.elim_cons

mutual

theorem Multiseries.const_trimmed {basis_hd : ℝ → ℝ} {basis_tl : Basis} {c : ℝ} (hc : c ≠ 0) :
    (Multiseries.const basis_hd basis_tl c).Trimmed := by
  simp only [Multiseries.const]
  constructor
  · exact const_trimmed hc
  cases basis_tl <;> simp [const, Multiseries.const, ofReal, toReal, hc]

theorem const_trimmed {basis : Basis} {c : ℝ} (hc : c ≠ 0) : (const basis c).Trimmed := by
  obtain _ | ⟨basis_hd, basis_tl⟩ := basis
  · constructor
  simp only [const, trimmed_iff_seq_trimmed, mk_seq]
  apply Multiseries.const_trimmed hc

end

mutual

theorem Multiseries.monomialRpow_trimmed {basis_hd : ℝ → ℝ} {basis_tl : Basis} {n : ℕ}
    (h : n < (basis_hd :: basis_tl).length) {r : ℝ} :
    (@Multiseries.monomialRpow basis_hd basis_tl n r).Trimmed := by
  cases n with
  | zero =>
    simp only [Multiseries.monomialRpow]
    apply Multiseries.Trimmed.cons
    · simp only [one]
      apply MultiseriesExpansion.const_trimmed (by simp)
    · cases basis_tl <;> simp [MultiseriesExpansion.one, MultiseriesExpansion.const,
        MultiseriesExpansion.ofReal, MultiseriesExpansion.toReal, Multiseries.const]
  | succ m =>
    simp only [Multiseries.monomialRpow]
    apply Multiseries.Trimmed.cons
    · apply monomialRpow_trimmed (by simpa using h)
    · cases basis_tl
      · simp at h
      cases m <;> simp [MultiseriesExpansion.monomialRpow, Multiseries.monomialRpow]

theorem monomialRpow_trimmed {basis : Basis} {n : ℕ} (h : n < basis.length) {r : ℝ} :
    (monomialRpow basis n r).Trimmed := by
  obtain _ | ⟨basis_hd, basis_tl⟩ := basis
  · constructor
  simp only [trimmed_iff_seq_trimmed, monomialRpow_seq]
  exact Multiseries.monomialRpow_trimmed h

end

theorem Multiseries.monomial_trimmed {basis_hd : ℝ → ℝ} {basis_tl : Basis} {n : ℕ}
    (h : n < (basis_hd :: basis_tl).length) :
    (@Multiseries.monomial basis_hd basis_tl n).Trimmed :=
  Multiseries.monomialRpow_trimmed h

theorem monomial_trimmed {basis : Basis} {n : ℕ} (h : n < basis.length) :
    (monomial basis n).Trimmed :=
  monomialRpow_trimmed h

theorem extendBasisEnd_ne_zero {basis : Basis} {b : ℝ → ℝ} {ms : MultiseriesExpansion basis}
    (h : ¬ IsZero ms) : ¬ IsZero (ms.extendBasisEnd b) := by
  obtain _ | ⟨basis_hd, basis_tl⟩ := basis
  · simp [extendBasisEnd, const, Multiseries.const]
  cases ms
  · simp at h
  simp [extendBasisEnd, Multiseries.extendBasisEnd]

mutual

theorem Multiseries.extendBasisEnd_trimmed {basis_hd : ℝ → ℝ} {basis_tl : Basis} {b : ℝ → ℝ}
    {ms : Multiseries basis_hd basis_tl} (h_trimmed : ms.Trimmed) :
    (ms.extendBasisEnd b).Trimmed := by
  cases ms with
  | nil => simp [Multiseries.extendBasisEnd]
  | cons exp coef tl =>
  simp only [Multiseries.extendBasisEnd, Multiseries.map_cons, id_eq]
  constructor
  · cases basis_tl with
    | nil =>
      simp only [List.nil_append, extendBasisEnd]
      apply const_trimmed
      simpa using h_trimmed.elim_cons.right
    | cons basis_tl_hd basis_tl_tl => exact extendBasisEnd_trimmed h_trimmed.elim_cons.left
  · obtain _ | ⟨basis_tl_hd, basis_tl_tl⟩ := basis_tl
    · simp [extendBasisEnd, const, Multiseries.const]
    · exact extendBasisEnd_ne_zero h_trimmed.elim_cons.right

theorem extendBasisEnd_trimmed {basis_hd : ℝ → ℝ} {basis_tl : Basis} {b : ℝ → ℝ}
    {ms : MultiseriesExpansion (basis_hd :: basis_tl)}
    (h_trimmed : ms.Trimmed) : (ms.extendBasisEnd b).Trimmed := by
  simp only [trimmed_iff_seq_trimmed, List.cons_append, List.append_eq, extendBasisEnd_seq] at *
  apply Multiseries.extendBasisEnd_trimmed h_trimmed

end

theorem extendBasisMiddle_trimmed {left right_tl : Basis} {right_hd b : ℝ → ℝ}
    {ms : MultiseriesExpansion (left ++ right_hd :: right_tl)}
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
    simp only [List.cons_append, extendBasisMiddle, List.append_eq, mk_seq,
      Multiseries.map_cons, id_eq, mk_toFun]
    simp only [List.cons_append, List.append_eq, trimmed_iff_seq_trimmed, mk_seq] at h_trimmed
    apply Multiseries.Trimmed.elim_cons at h_trimmed
    constructor
    · exact extendBasisMiddle_trimmed h_trimmed.left h_trimmed.right
    · obtain _ | ⟨left_tl_hd, left_tl_tl⟩ := left_tl
      · simp [extendBasisMiddle]
      · cases coef
        · simp at h_trimmed
        simp [extendBasisMiddle]

-- TODO: Where should I put it? Trimming is not needed here.
/-- If `f` can be approximated by multiseries with negative leading exponent, then
it tends to zero. -/
theorem neg_leadingExp_tendsto_zero {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {ms : MultiseriesExpansion (basis_hd :: basis_tl)}
    (h_neg : ms.leadingExp < 0) (h_approx : ms.Approximates) :
    Tendsto ms.toFun atTop (𝓝 0) := by
    cases ms
    · apply Approximates.elim_nil at h_approx
      apply Tendsto.congr' h_approx.symm
      apply tendsto_const_nhds
    · obtain ⟨h_coef, h_maj, h_tl⟩ := h_approx.elim_cons
      simp only [leadingExp_def, mk_seq, Multiseries.leadingExp_cons, WithBot.coe_lt_zero] at h_neg
      apply Majorized.tendsto_zero_of_neg h_neg h_maj

end MultiseriesExpansion

end Mathlib.Tactic.ComputeAsymptotics
