/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Tactic.ComputeAsymptotics.Multiseries.Defs

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

namespace Tactic.ComputeAsymptotics

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

/-- If `cons (exp, coef) tl` is trimmed, then `coef` is trimmed and is not zero. -/
theorem elim_cons {basis_hd} {basis_tl} {exp : ℝ} {coef : MultiseriesExpansion basis_tl}
    {tl : Multiseries basis_hd basis_tl} {f : ℝ → ℝ}
    (h : Trimmed (mk (.cons exp coef tl) f)) :
    coef.Trimmed ∧ ¬ IsZero coef := by
  simp only [trimmed_iff_seq_trimmed, mk_seq] at h
  exact h.elim_cons

end MultiseriesExpansion

end Tactic.ComputeAsymptotics
