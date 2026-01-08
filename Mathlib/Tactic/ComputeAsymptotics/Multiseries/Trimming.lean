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

inductive IsZero : {basis : Basis} → PreMS basis → Prop
| const {c : PreMS []} (hc : c.toReal = 0) : IsZero c
| nil {basis_hd} {basis_tl} (f) : @IsZero (basis_hd :: basis_tl) (mk .nil f)

@[simp]
theorem const_IsZero_iff {c : PreMS []} : IsZero c ↔ c.toReal = 0 := by
  constructor <;> grind [IsZero]

@[simp]
theorem nil_IsZero {basis_hd} {basis_tl} {f} : @IsZero (basis_hd :: basis_tl) (mk .nil f) := by
  constructor

@[simp]
theorem cons_not_IsZero {basis_hd} {basis_tl} {exp : ℝ} {coef : PreMS basis_tl}
    {tl : Seq (ℝ × PreMS basis_tl)} {f : ℝ → ℝ} :
    ¬ @IsZero (basis_hd :: basis_tl) (mk (.cons (exp, coef) tl) f) := by
  intro h
  generalize h_ms : (mk (Seq.cons (exp, coef) tl) f) = ms at h
  cases h
  simp at h_ms

/-- We call multiseries `Trimmed` if it is either constant, `[]` or `cons (exp, coef) tl` where
coef is trimmed and is not zero. Intuitively, when multiseries is trimmed, it guarantees that
leading term of multiseries is main asymptotics of the function, approximated by multiseries. -/
inductive Trimmed : {basis : Basis} → PreMS basis → Prop
| const {c : ℝ} : @Trimmed [] c
| nil {basis_hd} {basis_tl} {f} : @Trimmed (basis_hd :: basis_tl) (mk .nil f)
| cons {basis_hd} {basis_tl} {exp : ℝ} {coef : PreMS basis_tl}
  {tl : Seq (ℝ × PreMS basis_tl)} {f : ℝ → ℝ} (h_trimmed : coef.Trimmed)
  (h_ne_zero : ¬ IsZero coef) :
  @Trimmed (basis_hd :: basis_tl) (mk (.cons (exp, coef) tl) f)

/-- `cons (exp, coef) tl` means that `coef` is trimmed and is not zero. -/
theorem Trimmed_cons {basis_hd} {basis_tl} {exp : ℝ} {coef : PreMS basis_tl}
    {tl : Seq (ℝ × PreMS basis_tl)} {f : ℝ → ℝ}
    (h : @Trimmed (basis_hd :: basis_tl) (mk (.cons (exp, coef) tl) f)) :
    coef.Trimmed ∧ ¬ IsZero coef := by
  generalize h_ms : mk (Seq.cons (exp, coef) tl) f = ms at h
  cases h with
  | nil => simp at h_ms
  | cons h_trimmed h_ne_zero =>
    simp at h_ms
    grind

theorem const_Trimmed {basis : Basis} {c : ℝ} (hc : c ≠ 0) : (const basis c).Trimmed := by
  obtain _ | ⟨basis_hd, basis_tl⟩ := basis
  · constructor
  simp only [const]
  constructor
  · exact const_Trimmed hc
  cases basis_tl <;> simp [const, hc]

theorem monomial_rpow_Trimmed {basis : Basis} {n : ℕ} (h : n < basis.length) (r : ℝ) :
    (@monomial_rpow basis n r).Trimmed := by
  obtain _ | ⟨basis_hd, basis_tl⟩ := basis
  · constructor
  obtain _ | n := n
  · constructor
    · simp only [one]
      exact const_Trimmed (by simp)
    · cases basis_tl <;> simp [one, const]
  · constructor
    · apply monomial_rpow_Trimmed
      simpa using h
    · cases basis_tl
      · simp at h
      cases n <;> simp [monomial_rpow]

theorem monomial_Trimmed {basis : Basis} {n : ℕ} (h : n < basis.length) :
    (@monomial basis n).Trimmed :=
  monomial_rpow_Trimmed h 1

-- theorem extendBasisEnd_ne_zero {basis : Basis} {b : ℝ → ℝ} {ms : PreMS basis}
--     (h : ms ≠ 0) : ms.extendBasisEnd b ≠ 0 := by
--   obtain _ | ⟨basis_hd, basis_tl⟩ :=basis
--   · simp [extendBasisEnd, zero, const]
--   cases ms
--   · simp [zero] at h
--   simp [extendBasisEnd, zero]

-- theorem extendBasisEnd_Trimmed {basis_hd : ℝ → ℝ} {basis_tl : Basis} {b : ℝ → ℝ}
--     {ms : PreMS (basis_hd :: basis_tl)}
--     (h_trimmed : ms.Trimmed) : (ms.extendBasisEnd b).Trimmed := by
--   cases ms with
--   | nil => constructor
--   | cons exp coef tl =>
--   simp only [List.cons_append, extendBasisEnd, List.append_eq, map_cons]
--   constructor
--   · obtain _ | ⟨basis_tl_hd, basis_tl_tl⟩ := basis_tl
--     · simp only [List.nil_append, extendBasisEnd, const]
--       constructor
--       · exact (Trimmed_cons h_trimmed).left
--       · exact (Trimmed_cons h_trimmed).right
--     · exact extendBasisEnd_Trimmed (Trimmed_cons h_trimmed).left
--   · obtain _ | ⟨basis_tl_hd, basis_tl_tl⟩ := basis_tl
--     · simp [extendBasisEnd, const, zero]
--     · exact extendBasisEnd_ne_zero (Trimmed_cons h_trimmed).right

-- theorem extendBasisMiddle_Trimmed {left right_tl : Basis} {right_hd b : ℝ → ℝ}
--     {ms : PreMS (left ++ right_hd :: right_tl)}
--     (h_trimmed : ms.Trimmed) (h_ne_zero : ms ≠ zero _) : (ms.extendBasisMiddle b).Trimmed := by
--   obtain _ | ⟨left_hd, left_tl⟩ := left
--   · cases ms with
--     | nil => simp [zero] at h_ne_zero
--     | cons exp coef tl =>
--     simp only [List.nil_append, extendBasisMiddle]
--     constructor
--     · exact h_trimmed
--     · simp [zero]
--   · cases ms with
--     | nil =>simp [zero] at h_ne_zero
--     | cons exp coef tl =>
--     simp only [List.cons_append, extendBasisMiddle, List.append_eq, map_cons]
--     apply Trimmed_cons at h_trimmed
--     constructor
--     · exact extendBasisMiddle_Trimmed h_trimmed.left h_trimmed.right
--     · obtain _ | ⟨left_tl_hd, left_tl_tl⟩ := left_tl
--       · simp [extendBasisMiddle, zero]
--       · cases coef
--         · simp [zero] at h_trimmed
--         simp [extendBasisMiddle, zero]

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
      simp [Seq.leadingExp_cons, WithBot.coe_lt_zero] at h_neg
      apply majorated_tendsto_zero_of_neg h_neg h_maj

end PreMS

end ComputeAsymptotics
