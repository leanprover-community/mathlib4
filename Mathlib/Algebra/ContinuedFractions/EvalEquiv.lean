/-
Copyright (c) 2020 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
import Mathlib.Algebra.ContinuedFractions.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

#align_import algebra.continued_fractions.convergents_equiv from "leanprover-community/mathlib"@"a7e36e48519ab281320c4d192da6a7b348ce40ad"

/-!
# Equivalence of Recursive and Direct Computations of `FGCF`

## Summary

We show the equivalence of two computations of a value (recurrence relation (`eval?`) vs.
direct evaluation (`evalF?`)) for `FGCF`s. We follow the proof from [hardy2008introduction],
Chapter 10. Here's a sketch:

Let `f` be a fgcf `CF[h; (a₀, b₀), ..., (aₙ₋₂, bₙ₋₂), (aₙ₋₁, bₙ₋₁)]`.
One can compute the convergents of `f` in two ways:
1. Directly evaluating the fraction described by `f` (`evalF?`)
2. Using the recurrence (`eval?`):
  - `A₋₁ = 1,  A₀ = h,  Aₙ = bₙ₋₁ * Aₙ₋₁ + aₙ₋₁ * Aₙ₋₂`, and
  - `B₋₁ = 0,  B₀ = 1,  Bₙ = bₙ₋₁ * Bₙ₋₁ + aₙ₋₁ * Bₙ₋₂`.

To show the equivalence of the computations in the main theorem of this file
`eval?_eq_evalF?`, we proceed by induction. The case `n = 0` is trivial.

For `n + 1`, we first "squash" the `n + 1`th position of `f` into the `n`th position to obtain
another continued fraction:
 - `f' := CF[h; (a₀, b₀),..., (aₙ₋₂, bₙ₋₂), (aₙ₋₁, bₙ₋₁ + aₙ / bₙ)]` if `bₙ ≠ 0`
 - `f' := CF[h; (a₀, b₀),..., (aₙ₋₂, bₙ₋₂)]` if `bₙ = 0`
This squashing process is formalised in section `Squash`. Note that directly evaluating `f` up to
position `n + 1` is equal to evaluating `f'` up to `n`. This is shown in lemma
`bind_evalF?_squash_eq_evalF?_concat`.

By the inductive hypothesis, the two computations for the `n`th convergent of `f` coincide.
So all that is left to show is that the recurrence relation for `f` at `n + 1` and `f'` at
`n` coincide. This can be shown by another induction.
The corresponding lemma in this file is `eval?_squash_eq_eval?_concat`.

## Main Theorems

- `FGCF.eval?_eq_evalF?` shows the equivalence.

## References

- https://en.wikipedia.org/wiki/Generalized_continued_fraction
- [*Hardy, GH and Wright, EM and Heath-Brown, Roger and Silverman, Joseph*][hardy2008introduction]

## Tags

fractions, recurrence, equivalence
-/


open List

namespace FGCF

section Squash

/-!
We will show the equivalence of the computations by induction.
-/


variable {K : Type*}

section WithDivisionRing

variable [DivisionRing K] [DecidableEq K]

/-- Given a fgcf `f := CF[h; (a₀, bₒ), ..., (aₙ₋₁, bₙ₋₁)]` and `p := (aₙ, bₙ)`, we have
- `squash f = some CF[h + aₙ / bₙ]` if `n = 0` and `bₙ ≠ 0`,
- `squash f = none` if `n = 0` and `bₙ = 0`,
- `squash f = some ⟨h, squash.go f.l _ p⟩` if `n ≠ 0`.
-/
def squash : FGCF K → K × K → Option (FGCF K)
  | ⟨h, l⟩, (a', b') =>
    if hl : l = [] then
      if b' = 0 then
        none
      else
        some ⟨h + a' / b', []⟩
    else
      some ⟨h, go l hl (a', b')⟩
where
  /-- Given a nonempty list of `K × K`s `l = [(a₀, bₒ), ..., (aₙ, bₙ)]` and `p := (aₙ₊₁, bₙ₊₁)`,
  `squash.go l _ p` combines `(aₙ, bₙ)` and `(aₙ₊₁, bₙ₊₁)` at last position to
  `(aₙ, bₙ + aₙ₊₁ / bₙ₊₁)`.
  -/
  go (l : List (K × K)) (hl : l ≠ []) : K × K → List (K × K)
  | (a', b') =>
    if b' = 0 then
      dropLast l
    else
      match getLast l hl with
      | (a, b) =>
        dropLast l ++ [(a, b + a' / b')]
#align generalized_continued_fraction.squash_gcf FGCF.squashₓ
#align generalized_continued_fraction.squash_seq FGCF.squash.goₓ

#noalign generalized_continued_fraction.squash_seq_eq_self_of_terminated

#noalign generalized_continued_fraction.squash_seq_nth_of_not_terminated

#noalign generalized_continued_fraction.squash_seq_nth_of_lt

#noalign generalized_continued_fraction.squash_seq_succ_n_tail_eq_squash_seq_tail_n

/-- The auxiliary function `evalF?.loop` returns the same value for a list and the
corresponding squashed list. -/
@[simp]
theorem evalF?_loop_squash_go_eq_evalF?_concat (l : List (K × K)) (hl : l ≠ []) (p : K × K) :
    evalF?.loop (squash.go l hl p) = evalF?.loop (l ++ [p]) := by
  rcases Or.resolve_left (eq_nil_or_concat l) hl with ⟨l₂, ⟨a₁, b₁⟩, rfl⟩
  rcases p with ⟨a₂, b₂⟩
  induction l₂ with
  | nil =>
    simp [squash.go, evalF?.loop]
    split_ifs with hb₂ <;> simp [evalF?.loop]
  | cons p' l' hl' =>
    rcases p' with ⟨a₀, b₀⟩
    simp [squash.go, evalF?.loop] at hl' ⊢
    split_ifs at hl' ⊢ with hb₂ <;> simp [evalF?.loop, hl']
#align generalized_continued_fraction.succ_succ_nth_convergent'_aux_eq_succ_nth_convergent'_aux_squash_seq FGCF.evalF?_loop_squash_go_eq_evalF?_concatₓ

#noalign generalized_continued_fraction.squash_gcf_eq_self_of_terminated

#noalign generalized_continued_fraction.squash_gcf_nth_of_lt

/-- `evalF?` returns the same value for a fgcf and the corresponding squashed fgcf. -/
@[simp]
theorem bind_evalF?_squash_eq_evalF?_concat (h : K) (l : List (K × K)) (p : K × K) :
    (squash ⟨h, l⟩ p).bind evalF? = evalF? ⟨h, l ++ [p]⟩ := by
  rcases p with ⟨a', b'⟩
  by_cases hl : l = []
  · simp [squash, hl]
    by_cases hb' : b' = 0 <;> simp [hb', evalF?, evalF?.loop]
  · simp [squash, evalF?, hl]
#align generalized_continued_fraction.succ_nth_convergent'_eq_squash_gcf_nth_convergent' FGCF.bind_evalF?_squash_eq_evalF?_concat

#noalign generalized_continued_fraction.continuants_aux_eq_continuants_aux_squash_gcf_of_le

end WithDivisionRing



/-- `eval?` returns the same value for a fgcf and the corresponding squashed fgcf. -/
theorem bind_eval?_squash_eq_eval?_concat [Field K] [DecidableEq K] (h : K) (l : List (K × K))
    (p : K × K) :
    (squash ⟨h, l⟩ p).bind eval? = eval? ⟨h, l ++ [p]⟩ := by
  rcases p with ⟨a₂, b₂⟩
  rcases eq_nil_or_concat l with rfl | ⟨l', ⟨a₁, b₁⟩, rfl⟩
  · by_cases hb₂ : b₂ = 0 <;> simp [eval?, continuant, denominator, numerator, squash, hb₂]
    field_simp; ring
  · by_cases hb₂ : b₂ = 0 <;> simp [eval?, squash, squash.go, hb₂]
    sorry
  -- cases' Decidable.em (g.TerminatedAt n) with terminated_at_n not_terminated_at_n
  -- · have : squashFGCF g n = g := squashFGCF_eq_self_of_terminated terminated_at_n
  --   simp only [this, convergents_stable_of_terminated n.le_succ terminated_at_n]
  -- · obtain ⟨⟨a, b⟩, s_nth_eq⟩ : ∃ gp_n, g.s.get? n = some gp_n
  --   exact Option.ne_none_iff_exists'.mp not_terminated_at_n
  --   have b_ne_zero : b ≠ 0 := nth_part_denom_ne_zero (partDenom_eq_s_b s_nth_eq)
  --   cases' n with n'
  --   case zero =>
  --     suffices (b * g.h + a) / b = g.h + a / b by
  --       simpa [squashFGCF, s_nth_eq, convergent_eq_conts_a_div_conts_b,
  --         continuants_recurrenceAux s_nth_eq zeroth_continuantAux_eq_one_zero
  --           first_continuantAux_eq_h_one]
  --     calc
  --       (b * g.h + a) / b = b * g.h / b + a / b := by ring
  --       -- requires `Field`, not `DivisionRing`
  --       _ = g.h + a / b := by rw [mul_div_cancel_left _ b_ne_zero]
  --   case succ =>
  --     obtain ⟨⟨pa, pb⟩, s_n'th_eq⟩ : ∃ gp_n', g.s.get? n' = some gp_n' :=
  --       g.s.ge_stable n'.le_succ s_nth_eq
  --     -- Notations
  --     let g' := squashFGCF g (n' + 1)
  --     set pred_conts := g.continuantsAux (n' + 1) with succ_n'th_conts_aux_eq
  --     set ppred_conts := g.continuantsAux n' with n'th_conts_aux_eq
  --     let pA := pred_conts.a
  --     let pB := pred_conts.b
  --     let ppA := ppred_conts.a
  --     let ppB := ppred_conts.b
  --     set pred_conts' := g'.continuantsAux (n' + 1) with succ_n'th_conts_aux_eq'
  --     set ppred_conts' := g'.continuantsAux n' with n'th_conts_aux_eq'
  --     let pA' := pred_conts'.a
  --     let pB' := pred_conts'.b
  --     let ppA' := ppred_conts'.a
  --     let ppB' := ppred_conts'.b
  --     -- first compute the convergent of the squashed gcf
  --     have : g'.convergents (n' + 1) =
  --         ((pb + a / b) * pA' + pa * ppA') / ((pb + a / b) * pB' + pa * ppB') := by
  --       have : g'.s.get? n' = some ⟨pa, pb + a / b⟩ :=
  --         squashSeq_nth_of_not_terminated s_n'th_eq s_nth_eq
  --       rw [convergent_eq_conts_a_div_conts_b,
  --         continuants_recurrenceAux this n'th_conts_aux_eq'.symm succ_n'th_conts_aux_eq'.symm]
  --     rw [this]
  --     -- then compute the convergent of the original gcf by recursively unfolding the continuants
  --     -- computation twice
  --     have : g.convergents (n' + 2) =
  --         (b * (pb * pA + pa * ppA) + a * pA) / (b * (pb * pB + pa * ppB) + a * pB) := by
  --       -- use the recurrence once
  --       have : g.continuantsAux (n' + 2) = ⟨pb * pA + pa * ppA, pb * pB + pa * ppB⟩ :=
  --         continuantsAux_recurrence s_n'th_eq n'th_conts_aux_eq.symm succ_n'th_conts_aux_eq.symm
  --       -- and a second time
  --       rw [convergent_eq_conts_a_div_conts_b,
  --         continuants_recurrenceAux s_nth_eq succ_n'th_conts_aux_eq.symm this]
  --     rw [this]
  --     suffices
  --       ((pb + a / b) * pA + pa * ppA) / ((pb + a / b) * pB + pa * ppB) =
  --         (b * (pb * pA + pa * ppA) + a * pA) / (b * (pb * pB + pa * ppB) + a * pB) by
  --       obtain ⟨eq1, eq2, eq3, eq4⟩ : pA' = pA ∧ pB' = pB ∧ ppA' = ppA ∧ ppB' = ppB := by
  --         simp [*, (continuantsAux_eq_continuantsAux_squashFGCF_of_le <| le_refl <| n' + 1).symm,
  --           (continuantsAux_eq_continuantsAux_squashFGCF_of_le n'.le_succ).symm]
  --       symm
  --       simpa only [eq1, eq2, eq3, eq4, mul_div_cancel _ b_ne_zero]
  --     field_simp
  --     congr 1 <;> ring
#align generalized_continued_fraction.succ_nth_convergent_eq_squash_gcf_nth_convergent FGCF.bind_eval?_squash_eq_eval?_concat

end Squash

/-- Shows that the recurrence relation (`convergents`) and direct evaluation (`convergents'`) of the
gcf coincide at position `n` if the sequence of fractions contains strictly positive values only.
Requiring positivity of all values is just one possible condition to obtain this result.
For example, the dual - sequences with strictly negative values only - would also work.

In practice, one most commonly deals with (regular) continued fractions, which satisfy the
positivity criterion required here. The analogous result for them
(see `ContinuedFractions.convergents_eq_convergents`) hence follows directly from this theorem.
-/
theorem convergents_eq_convergents' [LinearOrderedField K]
    (s_pos : ∀ {gp : Pair K} {m : ℕ}, m < n → g.s.get? m = some gp → 0 < gp.a ∧ 0 < gp.b) :
    g.convergents n = g.convergents' n := by
  induction' n with n IH generalizing g
  case zero => simp
  case succ =>
    let g' := squashFGCF g n
    -- first replace the rhs with the squashed computation
    suffices g.convergents (n + 1) = g'.convergents' n by
      rwa [succ_nth_convergent'_eq_squashFGCF_nth_convergent']
    cases' Decidable.em (TerminatedAt g n) with terminated_at_n not_terminated_at_n
    · have g'_eq_g : g' = g := squashFGCF_eq_self_of_terminated terminated_at_n
      rw [convergents_stable_of_terminated n.le_succ terminated_at_n, g'_eq_g, IH _]
      intro _ _ m_lt_n s_mth_eq
      exact s_pos (Nat.lt.step m_lt_n) s_mth_eq
    · suffices g.convergents (n + 1) = g'.convergents n by
        -- invoke the IH for the squashed gcf
        rwa [← IH]
        intro gp' m m_lt_n s_mth_eq'
        -- case distinction on m + 1 = n or m + 1 < n
        cases' m_lt_n with n succ_m_lt_n
        · -- the difficult case at the squashed position: we first obtain the values from
          -- the sequence
          obtain ⟨gp_succ_m, s_succ_mth_eq⟩ : ∃ gp_succ_m, g.s.get? (m + 1) = some gp_succ_m
          exact Option.ne_none_iff_exists'.mp not_terminated_at_n
          obtain ⟨gp_m, mth_s_eq⟩ : ∃ gp_m, g.s.get? m = some gp_m
          exact g.s.ge_stable m.le_succ s_succ_mth_eq
          -- we then plug them into the recurrence
          suffices 0 < gp_m.a ∧ 0 < gp_m.b + gp_succ_m.a / gp_succ_m.b by
            have ot : g'.s.get? m = some ⟨gp_m.a, gp_m.b + gp_succ_m.a / gp_succ_m.b⟩ :=
              squashSeq_nth_of_not_terminated mth_s_eq s_succ_mth_eq
            have : gp' = ⟨gp_m.a, gp_m.b + gp_succ_m.a / gp_succ_m.b⟩ := by
              simp_all only [Option.some.injEq]
            rwa [this]
          have m_lt_n : m < m.succ := Nat.lt_succ_self m
          refine' ⟨(s_pos (Nat.lt.step m_lt_n) mth_s_eq).left, _⟩
          refine' add_pos (s_pos (Nat.lt.step m_lt_n) mth_s_eq).right _
          have : 0 < gp_succ_m.a ∧ 0 < gp_succ_m.b := s_pos (lt_add_one <| m + 1) s_succ_mth_eq
          exact div_pos this.left this.right
        · -- the easy case: before the squashed position, nothing changes
          refine' s_pos (Nat.lt.step <| Nat.lt.step succ_m_lt_n) _
          exact Eq.trans (squashFGCF_nth_of_lt succ_m_lt_n).symm s_mth_eq'
      -- now the result follows from the fact that the convergents coincide at the squashed position
      -- as established in `succ_nth_convergent_eq_squashFGCF_nth_convergent`.
      have : ∀ ⦃b⦄, g.partialDenominators.get? n = some b → b ≠ 0 := by
        intro b nth_partDenom_eq
        obtain ⟨gp, s_nth_eq, ⟨refl⟩⟩ : ∃ gp, g.s.get? n = some gp ∧ gp.b = b
        exact exists_s_b_of_partDenom nth_partDenom_eq
        exact (ne_of_lt (s_pos (lt_add_one n) s_nth_eq).right).symm
      exact succ_nth_convergent_eq_squashFGCF_nth_convergent @this
#align generalized_continued_fraction.convergents_eq_convergents' FGCF.convergents_eq_convergents'

/-- Shows that the recurrence relation (`convergents`) and direct evaluation (`convergents'`) of a
(regular) continued fraction coincide. -/
theorem convergents_eq_convergents'_of_isContinuedFraction [LinearOrderedField K]
    (g : FGCF K) [g.IsContinuedFraction] :
    g.convergents = g.convergents' := by
  ext n
  apply convergents_eq_convergents'
  intro gp m _ s_nth_eq
  exact ⟨zero_lt_one.trans_le
    (IsSimpleContinuedFraction.partNum_eq_one (partNum_eq_s_a s_nth_eq)).symm.le,
    IsContinuedFraction.zero_lt_partDenom <| partDenom_eq_s_b s_nth_eq⟩
#align continued_fraction.convergents_eq_convergents' FGCF.convergents_eq_convergents'_of_isContinuedFraction

end FGCF
