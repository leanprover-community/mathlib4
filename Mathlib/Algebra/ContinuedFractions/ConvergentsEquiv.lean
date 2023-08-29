/-
Copyright (c) 2020 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
import Mathlib.Algebra.ContinuedFractions.ContinuantsRecurrence
import Mathlib.Algebra.ContinuedFractions.TerminatedStable
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

#align_import algebra.continued_fractions.convergents_equiv from "leanprover-community/mathlib"@"a7e36e48519ab281320c4d192da6a7b348ce40ad"

/-!
# Equivalence of Recursive and Direct Computations of `GCF` Convergents

## Summary

We show the equivalence of two computations of convergents (recurrence relation (`convergents`) vs.
direct evaluation (`convergents'`)) for `GCF`s on linear ordered fields. We follow the proof from
[hardy2008introduction], Chapter 10. Here's a sketch:

Let `c` be a continued fraction `[h; (a₀, b₀), (a₁, b₁), (a₂, b₂),...]`, visually:
$$
  c = h + \dfrac{a_0}
                {b_0 + \dfrac{a_1}
                             {b_1 + \dfrac{a_2}
                                          {b_2 + \dfrac{a_3}
                                                       {b_3 + \dots}}}}
$$
One can compute the convergents of `c` in two ways:
1. Directly evaluating the fraction described by `c` up to a given `n` (`convergents'`)
2. Using the recurrence (`convergents`):
  - `A₋₁ = 1,  A₀ = h,  Aₙ = bₙ₋₁ * Aₙ₋₁ + aₙ₋₁ * Aₙ₋₂`, and
  - `B₋₁ = 0,  B₀ = 1,  Bₙ = bₙ₋₁ * Bₙ₋₁ + aₙ₋₁ * Bₙ₋₂`.

To show the equivalence of the computations in the main theorem of this file
`convergents_eq_convergents'`, we proceed by induction. The case `n = 0` is trivial.

For `n + 1`, we first "squash" the `n + 1`th position of `c` into the `n`th position to obtain
another continued fraction
  `c' := [h; (a₀, b₀),..., (aₙ-₁, bₙ-₁), (aₙ, bₙ + aₙ₊₁ / bₙ₊₁), (aₙ₊₁, bₙ₊₁),...]`.
This squashing process is formalised in section `Squash`. Note that directly evaluating `c` up to
position `n + 1` is equal to evaluating `c'` up to `n`. This is shown in lemma
`succ_nth_convergent'_eq_squashGCF_nth_convergent'`.

By the inductive hypothesis, the two computations for the `n`th convergent of `c` coincide.
So all that is left to show is that the recurrence relation for `c` at `n + 1` and `c'` at
`n` coincide. This can be shown by another induction.
The corresponding lemma in this file is `succ_nth_convergent_eq_squashGCF_nth_convergent`.

## Main Theorems

- `GeneralizedContinuedFraction.convergents_eq_convergents'` shows the equivalence under a strict
positivity restriction on the sequence.
- `continued_fractions.convergents_eq_convergents'` shows the equivalence for (regular) continued
fractions.

## References

- https://en.wikipedia.org/wiki/Generalized_continued_fraction
- [*Hardy, GH and Wright, EM and Heath-Brown, Roger and Silverman, Joseph*][hardy2008introduction]

## Tags

fractions, recurrence, equivalence
-/


variable {K : Type*} {n : ℕ}

namespace GeneralizedContinuedFraction

variable {g : GeneralizedContinuedFraction K} {s : Stream'.Seq <| Pair K}

section Squash

/-!
We will show the equivalence of the computations by induction. To make the induction work, we need
to be able to *squash* the nth and (n + 1)th value of a sequence. This squashing itself and the
lemmas about it are not very interesting. As a reader, you hence might want to skip this section.
-/


section WithDivisionRing

variable [DivisionRing K]

/-- Given a sequence of `GCF.Pair`s `s = [(a₀, bₒ), (a₁, b₁), ...]`, `squashSeq s n`
combines `⟨aₙ, bₙ⟩` and `⟨aₙ₊₁, bₙ₊₁⟩` at position `n` to `⟨aₙ, bₙ + aₙ₊₁ / bₙ₊₁⟩`. For example,
`squashSeq s 0 = [(a₀, bₒ + a₁ / b₁), (a₁, b₁),...]`.
If `s.TerminatedAt (n + 1)`, then `squashSeq s n = s`.
-/
def squashSeq (s : Stream'.Seq <| Pair K) (n : ℕ) : Stream'.Seq (Pair K) :=
  match Prod.mk (s.get? n) (s.get? (n + 1)) with
  | ⟨some gp_n, some gp_succ_n⟩ =>
    Stream'.Seq.nats.zipWith
      -- return the squashed value at position `n`; otherwise, do nothing.
      (fun n' gp => if n' = n then ⟨gp_n.a, gp_n.b + gp_succ_n.a / gp_succ_n.b⟩ else gp) s
  | _ => s
#align generalized_continued_fraction.squash_seq GeneralizedContinuedFraction.squashSeq

/-! We now prove some simple lemmas about the squashed sequence -/


/-- If the sequence already terminated at position `n + 1`, nothing gets squashed. -/
theorem squashSeq_eq_self_of_terminated (terminated_at_succ_n : s.TerminatedAt (n + 1)) :
    squashSeq s n = s := by
  change s.get? (n + 1) = none at terminated_at_succ_n
  -- ⊢ squashSeq s n = s
  cases s_nth_eq : s.get? n <;> simp only [*, squashSeq]
  -- ⊢ squashSeq s n = s
                                -- 🎉 no goals
                                -- 🎉 no goals
#align generalized_continued_fraction.squash_seq_eq_self_of_terminated GeneralizedContinuedFraction.squashSeq_eq_self_of_terminated

/-- If the sequence has not terminated before position `n + 1`, the value at `n + 1` gets
squashed into position `n`. -/
theorem squashSeq_nth_of_not_terminated {gp_n gp_succ_n : Pair K} (s_nth_eq : s.get? n = some gp_n)
    (s_succ_nth_eq : s.get? (n + 1) = some gp_succ_n) :
    (squashSeq s n).get? n = some ⟨gp_n.a, gp_n.b + gp_succ_n.a / gp_succ_n.b⟩ := by
  simp [*, squashSeq]
  -- 🎉 no goals
#align generalized_continued_fraction.squash_seq_nth_of_not_terminated GeneralizedContinuedFraction.squashSeq_nth_of_not_terminated

/-- The values before the squashed position stay the same. -/
theorem squashSeq_nth_of_lt {m : ℕ} (m_lt_n : m < n) : (squashSeq s n).get? m = s.get? m := by
  cases s_succ_nth_eq : s.get? (n + 1)
  -- ⊢ Stream'.Seq.get? (squashSeq s n) m = Stream'.Seq.get? s m
  case none => rw [squashSeq_eq_self_of_terminated s_succ_nth_eq]
  -- ⊢ Stream'.Seq.get? (squashSeq s n) m = Stream'.Seq.get? s m
  -- 🎉 no goals
  case some =>
    obtain ⟨gp_n, s_nth_eq⟩ : ∃ gp_n, s.get? n = some gp_n
    exact s.ge_stable n.le_succ s_succ_nth_eq
    obtain ⟨gp_m, s_mth_eq⟩ : ∃ gp_m, s.get? m = some gp_m
    exact s.ge_stable (le_of_lt m_lt_n) s_nth_eq
    simp [*, squashSeq, m_lt_n.ne]
#align generalized_continued_fraction.squash_seq_nth_of_lt GeneralizedContinuedFraction.squashSeq_nth_of_lt

/-- Squashing at position `n + 1` and taking the tail is the same as squashing the tail of the
sequence at position `n`. -/
theorem squashSeq_succ_n_tail_eq_squashSeq_tail_n :
    (squashSeq s (n + 1)).tail = squashSeq s.tail n := by
  cases' s_succ_succ_nth_eq : s.get? (n + 2) with gp_succ_succ_n
  -- ⊢ Stream'.Seq.tail (squashSeq s (n + 1)) = squashSeq (Stream'.Seq.tail s) n
  case none =>
    cases s_succ_nth_eq : s.get? (n + 1) <;>
      simp only [squashSeq, Stream'.Seq.get?_tail, s_succ_nth_eq, s_succ_succ_nth_eq]
  case some =>
    obtain ⟨gp_succ_n, s_succ_nth_eq⟩ : ∃ gp_succ_n, s.get? (n + 1) = some gp_succ_n;
    exact s.ge_stable (n + 1).le_succ s_succ_succ_nth_eq
    -- apply extensionality with `m` and continue by cases `m = n`.
    ext1 m
    cases' Decidable.em (m = n) with m_eq_n m_ne_n
    · simp [*, squashSeq]
    · have : s.tail.get? m = s.get? (m + 1) := s.get?_tail m
      cases s_succ_mth_eq : s.get? (m + 1)
      all_goals have _ := this.trans s_succ_mth_eq
      · simp only [*, squashSeq, Stream'.Seq.get?_tail, Stream'.Seq.get?_zipWith,
          Option.map₂_none_right]
      · simp [*, squashSeq]
#align generalized_continued_fraction.squash_seq_succ_n_tail_eq_squash_seq_tail_n GeneralizedContinuedFraction.squashSeq_succ_n_tail_eq_squashSeq_tail_n

/-- The auxiliary function `convergents'Aux` returns the same value for a sequence and the
corresponding squashed sequence at the squashed position. -/
theorem succ_succ_nth_convergent'_aux_eq_succ_nth_convergent'_aux_squashSeq :
    convergents'Aux s (n + 2) = convergents'Aux (squashSeq s n) (n + 1) := by
  cases' s_succ_nth_eq : s.get? <| n + 1 with gp_succ_n
  -- ⊢ convergents'Aux s (n + 2) = convergents'Aux (squashSeq s n) (n + 1)
  case none =>
    rw [squashSeq_eq_self_of_terminated s_succ_nth_eq,
      convergents'Aux_stable_step_of_terminated s_succ_nth_eq]
  case some =>
    induction' n with m IH generalizing s gp_succ_n
    case zero =>
      obtain ⟨gp_head, s_head_eq⟩ : ∃ gp_head, s.head = some gp_head
      exact s.ge_stable zero_le_one s_succ_nth_eq
      have : (squashSeq s 0).head = some ⟨gp_head.a, gp_head.b + gp_succ_n.a / gp_succ_n.b⟩ :=
        squashSeq_nth_of_not_terminated s_head_eq s_succ_nth_eq
      simp_all [convergents'Aux, Stream'.Seq.head, Stream'.Seq.get?_tail]
    case succ =>
      obtain ⟨gp_head, s_head_eq⟩ : ∃ gp_head, s.head = some gp_head
      exact s.ge_stable (m + 2).zero_le s_succ_nth_eq
      suffices
        gp_head.a / (gp_head.b + convergents'Aux s.tail (m + 2)) =
          convergents'Aux (squashSeq s (m + 1)) (m + 2)
        by simpa only [convergents'Aux, s_head_eq]
      have : convergents'Aux s.tail (m + 2) = convergents'Aux (squashSeq s.tail m) (m + 1) := by
        refine' IH gp_succ_n _
        simpa [Stream'.Seq.get?_tail] using s_succ_nth_eq
      have : (squashSeq s (m + 1)).head = some gp_head :=
        (squashSeq_nth_of_lt m.succ_pos).trans s_head_eq
      simp_all [convergents'Aux, squashSeq_succ_n_tail_eq_squashSeq_tail_n]
#align generalized_continued_fraction.succ_succ_nth_convergent'_aux_eq_succ_nth_convergent'_aux_squash_seq GeneralizedContinuedFraction.succ_succ_nth_convergent'_aux_eq_succ_nth_convergent'_aux_squashSeq

/-! Let us now lift the squashing operation to gcfs. -/


/-- Given a gcf `g = [h; (a₀, bₒ), (a₁, b₁), ...]`, we have
- `squashGCF g 0 = [h + a₀ / b₀); (a₀, bₒ), ...]`,
- `squashGCF g (n + 1) = ⟨g.h, squashSeq g.s n⟩`
-/
def squashGCF (g : GeneralizedContinuedFraction K) : ℕ → GeneralizedContinuedFraction K
  | 0 =>
    match g.s.get? 0 with
    | none => g
    | some gp => ⟨g.h + gp.a / gp.b, g.s⟩
  | n + 1 => ⟨g.h, squashSeq g.s n⟩
#align generalized_continued_fraction.squash_gcf GeneralizedContinuedFraction.squashGCF

/-! Again, we derive some simple lemmas that are not really of interest. This time for the
squashed gcf. -/


/-- If the gcf already terminated at position `n`, nothing gets squashed. -/
theorem squashGCF_eq_self_of_terminated (terminated_at_n : TerminatedAt g n) :
    squashGCF g n = g := by
  cases n
  -- ⊢ squashGCF g Nat.zero = g
  case zero =>
    change g.s.get? 0 = none at terminated_at_n
    simp only [convergents', squashGCF, convergents'Aux, terminated_at_n]
  case succ =>
    cases g
    simp only [squashGCF, mk.injEq, true_and]
    exact squashSeq_eq_self_of_terminated terminated_at_n
#align generalized_continued_fraction.squash_gcf_eq_self_of_terminated GeneralizedContinuedFraction.squashGCF_eq_self_of_terminated

/-- The values before the squashed position stay the same. -/
theorem squashGCF_nth_of_lt {m : ℕ} (m_lt_n : m < n) :
    (squashGCF g (n + 1)).s.get? m = g.s.get? m := by
  simp only [squashGCF, squashSeq_nth_of_lt m_lt_n, Nat.add_eq, add_zero]
  -- 🎉 no goals
#align generalized_continued_fraction.squash_gcf_nth_of_lt GeneralizedContinuedFraction.squashGCF_nth_of_lt

/-- `convergents'` returns the same value for a gcf and the corresponding squashed gcf at the
squashed position. -/
theorem succ_nth_convergent'_eq_squashGCF_nth_convergent' :
    g.convergents' (n + 1) = (squashGCF g n).convergents' n := by
  cases n
  -- ⊢ convergents' g (Nat.zero + 1) = convergents' (squashGCF g Nat.zero) Nat.zero
  case zero =>
    cases g_s_head_eq : g.s.get? 0 <;>
      simp [g_s_head_eq, squashGCF, convergents', convergents'Aux, Stream'.Seq.head]
  case succ =>
    simp only [succ_succ_nth_convergent'_aux_eq_succ_nth_convergent'_aux_squashSeq, convergents',
      squashGCF]
#align generalized_continued_fraction.succ_nth_convergent'_eq_squash_gcf_nth_convergent' GeneralizedContinuedFraction.succ_nth_convergent'_eq_squashGCF_nth_convergent'

/-- The auxiliary continuants before the squashed position stay the same. -/
theorem continuantsAux_eq_continuantsAux_squashGCF_of_le {m : ℕ} :
    m ≤ n → continuantsAux g m = (squashGCF g n).continuantsAux m :=
  Nat.strong_induction_on m
    (by
      clear m
      -- ⊢ ∀ (n_1 : ℕ), (∀ (m : ℕ), m < n_1 → m ≤ n → continuantsAux g m = continuantsA …
      intro m IH m_le_n
      -- ⊢ continuantsAux g m = continuantsAux (squashGCF g n) m
      cases' m with m'
      -- ⊢ continuantsAux g Nat.zero = continuantsAux (squashGCF g n) Nat.zero
      · rfl
        -- 🎉 no goals
      · cases' n with n'
        -- ⊢ continuantsAux g (Nat.succ m') = continuantsAux (squashGCF g Nat.zero) (Nat. …
        · exact (m'.not_succ_le_zero m_le_n).elim
          -- 🎉 no goals
        -- 1 ≰ 0
        · cases' m' with m''
          -- ⊢ continuantsAux g (Nat.succ Nat.zero) = continuantsAux (squashGCF g (Nat.succ …
          · rfl
            -- 🎉 no goals
          · -- get some inequalities to instantiate the IH for m'' and m'' + 1
            have m'_lt_n : m'' + 1 < n' + 1 := m_le_n
            -- ⊢ continuantsAux g (Nat.succ (Nat.succ m'')) = continuantsAux (squashGCF g (Na …
            have succ_m''th_conts_aux_eq := IH (m'' + 1) (lt_add_one (m'' + 1)) m'_lt_n.le
            -- ⊢ continuantsAux g (Nat.succ (Nat.succ m'')) = continuantsAux (squashGCF g (Na …
            have : m'' < m'' + 2 := lt_add_of_pos_right m'' zero_lt_two
            -- ⊢ continuantsAux g (Nat.succ (Nat.succ m'')) = continuantsAux (squashGCF g (Na …
            have m''th_conts_aux_eq := IH m'' this (le_trans this.le m_le_n)
            -- ⊢ continuantsAux g (Nat.succ (Nat.succ m'')) = continuantsAux (squashGCF g (Na …
            have : (squashGCF g (n' + 1)).s.get? m'' = g.s.get? m'' :=
              squashGCF_nth_of_lt (Nat.succ_lt_succ_iff.mp m'_lt_n)
            simp [continuantsAux, succ_m''th_conts_aux_eq, m''th_conts_aux_eq, this])
            -- 🎉 no goals
#align generalized_continued_fraction.continuants_aux_eq_continuants_aux_squash_gcf_of_le GeneralizedContinuedFraction.continuantsAux_eq_continuantsAux_squashGCF_of_le

end WithDivisionRing

/-- The convergents coincide in the expected way at the squashed position if the partial denominator
at the squashed position is not zero. -/
theorem succ_nth_convergent_eq_squashGCF_nth_convergent [Field K]
    (nth_part_denom_ne_zero : ∀ {b : K}, g.partialDenominators.get? n = some b → b ≠ 0) :
    g.convergents (n + 1) = (squashGCF g n).convergents n := by
  cases' Decidable.em (g.TerminatedAt n) with terminated_at_n not_terminated_at_n
  -- ⊢ convergents g (n + 1) = convergents (squashGCF g n) n
  · have : squashGCF g n = g := squashGCF_eq_self_of_terminated terminated_at_n
    -- ⊢ convergents g (n + 1) = convergents (squashGCF g n) n
    simp only [this, convergents_stable_of_terminated n.le_succ terminated_at_n]
    -- 🎉 no goals
  · obtain ⟨⟨a, b⟩, s_nth_eq⟩ : ∃ gp_n, g.s.get? n = some gp_n
    -- ⊢ ∃ gp_n, Stream'.Seq.get? g.s n = some gp_n
    exact Option.ne_none_iff_exists'.mp not_terminated_at_n
    -- ⊢ convergents g (n + 1) = convergents (squashGCF g n) n
    have b_ne_zero : b ≠ 0 := nth_part_denom_ne_zero (part_denom_eq_s_b s_nth_eq)
    -- ⊢ convergents g (n + 1) = convergents (squashGCF g n) n
    cases' n with n'
    -- ⊢ convergents g (Nat.zero + 1) = convergents (squashGCF g Nat.zero) Nat.zero
    case zero =>
      suffices (b * g.h + a) / b = g.h + a / b by
        simpa [squashGCF, s_nth_eq, convergent_eq_conts_a_div_conts_b,
          continuants_recurrenceAux s_nth_eq zeroth_continuant_aux_eq_one_zero
            first_continuant_aux_eq_h_one]
      calc
        (b * g.h + a) / b = b * g.h / b + a / b := by ring
        -- requires `Field`, not `DivisionRing`
        _ = g.h + a / b := by rw [mul_div_cancel_left _ b_ne_zero]
    case succ =>
      obtain ⟨⟨pa, pb⟩, s_n'th_eq⟩ : ∃ gp_n', g.s.get? n' = some gp_n' :=
        g.s.ge_stable n'.le_succ s_nth_eq
      -- Notations
      let g' := squashGCF g (n' + 1)
      set pred_conts := g.continuantsAux (n' + 1) with succ_n'th_conts_aux_eq
      set ppred_conts := g.continuantsAux n' with n'th_conts_aux_eq
      let pA := pred_conts.a
      let pB := pred_conts.b
      let ppA := ppred_conts.a
      let ppB := ppred_conts.b
      set pred_conts' := g'.continuantsAux (n' + 1) with succ_n'th_conts_aux_eq'
      set ppred_conts' := g'.continuantsAux n' with n'th_conts_aux_eq'
      let pA' := pred_conts'.a
      let pB' := pred_conts'.b
      let ppA' := ppred_conts'.a
      let ppB' := ppred_conts'.b
      -- first compute the convergent of the squashed gcf
      have : g'.convergents (n' + 1) =
          ((pb + a / b) * pA' + pa * ppA') / ((pb + a / b) * pB' + pa * ppB') := by
        have : g'.s.get? n' = some ⟨pa, pb + a / b⟩ :=
          squashSeq_nth_of_not_terminated s_n'th_eq s_nth_eq
        rw [convergent_eq_conts_a_div_conts_b,
          continuants_recurrenceAux this n'th_conts_aux_eq'.symm succ_n'th_conts_aux_eq'.symm]
      rw [this]
      -- then compute the convergent of the original gcf by recursively unfolding the continuants
      -- computation twice
      have : g.convergents (n' + 2) =
          (b * (pb * pA + pa * ppA) + a * pA) / (b * (pb * pB + pa * ppB) + a * pB) := by
        -- use the recurrence once
        have : g.continuantsAux (n' + 2) = ⟨pb * pA + pa * ppA, pb * pB + pa * ppB⟩ :=
          continuantsAux_recurrence s_n'th_eq n'th_conts_aux_eq.symm succ_n'th_conts_aux_eq.symm
        -- and a second time
        rw [convergent_eq_conts_a_div_conts_b,
          continuants_recurrenceAux s_nth_eq succ_n'th_conts_aux_eq.symm this]
      rw [this]
      suffices
        ((pb + a / b) * pA + pa * ppA) / ((pb + a / b) * pB + pa * ppB) =
          (b * (pb * pA + pa * ppA) + a * pA) / (b * (pb * pB + pa * ppB) + a * pB) by
        obtain ⟨eq1, eq2, eq3, eq4⟩ : pA' = pA ∧ pB' = pB ∧ ppA' = ppA ∧ ppB' = ppB := by
          simp [*, (continuantsAux_eq_continuantsAux_squashGCF_of_le <| le_refl <| n' + 1).symm,
            (continuantsAux_eq_continuantsAux_squashGCF_of_le n'.le_succ).symm]
        symm
        simpa only [eq1, eq2, eq3, eq4, mul_div_cancel _ b_ne_zero]
      field_simp
      congr 1 <;> ring
#align generalized_continued_fraction.succ_nth_convergent_eq_squash_gcf_nth_convergent GeneralizedContinuedFraction.succ_nth_convergent_eq_squashGCF_nth_convergent

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
  -- ⊢ convergents g Nat.zero = convergents' g Nat.zero
  case zero => simp
  -- ⊢ convergents g (Nat.succ n) = convergents' g (Nat.succ n)
  -- 🎉 no goals
  case succ =>
    let g' := squashGCF g n
    -- first replace the rhs with the squashed computation
    suffices g.convergents (n + 1) = g'.convergents' n by
      rwa [succ_nth_convergent'_eq_squashGCF_nth_convergent']
    cases' Decidable.em (TerminatedAt g n) with terminated_at_n not_terminated_at_n
    · have g'_eq_g : g' = g := squashGCF_eq_self_of_terminated terminated_at_n
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
          exact Eq.trans (squashGCF_nth_of_lt succ_m_lt_n).symm s_mth_eq'
      -- now the result follows from the fact that the convergents coincide at the squashed position
      -- as established in `succ_nth_convergent_eq_squashGCF_nth_convergent`.
      have : ∀ ⦃b⦄, g.partialDenominators.get? n = some b → b ≠ 0 := by
        intro b nth_part_denom_eq
        obtain ⟨gp, s_nth_eq, ⟨refl⟩⟩ : ∃ gp, g.s.get? n = some gp ∧ gp.b = b
        exact exists_s_b_of_part_denom nth_part_denom_eq
        exact (ne_of_lt (s_pos (lt_add_one n) s_nth_eq).right).symm
      exact succ_nth_convergent_eq_squashGCF_nth_convergent @this
#align generalized_continued_fraction.convergents_eq_convergents' GeneralizedContinuedFraction.convergents_eq_convergents'

end GeneralizedContinuedFraction

open GeneralizedContinuedFraction

namespace ContinuedFraction

/-- Shows that the recurrence relation (`convergents`) and direct evaluation (`convergents'`) of a
(regular) continued fraction coincide. -/
nonrec theorem convergents_eq_convergents' [LinearOrderedField K] {c : ContinuedFraction K} :
    (↑c : GeneralizedContinuedFraction K).convergents =
    (↑c : GeneralizedContinuedFraction K).convergents' := by
  ext n
  -- ⊢ Stream'.nth (convergents ↑↑c) n = Stream'.nth (convergents' ↑↑c) n
  apply convergents_eq_convergents'
  -- ⊢ ∀ {gp : Pair K} {m : ℕ}, m < n → Stream'.Seq.get? (↑↑c).s m = some gp → 0 <  …
  intro gp m _ s_nth_eq
  -- ⊢ 0 < gp.a ∧ 0 < gp.b
  exact ⟨zero_lt_one.trans_le ((c : SimpleContinuedFraction K).property m gp.a
    (part_num_eq_s_a s_nth_eq)).symm.le, c.property m gp.b <| part_denom_eq_s_b s_nth_eq⟩
#align continued_fraction.convergents_eq_convergents' ContinuedFraction.convergents_eq_convergents'

end ContinuedFraction
