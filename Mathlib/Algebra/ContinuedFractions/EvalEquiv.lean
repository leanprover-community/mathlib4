/-
Copyright (c) 2020 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
import Mathlib.Algebra.ContinuedFractions.ContinuantRecurrence
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
 - `f' := some CF[h; (a₀, b₀),..., (aₙ₋₂, bₙ₋₂), (aₙ₋₁, bₙ₋₁ + aₙ / bₙ)]` if `bₙ ≠ 0`
 - `f' := some CF[h; (a₀, b₀),..., (aₙ₋₂, bₙ₋₂)]` if `bₙ = 0` and `aₙ ≠ 0`
 - `f' := none` if `bₙ = 0` and `aₙ = 0`
This squashing process is formalised in section `Squash`. Note that directly evaluating `f` up to
position `n + 1` is equal to evaluating `f'` up to `n`. This is shown in lemma
`bind_squash?_evalF?_eq_evalF?_mk_concat`.

By the inductive hypothesis, the two computations for the `n`th convergent of `f` coincide.
So all that is left to show is that the recurrence relation for `f` at `n + 1` and `f'` at
`n` coincide. This can be shown by another induction.
The corresponding lemma in this file is `bind_squash?_eval?_eq_eval?_mk_concat`.

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

variable {K : Type*}

section Squash

/-!
We will show the equivalence of the computations by induction.
-/


section WithDivisionRing

variable [DivisionRing K] [DecidableEq K]

/-- Given a fgcf `f := CF[h; (a₀, bₒ), ..., (aₙ₋₁, bₙ₋₁)]` and `p := (aₙ, bₙ)`, we have
- `squash? f = some CF[h + aₙ / bₙ]` if `n = 0` and `bₙ ≠ 0`,
- `squash? f = none` if `n = 0` and `bₙ = 0`,
- `squash? f = some ⟨h, l'⟩` if `n ≠ 0` and `squash.go f.l _ p = some l'`.
- `squash? f = none` if `n ≠ 0` and `squash.go f.l _ p = none`.
-/
def squash? (f : FGCF K) (p : K × K) : Option (FGCF K) :=
  if hl : f.l = [] then
    if p.2 = 0 then
      none
    else
      some ⟨f.h + p.1 / p.2, []⟩
  else
    (go f.l hl p).map (fun l' => ⟨f.h, l'⟩)
where
  /-- Given a nonempty list of `K × K`s `l = [(a₀, bₒ), ..., (aₙ, bₙ)]` and `p := (aₙ₊₁, bₙ₊₁)`,
  `squash.go l _ p` combines `(aₙ, bₙ)` and `(aₙ₊₁, bₙ₊₁)` at last position to
  `(aₙ, bₙ + aₙ₊₁ / bₙ₊₁)`.
  -/
  go (l : List (K × K)) (hl : l ≠ []) (p : K × K) : Option (List (K × K)) :=
    if p.2 = 0 then
      if p.1 = 0 then
        none
      else
        some (dropLast l)
    else
      some (dropLast l ++ [((getLast l hl).1, (getLast l hl).2 + p.1 / p.2)])
#align generalized_continued_fraction.squash_gcf FGCF.squash?ₓ
#align generalized_continued_fraction.squash_seq FGCF.squash?.goₓ

theorem length_lt_length_add_one_of_mk_mem_squash? {h h' : K} {l l' : List (K × K)} {p : K × K}
    (hl' : ⟨h', l'⟩ ∈ squash? ⟨h, l⟩ p) : l'.length < l.length + 1 := by
  by_cases hl : l = []
  · subst hl
    by_cases hps : p.2 = 0 <;> simp [squash?, hps] at hl'
    rcases hl' with ⟨-, rfl⟩; simp
  · by_cases hps : p.2 = 0
    · by_cases hpf : p.1 = 0 <;> simp [squash?, squash?.go, hl, hps, hpf] at hl'
      rcases hl' with ⟨-, rfl⟩
      apply lt_of_le_of_lt (b := l.length) <;> simp
    · simp [squash?, squash?.go, hl, hps] at hl'
      rcases hl' with ⟨-, rfl⟩
      simp [Nat.sub_one, Nat.pred_lt' (List.length_pos_of_ne_nil hl)]

#noalign generalized_continued_fraction.squash_seq_eq_self_of_terminated

#noalign generalized_continued_fraction.squash_seq_nth_of_not_terminated

#noalign generalized_continued_fraction.squash_seq_nth_of_lt

#noalign generalized_continued_fraction.squash_seq_succ_n_tail_eq_squash_seq_tail_n

/-- The auxiliary function `evalF?.loop` returns the same value for a list and the
corresponding squashed list. -/
theorem bind_squash?_go_evalF?_loop_eq_evalF?_mk_concat
    (l : List (K × K)) (hl : l ≠ []) (p : K × K) :
    (squash?.go l hl p).bind evalF?.loop = evalF?.loop (l ++ [p]) := by
  rcases Or.resolve_left (eq_nil_or_concat l) hl with ⟨l₂, p', rfl⟩
  induction l₂ with
  | nil =>
    by_cases hps : p.2 = 0
    · by_cases hpf : p.1 = 0 <;> simp [squash?.go, hps, hpf]
    · simp [squash?.go, hps]
  | cons p'' l' hl' =>
    by_cases hps : p.2 = 0
    · by_cases hpf : p.1 = 0 <;> simp [squash?.go, hps, hpf] at hl' <;>
        simp [squash?.go, ← hl', hps, hpf]
    · simp [squash?.go, hps] at hl'; simp [squash?.go, ← hl', hps]
#align generalized_continued_fraction.succ_succ_nth_convergent'_aux_eq_succ_nth_convergent'_aux_squash_seq FGCF.bind_squash?_go_evalF?_loop_eq_evalF?_mk_concatₓ

#noalign generalized_continued_fraction.squash_gcf_eq_self_of_terminated

#noalign generalized_continued_fraction.squash_gcf_nth_of_lt

/-- `evalF?` returns the same value for a fgcf and the corresponding squashed fgcf. -/
theorem bind_squash?_evalF?_eq_evalF?_mk_concat (h : K) (l : List (K × K)) (p : K × K) :
    (squash? ⟨h, l⟩ p).bind evalF? = evalF? ⟨h, l ++ [p]⟩ := by
  by_cases hl : l = []
  · by_cases hps : p.2 = 0
    · by_cases hpf : p.1 = 0 <;> simp [squash?, evalF?, hl, hps, hpf]
    · simp [squash?, evalF?, hl, hps]
  · simp [squash?, evalF?, hl,
      ← bind_squash?_go_evalF?_loop_eq_evalF?_mk_concat, Option.map_eq_bind,
      Option.bind_assoc, Function.comp]
#align generalized_continued_fraction.succ_nth_convergent'_eq_squash_gcf_nth_convergent' FGCF.bind_squash?_evalF?_eq_evalF?_mk_concatₓ

#noalign generalized_continued_fraction.continuants_aux_eq_continuants_aux_squash_gcf_of_le

end WithDivisionRing

/-- `eval?` returns the same value for a fgcf and the corresponding squashed fgcf. -/
theorem bind_squash?_eval?_eq_eval?_mk_concat [Field K] [DecidableEq K] (h : K) (l : List (K × K))
    (p : K × K) :
    (squash? ⟨h, l⟩ p).bind eval? = eval? ⟨h, l ++ [p]⟩ := by
  rcases eq_nil_or_concat l with rfl | ⟨l', p', rfl⟩
  · by_cases hps : p.2 = 0 <;> simp [eval?, squash?, hps]
    field_simp; ring
  · by_cases hps : p.2 = 0
    · by_cases hpf : p.1 = 0
      · simp [eval?, squash?, squash?.go, hps, hpf]
      · by_cases hd : denominator ⟨h, l'⟩ = 0 <;> simp [eval?, squash?, squash?.go, hps, hpf, hd]
        field_simp; ring
    · simp [eval?, squash?, squash?.go, hps]
      rcases eq_nil_or_concat l' with rfl | ⟨l'', p'', rfl⟩ <;> simp <;> field_simp <;> ring_nf
#align generalized_continued_fraction.succ_nth_convergent_eq_squash_gcf_nth_convergent FGCF.bind_squash?_eval?_eq_eval?_mk_concatₓ

end Squash

/-- Shows that the recurrence relation (`eval?`) and direct evaluation (`evalF?`) of the
fgcf coincide including their definability.
-/
theorem eval?_eq_evalF? [Field K] [DecidableEq K] (f : FGCF K) :
    eval? f = evalF? f := by
  rcases f with ⟨h, l⟩
  induction' hn : l.length using Nat.strongInductionOn with ll hll generalizing h l
  subst hn
  rcases eq_nil_or_concat l with rfl | ⟨l', p, rfl⟩
  · simp
  · rw [← bind_squash?_evalF?_eq_evalF?_mk_concat, ← bind_squash?_eval?_eq_eval?_mk_concat]
    apply Option.bind_congr; rintro ⟨h', l''⟩ hl''
    refine hll l''.length ?_ h' l'' rfl
    simp [length_lt_length_add_one_of_mk_mem_squash? hl'']
#align generalized_continued_fraction.convergents_eq_convergents' FGCF.eval?_eq_evalF?ₓ

#align continued_fraction.convergents_eq_convergents' FGCF.eval?_eq_evalF?ₓ

end FGCF
