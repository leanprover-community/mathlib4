/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Order.Partition.Equipartition

/-!
# Numerical bounds for Szemerédi Regularity Lemma

This file gathers the numerical facts required by the proof of Szemerédi's regularity lemma.

This entire file is internal to the proof of Szemerédi Regularity Lemma.

## Main declarations

* `SzemerediRegularity.stepBound`: During the inductive step, a partition of size `n` is blown to
  size at most `stepBound n`.
* `SzemerediRegularity.initialBound`: The size of the partition we start the induction with.
* `SzemerediRegularity.bound`: The upper bound on the size of the partition produced by our version
  of Szemerédi's regularity lemma.

## References

[Yaël Dillies, Bhavik Mehta, *Formalising Szemerédi’s Regularity Lemma in Lean*][srl_itp]
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section


open Finset Fintype Function Real

namespace SzemerediRegularity

/-- Auxiliary function for Szemerédi's regularity lemma. Blowing up a partition of size `n` during
the induction results in a partition of size at most `stepBound n`. -/
def stepBound (n : ℕ) : ℕ :=
  n * 4 ^ n

theorem le_stepBound : id ≤ stepBound := fun n =>
  Nat.le_mul_of_pos_right _ <| pow_pos (by simp) n

theorem stepBound_mono : Monotone stepBound := fun _ _ h => by unfold stepBound; gcongr; decide

theorem stepBound_pos_iff {n : ℕ} : 0 < stepBound n ↔ 0 < n :=
  mul_pos_iff_of_pos_right <| by positivity

alias ⟨_, stepBound_pos⟩ := stepBound_pos_iff

@[norm_cast] lemma coe_stepBound {α : Type*} [Semiring α] (n : ℕ) :
    (stepBound n : α) = n * 4 ^ n := by unfold stepBound; norm_cast

end SzemerediRegularity

open SzemerediRegularity

variable {α : Type*} [DecidableEq α] [Fintype α] {P : Finpartition (univ : Finset α)}
  {u : Finset α} {ε : ℝ}

local notation3 "m" => (card α / stepBound #P.parts : ℕ)

local notation3 "a" => (card α / #P.parts - m * 4 ^ #P.parts : ℕ)

namespace SzemerediRegularity.Positivity

set_option backward.privateInPublic true in
private theorem eps_pos {ε : ℝ} {n : ℕ} (h : 100 ≤ (4 : ℝ) ^ n * ε ^ 5) : 0 < ε :=
  (Odd.pow_pos_iff (by decide)).mp
    (pos_of_mul_pos_right ((show 0 < (100 : ℝ) by simp).trans_le h) (by positivity))

set_option backward.privateInPublic true in
private theorem m_pos [Nonempty α] (hPα : #P.parts * 16 ^ #P.parts ≤ card α) : 0 < m :=
  Nat.div_pos (hPα.trans' <| by unfold stepBound; gcongr; simp) <|
    stepBound_pos (P.parts_nonempty <| univ_nonempty.ne_empty).card_pos

/-- Local extension for the `positivity` tactic: A few facts that are needed many times for the
proof of Szemerédi's regularity lemma. -/
scoped macro "sz_positivity" : tactic =>
  `(tactic|
      { try have := m_pos ‹_›
        try have := eps_pos ‹_›
        positivity })

-- Original meta code
/- meta def positivity_szemeredi_regularity : expr → tactic strictness
| `(%%n / step_bound (finpartition.parts %%P).card) := do
    p ← to_expr
      ``((finpartition.parts %%P).card * 16^(finpartition.parts %%P).card ≤ %%n)
      >>= find_assumption,
    positive <$> mk_app ``m_pos [p]
| ε := do
    typ ← infer_type ε,
    unify typ `(ℝ),
    p ← to_expr ``(100 ≤ 4 ^ _ * %%ε ^ 5) >>= find_assumption,
    positive <$> mk_app ``eps_pos [p] -/

end SzemerediRegularity.Positivity

namespace SzemerediRegularity

open scoped SzemerediRegularity.Positivity

theorem m_pos [Nonempty α] (hPα : #P.parts * 16 ^ #P.parts ≤ card α) : 0 < m := by
  sz_positivity

theorem coe_m_add_one_pos : 0 < (m : ℝ) + 1 := by positivity

theorem one_le_m_coe [Nonempty α] (hPα : #P.parts * 16 ^ #P.parts ≤ card α) : (1 : ℝ) ≤ m :=
  Nat.one_le_cast.2 <| m_pos hPα

theorem eps_pow_five_pos (hPε : 100 ≤ (4 : ℝ) ^ #P.parts * ε ^ 5) : ↑0 < ε ^ 5 :=
  pos_of_mul_pos_right ((by simp : (0 : ℝ) < 100).trans_le hPε) <| by positivity

theorem eps_pos (hPε : 100 ≤ (4 : ℝ) ^ #P.parts * ε ^ 5) : 0 < ε :=
  (Odd.pow_pos_iff (by decide)).mp (eps_pow_five_pos hPε)

theorem hundred_div_ε_pow_five_le_m [Nonempty α] (hPα : #P.parts * 16 ^ #P.parts ≤ card α)
    (hPε : 100 ≤ (4 : ℝ) ^ #P.parts * ε ^ 5) : 100 / ε ^ 5 ≤ m :=
  (div_le_of_le_mul₀ (eps_pow_five_pos hPε).le (by positivity) hPε).trans <| by
    norm_cast
    rwa [Nat.le_div_iff_mul_le (stepBound_pos (P.parts_nonempty <|
      univ_nonempty.ne_empty).card_pos), stepBound, mul_left_comm, ← mul_pow]

theorem hundred_le_m [Nonempty α] (hPα : #P.parts * 16 ^ #P.parts ≤ card α)
    (hPε : 100 ≤ (4 : ℝ) ^ #P.parts * ε ^ 5) (hε : ε ≤ 1) : 100 ≤ m :=
  mod_cast
    (hundred_div_ε_pow_five_le_m hPα hPε).trans'
      (le_div_self (by simp) (by sz_positivity) <| pow_le_one₀ (by sz_positivity) hε)

theorem a_add_one_le_four_pow_parts_card : a + 1 ≤ 4 ^ #P.parts := by
  have h : 1 ≤ 4 ^ #P.parts := one_le_pow₀ (by simp)
  rw [stepBound, ← Nat.div_div_eq_div_mul]
  conv_rhs => rw [← Nat.sub_add_cancel h]
  rw [add_le_add_iff_right, tsub_le_iff_left, ← Nat.add_sub_assoc h]
  exact Nat.le_sub_one_of_lt (Nat.lt_div_mul_add h)

theorem card_aux₁ (hucard : #u = m * 4 ^ #P.parts + a) :
    (4 ^ #P.parts - a) * m + a * (m + 1) = #u := by
  rw [hucard, mul_add, mul_one, ← add_assoc, ← add_mul,
    Nat.sub_add_cancel ((Nat.le_succ _).trans a_add_one_le_four_pow_parts_card), mul_comm]

theorem card_aux₂ (hP : P.IsEquipartition) (hu : u ∈ P.parts) (hucard : #u ≠ m * 4 ^ #P.parts + a) :
    (4 ^ #P.parts - (a + 1)) * m + (a + 1) * (m + 1) = #u := by
  have : m * 4 ^ #P.parts ≤ card α / #P.parts := by
    rw [stepBound, ← Nat.div_div_eq_div_mul]
    exact Nat.div_mul_le_self _ _
  rw [Nat.add_sub_of_le this] at hucard
  rw [(hP.card_parts_eq_average hu).resolve_left hucard, mul_add, mul_one, ← add_assoc, ← add_mul,
    Nat.sub_add_cancel a_add_one_le_four_pow_parts_card, ← add_assoc, mul_comm,
    Nat.add_sub_of_le this, card_univ]

theorem pow_mul_m_le_card_part (hP : P.IsEquipartition) (hu : u ∈ P.parts) :
    (4 : ℝ) ^ #P.parts * m ≤ #u := by
  norm_cast
  rw [stepBound, ← Nat.div_div_eq_div_mul]
  exact (Nat.mul_div_le _ _).trans (hP.average_le_card_part hu)

variable (P ε) (l : ℕ)

/-- Auxiliary function for Szemerédi's regularity lemma. The size of the partition by which we start
blowing. -/
noncomputable def initialBound : ℕ :=
  max 7 <| max l <| ⌊log (100 / ε ^ 5) / log 4⌋₊ + 1

theorem le_initialBound : l ≤ initialBound ε l :=
  (le_max_left _ _).trans <| le_max_right _ _

theorem seven_le_initialBound : 7 ≤ initialBound ε l :=
  le_max_left _ _

theorem initialBound_pos : 0 < initialBound ε l :=
  Nat.succ_pos'.trans_le <| seven_le_initialBound _ _

theorem hundred_lt_pow_initialBound_mul {ε : ℝ} (hε : 0 < ε) (l : ℕ) :
    100 < ↑4 ^ initialBound ε l * ε ^ 5 := by
  rw [← rpow_natCast 4, ← div_lt_iff₀ (pow_pos hε 5), lt_rpow_iff_log_lt _ zero_lt_four, ←
    div_lt_iff₀, initialBound, Nat.cast_max, Nat.cast_max]
  · push_cast
    exact lt_max_of_lt_right (lt_max_of_lt_right <| Nat.lt_floor_add_one _)
  · exact log_pos (by simp)
  · exact div_pos (by simp) (pow_pos hε 5)

/-- An explicit bound on the size of the equipartition whose existence is given by Szemerédi's
regularity lemma. -/
noncomputable def bound : ℕ :=
  (stepBound^[⌊4 / ε ^ 5⌋₊] <| initialBound ε l) *
    16 ^ (stepBound^[⌊4 / ε ^ 5⌋₊] <| initialBound ε l)

theorem initialBound_le_bound : initialBound ε l ≤ bound ε l :=
  (id_le_iterate_of_id_le le_stepBound _ _).trans <| Nat.le_mul_of_pos_right _ <| by positivity

theorem le_bound : l ≤ bound ε l :=
  (le_initialBound ε l).trans <| initialBound_le_bound ε l

theorem bound_pos : 0 < bound ε l :=
  (initialBound_pos ε l).trans_le <| initialBound_le_bound ε l

variable {ι 𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] {s t : Finset ι} {x : 𝕜}

theorem mul_sq_le_sum_sq (hst : s ⊆ t) (f : ι → 𝕜) (hs : x ^ 2 ≤ ((∑ i ∈ s, f i) / #s) ^ 2)
    (hs' : (#s : 𝕜) ≠ 0) : (#s : 𝕜) * x ^ 2 ≤ ∑ i ∈ t, f i ^ 2 := calc
  _ ≤ (#s : 𝕜) * ((∑ i ∈ s, f i ^ 2) / #s) := by
    gcongr
    exact hs.trans sum_div_card_sq_le_sum_sq_div_card
  _ = ∑ i ∈ s, f i ^ 2 := mul_div_cancel₀ _ hs'
  _ ≤ ∑ i ∈ t, f i ^ 2 := by gcongr

theorem add_div_le_sum_sq_div_card (hst : s ⊆ t) (f : ι → 𝕜) (d : 𝕜) (hx : 0 ≤ x)
    (hs : x ≤ |(∑ i ∈ s, f i) / #s - (∑ i ∈ t, f i) / #t|) (ht : d ≤ ((∑ i ∈ t, f i) / #t) ^ 2) :
    d + #s / #t * x ^ 2 ≤ (∑ i ∈ t, f i ^ 2) / #t := by
  obtain hscard | hscard := ((#s).cast_nonneg : (0 : 𝕜) ≤ #s).eq_or_lt
  · simpa [← hscard] using ht.trans sum_div_card_sq_le_sum_sq_div_card
  have htcard : (0 : 𝕜) < #t := hscard.trans_le (Nat.cast_le.2 (card_le_card hst))
  have h₁ : x ^ 2 ≤ ((∑ i ∈ s, f i) / #s - (∑ i ∈ t, f i) / #t) ^ 2 :=
    sq_le_sq.2 (by rwa [abs_of_nonneg hx])
  have h₂ : x ^ 2 ≤ ((∑ i ∈ s, (f i - (∑ j ∈ t, f j) / #t)) / #s) ^ 2 := by
    apply h₁.trans
    rw [sum_sub_distrib, sum_const, nsmul_eq_mul, sub_div, mul_div_cancel_left₀ _ hscard.ne']
  grw [ht]
  rw [← mul_div_right_comm, le_div_iff₀ htcard, add_mul, div_mul_cancel₀ _ htcard.ne']
  have h₃ := mul_sq_le_sum_sq hst (fun i => (f i - (∑ j ∈ t, f j) / #t)) h₂ hscard.ne'
  grw [h₃]
  simp only [sub_div' htcard.ne', div_pow, ← sum_div, ← mul_div_right_comm _ (#t : 𝕜), ← add_div,
    div_le_iff₀ (sq_pos_of_ne_zero htcard.ne'), sub_sq, sum_add_distrib, sum_const,
    sum_sub_distrib, mul_pow, ← sum_mul, nsmul_eq_mul, two_mul]
  ring_nf
  rfl

end SzemerediRegularity

namespace Mathlib.Meta.Positivity

open Lean.Meta Qq

/-- Extension for the `positivity` tactic: `SzemerediRegularity.initialBound` is always positive. -/
@[positivity SzemerediRegularity.initialBound _ _]
meta def evalInitialBound : PositivityExt where eval {u α} _ _ e := do
  match u, α, e with
  | 0, ~q(ℕ), ~q(SzemerediRegularity.initialBound $ε $l) =>
    assertInstancesCommute
    pure (.positive q(SzemerediRegularity.initialBound_pos $ε $l))
  | _, _, _ => throwError "not initialBound"


example (ε : ℝ) (l : ℕ) : 0 < SzemerediRegularity.initialBound ε l := by positivity

/-- Extension for the `positivity` tactic: `SzemerediRegularity.bound` is always positive. -/
@[positivity SzemerediRegularity.bound _ _]
meta def evalBound : PositivityExt where eval {u α} _ _ e := do
  match u, α, e with
  | 0, ~q(ℕ), ~q(SzemerediRegularity.bound $ε $l) =>
    assertInstancesCommute
    pure (.positive q(SzemerediRegularity.bound_pos $ε $l))
  | _, _, _ => throwError "not bound"

example (ε : ℝ) (l : ℕ) : 0 < SzemerediRegularity.bound ε l := by positivity

end Mathlib.Meta.Positivity
