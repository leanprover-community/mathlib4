/-
Copyright (c) 2020 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
import Mathlib.Algebra.ContinuedFractions.Computation.Approximations
import Mathlib.Algebra.ContinuedFractions.Computation.CorrectnessTerminating
import Mathlib.Data.Rat.Floor

/-!
# Termination of Continued Fraction Computations (`GenContFract.of`)

## Summary
We show that the continued fraction for a value `v`, as defined in
`Mathlib/Algebra/ContinuedFractions/Basic.lean`, terminates if and only if `v` corresponds to a
rational number, that is `↑v = q` for some `q : ℚ`.

## Main Theorems

- `GenContFract.coe_of_rat_eq` shows that
  `GenContFract.of v = GenContFract.of q` for `v : α` given that `↑v = q` and `q : ℚ`.
- `GenContFract.terminates_iff_rat` shows that
  `GenContFract.of v` terminates if and only if `↑v = q` for some `q : ℚ`.

## Tags

rational, continued fraction, termination
-/


namespace GenContFract

open GenContFract (of)

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

/-
We will have to constantly coerce along our structures in the following proofs using their provided
map functions.
-/
attribute [local simp] Pair.map IntFractPair.mapFr

section RatOfTerminates

/-!
### Terminating Continued Fractions Are Rational

We want to show that the computation of a continued fraction `GenContFract.of v`
terminates if and only if `v ∈ ℚ`. In this section, we show the implication from left to right.

We first show that every finite convergent corresponds to a rational number `q` and then use the
finite correctness proof (`of_correctness_of_terminates`) of `GenContFract.of` to show that
`v = ↑q`.
-/


variable (v : K) (n : ℕ)

nonrec theorem exists_gcf_pair_rat_eq_of_nth_contsAux :
    ∃ conts : Pair ℚ, (of v).contsAux n = (conts.map (↑) : Pair K) :=
  Nat.strong_induction_on n
    (by
      clear n
      let g := of v
      intro n IH
      rcases n with (_ | _ | n)
      -- n = 0
      · suffices ∃ gp : Pair ℚ, Pair.mk (1 : K) 0 = gp.map (↑) by simpa [contsAux]
        use Pair.mk 1 0
        simp
      -- n = 1
      · suffices ∃ conts : Pair ℚ, Pair.mk g.h 1 = conts.map (↑) by simpa [contsAux]
        use Pair.mk ⌊v⌋ 1
        simp [g]
      -- 2 ≤ n
      · obtain ⟨pred_conts, pred_conts_eq⟩ := IH (n + 1) <| lt_add_one (n + 1)
        -- invoke the IH
        rcases s_ppred_nth_eq : g.s.get? n with gp_n | gp_n
        -- option.none
        · use pred_conts
          have : g.contsAux (n + 2) = g.contsAux (n + 1) :=
            contsAux_stable_of_terminated (n + 1).le_succ s_ppred_nth_eq
          simp only [g, this, pred_conts_eq]
        -- option.some
        · -- invoke the IH a second time
          obtain ⟨ppred_conts, ppred_conts_eq⟩ :=
            IH n <| lt_of_le_of_lt n.le_succ <| lt_add_one <| n + 1
          obtain ⟨a_eq_one, z, b_eq_z⟩ : gp_n.a = 1 ∧ ∃ z : ℤ, gp_n.b = (z : K) :=
            of_partNum_eq_one_and_exists_int_partDen_eq s_ppred_nth_eq
          -- finally, unfold the recurrence to obtain the required rational value.
          simp only [g, a_eq_one, b_eq_z,
            contsAux_recurrence s_ppred_nth_eq ppred_conts_eq pred_conts_eq]
          use nextConts 1 (z : ℚ) ppred_conts pred_conts
          cases ppred_conts; cases pred_conts
          simp [nextConts, nextNum, nextDen])

theorem exists_gcf_pair_rat_eq_nth_conts :
    ∃ conts : Pair ℚ, (of v).conts n = (conts.map (↑) : Pair K) := by
  rw [nth_cont_eq_succ_nth_contAux]; exact exists_gcf_pair_rat_eq_of_nth_contsAux v <| n + 1

theorem exists_rat_eq_nth_num : ∃ q : ℚ, (of v).nums n = (q : K) := by
  rcases exists_gcf_pair_rat_eq_nth_conts v n with ⟨⟨a, _⟩, nth_cont_eq⟩
  use a
  simp [num_eq_conts_a, nth_cont_eq]

theorem exists_rat_eq_nth_den : ∃ q : ℚ, (of v).dens n = (q : K) := by
  rcases exists_gcf_pair_rat_eq_nth_conts v n with ⟨⟨_, b⟩, nth_cont_eq⟩
  use b
  simp [den_eq_conts_b, nth_cont_eq]

/-- Every finite convergent corresponds to a rational number. -/
theorem exists_rat_eq_nth_conv : ∃ q : ℚ, (of v).convs n = (q : K) := by
  rcases exists_rat_eq_nth_num v n with ⟨Aₙ, nth_num_eq⟩
  rcases exists_rat_eq_nth_den v n with ⟨Bₙ, nth_den_eq⟩
  use Aₙ / Bₙ
  simp [nth_num_eq, nth_den_eq, conv_eq_num_div_den]

variable {v}

/-- Every terminating continued fraction corresponds to a rational number. -/
theorem exists_rat_eq_of_terminates (terminates : (of v).Terminates) : ∃ q : ℚ, v = ↑q := by
  obtain ⟨n, v_eq_conv⟩ : ∃ n, v = (of v).convs n := of_correctness_of_terminates terminates
  obtain ⟨q, conv_eq_q⟩ : ∃ q : ℚ, (of v).convs n = (↑q : K) := exists_rat_eq_nth_conv v n
  have : v = (↑q : K) := Eq.trans v_eq_conv conv_eq_q
  use q, this

end RatOfTerminates

section RatTranslation

/-!
### Technical Translation Lemmas

Before we can show that the continued fraction of a rational number terminates, we have to prove
some technical translation lemmas. More precisely, in this section, we show that, given a rational
number `q : ℚ` and value `v : K` with `v = ↑q`, the continued fraction of `q` and `v` coincide.
In particular, we show that
```lean
    (↑(GenContFract.of q : GenContFract ℚ) : GenContFract K) = GenContFract.of v
```
in `GenContFract.coe_of_rat_eq`.

To do this, we proceed bottom-up, showing the correspondence between the basic functions involved in
the Computation first and then lift the results step-by-step.
-/


-- The lifting works for arbitrary linear ordered fields with a floor function.
variable {v : K} {q : ℚ}

/-! First, we show the correspondence for the very basic functions in
`GenContFract.IntFractPair`. -/


namespace IntFractPair

theorem coe_of_rat_eq (v_eq_q : v = (↑q : K)) :
    ((IntFractPair.of q).mapFr (↑) : IntFractPair K) = IntFractPair.of v := by
  simp [IntFractPair.of, v_eq_q]

theorem coe_stream_nth_rat_eq (v_eq_q : v = (↑q : K)) (n : ℕ) :
    ((IntFractPair.stream q n).map (mapFr (↑)) : Option <| IntFractPair K) =
      IntFractPair.stream v n := by
  induction n with
  | zero =>
    simp only [IntFractPair.stream, Option.map_some, coe_of_rat_eq v_eq_q]
  | succ n IH =>
    rw [v_eq_q] at IH
    cases stream_q_nth_eq : IntFractPair.stream q n with
    | none => simp [IntFractPair.stream, IH.symm, v_eq_q, stream_q_nth_eq]
    | some ifp_n =>
      obtain ⟨b, fr⟩ := ifp_n
      rcases Decidable.em (fr = 0) with fr_zero | fr_ne_zero
      · simp [IntFractPair.stream, IH.symm, v_eq_q, stream_q_nth_eq, fr_zero]
      · replace IH : some (IntFractPair.mk b (fr : K)) = IntFractPair.stream (↑q) n := by
          rwa [stream_q_nth_eq] at IH
        have : (fr : K)⁻¹ = ((fr⁻¹ : ℚ) : K) := by norm_cast
        have coe_of_fr := coe_of_rat_eq this
        simpa [IntFractPair.stream, IH.symm, v_eq_q, stream_q_nth_eq, fr_ne_zero]

theorem coe_stream'_rat_eq (v_eq_q : v = (↑q : K)) :
    ((IntFractPair.stream q).map (Option.map (mapFr (↑))) : Stream' <| Option <| IntFractPair K) =
      IntFractPair.stream v := by
  funext n; exact IntFractPair.coe_stream_nth_rat_eq v_eq_q n

end IntFractPair

/-! Now we lift the coercion results to the continued fraction computation. -/


theorem coe_of_h_rat_eq (v_eq_q : v = (↑q : K)) : (↑((of q).h : ℚ) : K) = (of v).h := by
  simp_all

theorem coe_of_s_get?_rat_eq (v_eq_q : v = (↑q : K)) (n : ℕ) :
    (((of q).s.get? n).map (Pair.map (↑)) : Option <| Pair K) = (of v).s.get? n := by
  simp only [of, IntFractPair.seq1, Stream'.Seq.map_get?, Stream'.Seq.get?_tail]
  simp only [Stream'.Seq.get?]
  rw [← IntFractPair.coe_stream'_rat_eq v_eq_q]
  rcases succ_nth_stream_eq : IntFractPair.stream q (n + 1) with (_ | ⟨_, _⟩) <;>
    simp [Stream'.map, Stream'.get, succ_nth_stream_eq]

theorem coe_of_s_rat_eq (v_eq_q : v = (↑q : K)) :
    ((of q).s.map (Pair.map ((↑))) : Stream'.Seq <| Pair K) = (of v).s := by
  ext n; rw [← coe_of_s_get?_rat_eq v_eq_q]; rfl

/-- Given `(v : K), (q : ℚ), and v = q`, we have that `of q = of v` -/
theorem coe_of_rat_eq (v_eq_q : v = (↑q : K)) :
    (⟨(of q).h, (of q).s.map (Pair.map (↑))⟩ : GenContFract K) = of v := by
  rcases gcf_v_eq : of v with ⟨h, s⟩; subst v
  obtain rfl : ↑⌊(q : K)⌋ = h := by injection gcf_v_eq
  simp [coe_of_s_rat_eq rfl, gcf_v_eq]

theorem of_terminates_iff_of_rat_terminates {v : K} {q : ℚ} (v_eq_q : v = (q : K)) :
    (of v).Terminates ↔ (of q).Terminates := by
  constructor <;> intro h <;> obtain ⟨n, h⟩ := h <;> use n <;>
    simp only [Stream'.Seq.TerminatedAt, (coe_of_s_get?_rat_eq v_eq_q n).symm] at h ⊢ <;>
    cases h' : (of q).s.get? n <;>
    simp only [h'] at h <;>
    trivial

end RatTranslation

section TerminatesOfRat

/-!
### Continued Fractions of Rationals Terminate

Finally, we show that the continued fraction of a rational number terminates.

The crucial insight is that, given any `q : ℚ` with `0 < q < 1`, the numerator of `Int.fract q` is
smaller than the numerator of `q`. As the continued fraction computation recursively operates on
the fractional part of a value `v` and `0 ≤ Int.fract v < 1`, we infer that the numerator of the
fractional part in the computation decreases by at least one in each step. As `0 ≤ Int.fract v`,
this process must stop after finite number of steps, and the computation hence terminates.
-/


namespace IntFractPair

variable {q : ℚ} {n : ℕ}

/-- Shows that for any `q : ℚ` with `0 < q < 1`, the numerator of the fractional part of
`IntFractPair.of q⁻¹` is smaller than the numerator of `q`.
-/
theorem of_inv_fr_num_lt_num_of_pos (q_pos : 0 < q) : (IntFractPair.of q⁻¹).fr.num < q.num :=
  Rat.fract_inv_num_lt_num_of_pos q_pos

/-- Shows that the sequence of numerators of the fractional parts of the stream is strictly
antitone. -/
theorem stream_succ_nth_fr_num_lt_nth_fr_num_rat {ifp_n ifp_succ_n : IntFractPair ℚ}
    (stream_nth_eq : IntFractPair.stream q n = some ifp_n)
    (stream_succ_nth_eq : IntFractPair.stream q (n + 1) = some ifp_succ_n) :
    ifp_succ_n.fr.num < ifp_n.fr.num := by
  obtain ⟨ifp_n', stream_nth_eq', ifp_n_fract_ne_zero, IntFractPair.of_eq_ifp_succ_n⟩ :
    ∃ ifp_n',
      IntFractPair.stream q n = some ifp_n' ∧
        ifp_n'.fr ≠ 0 ∧ IntFractPair.of ifp_n'.fr⁻¹ = ifp_succ_n :=
    succ_nth_stream_eq_some_iff.mp stream_succ_nth_eq
  have : ifp_n = ifp_n' := by injection Eq.trans stream_nth_eq.symm stream_nth_eq'
  cases this
  rw [← IntFractPair.of_eq_ifp_succ_n]
  obtain ⟨zero_le_ifp_n_fract, _⟩ := nth_stream_fr_nonneg_lt_one stream_nth_eq
  have : 0 < ifp_n.fr := lt_of_le_of_ne zero_le_ifp_n_fract <| ifp_n_fract_ne_zero.symm
  exact of_inv_fr_num_lt_num_of_pos this

theorem stream_nth_fr_num_le_fr_num_sub_n_rat :
    ∀ {ifp_n : IntFractPair ℚ},
      IntFractPair.stream q n = some ifp_n → ifp_n.fr.num ≤ (IntFractPair.of q).fr.num - n := by
  induction n with
  | zero =>
    intro ifp_zero stream_zero_eq
    have : IntFractPair.of q = ifp_zero := by injection stream_zero_eq
    simp [le_refl, this.symm]
  | succ n IH =>
    intro ifp_succ_n stream_succ_nth_eq
    suffices ifp_succ_n.fr.num + 1 ≤ (IntFractPair.of q).fr.num - n by
      rw [Int.natCast_succ, sub_add_eq_sub_sub]
      solve_by_elim [le_sub_right_of_add_le]
    rcases succ_nth_stream_eq_some_iff.mp stream_succ_nth_eq with ⟨ifp_n, stream_nth_eq, -⟩
    have : ifp_succ_n.fr.num < ifp_n.fr.num :=
      stream_succ_nth_fr_num_lt_nth_fr_num_rat stream_nth_eq stream_succ_nth_eq
    exact le_trans this (IH stream_nth_eq)

theorem exists_nth_stream_eq_none_of_rat (q : ℚ) : ∃ n : ℕ, IntFractPair.stream q n = none := by
  let fract_q_num := (Int.fract q).num; let n := fract_q_num.natAbs + 1
  rcases stream_nth_eq : IntFractPair.stream q n with ifp | ifp
  · use n, stream_nth_eq
  · -- arrive at a contradiction since the numerator decreased num + 1 times but every fractional
    -- value is nonnegative.
    have ifp_fr_num_le_q_fr_num_sub_n : ifp.fr.num ≤ fract_q_num - n :=
      stream_nth_fr_num_le_fr_num_sub_n_rat stream_nth_eq
    have : fract_q_num - n = -1 := by
      have : 0 ≤ fract_q_num := Rat.num_nonneg.mpr (Int.fract_nonneg q)
      simp only [n, Nat.cast_add, Int.natAbs_of_nonneg this, Nat.cast_one,
        sub_add_eq_sub_sub_swap, sub_right_comm, sub_self, zero_sub]
    have : 0 ≤ ifp.fr := (nth_stream_fr_nonneg_lt_one stream_nth_eq).left
    have : 0 ≤ ifp.fr.num := Rat.num_nonneg.mpr this
    cutsat

end IntFractPair

/-- The continued fraction of a rational number terminates. -/
theorem terminates_of_rat (q : ℚ) : (of q).Terminates :=
  Exists.elim (IntFractPair.exists_nth_stream_eq_none_of_rat q) fun n stream_nth_eq_none =>
    Exists.intro n
      (have : IntFractPair.stream q (n + 1) = none := IntFractPair.stream_isSeq q stream_nth_eq_none
      of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none.mpr this)

end TerminatesOfRat

/-- The continued fraction `GenContFract.of v` terminates if and only if `v ∈ ℚ`. -/
theorem terminates_iff_rat (v : K) : (of v).Terminates ↔ ∃ q : ℚ, v = (q : K) :=
  Iff.intro
    (fun terminates_v : (of v).Terminates =>
      show ∃ q : ℚ, v = (q : K) from exists_rat_eq_of_terminates terminates_v)
    fun exists_q_eq_v : ∃ q : ℚ, v = (↑q : K) =>
    Exists.elim exists_q_eq_v fun q => fun v_eq_q : v = ↑q =>
      have : (of q).Terminates := terminates_of_rat q
      (of_terminates_iff_of_rat_terminates v_eq_q).mpr this

end GenContFract
