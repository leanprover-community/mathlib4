/-
Copyright (c) 2026 Essam Abadir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Essam Abadir
-/
module
public import Mathlib.InformationTheory.EntropyNumber.Int
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Algebra.Order.Ring.Unbundled.Rat

@[expose] public section


/-!
# EntropyRat: Information-Theoretic Rationals

The rationals viewed as asymmetric particle history PMFs. An `EntropyRat` is a
`List Bool` in canonical form `sign :: 1…1 ++ 0…0` where the count of `true`s
is the numerator and the count of `false`s is the denominator. This gives a
bijection `EntropyRat ≃ ℚ`.

## Main definitions

* `EntropyRat.IsCanonical` — predicate for canonical rational form.
* `EntropyRat` — the subtype `{ l : List Bool // EntropyRat.IsCanonical l }`.
* `EntropyRat.num` / `EntropyRat.den` / `EntropyRat.sign` — projections.
* `EntropyRat.toRat` / `EntropyRat.ofRat` — bijection with `ℚ`.
* `entropyRatEquivRat` — the bundled equivalence `EntropyRat ≃ ℚ`.
* `EntropyRat.toBiasedSource` — instantiate a biased i.i.d. source from an
  `EntropyRat`.

## Main results

(No standalone theorems; the key result is the construction of the
equivalence `entropyRatEquivRat : EntropyRat ≃ ℚ`.)
-/

namespace InformationTheory

/--
A predicate asserting that a `List Bool` is in the canonical form for a
rational. The form is `sign :: 1...1 ++ 0...0`. We also enforce that the
rational is normalized (numerator and denominator are coprime), the denominator
is non-zero, and zero has a unique non-negative representation.
-/
def EntropyRat.IsCanonical (l : List Bool) : Prop :=
  ∃ (s : Bool) (p q : ℕ),
    l = [s] ++ List.replicate p true ++ List.replicate q false ∧
    q > 0 ∧
    Nat.Coprime p q ∧
    (p = 0 → s = true)

/--
An `EntropyRat` is a `List Bool` that is proven to be in the canonical,
normalized form for a rational number.
-/
abbrev EntropyRat := { l : List Bool // EntropyRat.IsCanonical l }

/-- A `ParticleWaveform` is a synonym for `EntropyRat`. -/
abbrev ParticleWaveform := EntropyRat

/-- Parses the numerator (count of `true`s) from a canonical rational list. -/
def EntropyRat.num (r : EntropyRat) : ℕ :=
  r.val.tail.count true

/-- Parses the denominator (count of `false`s) from a canonical rational
list. -/
def EntropyRat.den (r : EntropyRat) : ℕ :=
  r.val.tail.count false

/-- Parses the sign bit from a canonical rational list. -/
def EntropyRat.sign (r : EntropyRat) : Bool :=
  r.val.head (by
    rcases r.property with ⟨s, p, q, h_struct, _, _⟩
    rw [h_struct]; simp)

/-- Decodes the abstract mathematical value `p/q` from its canonical
`List Bool` representation. -/
noncomputable def EntropyRat.toRat (r : EntropyRat) : ℚ :=
  let s := EntropyRat.sign r
  let p := EntropyRat.num r
  let q := EntropyRat.den r
  let num_int : ℤ := if s then p else -p
  mkRat num_int q

/-- Encodes a standard `ℚ` into its canonical, normalized `List Bool`
representation. -/
noncomputable def EntropyRat.ofRat (q_in : ℚ) : EntropyRat :=
  let s := decide (0 ≤ q_in.num)
  let p := q_in.num.natAbs
  let q := q_in.den
  let l := [s] ++ List.replicate p true ++ List.replicate q false
  ⟨l, by
    use s, p, q
    refine ⟨rfl, q_in.den_pos, ?_, ?_⟩
    · simpa [p, q] using q_in.reduced
    · intro hp_eq_zero
      dsimp [s, p]
      have h_num_zero : q_in.num = 0 := Int.natAbs_eq_zero.mp hp_eq_zero
      rw [h_num_zero]; simp⟩

/-- Takes an `EntropyRat` and creates the corresponding `BiasedIIDParticleSource`
that generates `true` with probability `p/(p+q)`. -/
noncomputable def EntropyRat.toBiasedSource (r : EntropyRat) (seed : ℕ) :
    IIDParticleSource Bool :=
  let p := EntropyRat.num r
  let q := EntropyRat.den r
  have h_total_pos : p + q > 0 := by
    rcases r.property with ⟨_, _, q_prop, h_struct, h_q_pos, _⟩
    have h_q_eq : q = q_prop := by
      dsimp [q, EntropyRat.den]
      simp [h_struct, List.singleton_append, List.cons_append,
            List.tail_cons, List.count_append, List.count_replicate]
    rw [h_q_eq]; omega
  mkBiasedIIDParticleSource seed p q h_total_pos

/-- The canonical equivalence `EntropyRat ≃ ℚ`. -/
noncomputable def entropyRatEquivRat : EntropyRat ≃ ℚ :=
{ toFun    := EntropyRat.toRat,
  invFun   := EntropyRat.ofRat,
  left_inv := by
    intro r
    apply Subtype.ext
    rcases r.property with ⟨s, p, q, h_struct, h_q_pos, h_coprime,
      h_zero_sign⟩
    have h_toRat_r_eq_mkRat :
        EntropyRat.toRat r = mkRat (if s then p else -p) q := by
      dsimp [EntropyRat.toRat]
      have h_s_loc : EntropyRat.sign r = s := by
        dsimp [EntropyRat.sign]; simp [h_struct]
      have h_p_loc : EntropyRat.num r = p := by
        dsimp [EntropyRat.num]; rw [h_struct, List.singleton_append]
        simp [List.tail_cons, List.count_append,
              List.count_replicate, add_zero]
      have h_q_loc : EntropyRat.den r = q := by
        dsimp [EntropyRat.den]; rw [h_struct, List.singleton_append]
        simp [List.tail_cons, List.count_append,
              List.count_replicate, zero_add]
      rw [h_s_loc, h_p_loc, h_q_loc]
    dsimp [EntropyRat.ofRat]
    rw [h_toRat_r_eq_mkRat]
    have h_num_den :
      (mkRat (if s then (↑p : ℤ) else -(↑p : ℤ)) q).num =
        (if s then (↑p : ℤ) else -(↑p : ℤ)) ∧
      (mkRat (if s then (↑p : ℤ) else -(↑p : ℤ)) q).den = q := by
      let v : ℤ := if s then ↑p else -↑p
      have hq_pos_int : (0 : ℤ) < (q : ℤ) := by exact_mod_cast h_q_pos
      have h_coprime_int :
        (Int.natAbs v).Coprime (Int.natAbs (q : ℤ)) := by
        dsimp only [v]
        rw [Int.natAbs_natCast q]
        split_ifs with hs_cond
        · simp only [Int.natAbs_natCast]; exact h_coprime
        · simp only [Int.natAbs_neg, Int.natAbs_natCast]
          exact h_coprime
      constructor
      · rw [Rat.mkRat_eq_divInt v q, Rat.divInt_eq_div v ↑q]
        exact Rat.num_div_eq_of_coprime hq_pos_int h_coprime_int
      · rw [Rat.mkRat_eq_divInt v q, Rat.divInt_eq_div v ↑q]
        have h_den := Rat.den_div_eq_of_coprime hq_pos_int h_coprime_int
        exact_mod_cast h_den
    rw [h_num_den.1, h_num_den.2, h_struct]
    simp
    constructor
    · by_cases hs : s
      · simp [hs]
      · simp [hs]
        have hp_ne_zero : p ≠ 0 := by
          intro hp_is_zero
          exact hs (h_zero_sign hp_is_zero)
        omega
    · omega,
  right_inv := by
    intro q_in
    show EntropyRat.toRat (EntropyRat.ofRat q_in) = q_in
    simp (config := { decide := true }) [EntropyRat.toRat, EntropyRat.ofRat,
      EntropyRat.num, EntropyRat.sign, EntropyRat.den,
      List.head_cons, List.tail_cons, List.count_append,
      List.count_replicate_self, List.count_replicate]
    by_cases h_nonneg : (0 : ℚ) ≤ q_in
    · -- Goal: mkRat (↑q_in.num.natAbs) q_in.den = q_in
      have h_num_nn : 0 ≤ q_in.num := Rat.num_nonneg.2 h_nonneg
      rw [Int.natAbs_of_nonneg h_num_nn]
      simp only [h_nonneg, ite_true]
      exact Rat.mkRat_self q_in
    · -- Goal: mkRat (-↑q_in.num.natAbs) q_in.den = q_in
      have h_lt : q_in < 0 := lt_of_not_ge h_nonneg
      have h_num_neg : q_in.num < 0 := Rat.num_neg.mpr h_lt
      simp only [h_nonneg, ite_false]
      have h_abs : (↑q_in.num.natAbs : ℤ) = -q_in.num := by omega
      rw [h_abs, neg_neg]
      exact Rat.mkRat_self q_in }

end InformationTheory
