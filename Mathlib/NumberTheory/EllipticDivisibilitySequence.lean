/-
Copyright (c) 2024 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/
import Mathlib.Data.Nat.EvenOddRec
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# Elliptic divisibility sequences

This file defines the types of elliptic nets and elliptic divisibility sequences, as well as the
canonical example of a normalised elliptic divisibility sequence.

## Mathematical background

Let `R` be a commutative ring, and let `W` be a sequence of elements in `R` indexed by `ℤ`. The
*elliptic relator* `ER(m, n, r, s) ∈ R` associated to `W` is given for all `m, n, r, s ∈ ℤ` by
`ER(m, n, r, s) := W(m+n+s)W(m-n)W(r+s)W(r) - W(m+r+s)W(m-r)W(n+s)W(n) + W(n+r+s)W(n-r)W(m+s)W(m)`.
Call `W` an *elliptic net* if it satisfies the *elliptic relation* `ER(m, n, r, s) = 0` for any
`m, n, r, s ∈ ℤ`. By a cyclic permutation of variables, `ER(m, n, r, s) = 0` is essentially
equivalent to the symmetric relation `ERₐ(m, n, r, s) = 0`, where `ERₐ(m, n, r, s) ∈ R` is given for
all `m, n, r, s ∈ ℤ` by `ERₐ(m, n, r, s) := Wₐ(m, n)Wₐ(r, s) - Wₐ(m, r)Wₐ(n, s) + Wₐ(m, s)Wₐ(n, r)`
defined in terms of *elliptic atoms* `Wₐ(m, n) := W((m + n) / 2)W((m - n) / 2)` for all `m, n ∈ ℤ`.

As a special case, `W` is an *elliptic sequence* if it satisfies `ER(m, n, r, 0) = 0` for any
`m, n, r ∈ ℤ`, a *divisibility sequence* if it satisfies `W(k) ∣ W(nk)` for any `k, n ∈ ℤ`, and an
*elliptic divisibility sequence* (EDS) if it is a divisibility sequence that is elliptic. If `W` is
an EDS, then `x • W` is also an EDS for any `x ∈ R`. It turns out that any EDS `W` can be normalised
such that `W(1) = 1`, in which case it can be characterised completely by
* the *even relations* `ER(m + 1, m, 1, 0) = 0` for all `m ∈ ℤ`, or in other words that
  `W(2m) = W(m - 1)²W(m)W(m + 2) - W(m - 2)W(m)W(m + 1)²` for all `m ∈ ℤ`, and
* the *odd relations* `ER(m + 1, m - 1, 1, 0) = 0` for all `m ∈ ℤ`, or in other words that
  `W(2m + 1) = W(m + 2)W(m)³ - W(m - 1)W(m + 1)³` for all `m ∈ ℤ`,
with initial values `W(0) = 0`, `W(1) = 1`, `W(2) = b`, `W(3) = c`, and `W(4) = db` for some
`b, c, d ∈ ℤ`. This will be called the *canonical example of a normalised EDS* in this file.

Some examples of EDSs include
* the identity sequence,
* certain terms of Lucas sequences, and
* division polynomials of elliptic curves.

## Main definitions

* `ellRel`: the elliptic relator `ER(m, n, r, s)` indexed by `ℤ`.
* `ellAtom`: the elliptic atom `Wₐ(m, n)` indexed by `ℤ`.
* `ellAtomRel`: the relator `ERₐ(m, n, r, s)` indexed by `ℤ`.
* `IsEllNet`: a sequence indexed by `ℤ` is an elliptic net.
* `IsEllSequence`: a sequence indexed by `ℤ` is an elliptic sequence.
* `IsDivSequence`: a sequence indexed by `ℤ` is a divisibility sequence.
* `IsEllDivSequence`: a sequence indexed by `ℤ` is an EDS.
* `preNormEDS'`: the auxiliary sequence for a normalised EDS indexed by `ℕ`.
* `preNormEDS`: the auxiliary sequence for a normalised EDS indexed by `ℤ`.
* `normEDS`: the canonical example of a normalised EDS indexed by `ℤ`.

## Main statements

* TODO: prove that `normEDS` satisfies `IsEllDivSequence`.
* TODO: prove that a sequence satisfying `IsEllDivSequence` can be normalised to give `normEDS`.

## Implementation notes

The elliptic relator is identical to the elliptic net recurrence defined by Stange, except that the
final term in the latter is negated. This unifies the definitions of Stange's elliptic nets and
Ward's elliptic sequences without requiring the sequence to be an odd function.

The normalised EDS `normEDS b c d n` is defined in terms of the auxiliary sequence
`preNormEDS (b ^ 4) c d n`, which are equal when `n` is odd, and which differ by a factor of `b`
when `n` is even. This coincides with the definition in the references since both agree for
`normEDS b c d 2` and for `normEDS b c d 4`, and the correct factors of `b` are removed in
`normEDS b c d (2 * (m + 2) + 1)` and in `normEDS b c d (2 * (m + 3))`.

One reason is to avoid the necessity for ring division by `b` in the inductive definition of
`normEDS b c d (2 * (m + 3))`. The idea is that, it can be shown that `normEDS b c d (2 * (m + 3))`
always contains a factor of `b`, so it is possible to remove a factor of `b` *a posteriori*, but
stating this lemma requires first defining `normEDS b c d (2 * (m + 3))`, which requires having this
factor of `b` *a priori*. Another reason is to allow the definition of univariate `n`-division
polynomials of elliptic curves, omitting a factor of the bivariate `2`-division polynomial.

## References

* M Ward, *Memoir on Elliptic Divisibility Sequences*
* K Stange, *Elliptic Nets and Elliptic Curves*

## Tags

elliptic net, elliptic divisibility sequence
-/

universe u v

variable {R : Type u} [CommRing R]

section IsEllDivSequence

variable (W : ℤ → R)

/-- The elliptic relator `ER(m, n, r, s)` that defines an elliptic net. -/
def ellRel (m n r s : ℤ) : R :=
  W (m + n + s) * W (m - n) * W (r + s) * W r - W (m + r + s) * W (m - r) * W (n + s) * W n +
    W (n + r + s) * W (n - r) * W (m + s) * W m

/-- The elliptic atom `Wₐ(m, n)` that defines an elliptic net. Note that this is defined in terms of
truncated integer division, and hence should only be used when `m` and `n` have the same parity. -/
def ellAtom (m n : ℤ) : R :=
  W ((m + n).tdiv 2) * W ((m - n).tdiv 2)

/-- The relator `ERₐ(m, n, r, s)` obtained by a cyclic permutation of variables in `ER(m, n, r, s)`.
Note that this is defined in terms of elliptic atoms, and hence should only be used when `m`, `n`,
`r`, and `s` all have the same parity. -/
def ellAtomRel (m n r s : ℤ) : R :=
  ellAtom W m n * ellAtom W r s - ellAtom W m r * ellAtom W n s + ellAtom W m s * ellAtom W n r

lemma ellRel_eq (m n r s : ℤ) :
    ellRel W m n r s = ellAtomRel W (2 * m + s) (2 * n + s) (2 * r + s) s := by
  simp_rw [ellRel, ellAtomRel, ellAtom, add_add_add_comm _ s, add_assoc _ s, ← two_mul, ← mul_add,
    add_sub_add_comm, add_sub_assoc, sub_self, add_zero, ← mul_sub,
    Int.mul_tdiv_cancel_left _ two_ne_zero, mul_comm <| _ * W m, mul_assoc]

lemma ellAtomRel_eq (m n r s : ℤ) : ellAtomRel W (2 * m) (2 * n) (2 * r) (2 * s) =
    ellRel W (m - s) (n - s) (r - s) (2 * s) := by
  simp_rw [ellAtomRel, ellAtom, ellRel, ← mul_add, ← mul_sub,
    Int.mul_tdiv_cancel_left _ two_ne_zero, two_mul]
  ring_nf

/-- The proposition that a sequence indexed by `ℤ` is an elliptic net. -/
def IsEllNet : Prop :=
  ∀ m n r s : ℤ, ellRel W m n r s = 0

/-- The proposition that a sequence indexed by `ℤ` is an elliptic sequence. -/
def IsEllSequence : Prop :=
  ∀ m n r : ℤ, ellRel W m n r 0 = 0

/-- The proposition that a sequence indexed by `ℤ` is a divisibility sequence. -/
def IsDivSequence : Prop :=
  ∀ m n : ℕ, m ∣ n → W m ∣ W n

/-- The proposition that a sequence indexed by `ℤ` is an EDS. -/
def IsEllDivSequence : Prop :=
  IsEllSequence W ∧ IsDivSequence W

variable {W} in
lemma IsEllNet.isEllSequence (h : IsEllNet W) : IsEllSequence W :=
  (h · · · 0)

variable {W} in
lemma IsEllNet.smul (h : IsEllNet W) (x : R) : IsEllNet (x • W) := fun m n r s => by
  linear_combination (norm := (simp_rw [ellRel, Pi.smul_apply, smul_eq_mul]; ring1))
    x ^ 4 * h m n r s

variable {W} in
lemma IsEllSequence.smul (h : IsEllSequence W) (x : R) : IsEllSequence (x • W) := fun m n r => by
  linear_combination (norm := (simp_rw [ellRel, Pi.smul_apply, smul_eq_mul]; ring1)) x ^ 4 * h m n r

variable {W} in
lemma IsDivSequence.smul (h : IsDivSequence W) (x : R) : IsDivSequence (x • W) :=
  (mul_dvd_mul_left x <| h · · ·)

variable {W} in
lemma IsEllDivSequence.smul (h : IsEllDivSequence W) (x : R) : IsEllDivSequence (x • W) :=
  ⟨h.left.smul x, h.right.smul x⟩

lemma isEllNet_id : IsEllNet id :=
  fun _ _ _ _ => by simp_rw [ellRel, id_eq]; ring1

lemma isEllSequence_id : IsEllSequence id :=
  isEllNet_id.isEllSequence

lemma isDivSequence_id : IsDivSequence id :=
  fun _ _ => Int.ofNat_dvd.mpr

/-- The identity sequence is an EDS. -/
theorem isEllDivSequence_id : IsEllDivSequence id :=
  ⟨isEllSequence_id, isDivSequence_id⟩

end IsEllDivSequence

variable (b c d : R)

section PreNormEDS

/-- The auxiliary sequence for a normalised EDS `W : ℕ → R`, with initial values
`W(0) = 0`, `W(1) = 1`, `W(2) = 1`, `W(3) = c`, and `W(4) = d` and extra parameter `b`. -/
def preNormEDS' : ℕ → R
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => c
  | 4 => d
  | (n + 5) => let m := n / 2
    if hn : Even n then
      preNormEDS' (m + 4) * preNormEDS' (m + 2) ^ 3 * (if Even m then b else 1) -
        preNormEDS' (m + 1) * preNormEDS' (m + 3) ^ 3 * (if Even m then 1 else b)
    else
      have : m + 5 < n + 5 :=
        add_lt_add_right (Nat.div_lt_self (Nat.not_even_iff_odd.mp hn).pos one_lt_two) 5
      preNormEDS' (m + 2) ^ 2 * preNormEDS' (m + 3) * preNormEDS' (m + 5) -
        preNormEDS' (m + 1) * preNormEDS' (m + 3) * preNormEDS' (m + 4) ^ 2

@[simp]
lemma preNormEDS'_zero : preNormEDS' b c d 0 = 0 := by
  rw [preNormEDS']

@[simp]
lemma preNormEDS'_one : preNormEDS' b c d 1 = 1 := by
  rw [preNormEDS']

@[simp]
lemma preNormEDS'_two : preNormEDS' b c d 2 = 1 := by
  rw [preNormEDS']

@[simp]
lemma preNormEDS'_three : preNormEDS' b c d 3 = c := by
  rw [preNormEDS']

@[simp]
lemma preNormEDS'_four : preNormEDS' b c d 4 = d := by
  rw [preNormEDS']

lemma preNormEDS'_even (m : ℕ) : preNormEDS' b c d (2 * (m + 3)) =
    preNormEDS' b c d (m + 2) ^ 2 * preNormEDS' b c d (m + 3) * preNormEDS' b c d (m + 5) -
      preNormEDS' b c d (m + 1) * preNormEDS' b c d (m + 3) * preNormEDS' b c d (m + 4) ^ 2 := by
  rw [show 2 * (m + 3) = 2 * m + 1 + 5 by rfl, preNormEDS', dif_neg m.not_even_two_mul_add_one]
  simpa only [Nat.mul_add_div two_pos] using by rfl

lemma preNormEDS'_odd (m : ℕ) : preNormEDS' b c d (2 * (m + 2) + 1) =
    preNormEDS' b c d (m + 4) * preNormEDS' b c d (m + 2) ^ 3 * (if Even m then b else 1) -
      preNormEDS' b c d (m + 1) * preNormEDS' b c d (m + 3) ^ 3 * (if Even m then 1 else b) := by
  rw [show 2 * (m + 2) + 1 = 2 * m + 5 by rfl, preNormEDS', dif_pos <| even_two_mul m,
    m.mul_div_cancel_left two_pos]

/-- The auxiliary sequence for a normalised EDS `W : ℤ → R`, with initial values
`W(0) = 0`, `W(1) = 1`, `W(2) = 1`, `W(3) = c`, and `W(4) = d` and extra parameter `b`.

This extends `preNormEDS'` by defining its values at negative `ℤ`. -/
def preNormEDS (n : ℤ) : R :=
  n.sign * preNormEDS' b c d n.natAbs

@[simp]
lemma preNormEDS_ofNat (n : ℕ) : preNormEDS b c d n = preNormEDS' b c d n := by
  by_cases hn : n = 0
  · simp [hn, preNormEDS]
  · simp [preNormEDS, Int.sign_natCast_of_ne_zero hn]

@[simp]
lemma preNormEDS_zero : preNormEDS b c d 0 = 0 := by
  simp [preNormEDS]

@[simp]
lemma preNormEDS_one : preNormEDS b c d 1 = 1 := by
  simp [preNormEDS]

@[simp]
lemma preNormEDS_two : preNormEDS b c d 2 = 1 := by
  simp [preNormEDS, Int.sign_eq_one_of_pos]

@[simp]
lemma preNormEDS_three : preNormEDS b c d 3 = c := by
  simp [preNormEDS, Int.sign_eq_one_of_pos]

@[simp]
lemma preNormEDS_four : preNormEDS b c d 4 = d := by
  simp [preNormEDS, Int.sign_eq_one_of_pos]

@[simp]
lemma preNormEDS_neg (n : ℤ) : preNormEDS b c d (-n) = -preNormEDS b c d n := by
  simp [preNormEDS]

lemma preNormEDS_even (m : ℤ) : preNormEDS b c d (2 * m) =
    preNormEDS b c d (m - 1) ^ 2 * preNormEDS b c d m * preNormEDS b c d (m + 2) -
      preNormEDS b c d (m - 2) * preNormEDS b c d m * preNormEDS b c d (m + 1) ^ 2 := by
  induction m using Int.negInduction with
  | nat m =>
    rcases m with _ | _ | _ | m
    iterate 3 simp
    simp_rw [Nat.cast_succ, Int.add_sub_cancel, show (m : ℤ) + 1 + 1 + 1 = m + 1 + 2 by rfl,
      Int.add_sub_cancel]
    norm_cast
    simpa only [preNormEDS_ofNat] using preNormEDS'_even ..
  | neg ih m =>
    simp_rw [mul_neg, ← sub_neg_eq_add, ← neg_sub', ← neg_add', preNormEDS_neg, ih]
    ring1

@[deprecated (since := "2025-05-15")] alias preNormEDS_even_ofNat := preNormEDS_even

lemma preNormEDS_odd (m : ℤ) : preNormEDS b c d (2 * m + 1) =
    preNormEDS b c d (m + 2) * preNormEDS b c d m ^ 3 * (if Even m then b else 1) -
      preNormEDS b c d (m - 1) * preNormEDS b c d (m + 1) ^ 3 * (if Even m then 1 else b) := by
  induction m using Int.negInduction with
  | nat m =>
    rcases m with _ | _ | _
    iterate 2 simp
    simp_rw [Nat.cast_succ, Int.add_sub_cancel, Int.even_add_one, not_not, Int.even_coe_nat]
    norm_cast
    simpa only [preNormEDS_ofNat] using preNormEDS'_odd ..
  | neg ih m =>
    rcases m with _ | m
    · simp
    simp_rw [Nat.cast_succ, show 2 * -(m + 1 : ℤ) + 1 = -(2 * m + 1) by rfl,
      show -(m + 1 : ℤ) + 2 = -(m - 1) by ring1, show -(m + 1 : ℤ) - 1 = -(m + 2) by rfl,
      show -(m + 1 : ℤ) + 1 = -m by ring1, preNormEDS_neg, even_neg, Int.even_add_one, ite_not, ih]
    ring1

@[deprecated (since := "2025-05-15")] alias preNormEDS_odd_ofNat := preNormEDS_odd

end PreNormEDS

section NormEDS

/-- The canonical example of a normalised EDS `W : ℤ → R`, with initial values
`W(0) = 0`, `W(1) = 1`, `W(2) = b`, `W(3) = c`, and `W(4) = db`.

This is defined in terms of `preNormEDS` whose even terms differ by a factor of `b`. -/
def normEDS (n : ℤ) : R :=
  preNormEDS (b ^ 4) c d n * if Even n then b else 1

@[simp]
lemma normEDS_ofNat (n : ℕ) :
    normEDS b c d n = preNormEDS' (b ^ 4) c d n * if Even n then b else 1 := by
  simp [normEDS]

@[simp]
lemma normEDS_zero : normEDS b c d 0 = 0 := by
  simp [normEDS]

@[simp]
lemma normEDS_one : normEDS b c d 1 = 1 := by
  simp [normEDS]

@[simp]
lemma normEDS_two : normEDS b c d 2 = b := by
  simp [normEDS]

@[simp]
lemma normEDS_three : normEDS b c d 3 = c := by
  simp [normEDS, show ¬Even (3 : ℤ) by decide]

@[simp]
lemma normEDS_four : normEDS b c d 4 = d * b := by
  simp [normEDS, show ¬Odd (4 : ℤ) by decide]

@[simp]
lemma normEDS_neg (n : ℤ) : normEDS b c d (-n) = -normEDS b c d n := by
  simp_rw [normEDS, preNormEDS_neg, even_neg, neg_mul]

lemma normEDS_even (m : ℤ) : normEDS b c d (2 * m) * b =
    normEDS b c d (m - 1) ^ 2 * normEDS b c d m * normEDS b c d (m + 2) -
      normEDS b c d (m - 2) * normEDS b c d m * normEDS b c d (m + 1) ^ 2 := by
  simp_rw [normEDS, preNormEDS_even, if_pos <| even_two_mul m, Int.even_add, Int.even_sub, even_two,
    iff_true, Int.not_even_one, iff_false]
  split_ifs <;> ring1

@[deprecated (since := "2025-05-15")] alias normEDS_even_ofNat := normEDS_even

lemma normEDS_odd (m : ℤ) : normEDS b c d (2 * m + 1) =
    normEDS b c d (m + 2) * normEDS b c d m ^ 3 -
      normEDS b c d (m - 1) * normEDS b c d (m + 1) ^ 3 := by
  simp_rw [normEDS, preNormEDS_odd, if_neg m.not_even_two_mul_add_one, Int.even_add, Int.even_sub,
    even_two, iff_true, Int.not_even_one, iff_false]
  split_ifs <;> ring1

@[deprecated (since := "2025-05-15")] alias normEDS_odd_ofNat := normEDS_odd

/-- Strong recursion principle for a normalised EDS: if we have
* `P 0`, `P 1`, `P 2`, `P 3`, and `P 4`,
* for all `m : ℕ` we can prove `P (2 * (m + 3))` from `P k` for all `k < 2 * (m + 3)`, and
* for all `m : ℕ` we can prove `P (2 * (m + 2) + 1)` from `P k` for all `k < 2 * (m + 2) + 1`,
then we have `P n` for all `n : ℕ`. -/
@[elab_as_elim]
noncomputable def normEDSRec' {P : ℕ → Sort u}
    (zero : P 0) (one : P 1) (two : P 2) (three : P 3) (four : P 4)
    (even : ∀ m : ℕ, (∀ k < 2 * (m + 3), P k) → P (2 * (m + 3)))
    (odd : ∀ m : ℕ, (∀ k < 2 * (m + 2) + 1, P k) → P (2 * (m + 2) + 1)) (n : ℕ) : P n :=
  n.evenOddStrongRec (by rintro (_ | _ | _ | _) h; exacts [zero, two, four, even _ h])
    (by rintro (_ | _ | _) h; exacts [one, three, odd _ h])

/-- Recursion principle for a normalised EDS: if we have
* `P 0`, `P 1`, `P 2`, `P 3`, and `P 4`,
* for all `m : ℕ` we can prove `P (2 * (m + 3))` from `P (m + 1)`, `P (m + 2)`, `P (m + 3)`,
  `P (m + 4)`, and `P (m + 5)`, and
* for all `m : ℕ` we can prove `P (2 * (m + 2) + 1)` from `P (m + 1)`, `P (m + 2)`, `P (m + 3)`,
  and `P (m + 4)`,
then we have `P n` for all `n : ℕ`. -/
@[elab_as_elim]
noncomputable def normEDSRec {P : ℕ → Sort u}
    (zero : P 0) (one : P 1) (two : P 2) (three : P 3) (four : P 4)
    (even : ∀ m : ℕ, P (m + 1) → P (m + 2) → P (m + 3) → P (m + 4) → P (m + 5) → P (2 * (m + 3)))
    (odd : ∀ m : ℕ, P (m + 1) → P (m + 2) → P (m + 3) → P (m + 4) → P (2 * (m + 2) + 1)) (n : ℕ) :
    P n :=
  normEDSRec' zero one two three four (fun _ ih => by apply even <;> exact ih _ <| by linarith only)
    (fun _ ih => by apply odd <;> exact ih _ <| by linarith only) n

end NormEDS

section Map

variable {S : Type v} [CommRing S] (f : R →+* S)

@[simp]
lemma map_preNormEDS' (n : ℕ) : f (preNormEDS' b c d n) = preNormEDS' (f b) (f c) (f d) n := by
  induction n using normEDSRec' with
  | zero => simp
  | one => simp
  | two => simp
  | three => simp
  | four => simp
  | _ _ ih =>
    simp only [preNormEDS'_even, preNormEDS'_odd, apply_ite f, map_pow, map_mul, map_sub, map_one]
    repeat rw [ih _ <| by linarith only]

@[simp]
lemma map_preNormEDS (n : ℤ) : f (preNormEDS b c d n) = preNormEDS (f b) (f c) (f d) n := by
  simp [preNormEDS]

@[simp]
lemma map_normEDS (n : ℤ) : f (normEDS b c d n) = normEDS (f b) (f c) (f d) n := by
  simp [normEDS, apply_ite f]

end Map
