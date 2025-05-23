/-
Copyright (c) 2024 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata, Junyan Xu
-/
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.EvenOddRec
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# Elliptic divisibility sequences

This file defines the types of elliptic nets and elliptic divisibility sequences, as well as the
canonical example of a normalised elliptic divisibility sequence.

## Mathematical background

Let `R` be a commutative ring, and let `W` be a sequence of elements in `R` indexed by `ℤ`. The
*elliptic relator* `ER(p, q, r, s) ∈ R` associated to `W` is given for all `p, q, r, s ∈ ℤ` by
`ER(p, q, r, s) := W(p+q+s)W(p-q)W(r+s)W(r) - W(p+r+s)W(p-r)W(q+s)W(q) + W(q+r+s)W(q-r)W(p+s)W(p)`.
Call `W` an *elliptic net* if it satisfies the *elliptic relation* `ER(p, q, r, s) = 0` for any
`p, q, r, s ∈ ℤ`. By a cyclic permutation of variables, `ER(p, q, r, s) = 0` is essentially the same
as the symmetric elliptic relation `ERₐ(p, q, r, s) = 0`, where `ERₐ(p, q, r, s) ∈ R` is given for
all `p, q, r, s ∈ ℤ` by `ERₐ(p, q, r, s) := Wₐ(p, q)Wₐ(r, s) - Wₐ(p, r)Wₐ(q, s) + Wₐ(p, s)Wₐ(q, r)`
defined in terms of *elliptic atoms* `Wₐ(p, q) := W((p + q) / 2)W((p - q) / 2)` for some `p, q ∈ ℤ`.

As a special case, `W` is an *elliptic sequence* if it satisfies `ER(p, q, r, 0) = 0` for any
`p, q, r ∈ ℤ`. It is a *divisibility sequence* if it satisfies `W(k) ∣ W(nk)` for any `k, n ∈ ℤ`,
and an *elliptic divisibility sequence* (EDS) if it is a divisibility sequence that is elliptic. If
`W` is an EDS, then `x • W` is also an EDS for any `x ∈ R`. It turns out that any EDS `W` can be
normalised such that `W(1) = 1`, in which case it can be characterised completely by
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

* `IsEllipticNet.atom`: the elliptic atom `Wₐ(p, q)` indexed by `ℤ`.
* `IsEllipticNet.atomRel`: the elliptic relator `ERₐ(p, q, r, s)` indexed by `ℤ`.
* `IsEllipticNet.rel`: the elliptic relator `ER(p, q, r, s)` indexed by `ℤ`.
* `IsEllipticNet`: a sequence indexed by `ℤ` is an elliptic net.
* `IsElliptic`: a sequence indexed by `ℤ` is an elliptic sequence.
* `IsDivisibility`: a sequence indexed by `ℤ` is a divisibility sequence.
* `IsEDS`: a sequence indexed by `ℤ` is an EDS.
* `preNormEDS'`: the auxiliary sequence for a normalised EDS indexed by `ℕ`.
* `preNormEDS`: the auxiliary sequence for a normalised EDS indexed by `ℤ`.
* `complEDS₂`: the 2-complement sequence for a normalised EDS indexed by `ℕ`.
* `normEDS`: the canonical example of a normalised EDS indexed by `ℤ`.
* `complEDS'`: the complement sequence for a normalised EDS indexed by `ℕ`.
* `complEDS`: the complement sequence for a normalised EDS indexed by `ℤ`.

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

* K Stange, *Elliptic Nets and Elliptic Curves*
* M Ward, *Memoir on Elliptic Divisibility Sequences*

## Tags

elliptic net, elliptic divisibility sequence
-/

universe u v

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] (W : ℤ → R) (f : R →+* S)

namespace IsEllipticNet

/-- The elliptic atom `Wₐ(p, q)` that defines an elliptic net. Note that this is defined in terms of
truncated integer division, and hence should only be used when `p` and `q` have the same parity. -/
def atom (p q : ℤ) : R :=
  W ((p + q).tdiv 2) * W ((p - q).tdiv 2)

@[simp]
lemma atom_same (p : ℤ) : atom W p p = W p * W 0 := by
  rw [atom, ← two_mul, Int.mul_tdiv_cancel_left _ two_ne_zero, sub_self, Int.zero_tdiv]

variable {W} in
@[simp]
lemma neg_atom (odd : ∀ n : ℤ, W (-n) = -W n) (p q : ℤ) : -atom W p q = atom W q p := by
  simp_rw [atom, add_comm, ← neg_sub p, Int.neg_tdiv, odd, mul_neg]

variable {W} in
lemma atom_mul_atom (odd : ∀ n : ℤ, W (-n) = -W n) (p q r s : ℤ) :
    atom W p q * atom W r s = atom W q p * atom W s r := by
  rw [← neg_atom odd p q, ← neg_atom odd r s, neg_mul_neg]

variable {W} in
@[simp]
lemma atom_neg_left (odd : ∀ n : ℤ, W (-n) = -W n) (p q : ℤ) : atom W (-p) q = atom W p q := by
  simp_rw [atom, neg_add_eq_sub, ← neg_sub p, ← neg_add', Int.neg_tdiv, odd, neg_mul_neg, mul_comm]

@[simp]
lemma atom_neg_right (p q : ℤ) : atom W p (-q) = atom W p q := by
  simp_rw [atom, ← sub_eq_add_neg, sub_neg_eq_add, mul_comm]

variable {W} in
@[simp]
lemma atom_abs_left (odd : ∀ n : ℤ, W (-n) = -W n) (p q : ℤ) : atom W |p| q = atom W p q := by
  rcases abs_choice p with h | h <;> simp only [h, atom_neg_left odd]

@[simp]
lemma atom_abs_right (p q : ℤ) : atom W p |q| = atom W p q := by
  rcases abs_choice q with h | h <;> simp only [h, atom_neg_right]

lemma atom_even (p q : ℤ) : atom W (2 * p) (2 * q) = W (p + q) * W (p - q) := by
  simp_rw [atom, ← mul_add, ← mul_sub, Int.mul_tdiv_cancel_left _ two_ne_zero]

lemma atom_odd (p q : ℤ) : atom W (2 * p + 1) (2 * q + 1) = W (p + q + 1) * W (p - q) := by
  simp_rw [atom, add_add_add_comm _ (1 : ℤ), ← two_mul, ← mul_add, add_sub_add_comm, sub_self,
    add_zero, ← mul_sub, Int.mul_tdiv_cancel_left _ two_ne_zero]

@[simp]
lemma map_atom (W : ℤ → R) (p q : ℤ) : f (atom W p q) = atom (f ∘ W) p q := by
  simp_rw [atom, map_mul, Function.comp]

/-- The elliptic relator `ERₐ(p, q, r, s)` obtained by a cyclic permutation of variables in
`ER(p, q, r, s)`. Note that this is defined in terms of elliptic atoms, and hence should only be
used when `p`, `q`, `r`, and `s` all have the same parity. -/
def atomRel (p q r s : ℤ) : R :=
  atom W p q * atom W r s - atom W p r * atom W q s + atom W p s * atom W q r

@[simp]
lemma atomRel_same₁₂ (p q r : ℤ) : atomRel W p p q r = W p * W 0 * atom W q r := by
  simp_rw [atomRel, atom_same, mul_comm <| atom W p q, sub_add_cancel]

variable {W} in
@[simp]
lemma atomRel_same₁₃ (odd : ∀ n : ℤ, W (-n) = -W n) (p q r : ℤ) :
    atomRel W p q p r = W p * W 0 * atom W r q := by
  linear_combination (norm := (simp_rw [atomRel, atom_same]; ring1))
    W p * W 0 * neg_atom odd r q - atom W p r * neg_atom odd p q

variable {W} in
@[simp]
lemma atomRel_same₁₄ (odd : ∀ n : ℤ, W (-n) = -W n) (p q r : ℤ) :
    atomRel W p q r p = W p * W 0 * atom W q r := by
  simp_rw [atomRel, atom_mul_atom odd p q, mul_comm <| atom W q p, sub_self, zero_add, atom_same]

@[simp]
lemma atomRel_same₂₃ (p q r : ℤ) : atomRel W p q q r = W q * W 0 * atom W p r := by
  simp_rw [atomRel, atom_same, sub_self, zero_add, mul_comm]

variable {W} in
@[simp]
lemma atomRel_same₂₄ (odd : ∀ n : ℤ, W (-n) = -W n) (p q r : ℤ) :
    atomRel W p q r q = W q * W 0 * atom W r p := by
  linear_combination (norm := (simp_rw [atomRel, atom_same]; ring1))
    W q * W 0 * neg_atom odd p r - atom W p q * neg_atom odd q r

@[simp]
lemma atomRel_same₃₄ (p q r : ℤ) : atomRel W p q r r = W r * W 0 * atom W p q := by
  simp_rw [atomRel, atom_same, mul_comm, sub_add_cancel]

variable {W} in
@[simp]
lemma atomRel_neg₁ (odd : ∀ n : ℤ, W (-n) = -W n) (p q r s : ℤ) :
    atomRel W (-p) q r s = atomRel W p q r s := by
  simp_rw [atomRel, atom_neg_left odd]

variable {W} in
@[simp]
lemma atomRel_neg₂ (odd : ∀ n : ℤ, W (-n) = -W n) (p q r s : ℤ) :
    atomRel W p (-q) r s = atomRel W p q r s := by
  simp_rw [atomRel, atom_neg_left odd, atom_neg_right]

variable {W} in
@[simp]
lemma atomRel_neg₃ (odd : ∀ n : ℤ, W (-n) = -W n) (p q r s : ℤ) :
    atomRel W p q (-r) s = atomRel W p q r s := by
  simp_rw [atomRel, atom_neg_left odd, atom_neg_right]

@[simp]
lemma atomRel_neg₄ (p q r s : ℤ) : atomRel W p q r (-s) = atomRel W p q r s := by
  simp_rw [atomRel, atom_neg_right]

variable {W} in
@[simp]
lemma atomRel_abs₁ (odd : ∀ n : ℤ, W (-n) = -W n) (p q r s : ℤ) :
    atomRel W |p| q r s = atomRel W p q r s := by
  simp_rw [atomRel, atom_abs_left odd]

variable {W} in
@[simp]
lemma atomRel_abs₂ (odd : ∀ n : ℤ, W (-n) = -W n) (p q r s : ℤ) :
    atomRel W p |q| r s = atomRel W p q r s := by
  simp_rw [atomRel, atom_abs_left odd, atom_abs_right]

variable {W} in
@[simp]
lemma atomRel_abs₃ (odd : ∀ n : ℤ, W (-n) = -W n) (p q r s : ℤ) :
    atomRel W p q |r| s = atomRel W p q r s := by
  simp_rw [atomRel, atom_abs_left odd, atom_abs_right]

@[simp]
lemma atomRel_abs₄ (p q r s : ℤ) : atomRel W p q r |s| = atomRel W p q r s := by
  simp_rw [atomRel, atom_abs_right]

@[simp]
lemma atomRel_avg_sub {p q r s : ℤ} (parity : s % 2 = p % 2 ∧ s % 2 = q % 2 ∧ s % 2 = r % 2) :
    atomRel W ((p + q + r + s) / 2 - s) ((p + q + r + s) / 2 - r) ((p + q + r + s) / 2 - q)
      ((p + q + r + s) / 2 - p) = atomRel W p q r s := by
  have h {m n : ℤ} (h : n % 2 = m % 2) : 2 ∣ m + n := by
    rw [← sub_neg_eq_add, ← Int.modEq_iff_dvd, Int.ModEq, ← h, Int.neg_emod_two]
  simp_rw [add_assoc <| p + q, atomRel, atom, sub_add_sub_comm, ← two_mul,
    Int.mul_ediv_cancel' <| Int.dvd_add (h <| parity.2.1 ▸ parity.1) <| h parity.2.2]
  ring_nf

@[simp]
lemma map_atomRel (W : ℤ → R) (p q r s : ℤ) : f (atomRel W p q r s) = atomRel (f ∘ W) p q r s := by
  simp_rw [atomRel, map_add, map_sub, map_mul, map_atom]

/-- The elliptic relator `ER(p, q, r, s)` that defines an elliptic net. -/
def rel (p q r s : ℤ) : R :=
  W (p + q + s) * W (p - q) * W (r + s) * W r - W (p + r + s) * W (p - r) * W (q + s) * W q +
    W (q + r + s) * W (q - r) * W (p + s) * W p

lemma rel_eq (p q r s : ℤ) : rel W p q r s = atomRel W (2 * p + s) (2 * q + s) (2 * r + s) s := by
  simp_rw [rel, atomRel, atom, add_add_add_comm _ s, add_assoc _ s, ← two_mul, ← mul_add,
    add_sub_add_comm, add_sub_assoc, sub_self, add_zero, ← mul_sub,
    Int.mul_tdiv_cancel_left _ two_ne_zero, mul_comm <| _ * W p, mul_assoc]

lemma atomRel_two_mul (p q r s : ℤ) :
    atomRel W (2 * p) (2 * q) (2 * r) (2 * s) = rel W (p - s) (q - s) (r - s) (2 * s) := by
  simp_rw [rel_eq, mul_sub, sub_add_cancel]

lemma atomRel_eq {p q r s : ℤ} (parity : s % 2 = p % 2 ∧ s % 2 = q % 2 ∧ s % 2 = r % 2) :
    atomRel W p q r s = rel W ((p - s) / 2) ((q - s) / 2) ((r - s) / 2) s := by
  simp only [rel_eq, Int.mul_ediv_cancel', Int.ModEq.dvd parity.1, Int.ModEq.dvd parity.2.1,
    Int.ModEq.dvd parity.2.2, sub_add_cancel]

variable {W} in
@[simp]
lemma rel_neg (odd : ∀ n : ℤ, W (-n) = -W n) (p q r s : ℤ) :
    rel W (-p) (-q) (-r) (-s) = rel W p q r s := by
  simp_rw [rel_eq, mul_neg, ← neg_add, atomRel_neg₁ odd, atomRel_neg₂ odd, atomRel_neg₃ odd,
    atomRel_neg₄]

lemma rel_even (m : ℤ) : rel W (m + 1) (m - 1) 1 0 = W (2 * m) * W 2 * W 1 ^ 2 -
    W (m - 1) ^ 2 * W m * W (m + 2) + W (m - 2) * W m * W (m + 1) ^ 2 := by
  rw [rel]
  ring_nf

lemma rel_odd (m : ℤ) : rel W (m + 1) m 1 0 =
    W (2 * m + 1) * W 1 ^ 3 - W (m + 2) * W m ^ 3 + W (m - 1) * W (m + 1) ^ 3 := by
  rw [rel]
  ring_nf

@[simp]
lemma map_rel (W : ℤ → R) (p q r s : ℤ) : f (rel W p q r s) = rel (f ∘ W) p q r s := by
  simp_rw [rel, map_add, map_sub, map_mul, Function.comp]

end IsEllipticNet

/-- The proposition that a sequence indexed by `ℤ` is an elliptic net. -/
def IsEllipticNet : Prop :=
  ∀ p q r s : ℤ, IsEllipticNet.rel W p q r s = 0

/-- The proposition that a sequence indexed by `ℤ` is an elliptic sequence. -/
def IsElliptic : Prop :=
  ∀ p q r : ℤ, IsEllipticNet.rel W p q r 0 = 0

/-- The proposition that a sequence indexed by `ℤ` is a divisibility sequence. -/
def IsDivisibility : Prop :=
  ∀ m n : ℕ, m ∣ n → W m ∣ W n

/-- The proposition that a sequence indexed by `ℤ` is an EDS. -/
def IsEDS : Prop :=
  IsElliptic W ∧ IsDivisibility W

variable {W} in
lemma IsEllipticNet.isElliptic (h : IsEllipticNet W) : IsElliptic W :=
  (h · · · 0)

variable {W} in
lemma IsEllipticNet.smul (h : IsEllipticNet W) (x : R) : IsEllipticNet <| x • W := fun m n r s => by
  linear_combination (norm := (simp_rw [rel, Pi.smul_apply, smul_eq_mul]; ring1)) x ^ 4 * h m n r s

variable {W} in
lemma IsElliptic.smul (h : IsElliptic W) (x : R) : IsElliptic <| x • W := fun m n r => by
  linear_combination (norm := (simp_rw [IsEllipticNet.rel, Pi.smul_apply, smul_eq_mul]; ring1))
    x ^ 4 * h m n r

variable {W} in
lemma IsDivisibility.smul (h : IsDivisibility W) (x : R) : IsDivisibility <| x • W :=
  (mul_dvd_mul_left x <| h · · ·)

variable {W} in
lemma IsEDS.smul (h : IsEDS W) (x : R) : IsEDS <| x • W :=
  ⟨h.left.smul x, h.right.smul x⟩

lemma isEllipticNet_id : IsEllipticNet id :=
  fun _ _ _ _ => by simp_rw [IsEllipticNet.rel, id_eq]; ring1

lemma isElliptic_id : IsElliptic id :=
  isEllipticNet_id.isElliptic

lemma isDivisibility_id : IsDivisibility id :=
  fun _ _ => Int.ofNat_dvd.mpr

lemma isEDS_id : IsEDS id :=
  ⟨isElliptic_id, isDivisibility_id⟩

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

This extends `preNormEDS'` by defining its values at negative integers. -/
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

/-- The 2-complement sequence `Wᶜ₂ : ℤ → R` for a normalised EDS `W : ℤ → R` that witnesses
`W(k) ∣ W(2k)`. In other words, `W(k)Wᶜ₂(k) = W(2k)` for any `k ∈ ℤ`.

This is defined in terms of `preNormEDS`. -/
def complEDS₂ (k : ℤ) : R :=
  (preNormEDS (b ^ 4) c d (k - 1) ^ 2 * preNormEDS (b ^ 4) c d (k + 2) -
    preNormEDS (b ^ 4) c d (k - 2) * preNormEDS (b ^ 4) c d (k + 1) ^ 2) * if Even k then 1 else b

@[simp]
lemma complEDS₂_zero : complEDS₂ b c d 0 = 2 := by
  simp [complEDS₂, one_add_one_eq_two]

@[simp]
lemma complEDS₂_one : complEDS₂ b c d 1 = b := by
  simp [complEDS₂]

@[simp]
lemma complEDS₂_two : complEDS₂ b c d 2 = d := by
  simp [complEDS₂]

@[simp]
lemma complEDS₂_three : complEDS₂ b c d 3 = preNormEDS (b ^ 4) c d 5 * b - d ^ 2 * b := by
  simp [complEDS₂, if_neg (by decide : ¬Even (3 : ℤ)), sub_mul]

@[simp]
lemma complEDS₂_four : complEDS₂ b c d 4 =
    c ^ 2 * preNormEDS (b ^ 4) c d 6 - preNormEDS (b ^ 4) c d 5 ^ 2 := by
  simp [complEDS₂, if_pos (by decide : Even (4 : ℤ))]

@[simp]
lemma complEDS₂_neg (k : ℤ) : complEDS₂ b c d (-k) = complEDS₂ b c d k := by
  simp_rw [complEDS₂, ← neg_add', ← sub_neg_eq_add, ← neg_sub', preNormEDS_neg, even_neg]
  ring1

lemma preNormEDS_mul_complEDS₂ (k : ℤ) : preNormEDS (b ^ 4) c d k * complEDS₂ b c d k =
    preNormEDS (b ^ 4) c d (2 * k) * if Even k then 1 else b := by
  rw [complEDS₂, preNormEDS_even]
  ring1

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

lemma normEDS_mul_complEDS₂ (k : ℤ) :
    normEDS b c d k * complEDS₂ b c d k = normEDS b c d (2 * k) := by
  simp_rw [normEDS, mul_right_comm, preNormEDS_mul_complEDS₂, mul_assoc, apply_ite₂, one_mul,
    mul_one, ite_self, if_pos <| even_two_mul k]

lemma normEDS_dvd_normEDS_two_mul (k : ℤ) : normEDS b c d k ∣ normEDS b c d (2 * k) :=
  ⟨complEDS₂ .., (normEDS_mul_complEDS₂ ..).symm⟩

lemma complEDS₂_mul_b (k : ℤ) : complEDS₂ b c d k * b =
    normEDS b c d (k - 1) ^ 2 * normEDS b c d (k + 2) -
      normEDS b c d (k - 2) * normEDS b c d (k + 1) ^ 2 := by
  induction k using Int.negInduction with
  | nat k =>
    simp_rw [complEDS₂, normEDS, Int.even_add, Int.even_sub, even_two, iff_true, Int.not_even_one,
      iff_false]
    split_ifs <;> ring1
  | neg ih =>
    simp_rw [complEDS₂_neg, ← sub_neg_eq_add, ← neg_sub', ← neg_add', normEDS_neg, ih]
    ring1

lemma normEDS_even (m : ℤ) : normEDS b c d (2 * m) * b =
    normEDS b c d (m - 1) ^ 2 * normEDS b c d m * normEDS b c d (m + 2) -
      normEDS b c d (m - 2) * normEDS b c d m * normEDS b c d (m + 1) ^ 2 := by
  rw [← normEDS_mul_complEDS₂, mul_assoc, complEDS₂_mul_b]
  ring1

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

section ComplEDS

variable (k : ℤ)

/-- The complement sequence `Wᶜ : ℤ × ℕ → R` for a normalised EDS `W : ℤ → R` that witnesses
`W(k) ∣ W(nk)`. In other words, `W(k)Wᶜ(k, n) = W(nk)` for any `k, n ∈ ℤ`.

This is defined in terms of `normEDS` and agrees with `complEDS₂` when `n = 2`. -/
def complEDS' : ℕ → R
  | 0 => 0
  | 1 => 1
  | (n + 2) => let m := n / 2 + 1
    if hn : Even n then complEDS' m * complEDS₂ b c d (m * k) else
      have : m + 1 < n + 2 :=
        add_lt_add_right (Nat.div_lt_self (Nat.not_even_iff_odd.mp hn).pos one_lt_two) 2
      complEDS' m ^ 2 * normEDS b c d ((m + 1) * k + 1) * normEDS b c d ((m + 1) * k - 1) -
        complEDS' (m + 1) ^ 2 * normEDS b c d (m * k + 1) * normEDS b c d (m * k - 1)

@[simp]
lemma complEDS'_zero : complEDS' b c d k 0 = 0 := by
  rw [complEDS']

@[simp]
lemma complEDS'_one : complEDS' b c d k 1 = 1 := by
  rw [complEDS']

lemma complEDS'_even (m : ℕ) : complEDS' b c d k (2 * (m + 1)) =
    complEDS' b c d k (m + 1) * complEDS₂ b c d ((m + 1) * k) := by
  rw [show 2 * (m + 1) = 2 * m + 2 by rfl, complEDS', dif_pos <| even_two_mul m,
    m.mul_div_cancel_left two_pos, Nat.cast_succ]

lemma complEDS'_odd (m : ℕ) : complEDS' b c d k (2 * (m + 1) + 1) =
    complEDS' b c d k (m + 1) ^ 2
        * normEDS b c d ((m + 2) * k + 1) * normEDS b c d ((m + 2) * k - 1) -
      complEDS' b c d k (m + 2) ^ 2
          * normEDS b c d ((m + 1) * k + 1) * normEDS b c d ((m + 1) * k - 1) := by
  rw [show 2 * (m + 1) + 1 = 2 * m + 3 by rfl, complEDS', dif_neg m.not_even_two_mul_add_one]
  simpa only [Nat.mul_add_div two_pos] using by rfl

/-- The complement sequence `Wᶜ : ℤ × ℤ → R` for a normalised EDS `W : ℤ → R` that witnesses
`W(k) ∣ W(nk)`. In other words, `W(k)Wᶜ(k, n) = W(nk)` for any `k, n ∈ ℤ`.

This extends `complEDS'` by defining its values at negative integers. -/
def complEDS (n : ℤ) : R :=
  n.sign * complEDS' b c d k n.natAbs

@[simp]
lemma complEDS_ofNat (n : ℕ) : complEDS b c d k n = complEDS' b c d k n := by
  by_cases hn : n = 0
  · simp [hn, complEDS]
  · simp [complEDS, Int.sign_natCast_of_ne_zero hn]

@[simp]
lemma complEDS_zero : complEDS b c d k 0 = 0 := by
  simp [complEDS]

@[simp]
lemma complEDS_one : complEDS b c d k 1 = 1 := by
  simp [complEDS]

@[simp]
lemma complEDS_neg (n : ℤ) : complEDS b c d k (-n) = -complEDS b c d k n := by
  simp [complEDS]

lemma complEDS_even (m : ℤ) :
    complEDS b c d k (2 * m) = complEDS b c d k m * complEDS₂ b c d (m * k) := by
  induction m using Int.negInduction with
  | nat m =>
    rcases m with _ | _
    · simp
    norm_cast
    simpa only [complEDS_ofNat] using complEDS'_even ..
  | neg ih => simp_rw [mul_neg, complEDS_neg, ih, neg_mul, complEDS₂_neg]

lemma complEDS_odd (m : ℤ) : complEDS b c d k (2 * m + 1) =
    complEDS b c d k m ^ 2 * normEDS b c d ((m + 1) * k + 1) * normEDS b c d ((m + 1) * k - 1) -
      complEDS b c d k (m + 1) ^ 2 * normEDS b c d (m * k + 1) * normEDS b c d (m * k - 1) := by
  induction m using Int.negInduction with
  | nat m =>
    rcases m with _ | _
    · simp
    norm_cast
    simpa only [complEDS_ofNat] using complEDS'_odd ..
  | neg ih m =>
    rcases m with _ | m
    · simp
    simp_rw [Nat.cast_succ, show 2 * -(m + 1 : ℤ) + 1 = -(2 * m + 1) by rfl,
      show (-(m + 1 : ℤ) + 1) = -m by ring1, neg_mul, ← sub_neg_eq_add, ← neg_sub', sub_neg_eq_add,
      ← neg_add', complEDS_neg, normEDS_neg, ih]
    ring1

/-- Strong recursion principle for the complement sequence for a normalised EDS: if we have
 * `P 0`, `P 1`,
 * for all `m : ℕ` we can prove `P (2 * (m + 3))` from `P k` for all `k < 2 * (m + 3)`, and
 * for all `m : ℕ` we can prove `P (2 * (m + 2) + 1)` from `P k` for all `k < 2 * (m + 2) + 1`,
then we have `P n` for all `n : ℕ`. -/
@[elab_as_elim]
noncomputable def complEDSRec' {P : ℕ → Sort u} (zero : P 0) (one : P 1)
    (even : ∀ m : ℕ, (∀ k < 2 * (m + 1), P k) → P (2 * (m + 1)))
    (odd : ∀ m : ℕ, (∀ k < 2 * (m + 1) + 1, P k) → P (2 * (m + 1) + 1)) (n : ℕ) : P n :=
  n.evenOddStrongRec (by rintro (_ | _) h; exacts [zero, even _ h])
    (by rintro (_ | _) h; exacts [one, odd _ h])

/-- Recursion principle for the complement sequence for a normalised EDS: if we have
 * `P 0`, `P 1`,
 * for all `m : ℕ` we can prove `P (2 * (m + 3))` from `P (m + 1)`, `P (m + 2)`, `P (m + 3)`,
    `P (m + 4)`, and `P (m + 5)`, and
 * for all `m : ℕ` we can prove `P (2 * (m + 2) + 1)` from `P (m + 1)`, `P (m + 2)`, `P (m + 3)`,
    and `P (m + 4)`,
then we have `P n` for all `n : ℕ`. -/
@[elab_as_elim]
noncomputable def complEDSRec {P : ℕ → Sort u} (zero : P 0) (one : P 1)
    (even : ∀ m : ℕ, P (m + 1) → P (2 * (m + 1)))
    (odd : ∀ m : ℕ, P (m + 1) → P (m + 2) → P (2 * (m + 1) + 1)) (n : ℕ) : P n :=
  complEDSRec' zero one (fun _ ih => even _ <| ih _ <| by linarith only)
    (fun _ ih => odd _ (ih _ <| by linarith only) <| ih _ <| by linarith only) n

end ComplEDS

section Map

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
lemma map_complEDS₂ (n : ℤ) : f (complEDS₂ b c d n) = complEDS₂ (f b) (f c) (f d) n := by
  simp [complEDS₂, apply_ite f]

@[simp]
lemma map_normEDS (n : ℤ) : f (normEDS b c d n) = normEDS (f b) (f c) (f d) n := by
  simp [normEDS, apply_ite f]

@[simp]
lemma map_complEDS' (k : ℤ) (n : ℕ) :
    f (complEDS' b c d k n) = complEDS' (f b) (f c) (f d) k n := by
  induction n using complEDSRec' with
  | zero => simp
  | one => simp
  | _ _ ih =>
    simp only [complEDS'_even, complEDS'_odd, map_normEDS, map_complEDS₂, map_pow, map_mul, map_sub]
    repeat rw [ih _ <| by linarith only]

@[simp]
lemma map_complEDS (k n : ℤ) : f (complEDS b c d k n) = complEDS (f b) (f c) (f d) k n := by
  simp [complEDS]

end Map
