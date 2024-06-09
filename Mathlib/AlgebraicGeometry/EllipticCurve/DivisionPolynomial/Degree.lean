/-
Copyright (c) 2024 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.Tactic.ComputeDegree

/-!
# Division polynomials of Weierstrass curves

This file computes the leading terms of certain polynomials associated to division polynomials of
Weierstrass curves defined in `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`.
In particular, they can be computed by strong induction to be:
 * $\tilde{\Psi}_n = nX^{\tfrac{n^2 - 4}{2}} + \dots$ if $n$ is even,
 * $\tilde{\Psi}_n = nX^{\tfrac{n^2 - 1}{2}} + \dots$ if $n$ is odd,
 * $\Psi_n^{[2]} = n^2X^{n^2 - 1} + \dots$, and
 * $\Phi_n = X^{n^2} + \dots$.

## Main statements

 * `WeierstrassCurve.natDegree_preΨ`: the degree of $\tilde{\Psi}_n$.
 * `WeierstrassCurve.coeff_preΨ`: the leading coefficient of $\tilde{\Psi}_n$.
 * `WeierstrassCurve.natDegree_ΨSq`: the degree of $\Psi_n^{[2]}$.
 * `WeierstrassCurve.coeff_ΨSq`: the leading coefficient of $\Psi_n^{[2]}$.
 * `WeierstrassCurve.natDegree_Φ`: the degree of $\Phi_n$.
 * `WeierstrassCurve.coeff_Φ`: the leading coefficient of $\Phi_n$.

## References

[J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, division polynomial, torsion point
-/

open Polynomial PolynomialPolynomial

universe u

namespace WeierstrassCurve

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

lemma natDegree_Ψ₂Sq : W.Ψ₂Sq.natDegree ≤ 3 := by
  rw [Ψ₂Sq]
  compute_degree

@[simp]
lemma coeff_Ψ₂Sq : W.Ψ₂Sq.coeff 3 = 4 := by
  rw [Ψ₂Sq]
  compute_degree!

lemma natDegree_Ψ₃ : W.Ψ₃.natDegree ≤ 4 := by
  rw [Ψ₃]
  compute_degree

@[simp]
lemma coeff_Ψ₃ : W.Ψ₃.coeff 4 = 3 := by
  rw [Ψ₃]
  compute_degree!

lemma natDegree_preΨ₄ : W.preΨ₄.natDegree ≤ 6 := by
  rw [preΨ₄]
  compute_degree

@[simp]
lemma coeff_preΨ₄ : W.preΨ₄.coeff 6 = 2 := by
  rw [preΨ₄]
  compute_degree!

private lemma natDegree_odd {a b c d e f : R[X]} {da db dc dd de df n : ℕ}
    (ha : a.natDegree ≤ da) (hb : b.natDegree ≤ db) (hc : c.natDegree ≤ dc)
    (hd : d.natDegree ≤ dd) (he : e.natDegree ≤ de) (hf : f.natDegree ≤ df)
    (habc : n = da + 3 * db + 2 * dc) (hdef : n = dd + 3 * de + 2 * df) :
    (a * b ^ 3 * c ^ 2 - d * e ^ 3 * f ^ 2).natDegree ≤ n := by
  nth_rw 1 [← max_self n, habc, hdef]
  convert natDegree_sub_le_of_le .. using 1
  · exact natDegree_mul_le_of_le (natDegree_mul_le_of_le ha <| natDegree_pow_le_of_le 3 hb) <|
      natDegree_pow_le_of_le 2 hc
  · exact natDegree_mul_le_of_le (natDegree_mul_le_of_le hd <| natDegree_pow_le_of_le 3 he) <|
      natDegree_pow_le_of_le 2 hf

private lemma coeff_odd {a b c d e f : R[X]} {da db dc dd de df n : ℕ}
    (ha : a.natDegree ≤ da) (hb : b.natDegree ≤ db) (hc : c.natDegree ≤ dc)
    (hd : d.natDegree ≤ dd) (he : e.natDegree ≤ de) (hf : f.natDegree ≤ df)
    (habc : n = da + 3 * db + 2 * dc) (hdef : n = dd + 3 * de + 2 * df) :
    (a * b ^ 3 * c ^ 2 - d * e ^ 3 * f ^ 2).coeff n = a.coeff da * b.coeff db ^ 3 * c.coeff dc ^ 2 -
      d.coeff dd * e.coeff de ^ 3 * f.coeff df ^ 2 := by
  rw [coeff_sub, habc, coeff_mul_of_natDegree_le
      (natDegree_mul_le_of_le ha <| natDegree_pow_le_of_le 3 hb) <| natDegree_pow_le_of_le 2 hc,
    coeff_pow_of_natDegree_le hc, coeff_mul_of_natDegree_le ha <| natDegree_pow_le_of_le 3 hb,
    coeff_pow_of_natDegree_le hb, ← habc, hdef, coeff_mul_of_natDegree_le
      (natDegree_mul_le_of_le hd <| natDegree_pow_le_of_le 3 he) <| natDegree_pow_le_of_le 2 hf,
    coeff_mul_of_natDegree_le hd <| natDegree_pow_le_of_le 3 he, coeff_pow_of_natDegree_le he,
    coeff_pow_of_natDegree_le hf]

private lemma natDegree_even {a b c d e f : R[X]} {da db dc dd de df n : ℕ}
    (ha : a.natDegree ≤ da) (hb : b.natDegree ≤ db) (hc : c.natDegree ≤ dc)
    (hd : d.natDegree ≤ dd) (he : e.natDegree ≤ de) (hf : f.natDegree ≤ df)
    (habc : n = 2 * da + db + dc) (hdef : n = dd + de + 2 * df) :
    (a ^ 2 * b * c - d * e * f ^ 2).natDegree ≤ n := by
  nth_rw 1 [← max_self n, habc, hdef]
  convert natDegree_sub_le_of_le .. using 1
  · exact natDegree_mul_le_of_le (natDegree_mul_le_of_le (natDegree_pow_le_of_le 2 ha) hb) hc
  · exact natDegree_mul_le_of_le (natDegree_mul_le_of_le hd he) <| natDegree_pow_le_of_le 2 hf

private lemma coeff_even {a b c d e f : R[X]} {da db dc dd de df n : ℕ}
    (ha : a.natDegree ≤ da) (hb : b.natDegree ≤ db) (hc : c.natDegree ≤ dc)
    (hd : d.natDegree ≤ dd) (he : e.natDegree ≤ de) (hf : f.natDegree ≤ df)
    (habc : n = 2 * da + db + dc) (hdef : n = dd + de + 2 * df) :
    (a ^ 2 * b * c - d * e * f ^ 2).coeff n =
      a.coeff da ^ 2 * b.coeff db * c.coeff dc - d.coeff dd * e.coeff de * f.coeff df ^ 2 := by
  rw [coeff_sub, habc, coeff_mul_of_natDegree_le
      (natDegree_mul_le_of_le (natDegree_pow_le_of_le 2 ha) hb) hc,
    coeff_mul_of_natDegree_le (natDegree_pow_le_of_le 2 ha) hb, coeff_pow_of_natDegree_le ha,
    ← habc, hdef, coeff_mul_of_natDegree_le (natDegree_mul_le_of_le hd he) <|
      natDegree_pow_le_of_le 2 hf, coeff_mul_of_natDegree_le hd he, coeff_pow_of_natDegree_le hf]

private lemma natDegree_preΨ'_zero : (W.preΨ' 0).natDegree = 0 := by
  rw [preΨ'_zero, natDegree_zero]

private lemma coeff_preΨ'_zero : (W.preΨ' 0).coeff 0 = 0 := by
  rw [preΨ'_zero, coeff_zero]

private lemma natDegree_preΨ'_one : (W.preΨ' 1).natDegree = 0 := by
  rw [preΨ'_one, natDegree_one]

private lemma coeff_preΨ'_one : (W.preΨ' 1).coeff 0 = 1 := by
  rw [preΨ'_one, coeff_one_zero]

private lemma natDegree_preΨ'_two : (W.preΨ' 2).natDegree = 0 := by
  rw [preΨ'_two, natDegree_one]

private lemma coeff_preΨ'_two : (W.preΨ' 2).coeff 0 = 1 := by
  rw [preΨ'_two, coeff_one_zero]

private lemma natDegree_preΨ'_three : (W.preΨ' 3).natDegree ≤ 4 := by
  simp only [preΨ'_three, natDegree_Ψ₃]

private lemma coeff_preΨ'_three : (W.preΨ' 3).coeff 4 = 3 := by
  rw [preΨ'_three, coeff_Ψ₃]

private lemma natDegree_preΨ'_four : (W.preΨ' 4).natDegree ≤ 6 := by
  simp only [preΨ'_four, natDegree_preΨ₄]

private lemma coeff_preΨ'_four : (W.preΨ' 4).coeff 6 = 2 := by
  rw [preΨ'_four, coeff_preΨ₄]

private lemma natDegree_preΨ'_five : (W.preΨ' 5).natDegree ≤ 12 := by
  rw [show 5 = 2 * 2 + 1 by rfl, preΨ'_odd, if_pos even_zero, if_pos even_zero, ← @one_pow R[X]]
  exact natDegree_odd W.natDegree_preΨ'_four W.natDegree_preΨ'_two.le W.natDegree_Ψ₂Sq
    W.natDegree_preΨ'_one.le W.natDegree_preΨ'_three natDegree_one.le rfl rfl

private lemma coeff_preΨ'_five : (W.preΨ' 5).coeff 12 = 5 := by
  rw [show 5 = 2 * 2 + 1 by rfl, preΨ'_odd, if_pos even_zero, if_pos even_zero, ← @one_pow R[X],
    coeff_odd W.natDegree_preΨ'_four W.natDegree_preΨ'_two.le W.natDegree_Ψ₂Sq
      W.natDegree_preΨ'_one.le W.natDegree_preΨ'_three natDegree_one.le rfl rfl, coeff_preΨ'_four,
    coeff_preΨ'_two, coeff_Ψ₂Sq, coeff_preΨ'_one, coeff_preΨ'_three, coeff_one_zero]
  norm_num1

private lemma natDegree_preΨ'_six : (W.preΨ' 6).natDegree ≤ 16 := by
  rw [show 6 = 2 * 3 by rfl, preΨ'_even]
  exact natDegree_even W.natDegree_preΨ'_two.le W.natDegree_preΨ'_three W.natDegree_preΨ'_five
    W.natDegree_preΨ'_one.le W.natDegree_preΨ'_three W.natDegree_preΨ'_four rfl rfl

private lemma coeff_preΨ'_six : (W.preΨ' 6).coeff 16 = 3 := by
  rw [show 6 = 2 * 3 by rfl, preΨ'_even, coeff_even W.natDegree_preΨ'_two.le W.natDegree_preΨ'_three
      W.natDegree_preΨ'_five W.natDegree_preΨ'_one.le W.natDegree_preΨ'_three W.natDegree_preΨ'_four
      rfl rfl, coeff_preΨ'_two, coeff_preΨ'_three, coeff_preΨ'_five, coeff_preΨ'_one,
    coeff_preΨ'_four]
  norm_num1

private lemma natDegree_preΨ'_eight : (W.preΨ' 8).natDegree ≤ 30 := by
  rw [show 8 = 2 * 4 by rfl, preΨ'_even]
  exact natDegree_even W.natDegree_preΨ'_three W.natDegree_preΨ'_four W.natDegree_preΨ'_six
    W.natDegree_preΨ'_two.le W.natDegree_preΨ'_four W.natDegree_preΨ'_five rfl rfl

private lemma coeff_preΨ'_eight : (W.preΨ' 8).coeff 30 = 4 := by
  rw [show 8 = 2 * 4 by rfl, preΨ'_even, coeff_even W.natDegree_preΨ'_three W.natDegree_preΨ'_four
      W.natDegree_preΨ'_six W.natDegree_preΨ'_two.le W.natDegree_preΨ'_four W.natDegree_preΨ'_five
      rfl rfl, coeff_preΨ'_three, coeff_preΨ'_four, coeff_preΨ'_six, coeff_preΨ'_two,
    coeff_preΨ'_five]
  norm_num1

variable {W} (m : ℕ) (ih : ∀ k < 2 * m + 2,
  ((W.preΨ' <| 2 * k).natDegree ≤ 2 * k ^ 2 - 2 ∧ (W.preΨ' <| 2 * k).coeff (2 * k ^ 2 - 2) = k) ∧
  ((W.preΨ' <| 2 * k + 1).natDegree ≤ 2 * k ^ 2 + 2 * k ∧
    (W.preΨ' <| 2 * k + 1).coeff (2 * k ^ 2 + 2 * k) = (2 * k + 1 : ℕ)))

private lemma natDegree_preΨ'_add_one : (W.preΨ' <| 2 * m + 1).natDegree ≤ 2 * m * (m + 1) := by
  convert (ih m <| by linarith only).right.left using 1
  ring1

private lemma coeff_preΨ'_add_one :
    (W.preΨ' <| 2 * m + 1).coeff (2 * m * (m + 1)) = (2 * m + 1 : ℕ) := by
  convert (ih m <| by linarith only).right.right using 2
  ring1

private lemma natDegree_preΨ'_add_two : (W.preΨ' <| 2 * m + 2).natDegree ≤ 2 * m * (m + 2) := by
  convert (ih (m + 1) <| by linarith only).left.left using 1
  rw [show 2 * (m + 1) ^ 2 = 2 * m * (m + 2) + 2 by ring1, Nat.add_sub_cancel]

private lemma coeff_preΨ'_add_two :
    (W.preΨ' <| 2 * m + 2).coeff (2 * m * (m + 2)) = (m + 1 : ℕ) := by
  convert (ih (m + 1) <| by linarith only).left.right using 2
  rw [show 2 * (m + 1) ^ 2 = 2 * m * (m + 2) + 2 by ring1, Nat.add_sub_cancel]

private lemma natDegree_preΨ'_add_three :
    (W.preΨ' <| 2 * m + 3).natDegree ≤ 2 * (m + 1) * (m + 2) := by
  convert (ih (m + 1) <| by linarith only).right.left using 1
  ring1

private lemma coeff_preΨ'_add_three :
    (W.preΨ' <| 2 * m + 3).coeff (2 * (m + 1) * (m + 2)) = (2 * m + 3 : ℕ) := by
  convert (ih (m + 1) <| by linarith only).right.right using 2
  ring1

private lemma natDegree_preΨ'_add_four :
    (W.preΨ' <| 2 * m + 4).natDegree ≤ 2 * (m + 1) * (m + 3) := by
  rcases m with _ | m
  · exact W.natDegree_preΨ'_four
  · convert (ih (m + 3) <| by linarith only).left.left using 1
    rw [show 2 * (m + 3) ^ 2 = 2 * (m + 2) * (m + 4) + 2 by ring1, Nat.add_sub_cancel]

private lemma coeff_preΨ'_add_four :
    (W.preΨ' <| 2 * m + 4).coeff (2 * (m + 1) * (m + 3)) = (m + 2 : ℕ) := by
  rcases m with _ | m
  · exact W.coeff_preΨ'_four
  · convert (ih (m + 3) <| by linarith only).left.right using 2
    rw [show 2 * (m + 3) ^ 2 = 2 * (m + 2) * (m + 4) + 2 by ring1, Nat.add_sub_cancel]

private lemma natDegree_preΨ'_add_five :
    (W.preΨ' <| 2 * m + 5).natDegree ≤ 2 * (m + 2) * (m + 3) := by
  rcases m with _ | m
  · exact W.natDegree_preΨ'_five
  · convert (ih (m + 3) <| by linarith only).right.left using 1
    ring1

private lemma coeff_preΨ'_add_five :
    (W.preΨ' <| 2 * m + 5).coeff (2 * (m + 2) * (m + 3)) = (2 * m + 5 : ℕ) := by
  rcases m with _ | m
  · exact W.coeff_preΨ'_five
  · convert (ih (m + 3) <| by linarith only).right.right using 2
    ring1

private lemma natDegree_preΨ'_add_six :
    (W.preΨ' <| 2 * m + 6).natDegree ≤ 2 * (m + 2) * (m + 4) := by
  rcases m with _ | _ | m
  · exact W.natDegree_preΨ'_six
  · exact W.natDegree_preΨ'_eight
  · convert (ih (m + 5) <| by linarith only).left.left using 1
    rw [show 2 * (m + 5) ^ 2 = 2 * (m + 4) * (m + 6) + 2 by ring1, Nat.add_sub_cancel]

private lemma coeff_preΨ'_add_six :
    (W.preΨ' <| 2 * m + 6).coeff (2 * (m + 2) * (m + 4)) = (m + 3 : ℕ) := by
  rcases m with _ | _ | m
  · exact W.coeff_preΨ'_six
  · exact W.coeff_preΨ'_eight
  · convert (ih (m + 5) <| by linarith only).left.right using 2
    rw [show 2 * (m + 5) ^ 2 = 2 * (m + 4) * (m + 6) + 2 by ring1, Nat.add_sub_cancel]

private lemma natDegree_odd_preΨ'_even :
    (W.preΨ' <| 2 * (2 * m + 2) + 1).natDegree ≤ 2 * (2 * m + 2) * (2 * m + 3) := by
  rw [preΨ'_odd, if_pos <| even_two_mul m, if_pos <| even_two_mul m, ← @one_pow R[X]]
  exact natDegree_odd (natDegree_preΨ'_add_four m ih) (natDegree_preΨ'_add_two m ih)
    W.natDegree_Ψ₂Sq (natDegree_preΨ'_add_one m ih) (natDegree_preΨ'_add_three m ih)
    natDegree_one.le (by ring1) (by ring1)

private lemma coeff_odd_preΨ'_even :
    (W.preΨ' <| 2 * (2 * m + 2) + 1).coeff (2 * (2 * m + 2) * (2 * m + 3)) =
      (2 * (2 * m + 2) + 1 : ℕ) := by
  rw [preΨ'_odd, if_pos <| even_two_mul m, if_pos <| even_two_mul m, ← @one_pow R[X],
    coeff_odd (natDegree_preΨ'_add_four m ih) (natDegree_preΨ'_add_two m ih) W.natDegree_Ψ₂Sq
      (natDegree_preΨ'_add_one m ih) (natDegree_preΨ'_add_three m ih) natDegree_one.le (by ring1)
      (by ring1), coeff_preΨ'_add_four m ih, coeff_preΨ'_add_two m ih, coeff_Ψ₂Sq,
    coeff_preΨ'_add_one m ih, coeff_preΨ'_add_three m ih, coeff_one_zero]
  push_cast
  ring1

private lemma natDegree_odd_preΨ'_odd :
    (W.preΨ' <| 2 * (2 * m + 3) + 1).natDegree ≤ 2 * (2 * m + 3) * (2 * m + 4) := by
  rw [preΨ'_odd, if_neg m.not_even_two_mul_add_one, ← @one_pow R[X],
    if_neg m.not_even_two_mul_add_one]
  exact natDegree_odd (natDegree_preΨ'_add_five m ih) (natDegree_preΨ'_add_three m ih)
    natDegree_one.le (natDegree_preΨ'_add_two m ih) (natDegree_preΨ'_add_four m ih) W.natDegree_Ψ₂Sq
    (by ring1) (by ring1)

private lemma coeff_odd_preΨ'_odd :
    (W.preΨ' <| 2 * (2 * m + 3) + 1).coeff (2 * (2 * m + 3) * (2 * m + 4)) =
      (2 * (2 * m + 3) + 1 : ℕ) := by
  rw [preΨ'_odd, if_neg m.not_even_two_mul_add_one, ← @one_pow R[X],
    if_neg m.not_even_two_mul_add_one, coeff_odd (natDegree_preΨ'_add_five m ih)
      (natDegree_preΨ'_add_three m ih) natDegree_one.le (natDegree_preΨ'_add_two m ih)
      (natDegree_preΨ'_add_four m ih) W.natDegree_Ψ₂Sq (by ring1) (by ring1),
    coeff_preΨ'_add_five m ih, coeff_preΨ'_add_three m ih, coeff_one_zero, coeff_preΨ'_add_two m ih,
    coeff_preΨ'_add_four m ih, coeff_Ψ₂Sq]
  push_cast
  ring1

private lemma natDegree_even_preΨ'_even :
    (W.preΨ' <| 2 * (2 * m + 3)).natDegree ≤ 2 * (2 * m + 2) * (2 * m + 4) := by
  rw [preΨ'_even]
  exact natDegree_even (natDegree_preΨ'_add_two m ih) (natDegree_preΨ'_add_three m ih)
    (natDegree_preΨ'_add_five m ih) (natDegree_preΨ'_add_one m ih) (natDegree_preΨ'_add_three m ih)
    (natDegree_preΨ'_add_four m ih) (by ring1) (by ring1)

private lemma coeff_even_preΨ'_even :
    (W.preΨ' <| 2 * (2 * m + 3)).coeff (2 * (2 * m + 2) * (2 * m + 4)) = (2 * m + 3 : ℕ) := by
  rw [preΨ'_even, coeff_even (natDegree_preΨ'_add_two m ih) (natDegree_preΨ'_add_three m ih)
      (natDegree_preΨ'_add_five m ih) (natDegree_preΨ'_add_one m ih)
      (natDegree_preΨ'_add_three m ih) (natDegree_preΨ'_add_four m ih) (by ring1) (by ring1),
    coeff_preΨ'_add_two m ih, coeff_preΨ'_add_three m ih, coeff_preΨ'_add_five m ih,
    coeff_preΨ'_add_one m ih, coeff_preΨ'_add_four m ih]
  push_cast
  ring1

private lemma natDegree_even_preΨ'_odd :
    (W.preΨ' <| 2 * (2 * m + 4)).natDegree ≤ 2 * (2 * m + 3) * (2 * m + 5) := by
  rw [preΨ'_even]
  exact natDegree_even (natDegree_preΨ'_add_three m ih) (natDegree_preΨ'_add_four m ih)
    (natDegree_preΨ'_add_six m ih) (natDegree_preΨ'_add_two m ih) (natDegree_preΨ'_add_four m ih)
    (natDegree_preΨ'_add_five m ih) (by ring1) (by ring1)

private lemma coeff_even_preΨ'_odd :
    (W.preΨ' <| 2 * (2 * m + 4)).coeff (2 * (2 * m + 3) * (2 * m + 5)) = (2 * m + 4 : ℕ) := by
  rw [preΨ'_even, coeff_even (natDegree_preΨ'_add_three m ih) (natDegree_preΨ'_add_four m ih)
      (natDegree_preΨ'_add_six m ih) (natDegree_preΨ'_add_two m ih) (natDegree_preΨ'_add_four m ih)
      (natDegree_preΨ'_add_five m ih) (by ring1) (by ring1), coeff_preΨ'_add_three m ih,
    coeff_preΨ'_add_four m ih, coeff_preΨ'_add_six m ih, coeff_preΨ'_add_two m ih,
    coeff_preΨ'_add_five m ih]
  push_cast
  ring1

private lemma natDegree_coeff_preΨ' (n : ℕ) :
    if Even n then (W.preΨ' n).natDegree ≤ (n ^ 2 - 4) / 2 ∧
        (W.preΨ' n).coeff ((n ^ 2 - 4) / 2) = (n / 2 : ℕ)
      else (W.preΨ' n).natDegree ≤ (n ^ 2 - 1) / 2 ∧ (W.preΨ' n).coeff ((n ^ 2 - 1) / 2) = n := by
  induction n using normEDSRec' with
  | zero => exact ⟨W.natDegree_preΨ'_zero.le, by erw [coeff_preΨ'_zero, Nat.cast_zero]⟩
  | one => exact ⟨W.natDegree_preΨ'_one.le, by erw [coeff_preΨ'_one, Nat.cast_one]⟩
  | two => exact ⟨W.natDegree_preΨ'_two.le, by erw [coeff_preΨ'_two, Nat.cast_one]⟩
  | three => exact ⟨W.natDegree_preΨ'_three, W.coeff_preΨ'_three⟩
  | four => exact ⟨W.natDegree_preΨ'_four, W.coeff_preΨ'_four⟩
  | _ m ih =>
    replace ih (k : ℕ) (hk : k < m + 2) :
        ((W.preΨ' <| 2 * k).natDegree ≤ 2 * k ^ 2 - 2 ∧
          (W.preΨ' <| 2 * k).coeff (2 * k ^ 2 - 2) = k) ∧
        ((W.preΨ' <| 2 * k + 1).natDegree ≤ 2 * k ^ 2 + 2 * k ∧
          (W.preΨ' <| 2 * k + 1).coeff (2 * k ^ 2 + 2 * k) = (2 * k + 1 : ℕ)) := by
      rw [← show ((2 * k) ^ 2 - 4) / 2 = 2 * k ^ 2 - 2 by
          exact Nat.div_eq_of_eq_mul_right two_pos <| by rw [Nat.mul_sub_left_distrib]; ring_nf,
        ← show ((2 * k + 1) ^ 2 - 1) / 2 = 2 * k ^ 2 + 2 * k by
          exact Nat.div_eq_of_eq_mul_right two_pos <| by erw [add_sq, Nat.add_sub_cancel]; ring1]
      nth_rw 5 [← k.mul_div_cancel_left two_pos]
      exact ⟨imp_of_if_pos (ih (2 * k) <| by linarith only [hk]) <| even_two_mul k,
        imp_of_if_neg (ih (2 * k + 1) <| by linarith only [hk]) k.not_even_two_mul_add_one⟩
    simp only [if_pos <| even_two_mul _, if_neg (m + 2).not_even_two_mul_add_one,
      show (2 * (m + 3)) ^ 2 = 2 * (2 * (m + 2) * (m + 4)) + 4 by ring1,
      show (2 * (m + 2) + 1) ^ 2 = 2 * (2 * (m + 2) * (m + 3)) + 1 by ring1, Nat.add_sub_cancel,
      Nat.mul_div_cancel_left _ two_pos]
    by_cases hm : Even m
    · rcases even_iff_exists_two_mul.mp hm with ⟨m, rfl⟩
      simp only [natDegree_odd_preΨ'_even m ih, coeff_odd_preΨ'_even m ih,
        natDegree_even_preΨ'_even m ih, coeff_even_preΨ'_even m ih, and_self]
    · replace ih (k : ℕ) (hk : k < m + 1) := ih k <| Nat.lt.step hk
      rcases Nat.odd_iff_not_even.mpr hm with ⟨m, rfl⟩
      simp only [natDegree_odd_preΨ'_odd m ih, coeff_odd_preΨ'_odd m ih,
        natDegree_even_preΨ'_odd m ih, coeff_even_preΨ'_odd m ih, and_self]

lemma natDegree_preΨ' (n : ℕ) :
    (W.preΨ' n).natDegree ≤ if Even n then (n ^ 2 - 4) / 2 else (n ^ 2 - 1) / 2 := by
  by_cases hn : Even n
  · simpa only [if_pos hn] using (imp_of_if_pos (W.natDegree_coeff_preΨ' n) hn).left
  · simpa only [if_neg hn] using (imp_of_if_neg (W.natDegree_coeff_preΨ' n) hn).left

lemma coeff_preΨ' (n : ℕ) :
    if Even n then (W.preΨ' n).coeff ((n ^ 2 - 4) / 2) = (n / 2 : ℕ)
      else (W.preΨ' n).coeff ((n ^ 2 - 1) / 2) = n := by
  by_cases hn : Even n
  · rw [if_pos hn, (imp_of_if_pos (W.natDegree_coeff_preΨ' n) hn).right]
  · rw [if_neg hn, (imp_of_if_neg (W.natDegree_coeff_preΨ' n) hn).right]

private lemma natDegree_coeff_Ψ' (n : ℤ) :
    if Even n then (W.preΨ n).natDegree ≤ (n.natAbs ^ 2 - 4) / 2 ∧
        (W.preΨ n).coeff ((n.natAbs ^ 2 - 4) / 2) = (n / 2 : ℤ)
      else (W.preΨ n).natDegree ≤ (n.natAbs ^ 2 - 1) / 2 ∧
          (W.preΨ n).coeff ((n.natAbs ^ 2 - 1) / 2) = n := by
  rcases n.eq_nat_or_neg with ⟨n, rfl | rfl⟩
  · norm_cast
    exact W.preΨ_ofNat n ▸ W.natDegree_coeff_preΨ' n
  · simp only [even_neg, Int.even_coe_nat, preΨ_neg, natDegree_neg, preΨ_ofNat, Int.natAbs_neg,
      Int.natAbs_cast, coeff_neg, neg_eq_iff_eq_neg, Int.cast_neg, Int.cast_natCast, neg_neg]
    convert W.natDegree_coeff_preΨ' n using 3 with hn
    rcases even_iff_exists_two_mul.mp hn with ⟨_, rfl⟩
    rw [Nat.cast_mul, neg_mul_eq_mul_neg, Nat.cast_ofNat, Int.mul_ediv_cancel_left _ two_ne_zero,
      Int.cast_neg, neg_neg, Int.cast_natCast, Nat.mul_div_cancel_left _ two_pos]

lemma natDegree_Ψ' (n : ℤ) :
    (W.preΨ n).natDegree ≤ if Even n then (n.natAbs ^ 2 - 4) / 2 else (n.natAbs ^ 2 - 1) / 2 := by
  by_cases hn : Even n
  · simpa only [if_pos hn] using (imp_of_if_pos (W.natDegree_coeff_Ψ' n) hn).left
  · simpa only [if_neg hn] using (imp_of_if_neg (W.natDegree_coeff_Ψ' n) hn).left

lemma coeff_Ψ' (n : ℤ) :
    if Even n then (W.preΨ n).coeff ((n.natAbs ^ 2 - 4) / 2) = (n / 2 : ℤ)
      else (W.preΨ n).coeff ((n.natAbs ^ 2 - 1) / 2) = n := by
  by_cases hn : Even n
  · rw [if_pos hn, (imp_of_if_pos (W.natDegree_coeff_Ψ' n) hn).right]
  · rw [if_neg hn, (imp_of_if_neg (W.natDegree_coeff_Ψ' n) hn).right]

private lemma natDegree_coeff_ΨSq_ofNat (n : ℕ) :
    (W.ΨSq n).natDegree ≤ n ^ 2 - 1 ∧ (W.ΨSq n).coeff (n ^ 2 - 1) = (n ^ 2 : ℕ) := by
  rcases n with _ | n
  · erw [ΨSq_zero]
    exact ⟨natDegree_zero.le, Nat.cast_zero.symm⟩
  · have h := W.natDegree_coeff_preΨ' <| n + 1
    simp only [ΨSq, preΨ_ofNat, Int.even_coe_nat, Nat.even_add_one, ite_not] at h ⊢
    by_cases hn : Even n
    · rcases even_iff_exists_two_mul.mp hn with ⟨m, rfl⟩
      rw [if_pos hn, show (2 * m + 1) ^ 2 = 2 * (2 * m * (m + 1)) + 1 by ring1, Nat.add_sub_cancel,
        Nat.mul_div_cancel_left _ two_pos] at h
      rw [if_pos hn, mul_one, show (2 * m + 1) ^ 2 = 2 * (2 * m * (m + 1)) + 1 by ring1,
        Nat.add_sub_cancel]
      constructor
      · exact natDegree_pow_le_of_le 2 h.left
      · rw [coeff_pow_of_natDegree_le h.left, h.right]
        push_cast
        ring1
    · rcases Nat.odd_iff_not_even.mpr hn with ⟨m, rfl⟩
      rw [if_neg hn, show (2 * m + 2) ^ 2 = 2 * (2 * m * (m + 2)) + 4 by ring1, Nat.add_sub_cancel,
        Nat.mul_div_cancel_left _ two_pos, show (2 * m + 2) / 2 = 2 * (m + 1) / 2 by rfl,
        Nat.mul_div_cancel_left _ two_pos] at h
      rw [if_neg hn, show (2 * m + 2) ^ 2 = 2 * (2 * m * (m + 2)) + 4 by ring1, Nat.succ_sub_one]
      constructor
      · exact natDegree_mul_le_of_le (natDegree_pow_le_of_le 2 h.left) W.natDegree_Ψ₂Sq
      · rw [coeff_mul_of_natDegree_le (natDegree_pow_le_of_le 2 h.left) W.natDegree_Ψ₂Sq,
          coeff_pow_of_natDegree_le h.left, h.right, coeff_Ψ₂Sq]
        push_cast
        ring1

private lemma natDegree_coeff_ΨSq (n : ℤ) :
    (W.ΨSq n).natDegree ≤ n.natAbs ^ 2 - 1 ∧
      (W.ΨSq n).coeff (n.natAbs ^ 2 - 1) = (n.natAbs ^ 2 : ℕ) := by
  rcases n.eq_nat_or_neg with ⟨n, rfl | rfl⟩
  · exact W.natDegree_coeff_ΨSq_ofNat n
  · simpa only [ΨSq_neg, Int.natAbs_neg] using W.natDegree_coeff_ΨSq_ofNat n

lemma natDegree_ΨSq (n : ℤ) :
    (W.ΨSq n).natDegree ≤ n.natAbs ^ 2 - 1 :=
  (W.natDegree_coeff_ΨSq n).left

lemma coeff_ΨSq (n : ℤ) :
    (W.ΨSq n).coeff (n.natAbs ^ 2 - 1) = (n.natAbs ^ 2 : ℕ) :=
  (W.natDegree_coeff_ΨSq n).right

private lemma natDegree_coeff_Φ_ofNat (n : ℕ) :
    (W.Φ n).natDegree ≤ n ^ 2 ∧ (W.Φ n).coeff (n ^ 2) = 1 := by
  rcases n with _ | _ | n
  · erw [Φ_zero]
    exact ⟨natDegree_one.le, coeff_one_zero⟩
  · erw [Φ_one]
    exact ⟨natDegree_X_le, coeff_X⟩
  · have h1 := W.natDegree_coeff_preΨ' <| n + 1
    have h2 := W.natDegree_coeff_ΨSq (n + 2 : ℕ)
    have h3 := W.natDegree_coeff_preΨ' <| n + 3
    simp only [WeierstrassCurve.Φ, Int.even_coe_nat, Nat.even_add_one, ite_not] at h1 h3 ⊢
    erw [preΨ_ofNat, ← Nat.cast_sub <| by linarith only, preΨ_ofNat, Nat.add_sub_cancel]
    by_cases hn : Even n
    · rcases even_iff_exists_two_mul.mp hn with ⟨m, rfl⟩
      rw [if_pos hn, show (2 * m + 1) ^ 2 = 2 * (2 * m * (m + 1)) + 1 by ring1, Nat.add_sub_cancel,
        Nat.mul_div_cancel_left _ two_pos] at h1
      rw [Int.natAbs_cast, show (2 * m + 2) ^ 2 = 4 * m * (m + 2) + 4 by ring1, Nat.succ_sub_one]
        at h2
      rw [if_pos hn, show (2 * m + 3) ^ 2 = 2 * (2 * (m + 1) * (m + 2)) + 1 by ring1,
        Nat.add_sub_cancel, Nat.mul_div_cancel_left _ two_pos] at h3
      rw [if_pos hn, mul_one]
      constructor
      · convert natDegree_sub_le_of_le (natDegree_mul_le_of_le natDegree_X_le h2.left) <|
          natDegree_mul_le_of_le h3.left h1.left using 1
        convert (max_self _).symm using 2 <;> ring1
      · rw [coeff_sub, show (2 * m + 2) ^ 2 = 4 * m * (m + 2) + 4 by ring1, coeff_X_mul, h2.right,
          show _ + _ = (2 * (m + 1) * (m + 2)) + (2 * m * (m + 1)) by ring1,
          coeff_mul_of_natDegree_le h3.left h1.left, h3.right, h1.right]
        push_cast
        ring1
    · rcases Nat.odd_iff_not_even.mpr hn with ⟨m, rfl⟩
      rw [if_neg hn, show (2 * m + 2) ^ 2 = 2 * (2 * m * (m + 2)) + 4 by ring1, Nat.add_sub_cancel,
        Nat.mul_div_cancel_left _ two_pos, show (2 * m + 2) / 2 = 2 * (m + 1) / 2 by rfl,
        Nat.mul_div_cancel_left _ two_pos] at h1
      rw [Int.natAbs_cast, show (2 * m + 3) ^ 2 = 4 * (m + 1) * (m + 2) + 1 by ring1,
        Nat.add_sub_cancel] at h2
      rw [if_neg hn, show (2 * m + 4) ^ 2 = 2 * (2 * (m + 1) * (m + 3)) + 4 by ring1,
        Nat.add_sub_cancel, Nat.mul_div_cancel_left _ two_pos,
        show (2 * m + 4) / 2 = 2 * (m + 2) / 2 by rfl, Nat.mul_div_cancel_left _ two_pos] at h3
      rw [if_neg hn]
      constructor
      · convert natDegree_sub_le_of_le (natDegree_mul_le_of_le natDegree_X_le h2.left) <|
          natDegree_mul_le_of_le (natDegree_mul_le_of_le h3.left h1.left) W.natDegree_Ψ₂Sq using 1
        convert (max_self _).symm using 2 <;> ring1
      · rw [coeff_sub, show (2 * m + 3) ^ 2 = 4 * (m + 1) * (m + 2) + 1 by ring1, coeff_X_mul,
          h2.right, show _ + _ = (2 * (m + 1) * (m + 3)) + (2 * m * (m + 2)) + 3 by ring1,
          coeff_mul_of_natDegree_le (natDegree_mul_le_of_le h3.left h1.left) W.natDegree_Ψ₂Sq,
          coeff_mul_of_natDegree_le h3.left h1.left, h3.right, h1.right, coeff_Ψ₂Sq]
        push_cast
        ring1

private lemma natDegree_coeff_Φ (n : ℤ) :
    (W.Φ n).natDegree ≤ n.natAbs ^ 2 ∧ (W.Φ n).coeff (n.natAbs ^ 2) = 1 := by
  rcases n.eq_nat_or_neg with ⟨n, rfl | rfl⟩
  · exact W.natDegree_coeff_Φ_ofNat n
  · simpa only [Φ_neg, Int.natAbs_neg] using W.natDegree_coeff_Φ_ofNat n

lemma natDegree_Φ (n : ℤ) : (W.Φ n).natDegree ≤ n.natAbs ^ 2 :=
  (W.natDegree_coeff_Φ n).left

lemma coeff_Φ (n : ℤ) : (W.Φ n).coeff (n.natAbs ^ 2) = 1 :=
  (W.natDegree_coeff_Φ n).right

end WeierstrassCurve
