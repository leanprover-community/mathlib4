/-
Copyright (c) 2025 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang
-/

import Mathlib.NumberTheory.Basic
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.Perfection

/-!
# Untilt Function

In this file, we define the untilt function from the pretilt of a
`p`-adically complete ring to the ring itself. Note that this
is not the untilt *functor*.

## Main definition
* `PreTilt.untilt` : Given a `p`-adically complete ring `O`, this is the
  multiplicative map from `PreTilt O p` to `O` itself. Specifically, it is
  defined as the limit of `p^n`-th powers of arbitrary lifts in `O` of the
  `n`-th component from the perfection of `O/p`.

## Main theorem
* `PreTilt.mk_untilt_eq_coeff_zero` : The composition of the mod `p` map
  with the untilt function equals taking the zeroth component of the perfection.

## Reference
* [Berkeley Lectures on \( p \)-adic Geometry][MR4446467]

## Tags
Perfectoid, Tilting equivalence, Untilt
-/

open Perfection Ideal

noncomputable section

variable {O : Type*} [CommRing O] {p : ℕ} [Fact (Nat.Prime p)] [Fact ¬IsUnit (p : O)]

namespace PreTilt

/--
The auxiliary sequence to define the untilt map. The `(n + 1)`-th term
is the `p^n`-th powers of arbitrary lifts in `O` of the `n`-th component
from the perfection of `O/p`.
-/
def untiltAux (x : PreTilt O p) (n : ℕ) : O :=
  match n with
  | 0 => 1
  | n + 1 =>
  (Quotient.out (coeff (ModP O p) _ n x)) ^ (p ^ n)

lemma pow_dvd_untiltAux_sub_untiltAux (x : PreTilt O p) {m n : ℕ} (h : m ≤ n) :
    (p : O) ^ m ∣ x.untiltAux m - x.untiltAux n := by
  cases m with
  | zero => simp [untiltAux]
  | succ m =>
    let n' := n.pred
    have : n = n' + 1 := by simp [n', Nat.sub_add_cancel (n := n) (m := 1) (by linarith)]
    simp only [this, add_le_add_iff_right, untiltAux] at h ⊢
    rw [← Nat.sub_add_cancel h, pow_add _ _ m, pow_mul]
    refine (dvd_sub_pow_of_dvd_sub ?_ m)
    rw [← mem_span_singleton, ← Ideal.Quotient.eq]
    simp only [Ideal.Quotient.mk_out, map_pow, Nat.sub_add_cancel h]
    calc
      _ = (coeff (ModP O p) p (n' - (n' - m))) x := by simp [Nat.sub_sub_self h]
      _ = (coeff (ModP O p) p n') (((frobenius (Perfection (ModP O p) p) p))^[n' - m] x) :=
        (coeff_iterate_frobenius' x n' (n' - m) (Nat.sub_le n' m)).symm
      _ = _ := by simp [iterate_frobenius]

lemma pow_dvd_one_untiltAux_sub_one (m : ℕ) :
    (p : O) ^ m ∣ (1 : PreTilt O p).untiltAux m - 1 := by
  cases m with
  | zero => simp [untiltAux]
  | succ m =>
    simp only [untiltAux]
    nth_rw 3 [← one_pow (p ^ m)]
    refine dvd_sub_pow_of_dvd_sub (R := O) ?_ m
    rw [← mem_span_singleton, ← Ideal.Quotient.eq]
    simp

lemma pow_dvd_mul_untiltAux_sub_untiltAux_mul (x y : PreTilt O p) (m : ℕ) :
    (p : O) ^ m ∣ (x * y).untiltAux m - (x.untiltAux m) * (y.untiltAux m) := by
  cases m with
  | zero => simp [untiltAux]
  | succ m =>
    simp only [untiltAux, map_mul, ← mul_pow]
    refine dvd_sub_pow_of_dvd_sub ?_ m
    rw [← mem_span_singleton, ← Ideal.Quotient.eq]
    simp

section IsPrecomplete

variable [IsPrecomplete (span {(p : O)}) O]

lemma exists_smodEq_untiltAux (x : PreTilt O p) :
    ∃ y, ∀ (n : ℕ), x.untiltAux n ≡ y [SMOD Ideal.span {(p : O)} ^ n • (⊤ : Ideal O)] := by
  refine IsPrecomplete.prec' x.untiltAux (fun {m n} h ↦ ?_)
  simpa only [span_singleton_pow, smul_eq_mul, mul_top, SModEq.sub_mem,
      mem_span_singleton] using x.pow_dvd_untiltAux_sub_untiltAux h

/--
Given a `p`-adically complete ring `O`, this is the underlying function of the untilt map.
It is defined as the limit of `p^n`-th powers of arbitrary lifts in `O` of the
`n`-th component from the perfection of `O/p`.
-/
def untiltFun (x : PreTilt O p) : O :=
  Classical.choose <| x.exists_smodEq_untiltAux

lemma untiltAux_smodEq_untiltFun (x : PreTilt O p) (n : ℕ) :
    x.untiltAux n ≡ x.untiltFun [SMOD (span {(p : O)}) ^ n] := by
  simpa [untiltFun] using Classical.choose_spec x.exists_smodEq_untiltAux n

end IsPrecomplete

section IsAdicComplete

variable [IsAdicComplete (span {(p : O)}) O]

/--
Given a `p`-adically complete ring `O`, this is the
multiplicative map from `PreTilt O p` to `O` itself. Specifically, it is
defined as the limit of `p^n`-th powers of arbitrary lifts in `O` of the
`n`-th component from the perfection of `O/p`.
-/
def untilt : PreTilt O p →* O where
  toFun := untiltFun
  map_one' := by
    rw [← sub_eq_zero, IsHausdorff.eq_iff_smodEq (I := (span {(p : O)}))]
    intro n
    rw [sub_smodEq_zero]
    simp only [smul_eq_mul, mul_top]
    apply (untiltAux_smodEq_untiltFun (1 : PreTilt O p) n).symm.trans
    simp only [span_singleton_pow, SModEq.sub_mem, mem_span_singleton]
    exact pow_dvd_one_untiltAux_sub_one (O := O) (p := p) n
  map_mul' _ _ := by
    rw [← sub_eq_zero, IsHausdorff.eq_iff_smodEq (I := (span {(p : O)}))]
    intro n
    rw [sub_smodEq_zero]
    simp only [smul_eq_mul, mul_top]
    apply (untiltAux_smodEq_untiltFun _ n).symm.trans
    refine SModEq.trans ?_ (SModEq.mul (untiltAux_smodEq_untiltFun _ n)
        (untiltAux_smodEq_untiltFun _ n))
    simp only [span_singleton_pow, SModEq.sub_mem, mem_span_singleton]
    exact pow_dvd_mul_untiltAux_sub_untiltAux_mul (O := O) (p := p) _ _ n

/--
The composition of the mod `p` map
with the untilt function equals taking the zeroth component of the perfection.
-/
theorem mk_untilt_eq_coeff_zero (x : PreTilt O p) :
    Ideal.Quotient.mk (Ideal.span {(p : O)}) (x.untilt) = coeff (ModP O p) p 0 x := by
  simp only [untilt]
  rw [← Ideal.Quotient.mk_out ((coeff (ModP O p) p 0) x), Ideal.Quotient.eq, ← SModEq.sub_mem]
  simpa [untiltAux] using (x.untiltAux_smodEq_untiltFun 1).symm

/--
The composition of the mod `p` map
with the untilt function equals taking the zeroth component of the perfection.
A variation of `PreTilt.mk_untilt_eq_coeff_zero`.
-/
theorem mk_comp_untilt_eq_coeff_zero :
    Ideal.Quotient.mk (Ideal.span {(p : O)}) ∘ untilt = coeff (ModP O p) p 0 :=
  funext mk_untilt_eq_coeff_zero

end IsAdicComplete

end PreTilt

end
