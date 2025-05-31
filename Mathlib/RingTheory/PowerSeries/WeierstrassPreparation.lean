/-
Copyright (c) 2025 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Polynomial.Eisenstein.Distinguished
import Mathlib.RingTheory.PowerSeries.CoeffMulMem
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Trunc

/-!

# Weierstrass preparation theorem for power series over a complete local ring

In this file we define Weierstrass division, Weierstrass factorization, and prove
Weierstrass preparation theorem.

We assume that a ring is adic complete with respect to some ideal.
If such ideal is a maximal ideal, then by `isLocalRing_of_isAdicComplete_maximal`,
such ring has only one maximal ideal, and hence it is a complete local ring.

## Main definitions

- `PowerSeries.IsWeierstrassDivisionAt f g q r I`: let `f` and `g` be power series over `A`, `I` be
  an ideal of `A`, this is a `Prop` which asserts that a power series
  `q` and a polynomial `r` of degree `< n` satisfy `f = g * q + r`, where `n` is the order of the
  image of `g` in `(A / I)⟦X⟧` (defined to be zero if such image is zero, in which case
  it's mathematically not considered).

- `PowerSeries.IsWeierstrassDivision`: version of `PowerSeries.IsWeierstrassDivisionAt`
  for local rings with respect to its maximal ideal.

- `PowerSeries.IsWeierstrassDivisorAt g I`: let `g` be a power series over `A`, `I` be an ideal of
  `A`, this is a `Prop` which asserts that the `n`-th coefficient
  of `g` is a unit, where `n` is the order of the image of `g` in `(A / I)⟦X⟧`
  (defined to be zero if such image is zero, in which case it's mathematically not considered).

  This property guarantees that if the `A` is `I`-adic complete, then `g` can be used as a divisor
  in Weierstrass division (`PowerSeries.IsWeierstrassDivisorAt.isWeierstrassDivisionAt_div_mod`).

- `PowerSeries.IsWeierstrassDivisor`: version of `PowerSeries.IsWeierstrassDivisorAt` for
  local rings with respect to its maximal ideal.

- `PowerSeries.IsWeierstrassFactorizationAt g f h I`: for a power series `g` over `A` and
  an ideal `I` of `A`, this is a `Prop` which asserts that `f` is a distinguished polynomial at `I`,
  `h` is a formal power series over `A` that is a unit and such that `g = f * h`.

- `PowerSeries.IsWeierstrassFactorization`: version of `PowerSeries.IsWeierstrassFactorizationAt`
  for local rings with respect to its maximal ideal.

## Main results

- `PowerSeries.exists_isWeierstrassDivision`: **Weierstrass division**
  ([washington_cyclotomic], Proposition 7.2): let `f`, `g` be power series
  over a complete local ring, such that the image of `g` in the residue field is not zero.
  Let `n` be the order of the image of `g` in the residue field. Then there exists a power series
  `q` and a polynomial `r` of degree `< n`, such that `f = g * q + r`.

- `PowerSeries.IsWeierstrassDivision.elim`,
  `PowerSeries.IsWeierstrassDivision.unique`: `q` and `r` in the Weierstrass division are unique.

- `PowerSeries.exists_isWeierstrassFactorization`: **Weierstrass preparation theorem**
  ([washington_cyclotomic], Theorem 7.3): let `g` be a power series
  over a complete local ring, such that its image in the residue field is
  not zero. Then there exists a distinguished polynomial `f` and a power series `h`
  which is a unit, such that `g = f * h`.

- `PowerSeries.IsWeierstrassFactorization.elim`,
  `PowerSeries.IsWeierstrassFactorization.unique`: `f` and `h` in Weierstrass preparation
  theorem are unique.

- `Polynomial.IsDistinguishedAt.algEquivQuotient`: a distinguished polynomial `g` induces a
  natural isomorphism `A[X] / (g) ≃ A⟦X⟧ / (g)`.

- `PowerSeries.IsWeierstrassFactorizationAt.algEquivQuotient`: a Weierstrass factorization
  `g = f * h` induces a natural isomorphism `A[X] / (f) ≃ A⟦X⟧ / (g)`.

- `PowerSeries.algEquivQuotientWeierstrassDistinguished`:
  if `g` is a power series over a complete local ring,
  such that its image in the residue field is not zero, then there is a natural isomorphism
  `A[X] / (f) ≃ A⟦X⟧ / (g)` where `f` is `PowerSeries.weierstrassDistinguished g`.

## References

- [Washington, Lawrence C. *Introduction to cyclotomic fields.*][washington_cyclotomic]

-/

open scoped Polynomial

namespace PowerSeries

variable {A : Type*} [CommRing A]

/-!

## Weierstrass division

-/

section IsWeierstrassDivisionAt

variable (f g q : A⟦X⟧) (r : A[X]) (I : Ideal A)

/-- Let `f`, `g` be power series over `A`, `I` be an ideal of `A`,
`PowerSeries.IsWeierstrassDivisionAt f g q r I` is a `Prop` which asserts that a power series
`q` and a polynomial `r` of degree `< n` satisfy `f = g * q + r`, where `n` is the order of the
image of `g` in `(A / I)⟦X⟧` (defined to be zero if such image is zero, in which case
it's mathematically not considered). -/
@[mk_iff]
structure IsWeierstrassDivisionAt : Prop where
  degree_lt : r.degree < (g.map (Ideal.Quotient.mk I)).order.toNat
  eq_mul_add : f = g * q + r

/-- Version of `PowerSeries.IsWeierstrassDivisionAt` for local rings with respect to
its maximal ideal. -/
abbrev IsWeierstrassDivision [IsLocalRing A] : Prop :=
  f.IsWeierstrassDivisionAt g q r (IsLocalRing.maximalIdeal A)

theorem isWeierstrassDivisionAt_zero : IsWeierstrassDivisionAt 0 g 0 0 I := by
  constructor
  · rw [Polynomial.degree_zero]
    exact WithBot.bot_lt_coe _
  · simp

variable {f g q r I}

namespace IsWeierstrassDivisionAt

theorem coeff_f_sub_r_mem (H : f.IsWeierstrassDivisionAt g q r I)
    {i : ℕ} (hi : i < (g.map (Ideal.Quotient.mk I)).order.toNat) : coeff A i (f - r) ∈ I := by
  replace H := H.2
  rw [← sub_eq_iff_eq_add] at H
  rw [H]
  refine coeff_mul_mem_ideal_of_coeff_left_mem_ideal i (fun j hj ↦ ?_) i le_rfl
  have := coeff_of_lt_order_toNat _ (lt_of_le_of_lt hj hi)
  rwa [coeff_map, ← RingHom.mem_ker, Ideal.mk_ker] at this

theorem add {f' q' r'} (H : f.IsWeierstrassDivisionAt g q r I)
    (H' : f'.IsWeierstrassDivisionAt g q' r' I) :
    (f + f').IsWeierstrassDivisionAt g (q + q') (r + r') I :=
  ⟨(Polynomial.degree_add_le _ _).trans_lt (sup_lt_iff.2 ⟨H.degree_lt, H'.degree_lt⟩), by
    rw [H.eq_mul_add, H'.eq_mul_add, Polynomial.coe_add]; ring⟩

theorem smul (H : f.IsWeierstrassDivisionAt g q r I) (a : A) :
    (a • f).IsWeierstrassDivisionAt g (a • q) (a • r) I :=
  ⟨(Polynomial.degree_smul_le a _).trans_lt H.degree_lt, by
    simp [H.eq_mul_add, Algebra.smul_def, mul_add, mul_left_comm]⟩

end IsWeierstrassDivisionAt

end IsWeierstrassDivisionAt

section IsWeierstrassDivisorAt

variable (g : A⟦X⟧) (I : Ideal A)

/-- `PowerSeries.IsWeierstrassDivisorAt g I` is a `Prop` which asserts that the `n`-th coefficient
of `g` is a unit, where `n` is the order of the
image of `g` in `(A / I)⟦X⟧` (defined to be zero if such image is zero, in which case
it's mathematically not considered).

This property guarantees that if the ring is `I`-adic complete, then `g` can be used as a divisor
in Weierstrass division (`PowerSeries.IsWeierstrassDivisorAt.isWeierstrassDivisionAt_div_mod`). -/
def IsWeierstrassDivisorAt : Prop :=
  IsUnit (coeff A (g.map (Ideal.Quotient.mk I)).order.toNat g)

/-- Version of `PowerSeries.IsWeierstrassDivisorAt` for local rings with respect to
its maximal ideal. -/
abbrev IsWeierstrassDivisor [IsLocalRing A] : Prop :=
  g.IsWeierstrassDivisorAt (IsLocalRing.maximalIdeal A)

variable {g} in
/-- If `g` is a power series over a local ring such that
its image in the residue field is not zero, then `g` can be used as a Weierstrass divisor. -/
theorem IsWeierstrassDivisor.of_map_ne_zero [IsLocalRing A]
    (hg : g.map (IsLocalRing.residue A) ≠ 0) : g.IsWeierstrassDivisor := by
  rw [IsWeierstrassDivisor, IsWeierstrassDivisorAt, ← IsLocalRing.notMem_maximalIdeal]
  have h := coeff_order hg
  contrapose! h
  rwa [coeff_map, IsLocalRing.residue_eq_zero_iff]

theorem _root_.Polynomial.IsDistinguishedAt.isWeierstrassDivisorAt {g : A[X]} {I : Ideal A}
    (H : g.IsDistinguishedAt I) (hI : I ≠ ⊤) : IsWeierstrassDivisorAt g I := by
  have : g.natDegree = _ := congr(ENat.toNat $(H.coe_natDegree_eq_order_map g 1
    (by rwa [constantCoeff_one, ← Ideal.ne_top_iff_one]) (by simp)))
  simp [IsWeierstrassDivisorAt, ← this, H.monic.leadingCoeff]

theorem _root_.Polynomial.IsDistinguishedAt.isWeierstrassDivisorAt' {g : A[X]} {I : Ideal A}
    (H : g.IsDistinguishedAt I) [IsHausdorff I A] : IsWeierstrassDivisorAt g I := by
  rcases eq_or_ne I ⊤ with rfl | hI
  · have := ‹IsHausdorff ⊤ A›.subsingleton
    exact isUnit_of_subsingleton _
  exact H.isWeierstrassDivisorAt hI

private theorem coeff_trunc_order_mem (i : ℕ) :
    (g.trunc (g.map (Ideal.Quotient.mk I)).order.toNat).coeff i ∈ I := by
  rw [coeff_trunc]
  split_ifs with h
  · simpa [← RingHom.mem_ker] using coeff_of_lt_order_toNat _ h
  · exact zero_mem _

namespace IsWeierstrassDivisorAt

variable {g I} (H : g.IsWeierstrassDivisorAt I)
include H

theorem isUnit_shift : IsUnit <| mk fun i ↦
    coeff A (i + (g.map (Ideal.Quotient.mk I)).order.toNat) g := by
  simpa [isUnit_iff_constantCoeff]

/-- The inductively constructed sequence `qₖ` in the proof of Weierstrass division. -/
noncomputable def seq (H : g.IsWeierstrassDivisorAt I) (f : A⟦X⟧) : ℕ → A⟦X⟧
  | 0 => 0
  | k + 1 =>
    H.seq f k + (mk fun i ↦ coeff A (i + (g.map (Ideal.Quotient.mk I)).order.toNat)
      (f - g * H.seq f k)) * H.isUnit_shift.unit⁻¹

variable {f : A⟦X⟧}

theorem coeff_seq_mem (k : ℕ) {i : ℕ} (hi : i ≥ (g.map (Ideal.Quotient.mk I)).order.toNat) :
    coeff A i (f - g * H.seq f k) ∈ I ^ k := by
  induction k generalizing hi i with
  | zero => simp
  | succ k hq =>
    rw [seq]
    set q := H.seq f k
    set s := f - g * q
    set n := (g.map (Ideal.Quotient.mk I)).order.toNat
    have hs := s.eq_X_pow_mul_shift_add_trunc n
    set s₀ := s.trunc n
    set s₁ := PowerSeries.mk fun i ↦ coeff A (i + n) s
    set q' := q + s₁ * H.isUnit_shift.unit⁻¹
    have key : f - g * q' = (s₀ : A⟦X⟧) - (g.trunc n : A⟦X⟧) * s₁ * H.isUnit_shift.unit⁻¹ := by
      trans s + g * (q - q')
      · simp_rw [s]; ring
      simp_rw [q']
      rw [sub_add_cancel_left, mul_neg, ← mul_assoc, mul_right_comm]
      nth_rw 1 [g.eq_X_pow_mul_shift_add_trunc n]
      rw [add_mul, mul_assoc, IsUnit.mul_val_inv, hs]
      ring
    rw [key, map_sub, Polynomial.coeff_coe, coeff_trunc, if_neg hi.not_lt, zero_sub, neg_mem_iff,
      pow_succ']
    refine coeff_mul_mem_ideal_of_coeff_left_mem_ideal' (fun i ↦ ?_) i
    refine coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal'
      (by simp [n, g.coeff_trunc_order_mem]) (fun i ↦ ?_) i
    rw [coeff_mk]
    exact hq (by simp)

theorem coeff_seq_succ_sub_seq_mem (k i : ℕ) :
    coeff A i (H.seq f (k + 1) - H.seq f k) ∈ I ^ k := by
  rw [seq, add_sub_cancel_left]
  refine coeff_mul_mem_ideal_of_coeff_left_mem_ideal' (fun i ↦ ?_) i
  rw [coeff_mk]
  exact H.coeff_seq_mem k (by simp)

@[simp]
theorem seq_zero : H.seq f 0 = 0 := rfl

theorem seq_one : H.seq f 1 = (PowerSeries.mk fun i ↦ coeff A
    (i + (g.map (Ideal.Quotient.mk I)).order.toNat) f) * H.isUnit_shift.unit⁻¹ := by
  simp_rw [seq, mul_zero, zero_add, sub_zero]

variable (f)

/-- The (bundled version of) coefficient of the limit `q` of the
inductively constructed sequence `qₖ` in the proof of Weierstrass division. -/
noncomputable def divCoeff [IsPrecomplete I A] (i : ℕ) :=
  Classical.indefiniteDescription _ <| IsPrecomplete.prec' (I := I)
    (fun k ↦ coeff A i (H.seq f k)) fun {m} {n} hn ↦ by
      induction n, hn using Nat.le_induction with
      | base => rw [SModEq.def]
      | succ n hn ih =>
        refine ih.trans (SModEq.symm ?_)
        rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← map_sub]
        exact Ideal.pow_le_pow_right hn (H.coeff_seq_succ_sub_seq_mem n i)

/-- The limit `q` of the
inductively constructed sequence `qₖ` in the proof of Weierstrass division. -/
noncomputable def div [IsPrecomplete I A] : A⟦X⟧ := PowerSeries.mk fun i ↦ (H.divCoeff f i).1

variable {f}

theorem coeff_div [IsPrecomplete I A] (i : ℕ) : coeff A i (H.div f) = (H.divCoeff f i).1 := by
  simp [div]

theorem coeff_div_sub_seq_mem [IsPrecomplete I A] (k i : ℕ) :
    coeff A i (H.div f - (H.seq f k)) ∈ I ^ k := by
  simpa [coeff_div, SModEq.sub_mem] using ((H.divCoeff f i).2 k).symm

variable (f)

/-- The remainder `r` in the proof of Weierstrass division. -/
noncomputable def mod [IsPrecomplete I A] : A[X] :=
  (f - g * H.div f).trunc (g.map (Ideal.Quotient.mk I)).order.toNat

/-- If the ring is `I`-adic complete, then `g` can be used as a divisor in Weierstrass division. -/
theorem isWeierstrassDivisionAt_div_mod [IsAdicComplete I A] :
    f.IsWeierstrassDivisionAt g (H.div f) (H.mod f) I := by
  rcases eq_or_ne I ⊤ with rfl | hI
  · have := ‹IsAdicComplete ⊤ A›.toIsHausdorff.subsingleton
    rw [Subsingleton.elim f 0, Subsingleton.elim (H.div 0) 0, Subsingleton.elim (H.mod 0) 0]
    exact g.isWeierstrassDivisionAt_zero _
  constructor
  · exact degree_trunc_lt _ _
  · rw [mod, add_comm, ← sub_eq_iff_eq_add]
    ext i
    rw [Polynomial.coeff_coe, coeff_trunc]
    split_ifs with hi
    · rfl
    refine IsHausdorff.haus' (I := I) _ fun k ↦ ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, show f - g * H.div f =
      f - g * (H.seq f k) - g * (H.div f - (H.seq f k)) by ring, map_sub]
    exact Ideal.sub_mem _ (H.coeff_seq_mem k (not_lt.1 hi)) <|
      coeff_mul_mem_ideal_of_coeff_right_mem_ideal' (H.coeff_div_sub_seq_mem k) i

/-- If `g * q = r` for some power series `q` and some polynomial `r` whose degree is `< n`,
then `q` and `r` are all zero. This implies the uniqueness of Weierstrass division. -/
theorem eq_zero_of_mul_eq [IsHausdorff I A]
    {q : A⟦X⟧} {r : A[X]} (hdeg : r.degree < (g.map (Ideal.Quotient.mk I)).order.toNat)
    (heq : g * q = r) : q = 0 ∧ r = 0 := by
  suffices ∀ k i, coeff A i q ∈ I ^ k by
    have hq : q = 0 := by
      ext i
      refine IsHausdorff.haus' (I := I) _ fun k ↦ ?_
      rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
      exact this _ _
    rw [hq, mul_zero, Eq.comm, Polynomial.coe_eq_zero_iff] at heq
    exact ⟨hq, heq⟩
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [g.eq_X_pow_mul_shift_add_trunc (g.map (Ideal.Quotient.mk I)).order.toNat] at heq
    have h1 : ∀ i, coeff A i r ∈ I ^ (k + 1) := fun i ↦ by
      rcases lt_or_le i (g.map (Ideal.Quotient.mk I)).order.toNat with hi | hi
      · rw [← heq, pow_succ']
        refine coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal i (fun j hj ↦ ?_)
          (fun j _ ↦ ih j) i le_rfl
        rw [map_add, Polynomial.coeff_coe]
        refine Ideal.add_mem _ ?_ (g.coeff_trunc_order_mem I j)
        simp_rw [coeff_X_pow_mul', if_neg (lt_of_le_of_lt hj hi).not_le, zero_mem]
      simp_rw [Polynomial.coeff_coe,
        Polynomial.coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hdeg (by simpa)), zero_mem]
    rw [add_mul, mul_comm (X ^ _), ← eq_sub_iff_add_eq] at heq
    replace heq := congr(H.isUnit_shift.unit⁻¹ * $heq)
    rw [← mul_assoc, ← mul_assoc, IsUnit.val_inv_mul, one_mul] at heq
    intro i
    rw [← coeff_X_pow_mul _ (g.map (Ideal.Quotient.mk I)).order.toNat i, heq]
    refine coeff_mul_mem_ideal_of_coeff_right_mem_ideal' (fun i ↦ ?_) _
    rw [map_sub]
    refine Ideal.sub_mem _ (h1 _) ?_
    rw [pow_succ']
    refine coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal' (fun i ↦ ?_) ih _
    simp_rw [Polynomial.coeff_coe, g.coeff_trunc_order_mem]

/-- If `g * q + r = g * q' + r'` for some power series `q`, `q'` and some polynomials `r`, `r'`
whose degrees are `< n`, then `q = q'` and `r = r'` are all zero.
This implies the uniqueness of Weierstrass division. -/
theorem eq_of_mul_add_eq_mul_add [IsHausdorff I A] {q q' : A⟦X⟧} {r r' : A[X]}
    (hr : r.degree < (g.map (Ideal.Quotient.mk I)).order.toNat)
    (hr' : r'.degree < (g.map (Ideal.Quotient.mk I)).order.toNat)
    (heq : g * q + r = g * q' + r') : q = q' ∧ r = r' := by
  replace heq : g * (q - q') = ↑(r' - r) := by
    rw [← eq_sub_iff_add_eq] at heq
    rw [Polynomial.coe_sub, mul_sub, heq]
    ring
  have h := H.eq_zero_of_mul_eq (lt_of_le_of_lt (r'.degree_sub_le r) (max_lt hr' hr)) heq
  simp_rw [sub_eq_zero] at h
  exact ⟨h.1, h.2.symm⟩

@[simp]
theorem div_add [IsAdicComplete I A] {f f' : A⟦X⟧} : H.div (f + f') = H.div f + H.div f' := by
  have H1 := (H.isWeierstrassDivisionAt_div_mod f).add (H.isWeierstrassDivisionAt_div_mod f')
  have H2 := H.isWeierstrassDivisionAt_div_mod (f + f')
  exact (H.eq_of_mul_add_eq_mul_add H2.degree_lt H1.degree_lt
    (H2.eq_mul_add.symm.trans H1.eq_mul_add)).1

@[simp]
theorem div_smul [IsAdicComplete I A] {a : A} {f : A⟦X⟧} : H.div (a • f) = a • H.div f := by
  have H1 := (H.isWeierstrassDivisionAt_div_mod f).smul a
  have H2 := H.isWeierstrassDivisionAt_div_mod (a • f)
  exact (H.eq_of_mul_add_eq_mul_add H2.degree_lt H1.degree_lt
    (H2.eq_mul_add.symm.trans H1.eq_mul_add)).1

@[simp]
theorem div_zero [IsAdicComplete I A] : H.div 0 = 0 := by
  simpa using H.div_smul (a := 0) (f := 0)

@[simp]
theorem mod_add [IsAdicComplete I A] {f f' : A⟦X⟧} : H.mod (f + f') = H.mod f + H.mod f' := by
  have H1 := (H.isWeierstrassDivisionAt_div_mod f).add (H.isWeierstrassDivisionAt_div_mod f')
  have H2 := H.isWeierstrassDivisionAt_div_mod (f + f')
  exact (H.eq_of_mul_add_eq_mul_add H2.degree_lt H1.degree_lt
    (H2.eq_mul_add.symm.trans H1.eq_mul_add)).2

@[simp]
theorem mod_smul [IsAdicComplete I A] {a : A} {f : A⟦X⟧} : H.mod (a • f) = a • H.mod f := by
  have H1 := (H.isWeierstrassDivisionAt_div_mod f).smul a
  have H2 := H.isWeierstrassDivisionAt_div_mod (a • f)
  exact (H.eq_of_mul_add_eq_mul_add H2.degree_lt H1.degree_lt
    (H2.eq_mul_add.symm.trans H1.eq_mul_add)).2

@[simp]
theorem mod_zero [IsAdicComplete I A] : H.mod 0 = 0 := by
  simpa using H.mod_smul (a := 0) (f := 0)

/-- The remainder map `PowerSeries.IsWeierstrassDivisorAt.mod` induces a linear map
`A⟦X⟧ / (g) → A[X]`. -/
noncomputable def mod' [IsAdicComplete I A] : A⟦X⟧ ⧸ Ideal.span {g} →ₗ[A] A[X] where
  toFun := Quotient.lift (fun f ↦ H.mod f) fun f f' hf ↦ by
    simp_rw [HasEquiv.Equiv, Submodule.quotientRel_def, Ideal.mem_span_singleton'] at hf
    obtain ⟨a, ha⟩ := hf
    obtain ⟨hf1, hf2⟩ := H.isWeierstrassDivisionAt_div_mod f
    obtain ⟨hf'1, hf'2⟩ := H.isWeierstrassDivisionAt_div_mod f'
    rw [eq_sub_iff_add_eq, hf2, hf'2, ← add_assoc, mul_comm, ← mul_add] at ha
    exact (H.eq_of_mul_add_eq_mul_add hf'1 hf1 ha).2.symm
  map_add' f f' := by
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective f
    obtain ⟨f', rfl⟩ := Ideal.Quotient.mk_surjective f'
    exact H.mod_add
  map_smul' a f := by
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective f
    exact H.mod_smul

@[simp]
theorem mod'_mk_eq_mod [IsAdicComplete I A] {f : A⟦X⟧} :
    H.mod' (Ideal.Quotient.mk _ f) = H.mod f := rfl

theorem div_coe_eq_zero [IsAdicComplete I A] {r : A[X]}
    (hr : r.degree < (g.map (Ideal.Quotient.mk I)).order.toNat) : H.div r = 0 := by
  obtain ⟨h1, h2⟩ := H.isWeierstrassDivisionAt_div_mod r
  exact (H.eq_of_mul_add_eq_mul_add (q := H.div r) (q' := 0) h1 hr (by simpa using h2.symm)).1

theorem mod_coe_eq_self [IsAdicComplete I A] {r : A[X]}
    (hr : r.degree < (g.map (Ideal.Quotient.mk I)).order.toNat) : H.mod r = r := by
  obtain ⟨h1, h2⟩ := H.isWeierstrassDivisionAt_div_mod r
  exact (H.eq_of_mul_add_eq_mul_add (q := H.div r) (q' := 0) h1 hr (by simpa using h2.symm)).2

@[simp]
theorem mk_mod'_eq_self [IsAdicComplete I A] {f : A⟦X⟧ ⧸ Ideal.span {g}} :
    Ideal.Quotient.mk _ (H.mod' f : A⟦X⟧) = f := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective f
  rw [mod'_mk_eq_mod, Eq.comm, Ideal.Quotient.mk_eq_mk_iff_sub_mem, Ideal.mem_span_singleton']
  use H.div f
  rw [eq_sub_iff_add_eq, mul_comm, (H.isWeierstrassDivisionAt_div_mod f).2.symm]

end IsWeierstrassDivisorAt

section Equiv

variable {g : A[X]} {I : Ideal A} (H : g.IsDistinguishedAt I) [IsAdicComplete I A]
include H

/-- A distinguished polynomial `g` induces a natural isomorphism `A[X] / (g) ≃ A⟦X⟧ / (g)`. -/
@[simps! apply symm_apply]
noncomputable def _root_.Polynomial.IsDistinguishedAt.algEquivQuotient :
    (A[X] ⧸ Ideal.span {g}) ≃ₐ[A] A⟦X⟧ ⧸ Ideal.span {(g : A⟦X⟧)} where
  __ := show (A[X] ⧸ Ideal.span {g}) →ₐ[A] A⟦X⟧ ⧸ Ideal.span {(g : A⟦X⟧)} from
    Ideal.quotientMapₐ _ (Polynomial.coeToPowerSeries.algHom A) fun a ha ↦ by
      obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 ha
      simp only [Ideal.mem_comap, Polynomial.coeToPowerSeries.algHom_apply, Algebra.id.map_eq_id,
        map_id, id_eq, Ideal.mem_span_singleton']
      exact ⟨b, by simp [← hb]⟩
  invFun := Ideal.Quotient.mk _ ∘ H.isWeierstrassDivisorAt'.mod'
  left_inv f := by
    rcases subsingleton_or_nontrivial A with _ | _
    · have : Subsingleton A[X] := inferInstance
      have : Subsingleton (A[X] ⧸ Ideal.span {g}) := Quot.Subsingleton
      exact Subsingleton.elim _ _
    have hI : I ≠ ⊤ := by
      rintro rfl
      exact not_subsingleton _ ‹IsAdicComplete ⊤ A›.toIsHausdorff.subsingleton
    have := Ideal.Quotient.nontrivial hI
    obtain ⟨f, hfdeg, rfl⟩ : ∃ r : A[X], r.degree < g.degree ∧ Ideal.Quotient.mk _ r = f := by
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective f
      refine ⟨f %ₘ g, Polynomial.degree_modByMonic_lt f H.monic, ?_⟩
      rw [Eq.comm, Ideal.Quotient.mk_eq_mk_iff_sub_mem, Ideal.mem_span_singleton']
      exact ⟨f /ₘ g, by rw [Polynomial.modByMonic_eq_sub_mul_div _ H.monic]; ring⟩
    have h1 : g.degree = ((g : A⟦X⟧).map (Ideal.Quotient.mk I)).order.toNat := by
      convert H.degree_eq_coe_lift_order_map g 1
        (by rwa [constantCoeff_one, ← Ideal.ne_top_iff_one]) (by simp)
      exact (ENat.lift_eq_toNat_of_lt_top _).symm
    dsimp
    rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, Ideal.mem_span_singleton']
    exact ⟨0, by simp [H.isWeierstrassDivisorAt'.mod_coe_eq_self (hfdeg.trans_eq h1)]⟩
  right_inv f := H.isWeierstrassDivisorAt'.mk_mod'_eq_self

end Equiv

end IsWeierstrassDivisorAt

section IsLocalRing

variable [IsLocalRing A] (a : A) (f f' g : A⟦X⟧)

variable {g} in
/-- **Weierstrass division** ([washington_cyclotomic], Proposition 7.2): let `f`, `g` be
power series over a complete local ring, such that
the image of `g` in the residue field is not zero. Let `n` be the order of the image of `g` in the
residue field. Then there exists a power series `q` and a polynomial `r` of degree `< n`, such that
`f = g * q + r`. -/
theorem exists_isWeierstrassDivision [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (hg : g.map (IsLocalRing.residue A) ≠ 0) : ∃ q r, f.IsWeierstrassDivision g q r :=
  ⟨_, _, (IsWeierstrassDivisor.of_map_ne_zero hg).isWeierstrassDivisionAt_div_mod f⟩

-- Unfortunately there is no Unicode subscript `w`.

/-- The quotient `q` in Weierstrass division, denoted by `f /ʷ g`. Note that when the image of
`g` in the residue field is zero, this is defined to be zero. -/
noncomputable def weierstrassDiv [IsPrecomplete (IsLocalRing.maximalIdeal A) A] : A⟦X⟧ :=
  open scoped Classical in
  if hg : g.map (IsLocalRing.residue A) ≠ 0 then
    (IsWeierstrassDivisor.of_map_ne_zero hg).div f
  else
    0

/-- The remainder `r` in Weierstrass division, denoted by `f %ʷ g`. Note that when the image of
`g` in the residue field is zero, this is defined to be zero. -/
noncomputable def weierstrassMod [IsPrecomplete (IsLocalRing.maximalIdeal A) A] : A[X] :=
  open scoped Classical in
  if hg : g.map (IsLocalRing.residue A) ≠ 0 then
    (IsWeierstrassDivisor.of_map_ne_zero hg).mod f
  else
    0

@[inherit_doc]
infixl:70 " /ʷ " => weierstrassDiv

@[inherit_doc]
infixl:70 " %ʷ " => weierstrassMod

@[simp]
theorem weierstrassDiv_zero_right [IsPrecomplete (IsLocalRing.maximalIdeal A) A] : f /ʷ 0 = 0 := by
  rw [weierstrassDiv, dif_neg (by simp)]

alias weierstrassDiv_zero := weierstrassDiv_zero_right

@[simp]
theorem weierstrassMod_zero_right [IsPrecomplete (IsLocalRing.maximalIdeal A) A] : f %ʷ 0 = 0 := by
  rw [weierstrassMod, dif_neg (by simp)]

alias weierstrassMod_zero := weierstrassMod_zero_right

theorem degree_weierstrassMod_lt [IsPrecomplete (IsLocalRing.maximalIdeal A) A] :
    (f %ʷ g).degree < (g.map (IsLocalRing.residue A)).order.toNat := by
  rw [weierstrassMod]
  split_ifs with hg
  · exact degree_trunc_lt _ _
  · nontriviality A
    rw [Polynomial.degree_zero]
    exact WithBot.bot_lt_coe _

section

variable {g} (hg : g.map (IsLocalRing.residue A) ≠ 0)
include hg

theorem isWeierstrassDivision_weierstrassDiv_weierstrassMod
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] :
    f.IsWeierstrassDivision g (f /ʷ g) (f %ʷ g) := by
  simp_rw [weierstrassDiv, weierstrassMod, dif_pos hg]
  exact (IsWeierstrassDivisor.of_map_ne_zero hg).isWeierstrassDivisionAt_div_mod f

theorem eq_mul_weierstrassDiv_add_weierstrassMod
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] :
    f = g * (f /ʷ g) + (f %ʷ g) := by
  simp_rw [weierstrassDiv, weierstrassMod, dif_pos hg]
  exact ((IsWeierstrassDivisor.of_map_ne_zero hg).isWeierstrassDivisionAt_div_mod f).2

variable {f} in
/-- The quotient `q` and the remainder `r` in the Weierstrass division are unique.

This result is stated using two `PowerSeries.IsWeierstrassDivision` assertions, and only requires
the ring being Hausdorff with respect to the maximal ideal. If you want `q` and `r` equal to
`f /ʷ g` and `f %ʷ g`, use `PowerSeries.IsWeierstrassDivision.unique`
instead, which requires the ring being complete with respect to the maximal ideal. -/
theorem IsWeierstrassDivision.elim [IsHausdorff (IsLocalRing.maximalIdeal A) A]
    {q q' : A⟦X⟧} {r r' : A[X]}
    (H : f.IsWeierstrassDivision g q r) (H2 : f.IsWeierstrassDivision g q' r') : q = q' ∧ r = r' :=
  (IsWeierstrassDivisor.of_map_ne_zero hg).eq_of_mul_add_eq_mul_add H.1 H2.1 (H.2.symm.trans H2.2)

/-- If `q` and `r` are quotient and remainder in the Weierstrass division `0 / g`, then they are
equal to `0`. -/
theorem IsWeierstrassDivision.eq_zero [IsHausdorff (IsLocalRing.maximalIdeal A) A]
    {q : A⟦X⟧} {r : A[X]}
    (H : IsWeierstrassDivision 0 g q r) : q = 0 ∧ r = 0 :=
  H.elim hg (g.isWeierstrassDivisionAt_zero _)

variable {f} in
/-- If `q` and `r` are quotient and remainder in the Weierstrass division `f / g`, then they are
equal to `f /ʷ g` and `f %ʷ g`. -/
theorem IsWeierstrassDivision.unique [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {q : A⟦X⟧} {r : A[X]}
    (H : f.IsWeierstrassDivision g q r) : q = f /ʷ g ∧ r = f %ʷ g :=
  H.elim hg (f.isWeierstrassDivision_weierstrassDiv_weierstrassMod hg)

end

@[simp]
theorem add_weierstrassDiv [IsAdicComplete (IsLocalRing.maximalIdeal A) A] :
    (f + f') /ʷ g = f /ʷ g + f' /ʷ g := by
  simp_rw [weierstrassDiv]
  split_ifs <;> simp

@[simp]
theorem smul_weierstrassDiv [IsAdicComplete (IsLocalRing.maximalIdeal A) A] :
    (a • f) /ʷ g = a • (f /ʷ g) := by
  simp_rw [weierstrassDiv]
  split_ifs <;> simp

@[simp]
theorem weierstrassDiv_zero_left [IsAdicComplete (IsLocalRing.maximalIdeal A) A] : 0 /ʷ g = 0 := by
  simp_rw [weierstrassDiv]
  split_ifs <;> simp

alias zero_weierstrassDiv := weierstrassDiv_zero_left

@[simp]
theorem add_weierstrassMod [IsAdicComplete (IsLocalRing.maximalIdeal A) A] :
    (f + f') %ʷ g = f %ʷ g + f' %ʷ g := by
  simp_rw [weierstrassMod]
  split_ifs <;> simp

@[simp]
theorem smul_weierstrassMod [IsAdicComplete (IsLocalRing.maximalIdeal A) A] :
    (a • f) %ʷ g = a • (f %ʷ g) := by
  simp_rw [weierstrassMod]
  split_ifs <;> simp

@[simp]
theorem weierstrassMod_zero_left [IsAdicComplete (IsLocalRing.maximalIdeal A) A] : 0 %ʷ g = 0 := by
  simp_rw [weierstrassMod]
  split_ifs <;> simp

alias zero_weierstrassMod := weierstrassMod_zero_left

end IsLocalRing

/-!

## Weierstrass preparation theorem

-/

/-- If `f` is a polynomial over `A`, `g` and `h` are power series over `A`,
then `PowerSeries.IsWeierstrassFactorizationAt g f h I` is a `Prop` which asserts that `f` is
distingushed at `I`, `h` is a unit, such that `g = f * h`. -/
@[mk_iff]
structure IsWeierstrassFactorizationAt (g : A⟦X⟧) (f : A[X]) (h : A⟦X⟧) (I : Ideal A) : Prop where
  isDistinguishedAt : f.IsDistinguishedAt I
  isUnit : IsUnit h
  eq_mul : g = f * h

/-- Version of `PowerSeries.IsWeierstrassFactorizationAt` for local rings with respect to
its maximal ideal. -/
abbrev IsWeierstrassFactorization (g : A⟦X⟧) (f : A[X]) (h : A⟦X⟧) [IsLocalRing A] : Prop :=
  g.IsWeierstrassFactorizationAt f h (IsLocalRing.maximalIdeal A)

theorem _root_.Polynomial.IsWeaklyEisensteinAt.mul
    {R : Type*} [CommSemiring R] {𝓟 : Ideal R} {f f' : R[X]}
    (hf : f.IsWeaklyEisensteinAt 𝓟) (hf' : f'.IsWeaklyEisensteinAt 𝓟) :
    (f * f').IsWeaklyEisensteinAt 𝓟 := by
  rw [Polynomial.isWeaklyEisensteinAt_iff] at hf hf' ⊢
  intro n hn
  rw [Polynomial.coeff_mul]
  refine Ideal.sum_mem _ fun x hx ↦ ?_
  rcases lt_or_le x.1 f.natDegree with hx1 | hx1
  · exact Ideal.mul_mem_right _ _ (hf hx1)
  replace hx1 : x.2 < f'.natDegree := by
    by_contra!
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    replace hn := hn.trans_le Polynomial.natDegree_mul_le
    linarith
  exact Ideal.mul_mem_left _ _ (hf' hx1)

theorem _root_.Polynomial.IsDistinguishedAt.mul
    {R : Type*} [CommRing R] {f f' : R[X]} {I : Ideal R}
    (hf : f.IsDistinguishedAt I) (hf' : f'.IsDistinguishedAt I) :
    (f * f').IsDistinguishedAt I :=
  ⟨hf.toIsWeaklyEisensteinAt.mul hf'.toIsWeaklyEisensteinAt, hf.monic.mul hf'.monic⟩

namespace IsWeierstrassFactorizationAt

variable {g : A⟦X⟧} {f : A[X]} {h : A⟦X⟧} {I : Ideal A} (H : g.IsWeierstrassFactorizationAt f h I)
include H

theorem map_ne_zero_of_ne_top (hI : I ≠ ⊤) : g.map (Ideal.Quotient.mk I) ≠ 0 := by
  have := Ideal.Quotient.nontrivial hI
  rw [congr(map (Ideal.Quotient.mk I) $(H.eq_mul)), map_mul, ← Polynomial.polynomial_map_coe, ne_eq,
    (H.isUnit.map _).mul_left_eq_zero]
  exact_mod_cast f.map_monic_ne_zero (f := Ideal.Quotient.mk I) H.isDistinguishedAt.monic

theorem degree_eq_coe_lift_order_map_of_ne_top (hI : I ≠ ⊤) :
    f.degree = (g.map (Ideal.Quotient.mk I)).order.lift
      (order_finite_iff_ne_zero.2 (H.map_ne_zero_of_ne_top hI)) := by
  refine H.isDistinguishedAt.degree_eq_coe_lift_order_map g h ?_ H.eq_mul
  contrapose! hI
  exact Ideal.eq_top_of_isUnit_mem _ hI (isUnit_iff_constantCoeff.1 H.isUnit)

theorem natDegree_eq_toNat_order_map_of_ne_top (hI : I ≠ ⊤) :
    f.natDegree = (g.map (Ideal.Quotient.mk I)).order.toNat := by
  rw [Polynomial.natDegree, H.degree_eq_coe_lift_order_map_of_ne_top hI,
    ENat.lift_eq_toNat_of_lt_top]
  exact WithBot.unbotD_coe _ _

/-- If `g = f * h` is a Weierstrass factorization, then there is a
natural isomorphism `A[X] / (f) ≃ A⟦X⟧ / (g)`. -/
@[simps! apply]
noncomputable def algEquivQuotient [IsAdicComplete I A] :
    (A[X] ⧸ Ideal.span {f}) ≃ₐ[A] A⟦X⟧ ⧸ Ideal.span {g} :=
  H.isDistinguishedAt.algEquivQuotient.trans <| Ideal.quotientEquivAlgOfEq A <|
    by rw [H.eq_mul, Ideal.span_singleton_mul_right_unit H.isUnit]

@[simp]
theorem algEquivQuotient_symm_apply [IsAdicComplete I A] (x : A⟦X⟧ ⧸ Ideal.span {g}) :
    H.algEquivQuotient.symm x = Ideal.Quotient.mk _
      (H.isDistinguishedAt.isWeierstrassDivisorAt'.mod' <| Ideal.quotientEquivAlgOfEq A
        (by rw [H.eq_mul, Ideal.span_singleton_mul_right_unit H.isUnit]) x) := by
  simp [algEquivQuotient]

theorem mul {g' : A⟦X⟧} {f' : A[X]} {h' : A⟦X⟧} (H' : g'.IsWeierstrassFactorizationAt f' h' I) :
    (g * g').IsWeierstrassFactorizationAt (f * f') (h * h') I :=
  ⟨H.isDistinguishedAt.mul H'.isDistinguishedAt, H.isUnit.mul H'.isUnit, by
    rw [H.eq_mul, H'.eq_mul, Polynomial.coe_mul]; ring⟩

theorem smul {a : A} (ha : IsUnit a) : (a • g).IsWeierstrassFactorizationAt f (a • h) I := by
  refine ⟨H.isDistinguishedAt, ?_, ?_⟩
  · rw [Algebra.smul_def]
    exact (ha.map _).mul H.isUnit
  · simp [H.eq_mul]

end IsWeierstrassFactorizationAt

variable [IsLocalRing A]

namespace IsWeierstrassFactorization

variable {g : A⟦X⟧} {f : A[X]} {h : A⟦X⟧} (H : g.IsWeierstrassFactorization f h)
include H

theorem map_ne_zero : g.map (IsLocalRing.residue A) ≠ 0 :=
  H.map_ne_zero_of_ne_top (Ideal.IsMaximal.ne_top inferInstance)

theorem degree_eq_coe_lift_order_map : f.degree = (g.map (IsLocalRing.residue A)).order.lift
    (order_finite_iff_ne_zero.2 H.map_ne_zero) :=
  H.degree_eq_coe_lift_order_map_of_ne_top (Ideal.IsMaximal.ne_top inferInstance)

theorem natDegree_eq_toNat_order_map :
    f.natDegree = (g.map (IsLocalRing.residue A)).order.toNat :=
  H.natDegree_eq_toNat_order_map_of_ne_top (Ideal.IsMaximal.ne_top inferInstance)

end IsWeierstrassFactorization

theorem IsWeierstrassDivision.isUnit_of_map_ne_zero
    {g q : A⟦X⟧} {r : A[X]} (hg : g.map (IsLocalRing.residue A) ≠ 0)
    (H : (X ^ (g.map (IsLocalRing.residue A)).order.toNat).IsWeierstrassDivision g q r) :
    IsUnit q := by
  obtain ⟨H1 : r.degree < (g.map (IsLocalRing.residue A)).order.toNat, H2⟩ := H
  set n := (g.map (IsLocalRing.residue A)).order.toNat
  replace H2 := congr(coeff _ n (($H2).map (IsLocalRing.residue A)))
  simp_rw [map_pow, map_X, coeff_X_pow_self, map_add, map_mul, coeff_map,
    Polynomial.coeff_coe, Polynomial.coeff_eq_zero_of_degree_lt H1, map_zero, add_zero] at H2
  rw [isUnit_iff_constantCoeff, ← isUnit_map_iff (IsLocalRing.residue A)]
  rw [coeff_mul, ← Finset.sum_subset (s₁ := {(n, 0)}) (by simp) (fun p hp hnotMem ↦ ?_),
    Finset.sum_singleton, coeff_map, coeff_map, coeff_zero_eq_constantCoeff, mul_comm] at H2
  · exact isUnit_of_mul_eq_one _ _ H2.symm
  · rw [coeff_of_lt_order p.1 ?_]
    · rw [zero_mul]
    · rw [← ENat.lt_lift_iff (h := order_finite_iff_ne_zero.2 hg), ENat.lift_eq_toNat_of_lt_top]
      refine (Finset.antidiagonal.fst_le hp).lt_of_ne ?_
      contrapose! hnotMem
      rwa [Finset.mem_singleton, Finset.antidiagonal_congr hp (by simp)]

theorem IsWeierstrassDivision.isWeierstrassFactorization
    {g q : A⟦X⟧} {r : A[X]} (hg : g.map (IsLocalRing.residue A) ≠ 0)
    (H : (X ^ (g.map (IsLocalRing.residue A)).order.toNat).IsWeierstrassDivision g q r) :
    g.IsWeierstrassFactorization
      (Polynomial.X ^ (g.map (IsLocalRing.residue A)).order.toNat - r)
      ↑(H.isUnit_of_map_ne_zero hg).unit⁻¹ := by
  have H1 : r.degree < (g.map (IsLocalRing.residue A)).order.toNat := H.1
  set n := (g.map (IsLocalRing.residue A)).order.toNat
  set f := Polynomial.X ^ n - r
  replace H1 : r.degree < (Polynomial.X (R := A) ^ n).degree := by rwa [Polynomial.degree_X_pow]
  have hfdeg : f.natDegree = n := by
    suffices f.degree = n by rw [Polynomial.natDegree, this]; rfl
    rw [Polynomial.degree_sub_eq_left_of_degree_lt H1, Polynomial.degree_X_pow]
  refine ⟨⟨⟨fun {i} hi ↦ ?_⟩, .sub_of_left (Polynomial.monic_X_pow _) H1⟩, Units.isUnit _, ?_⟩
  · rw [hfdeg] at hi
    simp_rw [f, Polynomial.coeff_sub, Polynomial.coeff_X_pow, if_neg hi.ne, zero_sub, neg_mem_iff]
    have := H.coeff_f_sub_r_mem hi
    rwa [map_sub, coeff_X_pow, if_neg hi.ne, zero_sub, neg_mem_iff, Polynomial.coeff_coe] at this
  · have := congr($(H.2) * ↑(H.isUnit_of_map_ne_zero hg).unit⁻¹)
    rw [add_mul, mul_assoc, IsUnit.mul_val_inv, mul_one, ← sub_eq_iff_eq_add] at this
    simp_rw [← this, f, Polynomial.coe_sub, Polynomial.coe_pow, Polynomial.coe_X, sub_mul]

theorem IsWeierstrassFactorization.isWeierstrassDivision
    {g : A⟦X⟧} {f : A[X]} {h : A⟦X⟧} (H : g.IsWeierstrassFactorization f h) :
    (X ^ (g.map (IsLocalRing.residue A)).order.toNat).IsWeierstrassDivision g ↑H.isUnit.unit⁻¹
      (Polynomial.X ^ (g.map (IsLocalRing.residue A)).order.toNat - f) := by
  set n := (g.map (IsLocalRing.residue A)).order.toNat with hn
  constructor
  · refine (Polynomial.degree_sub_lt ?_ (Polynomial.monic_X_pow n).ne_zero ?_).trans_eq (by simpa)
    · simp_rw [H.degree_eq_coe_lift_order_map, Polynomial.degree_X_pow, n,
        ENat.lift_eq_toNat_of_lt_top]
    · rw [(Polynomial.monic_X_pow n).leadingCoeff, H.isDistinguishedAt.monic.leadingCoeff]
  · simp_rw [H.eq_mul, mul_assoc, IsUnit.mul_val_inv, mul_one, Polynomial.coe_sub,
      Polynomial.coe_pow, Polynomial.coe_X, add_sub_cancel]

/-- The `f` and `h` in the Weierstrass preparation theorem are unique.

This result is stated using two `PowerSeries.IsWeierstrassFactorization` assertions, and only
requires the ring being Hausdorff with respect to the maximal ideal. If you want `f` and `h` equal
to `PowerSeries.weierstrassDistinguished` and `PowerSeries.weierstrassUnit`,
use `PowerSeries.IsWeierstrassFactorization.unique` instead, which requires the ring being
complete with respect to the maximal ideal. -/
theorem IsWeierstrassFactorization.elim [IsHausdorff (IsLocalRing.maximalIdeal A) A]
    {g : A⟦X⟧} {f f' : A[X]} {h h' : A⟦X⟧} (H : g.IsWeierstrassFactorization f h)
    (H2 : g.IsWeierstrassFactorization f' h') : f = f' ∧ h = h' := by
  obtain ⟨h1, h2⟩ := H.isWeierstrassDivision.elim H.map_ne_zero H2.isWeierstrassDivision
  rw [← Units.ext_iff, inv_inj, Units.ext_iff] at h1
  exact ⟨by simpa using h2, h1⟩

section IsAdicComplete

variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A] {a : A} {g g' : A⟦X⟧} {f : A[X]} {h : A⟦X⟧}

/-- **Weierstrass preparation theorem** ([washington_cyclotomic], Theorem 7.3):
let `g` be a power series over a complete local ring,
such that its image in the residue field is not zero. Then there exists a distinguished
polynomial `f` and a power series `h` which is a unit, such that `g = f * h`. -/
theorem exists_isWeierstrassFactorization (hg : g.map (IsLocalRing.residue A) ≠ 0) :
    ∃ f h, g.IsWeierstrassFactorization f h := by
  obtain ⟨q, r, H⟩ :=
    (X ^ (g.map (IsLocalRing.residue A)).order.toNat).exists_isWeierstrassDivision hg
  exact ⟨_, _, H.isWeierstrassFactorization hg⟩

variable (g) in
/-- The `f` in the Weierstrass preparation theorem. -/
noncomputable def weierstrassDistinguished (hg : g.map (IsLocalRing.residue A) ≠ 0) : A[X] :=
  (g.exists_isWeierstrassFactorization hg).choose

variable (g) in
/-- The `h` in the Weierstrass preparation theorem. -/
noncomputable def weierstrassUnit (hg : g.map (IsLocalRing.residue A) ≠ 0) : A⟦X⟧ :=
  (g.exists_isWeierstrassFactorization hg).choose_spec.choose

theorem isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit
    (hg : g.map (IsLocalRing.residue A) ≠ 0) :
    g.IsWeierstrassFactorization (g.weierstrassDistinguished hg) (g.weierstrassUnit hg) :=
  (g.exists_isWeierstrassFactorization hg).choose_spec.choose_spec

/-- If `g` is a power series over a complete local ring,
such that its image in the residue field is not zero, then there is a natural isomorphism
`A[X] / (f) ≃ A⟦X⟧ / (g)` where `f` is `PowerSeries.weierstrassDistinguished g`. -/
noncomputable abbrev algEquivQuotientWeierstrassDistinguished
    (hg : g.map (IsLocalRing.residue A) ≠ 0) :=
  (g.isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit hg).algEquivQuotient

theorem isDistinguishedAt_weierstrassDistinguished (hg : g.map (IsLocalRing.residue A) ≠ 0) :
    (g.weierstrassDistinguished hg).IsDistinguishedAt (IsLocalRing.maximalIdeal A) :=
  (g.exists_isWeierstrassFactorization hg).choose_spec.choose_spec.isDistinguishedAt

theorem isUnit_weierstrassUnit (hg : g.map (IsLocalRing.residue A) ≠ 0) :
    IsUnit (g.weierstrassUnit hg) :=
  (g.exists_isWeierstrassFactorization hg).choose_spec.choose_spec.isUnit

theorem eq_weierstrassDistinguished_mul_weierstrassUnit (hg : g.map (IsLocalRing.residue A) ≠ 0) :
    g = g.weierstrassDistinguished hg * g.weierstrassUnit hg :=
  (g.exists_isWeierstrassFactorization hg).choose_spec.choose_spec.eq_mul

/-- The `f` and `h` in Weierstrass preparation theorem are equal
to `PowerSeries.weierstrassDistinguished` and `PowerSeries.weierstrassUnit`. -/
theorem IsWeierstrassFactorization.unique
    (H : g.IsWeierstrassFactorization f h) (hg : g.map (IsLocalRing.residue A) ≠ 0) :
    f = g.weierstrassDistinguished hg ∧ h = g.weierstrassUnit hg :=
  H.elim (g.isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit hg)

@[simp]
theorem weierstrassDistinguished_mul (hg : (g * g').map (IsLocalRing.residue A) ≠ 0) :
    (g * g').weierstrassDistinguished hg =
      g.weierstrassDistinguished (fun h ↦ hg (by simp [h])) *
        g'.weierstrassDistinguished (fun h ↦ hg (by simp [h])) := by
  have H := g.isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit
    (fun h ↦ hg (by simp [h]))
  have H' := g'.isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit
    (fun h ↦ hg (by simp [h]))
  have H'' := (g * g').isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit hg
  exact (H''.elim (H.mul H')).1

@[simp]
theorem weierstrassUnit_mul (hg : (g * g').map (IsLocalRing.residue A) ≠ 0) :
    (g * g').weierstrassUnit hg =
      g.weierstrassUnit (fun h ↦ hg (by simp [h])) *
        g'.weierstrassUnit (fun h ↦ hg (by simp [h])) := by
  have H := g.isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit
    (fun h ↦ hg (by simp [h]))
  have H' := g'.isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit
    (fun h ↦ hg (by simp [h]))
  have H'' := (g * g').isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit hg
  exact (H''.elim (H.mul H')).2

@[simp]
theorem weierstrassDistinguished_smul (hg : (a • g).map (IsLocalRing.residue A) ≠ 0) :
    (a • g).weierstrassDistinguished hg =
      g.weierstrassDistinguished (fun h ↦ hg (by simp [Algebra.smul_def, h])) := by
  have H := g.isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit
    (fun h ↦ hg (by simp [Algebra.smul_def, h]))
  have H' := (a • g).isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit hg
  have ha : IsLocalRing.residue A a ≠ 0 := fun h ↦ hg (by simp [Algebra.smul_def, h])
  exact (H'.elim (H.smul (by simpa using ha))).1

@[simp]
theorem weierstrassUnit_smul (hg : (a • g).map (IsLocalRing.residue A) ≠ 0) :
    (a • g).weierstrassUnit hg =
      a • g.weierstrassUnit (fun h ↦ hg (by simp [Algebra.smul_def, h])) := by
  have H := g.isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit
    (fun h ↦ hg (by simp [Algebra.smul_def, h]))
  have H' := (a • g).isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit hg
  have ha : IsLocalRing.residue A a ≠ 0 := fun h ↦ hg (by simp [Algebra.smul_def, h])
  exact (H'.elim (H.smul (by simpa using ha))).2

end IsAdicComplete

end PowerSeries
