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
such ring has only on maximal ideal, and hence such ring is a complete local ring.

## Main definitions

- `PowerSeries.IsWeierstrassDivisionAt f g q r I`: a `Prop` which asserts that a power series
  `q` and a polynomial `r` of degree `< n` satisfy `f = g * q + r`, where `n` is the order of the
  image of `g` in `(A / I)⟦X⟧` (defined to be zero if such image is zero, in which case
  it's mathematically not considered).

- `PowerSeries.IsWeierstrassDivision`: version of `PowerSeries.IsWeierstrassDivisionAt`
  for local rings with respect to its maximal ideal.

- `PowerSeries.IsWeierstrassFactorizationAt g f h I`: a `Prop` which asserts that `f` is a
  distingushed polynomial at `I`, `h` is a formal power series over `A` which a unit, such that
  the formal power series `g` satisfies `g = f * h`.

- `PowerSeries.IsWeierstrassFactorization`: version of `PowerSeries.IsWeierstrassFactorizationAt`
  for local rings with respect to its maximal ideal.

## Main results

- `PowerSeries.exists_isWeierstrassDivision`: **Weierstrass division**
  ([washington_cyclotomic], Proposition 7.2): let `f`, `g` be power series
  over a complete local ring, such that the image of `g` in the residue field is not zero.
  Let `n` be the order of the image of `g` in the residue field. Then there exists a power series
  `q` and a polynomial `r` of degree `< n`, such that `f = g * q + r`.

- `PowerSeries.IsWeierstrassDivision.elim`: The `q` and `r` in the Weierstrass division is unique.

- `PowerSeries.exists_isWeierstrassFactorization`: **Weierstrass preparation theorem**
  ([washington_cyclotomic], Theorem 7.3): let `g` be a power series
  over a complete local ring, such that the image of `g` in the residue field is
  not zero. Then there exists a distinguished polynomial `f` and a power series `h`
  which is a unit, such that `g = f * h`.

- `PowerSeries.IsWeierstrassFactorization.elim`: The `f` and `h` in Werierstrass preparation
  theorem is unique.

## References

- [Washington, Lawrence C. *Introduction to cyclotomic fields.*][washington_cyclotomic]

-/

open scoped Polynomial PowerSeries

namespace PowerSeries

variable {A : Type*} [CommRing A]

/-!

## Weierstrass division

-/

/-- `PowerSeries.IsWeierstrassDivisionAt f g q r I` is a `Prop` which asserts that a power series
`q` and a polynomial `r` of degree `< n` satisfy `f = g * q + r`, where `n` is the order of the
image of `g` in `(A / I)⟦X⟧` (defined to be zero if such image is zero, in which case
it's mathematically not considered). -/
def IsWeierstrassDivisionAt (f g q : A⟦X⟧) (r : A[X]) (I : Ideal A) : Prop :=
  r.degree < (g.map (Ideal.Quotient.mk I)).order.toNat ∧ f = g * q + r

/-- Version of `PowerSeries.IsWeierstrassDivisionAt` for local rings with respect to
its maximal ideal. -/
abbrev IsWeierstrassDivision [IsLocalRing A] (f g q : A⟦X⟧) (r : A[X]) : Prop :=
  f.IsWeierstrassDivisionAt g q r (IsLocalRing.maximalIdeal A)

theorem isWeierstrassDivisionAt_zero (g : A⟦X⟧) (I : Ideal A) :
    IsWeierstrassDivisionAt 0 g 0 0 I := by
  constructor
  · rw [Polynomial.degree_zero]
    exact WithBot.bot_lt_coe _
  · simp

theorem IsWeierstrassDivisionAt.coeff_f_sub_r_mem {f g q : A⟦X⟧} {r : A[X]} {I : Ideal A}
    (H : f.IsWeierstrassDivisionAt g q r I) :
    ∀ i < (g.map (Ideal.Quotient.mk I)).order.toNat, coeff A i (f - r) ∈ I := fun i hi ↦ by
  replace H := H.2
  rw [← sub_eq_iff_eq_add] at H
  rw [H]
  refine coeff_mul_mem_ideal_of_coeff_left_mem_ideal _ _ i (fun j hj ↦ ?_) i le_rfl
  have := coeff_of_lt_order_toNat _ (lt_of_le_of_lt hj hi)
  rwa [coeff_map, ← RingHom.mem_ker, Ideal.mk_ker] at this

section

variable (I : Ideal A)

/-- The data used to construct Weierstrass division. -/
structure WeierstrassDivisionData where
  /-- The natural number `n` which is the order of the image of `g` in `(A / I)⟦X⟧`, such that the
  `n`-th coefficient of `g` in `A` is a unit. -/
  n : ℕ
  /-- The power series `g` which is the divisor of Weierstrass division. -/
  g : A⟦X⟧
  /-- The power series `f` which is the dividend of Weierstrass division. -/
  f : A⟦X⟧
  coeff_g_of_lt : ∀ i < n, coeff A i g ∈ I
  isUnit_coeff_g : IsUnit (coeff A n g)

/-- Construct a `WeierstrassDivisionData` from power series `f`, `g` over a local ring such that
the image of `g` in the residue field is not zero. -/
@[simps n g f]
noncomputable def WeierstrassDivisionData.ofMapResidueNeZero [IsLocalRing A]
    (f g : A⟦X⟧) (hg : g.map (IsLocalRing.residue A) ≠ 0) :
    WeierstrassDivisionData (IsLocalRing.maximalIdeal A) where
  n := (g.map (IsLocalRing.residue A)).order.toNat
  g := g
  f := f
  coeff_g_of_lt i hi := by
    simpa only [coeff_map, IsLocalRing.residue_eq_zero_iff] using coeff_of_lt_order_toNat _ hi
  isUnit_coeff_g := by
    rw [← IsLocalRing.not_mem_maximalIdeal]
    have h := coeff_order hg
    contrapose! h
    rwa [coeff_map, IsLocalRing.residue_eq_zero_iff]

variable {I} (S : WeierstrassDivisionData I)

namespace WeierstrassDivisionData

/-- The `g₀` is `∑ i < n, coeff g i * X ^ i`. -/
noncomputable def g₀ := S.g.trunc S.n

/-- The `g₁` is `∑ i, coeff g (i + n) * X ^ i`. -/
noncomputable def g₁ := PowerSeries.mk fun i ↦ coeff A (i + S.n) S.g

theorem g_eq : S.g = (S.g₀ : A⟦X⟧) + X ^ S.n * S.g₁ := by
  rw [S.g.eq_X_pow_mul_shift_add_trunc S.n, g₀, g₁]; ring

theorem coeff_g₀_mem : ∀ i, S.g₀.coeff i ∈ I := fun i ↦ by
  rw [g₀, coeff_trunc]
  split_ifs with h
  · exact S.coeff_g_of_lt i h
  · simp

theorem isUnit_g₁ : IsUnit S.g₁ := by
  simp_rw [g₁, isUnit_iff_constantCoeff, constantCoeff_mk, zero_add, S.isUnit_coeff_g]

/-- The `f₀` is `∑ i < n, coeff f i * X ^ i`. -/
noncomputable def f₀ := S.f.trunc S.n

/-- The `f₁` is `∑ i, coeff f (i + n) * X ^ i`. -/
noncomputable def f₁ := PowerSeries.mk fun i ↦ coeff A (i + S.n) S.f

theorem f_eq : S.f = (S.f₀ : A⟦X⟧) + X ^ S.n * S.f₁ := by
  rw [S.f.eq_X_pow_mul_shift_add_trunc S.n, f₀, f₁]; ring

theorem order_eq (hI : I ≠ ⊤) : (S.g.map (Ideal.Quotient.mk I)).order = S.n := by
  simp_rw [order_eq_nat, coeff_map, S.g_eq, map_add, Polynomial.coeff_coe,
    Ideal.Quotient.eq_zero_iff_mem.2 (S.coeff_g₀_mem _), zero_add]
  refine ⟨?_, fun i hi ↦ ?_⟩
  · nth_rw 1 [← zero_add S.n]
    rw [coeff_X_pow_mul, coeff_zero_eq_constantCoeff]
    contrapose! hI
    rw [Ideal.Quotient.eq_zero_iff_mem] at hI
    exact Ideal.eq_top_of_isUnit_mem _ hI (isUnit_iff_constantCoeff.1 S.isUnit_g₁)
  · rw [Ideal.Quotient.eq_zero_iff_mem]
    refine coeff_mul_mem_ideal_of_coeff_left_mem_ideal _ _ i (fun j hj ↦ ?_) i le_rfl
    simp_rw [coeff_X_pow, if_neg (lt_of_le_of_lt hj hi).ne, zero_mem]

theorem order_toNat_eq (hI : I ≠ ⊤) : (S.g.map (Ideal.Quotient.mk I)).order.toNat = S.n := by
  simpa using congr($(S.order_eq hI).toNat)

/-- The inductively constructed sequence `qₖ` in the proof of Weierstrass division. -/
noncomputable def seq (S : WeierstrassDivisionData I) : ℕ → A⟦X⟧
  | 0 => 0
  | k + 1 =>
    S.seq k + (PowerSeries.mk fun i ↦ coeff A (i + S.n) (S.f - S.g * S.seq k)) * S.isUnit_g₁.unit⁻¹

theorem coeff_seq_mem (k : ℕ) : ∀ i ≥ S.n, coeff A i (S.f - S.g * S.seq k) ∈ I ^ k := by
  induction k with
  | zero => simp
  | succ k hq =>
    rw [seq]
    set q := S.seq k
    set s := S.f - S.g * q
    have hs := s.eq_X_pow_mul_shift_add_trunc S.n
    set s₀ := s.trunc S.n
    set s₁ := PowerSeries.mk fun i ↦ coeff A (i + S.n) s
    set q' := q + s₁ * S.isUnit_g₁.unit⁻¹
    have key : S.f - S.g * q' = (s₀ : A⟦X⟧) - (S.g₀ : A⟦X⟧) * s₁ * S.isUnit_g₁.unit⁻¹ := by
      trans s + S.g * (q - q')
      · simp_rw [s]; ring
      simp_rw [q']
      rw [sub_add_cancel_left, mul_neg, ← mul_assoc, mul_right_comm, S.g_eq, add_mul, mul_assoc,
        IsUnit.mul_val_inv, hs]
      ring
    intro i hi
    rw [key, map_sub, Polynomial.coeff_coe, coeff_trunc, if_neg hi.not_lt, zero_sub, neg_mem_iff,
      pow_succ']
    refine coeff_mul_mem_ideal_of_coeff_left_mem_ideal' _ _ (fun i ↦ ?_) i
    refine coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal' _ _
      (by simp [S.coeff_g₀_mem]) (fun i ↦ ?_) i
    rw [coeff_mk]
    exact hq (i + S.n) (by simp)

theorem coeff_seq_succ_sub_seq_mem (k : ℕ) : ∀ i, coeff A i (S.seq (k + 1) - S.seq k) ∈ I ^ k := by
  simp_rw [seq, add_sub_cancel_left]
  refine coeff_mul_mem_ideal_of_coeff_left_mem_ideal' _ _ fun i ↦ ?_
  rw [coeff_mk]
  exact S.coeff_seq_mem k (i + S.n) (by simp)

@[simp]
theorem seq_zero : S.seq 0 = 0 := rfl

theorem seq_one : S.seq 1 = S.f₁ * S.isUnit_g₁.unit⁻¹ := by
  simp_rw [seq, mul_zero, zero_add, sub_zero, f₁]

/-- The (bundled version of) coefficient of the limit `q` of the
inductively constructed sequence `qₖ` in the proof of Weierstrass division. -/
noncomputable def divCoeff [IsPrecomplete I A] (i : ℕ) :=
  Classical.indefiniteDescription _ <| IsPrecomplete.prec' (I := I)
    (fun k ↦ coeff A i (S.seq k)) fun {m} {n} hn ↦ by
      induction n, hn using Nat.le_induction with
      | base => rfl
      | succ n hn ih =>
        refine ih.trans (SModEq.symm ?_)
        simp_rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← map_sub]
        exact Ideal.pow_le_pow_right hn (S.coeff_seq_succ_sub_seq_mem n i)

/-- The limit `q` of the
inductively constructed sequence `qₖ` in the proof of Weierstrass division. -/
noncomputable def div [IsPrecomplete I A] : A⟦X⟧ := PowerSeries.mk fun i ↦ (S.divCoeff i).1

theorem coeff_div [IsPrecomplete I A] : ∀ i, coeff A i S.div = (S.divCoeff i).1 := by
  simp [div]

theorem coeff_div_sub_seq_mem [IsPrecomplete I A] (k : ℕ) :
    ∀ i, coeff A i (S.div - (S.seq k)) ∈ I ^ k := fun i ↦ by
  rw [map_sub, coeff_div]
  simpa only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] using ((S.divCoeff i).2 k).symm

/-- The remainder `r` in the proof of Weierstrass division. -/
noncomputable def mod [IsPrecomplete I A] : A[X] := (S.f - S.g * S.div).trunc S.n

theorem isWeierstrassDivisionAt_div_mod [IsAdicComplete I A] :
    S.f.IsWeierstrassDivisionAt S.g S.div S.mod I := by
  rcases eq_or_ne I ⊤ with rfl | hI
  · have := ‹IsAdicComplete ⊤ A›.toIsHausdorff.subsingleton
    rw [Subsingleton.elim S.f 0, Subsingleton.elim S.div 0, Subsingleton.elim S.mod 0]
    exact S.g.isWeierstrassDivisionAt_zero _
  constructor
  · rw [S.order_toNat_eq hI]
    exact degree_trunc_lt _ _
  · rw [mod, add_comm, ← sub_eq_iff_eq_add]
    ext i
    by_cases hi : i < S.n
    · simp [coeff_trunc, hi]
    rw [Polynomial.coeff_coe, coeff_trunc, if_neg hi]
    refine IsHausdorff.haus' (I := I) _ fun k ↦ ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, show S.f - S.g * S.div =
      S.f - S.g * (S.seq k) - S.g * (S.div - (S.seq k)) by ring, map_sub]
    exact Ideal.sub_mem _ (S.coeff_seq_mem k _ (not_lt.1 hi)) <|
      coeff_mul_mem_ideal_of_coeff_right_mem_ideal' _ _ (S.coeff_div_sub_seq_mem k) i

/-- If `g * q = r` for some power series `q` and some polynomial `r` whose degree is `< n`,
then `q` and `r` are all zero. This implies the uniqueness of Weierstrass division. -/
theorem eq_zero_of_mul_eq [IsHausdorff I A]
    {q : A⟦X⟧} {r : A[X]} (hdeg : r.degree < S.n) (heq : S.g * q = r) : q = 0 ∧ r = 0 := by
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
    rw [S.g_eq] at heq
    have h1 : ∀ i, coeff A i r ∈ I ^ (k + 1) := fun i ↦ by
      rcases lt_or_le i S.n with hi | hi
      · rw [← heq, pow_succ']
        refine coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal _ _ i (fun j hj ↦ ?_)
          (fun j _ ↦ ih j) i le_rfl
        rw [map_add, Polynomial.coeff_coe]
        refine Ideal.add_mem _ (S.coeff_g₀_mem _) ?_
        simp_rw [coeff_X_pow_mul', if_neg (lt_of_le_of_lt hj hi).not_le, zero_mem]
      simp_rw [Polynomial.coeff_coe,
        Polynomial.coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hdeg (by simpa)), zero_mem]
    rw [add_mul, add_comm, ← eq_sub_iff_add_eq] at heq
    replace heq := congr($heq * S.isUnit_g₁.unit⁻¹)
    rw [mul_right_comm, mul_assoc _ S.g₁, IsUnit.mul_val_inv, mul_one] at heq
    intro i
    rw [← coeff_X_pow_mul _ S.n i, heq]
    refine coeff_mul_mem_ideal_of_coeff_left_mem_ideal' _ _ (fun i ↦ ?_) _
    rw [map_sub]
    refine Ideal.sub_mem _ (h1 _) ?_
    rw [pow_succ']
    refine coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal' _ _ (fun i ↦ ?_) ih _
    simp_rw [Polynomial.coeff_coe, S.coeff_g₀_mem]

/-- If `g * q + r = g * q' + r'` for some power series `q`, `q'` and some polynomials `r`, `r'`
whose degrees are `< n`, then `q = q'` and `r = r'` are all zero.
This implies the uniqueness of Weierstrass division. -/
theorem eq_of_mul_add_eq_mul_add [IsHausdorff I A] {q q' : A⟦X⟧} {r r' : A[X]} (hr : r.degree < S.n)
    (hr' : r'.degree < S.n) (heq : S.g * q + r = S.g * q' + r') : q = q' ∧ r = r' := by
  replace heq : S.g * (q - q') = ↑(r' - r) := by
    rw [← eq_sub_iff_add_eq] at heq
    rw [Polynomial.coe_sub, mul_sub, heq]
    ring
  have h := S.eq_zero_of_mul_eq (lt_of_le_of_lt (r'.degree_sub_le r) (max_lt hr' hr)) heq
  simp_rw [sub_eq_zero] at h
  exact ⟨h.1, h.2.symm⟩

end WeierstrassDivisionData

end

/-- **Weierstrass division** ([washington_cyclotomic], Proposition 7.2): let `f`, `g` be
power series over a complete local ring, such that
the image of `g` in the residue field is not zero. Let `n` be the order of the image of `g` in the
residue field. Then there exists a power series `q` and a polynomial `r` of degree `< n`, such that
`f = g * q + r`. -/
theorem exists_isWeierstrassDivision [IsLocalRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (f g : A⟦X⟧) (hg : g.map (IsLocalRing.residue A) ≠ 0) : ∃ q r, f.IsWeierstrassDivision g q r :=
  ⟨_, _, (WeierstrassDivisionData.ofMapResidueNeZero f g hg).isWeierstrassDivisionAt_div_mod⟩

-- Unfortunately there is no Unicode subscript `w`.

/-- The `q` in Werierstrass division, denoted by `f /ʷ g`. Note that when the image of `g` in the
residue field is zero, this is defined to be zero. -/
noncomputable def weierstrassDiv [IsLocalRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (f g : A⟦X⟧) : A⟦X⟧ :=
  open scoped Classical in
  if hg : g.map (IsLocalRing.residue A) ≠ 0 then
    (f.exists_isWeierstrassDivision g hg).choose
  else
    0

/-- The `r` in Werierstrass division, denoted by `f %ʷ g`. Note that when the image of `g` in the
residue field is zero, this is defined to be zero. -/
noncomputable def weierstrassMod [IsLocalRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (f g : A⟦X⟧) : A[X] :=
  open scoped Classical in
  if hg : g.map (IsLocalRing.residue A) ≠ 0 then
    (f.exists_isWeierstrassDivision g hg).choose_spec.choose
  else
    0

@[inherit_doc]
infixl:70 " /ʷ " => weierstrassDiv

@[inherit_doc]
infixl:70 " %ʷ " => weierstrassMod

@[simp]
theorem weierstrassDiv_zero_right [IsLocalRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (f : A⟦X⟧) : f /ʷ 0 = 0 := by
  rw [weierstrassDiv, dif_neg (by simp)]

@[simp]
theorem weierstrassMod_zero_right [IsLocalRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (f : A⟦X⟧) : f %ʷ 0 = 0 := by
  rw [weierstrassMod, dif_neg (by simp)]

theorem degree_weierstrassMod_lt [IsLocalRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (f g : A⟦X⟧) : (f %ʷ g).degree < (g.map (IsLocalRing.residue A)).order.toNat := by
  rw [weierstrassMod]
  split_ifs with hg
  · exact (f.exists_isWeierstrassDivision g hg).choose_spec.choose_spec.1
  · nontriviality A
    rw [Polynomial.degree_zero]
    exact WithBot.bot_lt_coe _

theorem isWeierstrassDivision_weierstrassDiv_weierstrassMod
    [IsLocalRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A] (f g : A⟦X⟧)
    (hg : g.map (IsLocalRing.residue A) ≠ 0) : f.IsWeierstrassDivision g (f /ʷ g) (f %ʷ g) := by
  simp_rw [weierstrassDiv, weierstrassMod, dif_pos hg]
  exact (f.exists_isWeierstrassDivision g hg).choose_spec.choose_spec

theorem eq_mul_weierstrassDiv_add_weierstrassMod
    [IsLocalRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A] (f g : A⟦X⟧)
    (hg : g.map (IsLocalRing.residue A) ≠ 0) : f = g * (f /ʷ g) + (f %ʷ g) := by
  simp_rw [weierstrassDiv, weierstrassMod, dif_pos hg]
  exact (f.exists_isWeierstrassDivision g hg).choose_spec.choose_spec.2

/-- The `q` and `r` in the Weierstrass division for `0` is equal to `0`. -/
theorem eq_zero_of_weierstrass_division [IsLocalRing A] [IsHausdorff (IsLocalRing.maximalIdeal A) A]
    (g : A⟦X⟧) (hg : g.map (IsLocalRing.residue A) ≠ 0) {q : A⟦X⟧} {r : A[X]}
    (hr : r.degree < (g.map (IsLocalRing.residue A)).order.toNat)
    (heq : g * q = r) : q = 0 ∧ r = 0 :=
  (WeierstrassDivisionData.ofMapResidueNeZero 0 g hg).eq_zero_of_mul_eq hr heq

/-- The `q` and `r` in the Weierstrass division is unique. -/
theorem eq_of_weierstrass_division [IsLocalRing A] [IsHausdorff (IsLocalRing.maximalIdeal A) A]
    (g : A⟦X⟧) (hg : g.map (IsLocalRing.residue A) ≠ 0) {q q' : A⟦X⟧} {r r' : A[X]}
    (hr : r.degree < (g.map (IsLocalRing.residue A)).order.toNat)
    (hr' : r'.degree < (g.map (IsLocalRing.residue A)).order.toNat)
    (heq : g * q + r = g * q' + r') : q = q' ∧ r = r' :=
  (WeierstrassDivisionData.ofMapResidueNeZero 0 g hg).eq_of_mul_add_eq_mul_add hr hr' heq

/-- The `q` and `r` in the Weierstrass division is unique. -/
theorem IsWeierstrassDivision.elim [IsLocalRing A] [IsHausdorff (IsLocalRing.maximalIdeal A) A]
    {f g : A⟦X⟧} (hg : g.map (IsLocalRing.residue A) ≠ 0) {q q' : A⟦X⟧} {r r' : A[X]}
    (H : f.IsWeierstrassDivision g q r) (H2 : f.IsWeierstrassDivision g q' r') : q = q' ∧ r = r' :=
  g.eq_of_weierstrass_division hg H.1 H2.1 (H.2.symm.trans H2.2)

/-- The `q` and `r` in the Weierstrass division for `0` is equal to `0`. -/
theorem IsWeierstrassDivision.eq_zero [IsLocalRing A] [IsHausdorff (IsLocalRing.maximalIdeal A) A]
    {g : A⟦X⟧} (hg : g.map (IsLocalRing.residue A) ≠ 0) {q : A⟦X⟧} {r : A[X]}
    (H : IsWeierstrassDivision 0 g q r) : q = 0 ∧ r = 0 :=
  H.elim hg (g.isWeierstrassDivisionAt_zero _)

/-- The `q` and `r` in the Weierstrass division is equal to `f /ʷ g` and `f %ʷ g`. -/
theorem IsWeierstrassDivision.eq_weierstrassDiv_weierstrassMod
    [IsLocalRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {f g : A⟦X⟧} (hg : g.map (IsLocalRing.residue A) ≠ 0) {q : A⟦X⟧} {r : A[X]}
    (H : f.IsWeierstrassDivision g q r) : q = f /ʷ g ∧ r = f %ʷ g :=
  H.elim hg (f.isWeierstrassDivision_weierstrassDiv_weierstrassMod g hg)

@[simp]
theorem weierstrassDiv_zero_left [IsLocalRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (g : A⟦X⟧) : 0 /ʷ g = 0 := by
  by_cases hg : g.map (IsLocalRing.residue A) ≠ 0
  · exact ((isWeierstrassDivision_weierstrassDiv_weierstrassMod 0 g hg).eq_zero hg).1
  rw [weierstrassDiv, dif_neg hg]

@[simp]
theorem weierstrassMod_zero_left [IsLocalRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (g : A⟦X⟧) : 0 %ʷ g = 0 := by
  by_cases hg : g.map (IsLocalRing.residue A) ≠ 0
  · exact ((isWeierstrassDivision_weierstrassDiv_weierstrassMod 0 g hg).eq_zero hg).2
  rw [weierstrassMod, dif_neg hg]

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

namespace IsWeierstrassFactorizationAt

variable {g : A⟦X⟧} {f : A[X]} {h : A⟦X⟧} {I : Ideal A} (H : g.IsWeierstrassFactorizationAt f h I)
include H

theorem map_ne_zero_of_ne_top (hI : I ≠ ⊤) : g.map (Ideal.Quotient.mk I) ≠ 0 := by
  rcases subsingleton_or_nontrivial (A ⧸ I) with h | _
  · apply (Submodule.Quotient.subsingleton_iff _).1 at h
    exact False.elim <| hI <| by ext; simp [h]
  rw [congr(map (Ideal.Quotient.mk I) $(H.eq_mul)), map_mul, ← Polynomial.polynomial_map_coe, ne_eq,
    (H.isUnit.map _).mul_left_eq_zero]
  exact_mod_cast f.map_monic_ne_zero (f := Ideal.Quotient.mk I) H.isDistinguishedAt.monic

theorem degree_eq_order_map_of_ne_top (hI : I ≠ ⊤) :
    f.degree = (g.map (Ideal.Quotient.mk I)).order := by
  refine H.isDistinguishedAt.degree_eq_order_map g h ?_ H.eq_mul
  contrapose! hI
  exact Ideal.eq_top_of_isUnit_mem _ hI (isUnit_iff_constantCoeff.1 H.isUnit)

theorem natDegree_eq_toNat_order_map_of_ne_top (hI : I ≠ ⊤) :
    f.natDegree = (g.map (Ideal.Quotient.mk I)).order.toNat := by
  rw [Polynomial.natDegree, H.degree_eq_order_map_of_ne_top hI]
  rfl

end IsWeierstrassFactorizationAt

variable [IsLocalRing A]

namespace IsWeierstrassFactorization

variable {g : A⟦X⟧} {f : A[X]} {h : A⟦X⟧} (H : g.IsWeierstrassFactorization f h)
include H

theorem map_ne_zero : g.map (IsLocalRing.residue A) ≠ 0 :=
  H.map_ne_zero_of_ne_top (Ideal.IsMaximal.ne_top inferInstance)

theorem degree_eq_order_map : f.degree = (g.map (IsLocalRing.residue A)).order :=
  H.degree_eq_order_map_of_ne_top (Ideal.IsMaximal.ne_top inferInstance)

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
  rw [coeff_mul, ← Finset.sum_subset (s₁ := {(n, 0)}) (by simp) (fun p hp hnmem ↦ by
    have hp1 : p.1 < n := (Finset.antidiagonal.fst_le hp).lt_of_ne <| by
      contrapose! hnmem
      rwa [Finset.mem_singleton, Finset.antidiagonal_congr hp (by simp)]
    rw [coeff_of_lt_order p.1 (by
      rwa [← ENat.lt_lift_iff (h := order_finite_iff_ne_zero.2 hg),
        ENat.lift_eq_toNat]), zero_mul]), Finset.sum_singleton,
    coeff_map, coeff_map, coeff_zero_eq_constantCoeff, mul_comm, Eq.comm] at H2
  rw [isUnit_iff_constantCoeff, ← isUnit_map_iff (IsLocalRing.residue A)]
  exact isUnit_of_mul_eq_one _ _ H2

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
    have := H.coeff_f_sub_r_mem i hi
    rwa [map_sub, coeff_X_pow, if_neg hi.ne, zero_sub, neg_mem_iff, Polynomial.coeff_coe] at this
  · have := congr($(H.2) * ↑(H.isUnit_of_map_ne_zero hg).unit⁻¹)
    rw [add_mul, mul_assoc, IsUnit.mul_val_inv, mul_one, ← sub_eq_iff_eq_add] at this
    simp_rw [← this, f, Polynomial.coe_sub, Polynomial.coe_pow, Polynomial.coe_X, sub_mul]

theorem IsWeierstrassFactorization.isWeierstrassDivision
    {g : A⟦X⟧} {f : A[X]} {h : A⟦X⟧} (H : g.IsWeierstrassFactorization f h) :
    (X ^ (g.map (IsLocalRing.residue A)).order.toNat).IsWeierstrassDivision g ↑H.isUnit.unit⁻¹
      (Polynomial.X ^ (g.map (IsLocalRing.residue A)).order.toNat - f) := by
  set n := (g.map (IsLocalRing.residue A)).order.toNat
  constructor
  · change (Polynomial.X ^ n - f).degree < ↑n
    refine (Polynomial.degree_sub_lt ?_ (Polynomial.monic_X_pow n).ne_zero ?_).trans_eq (by simp)
    · simp_rw [H.degree_eq_order_map, Polynomial.degree_X_pow, n,
        ← ENat.lift_eq_toNat (order_finite_iff_ne_zero.2 H.map_ne_zero)]
      exact ENat.coe_lift _ _
    · rw [(Polynomial.monic_X_pow n).leadingCoeff, H.isDistinguishedAt.monic.leadingCoeff]
  · simp_rw [H.eq_mul, mul_assoc, IsUnit.mul_val_inv, mul_one, Polynomial.coe_sub,
      Polynomial.coe_pow, Polynomial.coe_X, add_sub_cancel]

section

variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A] (g : A⟦X⟧)
  (hg : g.map (IsLocalRing.residue A) ≠ 0)
include hg

/-- **Weierstrass preparation theorem** ([washington_cyclotomic], Theorem 7.3):
let `g` be a power series over a complete local ring,
such that the image of `g` in the residue field is not zero. Then there exists a distinguished
polynomial `f` and a power series `h` which is a unit, such that `g = f * h`. -/
theorem exists_isWeierstrassFactorization : ∃ f h, g.IsWeierstrassFactorization f h := by
  obtain ⟨q, r, H⟩ :=
    (X ^ (g.map (IsLocalRing.residue A)).order.toNat).exists_isWeierstrassDivision g hg
  exact ⟨_, _, H.isWeierstrassFactorization hg⟩

/-- The `f` in Werierstrass preparation theorem. -/
noncomputable def weierstrassDistinguished : A[X] :=
  (g.exists_isWeierstrassFactorization hg).choose

/-- The `h` in Werierstrass preparation theorem. -/
noncomputable def weierstrassUnit : A⟦X⟧ :=
  (g.exists_isWeierstrassFactorization hg).choose_spec.choose

theorem isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit :
    g.IsWeierstrassFactorization (g.weierstrassDistinguished hg) (g.weierstrassUnit hg) :=
  (g.exists_isWeierstrassFactorization hg).choose_spec.choose_spec

theorem isDistinguishedAt_weierstrassDistinguished :
    (g.weierstrassDistinguished hg).IsDistinguishedAt (IsLocalRing.maximalIdeal A) :=
  (g.exists_isWeierstrassFactorization hg).choose_spec.choose_spec.isDistinguishedAt

theorem isUnit_weierstrassUnit :
    IsUnit (g.weierstrassUnit hg) :=
  (g.exists_isWeierstrassFactorization hg).choose_spec.choose_spec.isUnit

theorem eq_weierstrassDistinguished_mul_weierstrassUnit :
    g = g.weierstrassDistinguished hg * g.weierstrassUnit hg :=
  (g.exists_isWeierstrassFactorization hg).choose_spec.choose_spec.eq_mul

end

/-- The `f` and `h` in Werierstrass preparation theorem is unique. -/
theorem IsWeierstrassFactorization.elim [IsHausdorff (IsLocalRing.maximalIdeal A) A]
    {g : A⟦X⟧} {f f' : A[X]} {h h' : A⟦X⟧} (H : g.IsWeierstrassFactorization f h)
    (H2 : g.IsWeierstrassFactorization f' h') : f = f' ∧ h = h' := by
  obtain ⟨h1, h2⟩ := H.isWeierstrassDivision.elim H.map_ne_zero H2.isWeierstrassDivision
  rw [← Units.ext_iff, inv_inj, Units.ext_iff] at h1
  exact ⟨by simpa using h2, h1⟩

/-- The `f` and `h` in Werierstrass preparation theorem is unique. -/
theorem IsWeierstrassFactorization.eq_weierstrassDistinguished_weierstrassUnit
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {g : A⟦X⟧} {f : A[X]} {h : A⟦X⟧} (H : g.IsWeierstrassFactorization f h)
    (hg : g.map (IsLocalRing.residue A) ≠ 0) :
    f = g.weierstrassDistinguished hg ∧ h = g.weierstrassUnit hg :=
  H.elim (g.isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit hg)

end PowerSeries
