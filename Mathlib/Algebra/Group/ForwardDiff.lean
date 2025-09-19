/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Caflisch, David Loeffler, Yu Shao, Weijie Jiang, BeiBei Xiong
-/
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Abel
import Mathlib.Algebra.GroupWithZero.Action.Pi
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Forward difference operators and Newton series

We define the forward difference operator, sending `f` to the function `x ↦ f (x + h) - f x` for
a given `h` (for any additive semigroup, taking values in an abelian group). The notation `Δ_[h]` is
defined for this operator, scoped in namespace `fwdDiff`.

We prove two key formulae about this operator:

* `shift_eq_sum_fwdDiff_iter`: the **Gregory-Newton formula**, expressing `f (y + n • h)` as a
  linear combination of forward differences of `f` at `y`, for `n ∈ ℕ`;
* `fwdDiff_iter_eq_sum_shift`: formula expressing the `n`-th forward difference of `f` at `y` as
  a linear combination of `f (y + k • h)` for `0 ≤ k ≤ n`.

We also prove some auxiliary results about iterated forward differences of the function
`n ↦ n.choose k`.
-/

open Finset Nat Function Polynomial

variable {M G : Type*} [AddCommMonoid M] [AddCommGroup G] (h : M)

/--
Forward difference operator, `fwdDiff h f n = f (n + h) - f n`. The notation `Δ_[h]` for this
operator is available in the `fwdDiff` namespace.
-/
def fwdDiff (h : M) (f : M → G) : M → G := fun n ↦ f (n + h) - f n

@[inherit_doc] scoped[fwdDiff] notation "Δ_[" h "]" => fwdDiff h

open fwdDiff

@[simp] lemma fwdDiff_add (h : M) (f g : M → G) :
    Δ_[h] (f + g) = Δ_[h] f + Δ_[h] g :=
  add_sub_add_comm ..

@[simp] lemma fwdDiff_const (g : G) : Δ_[h] (fun _ ↦ g : M → G) = fun _ ↦ 0 :=
  funext fun _ ↦ sub_self g

section smul

lemma fwdDiff_smul {R : Type} [Ring R] [Module R G] (f : M → R) (g : M → G) :
    Δ_[h] (f • g) = Δ_[h] f • g + f • Δ_[h] g + Δ_[h] f • Δ_[h] g := by
  ext y
  simp only [fwdDiff, Pi.smul_apply', Pi.add_apply, smul_sub, sub_smul]
  abel

-- Note `fwdDiff_const_smul` is more general than `fwdDiff_smul` since it allows `R` to be a
-- semiring, rather than a ring; in particular `R = ℕ` is allowed.
@[simp] lemma fwdDiff_const_smul {R : Type*} [Monoid R] [DistribMulAction R G] (r : R) (f : M → G) :
    Δ_[h] (r • f) = r • Δ_[h] f :=
  funext fun _ ↦ (smul_sub ..).symm

@[simp] lemma fwdDiff_smul_const {R : Type} [Ring R] [Module R G] (f : M → R) (g : G) :
    Δ_[h] (fun y ↦ f y • g) = Δ_[h] f • fun _ ↦ g := by
  ext y
  simp only [fwdDiff, Pi.smul_apply', sub_smul]

end smul

namespace fwdDiff_aux
/-!
## Forward-difference and shift operators as linear endomorphisms

This section contains versions of the forward-difference operator and the shift operator bundled as
`ℤ`-linear endomorphisms. These are useful for certain proofs; but they are slightly annoying to
use, as the source and target types of the maps have to be specified each time, and various
coercions need to be un-wound when the operators are applied, so we also provide the un-bundled
version.
-/

variable (M G) in
/-- Linear-endomorphism version of the forward difference operator. -/
@[simps]
def fwdDiffₗ : Module.End ℤ (M → G) where
  toFun := fwdDiff h
  map_add' := fwdDiff_add h
  map_smul' := fwdDiff_const_smul h

lemma coe_fwdDiffₗ : ↑(fwdDiffₗ M G h) = fwdDiff h := rfl

lemma coe_fwdDiffₗ_pow (n : ℕ) : ↑(fwdDiffₗ M G h ^ n) = (fwdDiff h)^[n] := by
  ext; rw [Module.End.pow_apply, coe_fwdDiffₗ]

variable (M G) in
/-- Linear-endomorphism version of the shift-by-1 operator. -/
def shiftₗ : Module.End ℤ (M → G) := fwdDiffₗ M G h + 1

lemma shiftₗ_apply (f : M → G) (y : M) : shiftₗ M G h f y = f (y + h) := by simp [shiftₗ, fwdDiff]

lemma shiftₗ_pow_apply (f : M → G) (k : ℕ) (y : M) : (shiftₗ M G h ^ k) f y = f (y + k • h) := by
  induction k generalizing f with
  | zero => simp
  | succ k IH => simp [pow_add, IH (shiftₗ M G h f), shiftₗ_apply, add_assoc, add_nsmul]

end fwdDiff_aux

open fwdDiff_aux

@[simp] lemma fwdDiff_finset_sum {α : Type*} (s : Finset α) (f : α → M → G) :
    Δ_[h] (∑ k ∈ s, f k) = ∑ k ∈ s, Δ_[h] (f k) :=
  map_sum (fwdDiffₗ M G h) f s

@[simp] lemma fwdDiff_iter_add (f g : M → G) (n : ℕ) :
    Δ_[h]^[n] (f + g) = Δ_[h]^[n] f + Δ_[h]^[n] g := by
  simpa only [coe_fwdDiffₗ_pow] using map_add (fwdDiffₗ M G h ^ n) f g

@[simp] lemma fwdDiff_iter_const_smul {R : Type*} [Monoid R] [DistribMulAction R G]
    (r : R) (f : M → G) (n : ℕ) : Δ_[h]^[n] (r • f) = r • Δ_[h]^[n] f := by
  induction n generalizing f with
  | zero => simp only [iterate_zero, id_eq]
  | succ n IH => simp only [iterate_succ_apply, fwdDiff_const_smul, IH]

@[simp] lemma fwdDiff_iter_finset_sum {α : Type*} (s : Finset α) (f : α → M → G) (n : ℕ) :
    Δ_[h]^[n] (∑ k ∈ s, f k) = ∑ k ∈ s, Δ_[h]^[n] (f k) := by
  simpa only [coe_fwdDiffₗ_pow] using map_sum (fwdDiffₗ M G h ^ n) f s

section newton_formulae

/--
Express the `n`-th forward difference of `f` at `y` in terms of the values `f (y + k)`, for
`0 ≤ k ≤ n`.
-/
theorem fwdDiff_iter_eq_sum_shift (f : M → G) (n : ℕ) (y : M) :
    Δ_[h]^[n] f y = ∑ k ∈ range (n + 1), ((-1 : ℤ) ^ (n - k) * n.choose k) • f (y + k • h) := by
  -- rewrite in terms of `(shiftₗ - 1) ^ n`
  have : fwdDiffₗ M G h = shiftₗ M G h - 1 := by simp only [shiftₗ, add_sub_cancel_right]
  rw [← coe_fwdDiffₗ, this, ← Module.End.pow_apply]
  -- use binomial theorem `Commute.add_pow` to expand this
  have : Commute (shiftₗ M G h) (-1) := (Commute.one_right _).neg_right
  convert congr_fun (LinearMap.congr_fun (this.add_pow n) f) y using 3
  · simp only [sub_eq_add_neg]
  · rw [LinearMap.sum_apply, sum_apply]
    congr 1 with k
    have : ((-1) ^ (n - k) * n.choose k : Module.End ℤ (M → G))
              = ↑((-1) ^ (n - k) * n.choose k : ℤ) := by norm_cast
    rw [mul_assoc, Module.End.mul_apply, this, Module.End.intCast_apply, LinearMap.map_smul,
      Pi.smul_apply, shiftₗ_pow_apply]

lemma fwdDiff_iter_comp_add (f : M → G) (m : M) (n : ℕ) (y : M) :
    Δ_[h]^[n] (fun r ↦ f (r + m)) y = (Δ_[h]^[n] f) (y + m) := by
  simp [fwdDiff_iter_eq_sum_shift, add_right_comm]

lemma fwdDiff_comp_add (f : M → G) (m : M) (y : M) :
    Δ_[h] (fun r ↦ f (r + m)) y = (Δ_[h] f) (y + m) :=
  fwdDiff_iter_comp_add h f m 1 y

/--
**Gregory-Newton formula** expressing `f (y + n • h)` in terms of the iterated forward differences
of `f` at `y`.
-/
theorem shift_eq_sum_fwdDiff_iter (f : M → G) (n : ℕ) (y : M) :
    f (y + n • h) = ∑ k ∈ range (n + 1), n.choose k • Δ_[h]^[k] f y := by
  convert congr_fun (LinearMap.congr_fun
      ((Commute.one_right (fwdDiffₗ M G h)).add_pow n) f) y using 1
  · rw [← shiftₗ_pow_apply h f, shiftₗ]
  · simp [Module.End.pow_apply, coe_fwdDiffₗ]

end newton_formulae

section choose

lemma fwdDiff_choose (j : ℕ) : Δ_[1] (fun x ↦ x.choose (j + 1) : ℕ → ℤ) = fun x ↦ x.choose j := by
  ext n
  simp only [fwdDiff, choose_succ_succ' n j, cast_add, add_sub_cancel_right]

lemma fwdDiff_iter_choose (j k : ℕ) :
    Δ_[1]^[k] (fun x ↦ x.choose (k + j) : ℕ → ℤ) = fun x ↦ x.choose j := by
  induction k generalizing j with
  | zero => simp only [zero_add, iterate_zero, id_eq]
  | succ k IH =>
    simp only [iterate_succ_apply', add_assoc, add_comm 1 j, IH, fwdDiff_choose]

lemma fwdDiff_iter_choose_zero (m n : ℕ) :
    Δ_[1]^[n] (fun x ↦ x.choose m : ℕ → ℤ) 0 = if n = m then 1 else 0 := by
  rcases lt_trichotomy m n with hmn | rfl | hnm
  · rcases Nat.exists_eq_add_of_lt hmn with ⟨k, rfl⟩
    simp_rw [hmn.ne', if_false, (by ring : m + k + 1 = k + 1 + m), iterate_add_apply,
      add_zero m ▸ fwdDiff_iter_choose 0 m, choose_zero_right, iterate_one, cast_one, fwdDiff_const,
      fwdDiff_iter_eq_sum_shift, smul_zero, sum_const_zero]
  · simp only [if_true, add_zero m ▸ fwdDiff_iter_choose 0 m, choose_zero_right, cast_one]
  · rcases Nat.exists_eq_add_of_lt hnm with ⟨k, rfl⟩
    simp_rw [hnm.ne, if_false, add_assoc n k 1, fwdDiff_iter_choose, choose_zero_succ, cast_zero]

end choose

lemma fwdDiff_addChar_eq {M R : Type*} [AddCommMonoid M] [Ring R]
    (φ : AddChar M R) (x h : M) (n : ℕ) : Δ_[h]^[n] φ x = (φ h - 1) ^ n * φ x := by
  induction n generalizing x with
  | zero => simp
  | succ n IH =>
    simp only [pow_succ, iterate_succ_apply', fwdDiff, IH, ← mul_sub, mul_assoc]
    rw [sub_mul, ← AddChar.map_add_eq_mul, add_comm h x, one_mul]

/-!
## Forward differences of polynomials

We prove formulae about the forward difference operator applied to polynomials:

* `fwdDiff_iter_pow_eq_zero_of_lt` :
  The `n`-th forward difference of the function `x ↦ x^j` is zero if `j < n`;
* `fwdDiff_iter_eq_factorial` :
  The `n`-th forward difference of the function `x ↦ x^n` is the constant function `n!`;
* `fwdDiff_iter_sum_mul_pow_eq_zero` :
  The `n`-th forward difference of a polynomial of degree `< n` is zero (formulated using explicit
    sums over `range n`.
-/

variable {R : Type*} [CommRing R]

/--
The `n`-th forward difference of the function `x ↦ x^j` is zero if `j < n`.
-/
theorem fwdDiff_iter_pow_eq_zero_of_lt {j n : ℕ} (h : j < n) :
    Δ_[1]^[n] (fun (r : R) ↦ r ^ j) = 0 := by
  induction n generalizing j with
  | zero => aesop
  | succ n ih =>
    have : (Δ_[1] fun (r : R) ↦ r ^ j) = ∑ i ∈ range j, j.choose i • fun r ↦ r ^ i := by
      ext x
      simp [nsmul_eq_mul, fwdDiff, add_pow, sum_range_succ, mul_comm]
    rw [iterate_succ_apply, this, fwdDiff_iter_finset_sum]
    exact sum_eq_zero fun i hi ↦ by
      rw [fwdDiff_iter_const_smul, ih (by have := mem_range.1 hi; omega), nsmul_zero]

/--
The `n`-th forward difference of `x ↦ x^n` is the constant function `n!`.
-/
theorem fwdDiff_iter_eq_factorial {n : ℕ} :
    Δ_[1]^[n] (fun (r : R) ↦ r ^ n) = n ! := by
  induction n with
  | zero => aesop
  | succ n IH =>
    have : (Δ_[1] fun (r : R) ↦ r ^ (n + 1)) =
      ∑ i ∈ range (n + 1), (n + 1).choose i • fun r ↦ r ^ i := by
      ext x
      simp [nsmul_eq_mul, fwdDiff, add_pow, sum_range_succ, mul_comm]
    simp_rw [iterate_succ_apply, this, fwdDiff_iter_finset_sum, fwdDiff_iter_const_smul,
       sum_range_succ]
    simpa [IH, factorial_succ] using sum_eq_zero fun i hi ↦ by
      rw [fwdDiff_iter_pow_eq_zero_of_lt (by have := mem_range.1 hi; omega), mul_zero]

theorem Polynomial.fwdDiff_iter_degree_eq_factorial (P : R[X]) :
    Δ_[1]^[P.natDegree] P.eval = P.leadingCoeff • P.natDegree ! := funext fun x ↦ by
  simp_rw [P.eval_eq_sum_range, ← sum_apply _ _ (fun i x ↦ P.coeff i * x ^ i),
    fwdDiff_iter_finset_sum, ← smul_eq_mul, ← Pi.smul_def, fwdDiff_iter_const_smul, Pi.smul_apply]
  rw [sum_apply, sum_range_succ, sum_eq_zero (fun i hi ↦ ?_), zero_add,
    fwdDiff_iter_eq_factorial, leadingCoeff, Pi.smul_apply]
  rw [fwdDiff_iter_pow_eq_zero_of_lt (mem_range.mp hi), smul_zero, Pi.zero_apply]

theorem Polynomial.fwdDiff_iter_eq_zero_of_degree_lt {P : R[X]} {n : ℕ} (hP : P.natDegree < n) :
    Δ_[1]^[n] P.eval = 0 := funext fun x ↦ by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hP
  rw [add_assoc, add_comm, Function.iterate_add_apply, Function.iterate_succ_apply,
    P.fwdDiff_iter_degree_eq_factorial, Pi.smul_def]
  simp [fwdDiff_iter_eq_sum_shift]

theorem Polynomial.fwdDiff_iter_degree_add_one_eq_zero (P : R[X]) :
    Δ_[1]^[P.natDegree + 1] P.eval = 0 := by
  have hP : P.natDegree < P.natDegree + 1 := Nat.lt_succ_self P.natDegree
  exact Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hP

/--
The `n`-th forward difference of a polynomial of degree `< n` is zero (formulated using explicit
sums over `range n`.
-/
theorem fwdDiff_iter_sum_mul_pow_eq_zero {n : ℕ} (P : ℕ → R) :
    Δ_[1]^[n] (fun r : R ↦ ∑ k ∈ range n, P k * r ^ k) = 0 := by
  simp_rw [← sum_apply _ _ (fun i x ↦ P i * x ^ i), fwdDiff_iter_finset_sum, sum_fn, ← smul_eq_mul,
    ← Pi.smul_def, fwdDiff_iter_const_smul, ← sum_fn]
  exact sum_eq_zero fun i hi ↦ smul_eq_zero_of_right _ <| fwdDiff_iter_pow_eq_zero_of_lt
    <| mem_range.mp hi
