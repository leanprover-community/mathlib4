/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Caflisch, David Loeffler, Yu Shao, Weijie Jiang
-/
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Abel
import Mathlib.Algebra.Polynomial.Basic

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

open Finset Nat Function

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
  induction' k with k IH generalizing f
  · simp
  · simp [pow_add, IH (shiftₗ M G h f), shiftₗ_apply, add_assoc, add_nsmul]

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
  induction' n with n IH generalizing f
  · simp only [iterate_zero, id_eq]
  · simp only [iterate_succ_apply, fwdDiff_const_smul, IH]

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
  induction' k with k IH generalizing j
  · simp only [zero_add, iterate_zero, id_eq]
  · simp only [Function.iterate_succ_apply', add_assoc, add_comm 1 j, IH, fwdDiff_choose]

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
    simp only [pow_succ, Function.iterate_succ_apply', fwdDiff, IH, ← mul_sub, mul_assoc]
    rw [sub_mul, ← AddChar.map_add_eq_mul, add_comm h x, one_mul]


/-
We prove five key formulae about the forward difference operator

* `fwdDiff_iter_pow_lt` :
  The `n`-th forward difference of the function `x ↦ x^j` is zero if `j < n`;
* `fwdDiff_iter_eq_factorial` :
  The `n`-th forward difference of the function `x ↦ x^n` is the constant function `n!`;
* `fwdDiff_iter_succ_sum_eq_zero` :
  The `(n+1)`-th forward difference of a polynomial of degree at most `n` is zero.
* `fwdDiffTab_0th_diag_poly'` :
  **Newton's series** for a polynomial function. This is another definition.
* `sum_of_poly_sequence` :
  A generalization of **Faulhaber's formula**.
-/

open fwdDiff
variable {R : Type*} [CommRing R]

/--
The `n`-th forward difference of the function `x ↦ x^j` is zero if `j < n`.
This is a building block for showing that the `(p+1)`-th difference of a polynomial of
degree `p` is zero.
-/
theorem fwdDiff_iter_pow_lt  {x j n : ℕ} (h : j < n):
  Δ_[1] ^[n] (fun x ↦ x ^ j : ℕ → R) x = (fun _ ↦  0) x := by
  revert j
  induction' n with n IH
  . simp only [not_lt_zero', Function.iterate_zero, id_eq,
      pow_eq_zero_iff', Nat.cast_eq_zero, ne_eq, IsEmpty.forall_iff, implies_true]
  . intro j hj
    rw [Function.iterate_succ, Function.comp_apply, fwdDiff_iter_eq_sum_shift]
    simp only [Int.reduceNeg, smul_eq_mul, mul_one, zsmul_eq_mul, Int.cast_mul,
      Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast]
    simp [fwdDiff_iter_eq_sum_shift] at IH
    conv_lhs=> enter[2]; ext k; enter[2]; rw [fwdDiff, ← Nat.cast_pow,
      ← Nat.cast_pow,← Nat.cast_sub (by apply Nat.pow_le_pow_left; linarith),
      add_pow, Finset.sum_range_succ]
    simp only [one_pow, mul_one, Nat.cast_id,
      tsub_self, pow_zero, Nat.choose_self, Nat.cast_one]
    conv_lhs=> enter[2]; ext k; rw [Nat.add_sub_cancel_right (m := (x + k) ^ j),
      mul_assoc, ← Nat.cast_mul, Finset.mul_sum]
    norm_num
    simp [Finset.mul_sum, Finset.sum_comm, ← mul_assoc, ← mul_assoc, ← Finset.sum_mul]
    apply Finset.sum_eq_zero
    intro k hk
    simp only [Finset.mem_range] at hk
    rw [IH (by linarith)]
    simp

/-- The `n`-th forward difference of `x ↦ x^n` is the constant function `n!`. -/
theorem fwdDiff_iter_eq_factorial {n x : ℕ} :
   Δ_[1] ^[n] (fun x ↦ x ^ n : ℕ → R) x = (fun _ ↦  n.factorial) x := by
  induction' n with n IH
  . simp only [pow_zero, Function.iterate_zero, id_eq, Nat.factorial_zero, Nat.cast_one]
  . simp
    rw [fwdDiff_iter_eq_sum_shift]
    simp only [Int.reduceNeg, smul_eq_mul, mul_one, zsmul_eq_mul,
      Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast]
    simp [fwdDiff_iter_eq_sum_shift] at IH
    conv_lhs=> enter[2]; ext k; enter[2]; rw [fwdDiff, ← Nat.cast_pow,
      ← Nat.cast_pow, ← Nat.cast_sub (by apply Nat.pow_le_pow_left; linarith)]
    conv_lhs=> enter[2];ext k;enter[2,1,1]; rw [add_pow, Finset.sum_range_succ]
    simp only [one_pow, mul_one, Nat.cast_id, tsub_self, pow_zero, Nat.choose_self, Nat.cast_one]
    conv_lhs=> enter[2]; ext k; enter[2, 1]; rw [Nat.add_sub_cancel_right]
    conv_lhs=> enter [2]; ext k; rw [mul_assoc, ← Nat.cast_mul, Finset.mul_sum]
    norm_num
    simp [Finset.mul_sum]
    rw [Finset.sum_comm]
    conv_lhs=> enter[2]; ext i; enter [2]; ext k; rw [← mul_assoc, ← mul_assoc]
    simp [← Finset.sum_mul]
    rw [Finset.sum_range_succ, IH]
    simp only [Nat.choose_succ_self_right, Nat.cast_add, Nat.cast_one, zero_add]
    conv_lhs => enter [2]; norm_cast
    nth_rw 6 [show n = n + 1 - 1 by rw [Nat.add_sub_cancel]]
    rw [mul_comm, Nat.mul_factorial_pred (by linarith)]
    simp only [add_eq_right]
    apply Finset.sum_eq_zero
    intro k hk
    simp only [Finset.mem_range] at hk
    obtain h := fwdDiff_iter_eq_sum_shift (n := n) (y := x) (f := (fun x ↦ x ^ k : ℕ → R)) (h := 1)
    simp only [Int.reduceNeg, smul_eq_mul, mul_one, Nat.cast_add,
      zsmul_eq_mul, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast] at h
    rw [← h, fwdDiff_iter_pow_lt (by linarith), zero_mul]

/--
The `(n+1)`-th forward difference of a polynomial of degree at most `n` is zero.
A polynomial `P(x) = ∑_{k=0..n} aₖ xᵏ` has `Δ^[n+1] P = 0`.
-/
theorem fwdDiff_iter_succ_sum_eq_zero {n x : ℕ} (a : ℕ → R):
    Δ_[1] ^[n + 1] (fun (x : ℕ) =>
      ∑ k ∈ Finset.range (n + 1), a k • (x ^ k) : ℕ → R) x  = (fun _ ↦ 0) x := by
  induction' n with n IH
  . simp only [zero_add, Finset.range_one, smul_eq_mul,
      Finset.sum_singleton, pow_zero, mul_one, Function.iterate_one, fwdDiff_const]
  . rw [Function.iterate_add_apply, Function.iterate_one]
    conv_lhs => enter [0]; unfold fwdDiff
    simp only [smul_eq_mul, Function.comp_apply, fwdDiff_iter_eq_sum_shift]
    simp only [smul_eq_mul, fwdDiff_iter_eq_sum_shift] at IH
    conv_lhs => enter [2]; ext k; enter [2]; unfold fwdDiff
    simp_all only [Int.reduceNeg, smul_eq_mul, mul_one, Nat.cast_add, zsmul_eq_mul,
      Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast, Nat.cast_one]
    conv_lhs => enter [2]; ext x; rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    conv_lhs => enter [2, 2]; ext x; enter [2]; rw [Finset.sum_range_succ]
    conv_lhs => enter [2, 2]; ext x; rw [mul_add]
    rw [Finset.sum_add_distrib, IH, zero_add, ← Finset.sum_sub_distrib, ← IH]
    conv_lhs => enter [2]; ext k; rw [Finset.mul_sum]
    conv_rhs => enter [2]; ext k; rw [Finset.mul_sum]
    rw [Finset.sum_sub_distrib]
    rw [← add_left_inj (a := ∑ k ∈ Finset.range (n + 1 + 1), (-1) ^ (n + 1 - k) *
      ↑((n + 1).choose k) * (a (n + 1) * (x + k) ^ (n + 1)))]
    rw [sub_add_cancel, ← Finset.sum_add_distrib]
    conv_rhs => enter [2]; ext k; rw [← Finset.sum_range_succ]
    rw [Finset.sum_comm, Finset.sum_range_succ]
    nth_rw 2 [Finset.sum_comm]
    nth_rw 3 [Finset.sum_range_succ]
    have ih : ∑ k ∈ Finset.range (n + 1 + 1), (-1 : R) ^ (n + 1 - k) *
      ((n + 1).choose k) * ((x + k + 1) ^ (n + 1)) = (n + 1).factorial := by
      obtain h := fwdDiff_iter_eq_sum_shift (n := n + 1) (y := x + 1)
        (f := (fun x => x ^ (n + 1) : ℕ → R)) (h := 1)
      conv at h =>
        enter [2, 2]; ext k; rw [smul_eq_mul]; rw [zsmul_eq_mul, mul_one, ← Nat.cast_pow]
      nth_rw 2 [show (1 : R) = (1 : ℕ) by simp]
      nth_rw 1 [show (-1 : R) = (-1 : ℤ) by simp]
      have (k : ℕ): (((n + 1).choose k : ℤ).toNat : R) = ((n + 1).choose k : ℤ) := by simp
      conv_lhs => enter [2]; ext k; rw [add_right_comm ,
          ← Nat.cast_add, ← Nat.cast_add, ← Nat.cast_pow, ← Int.toNat_natCast (n := (n + 1).choose k),
          this k, ← Int.cast_pow, ← Int.cast_mul]
      rw [← h]
      rw [fwdDiff_iter_eq_factorial]
    have ih' : ∑ k ∈ Finset.range (n + 1 + 1), (-1 : R) ^ (n + 1 - k) * ↑((n + 1).choose k)
      * ((x + k) ^ (n + 1)) = (n + 1).factorial := by
      obtain h := fwdDiff_iter_eq_sum_shift (n := n + 1) (y := x)
        (f := (fun x => x ^ (n + 1) : ℕ → R)) (h := 1)
      conv at h =>
        enter [2, 2]; ext k; rw [smul_eq_mul]; rw [zsmul_eq_mul, mul_one, ← Nat.cast_pow]
      nth_rw 1 [show (-1 : R) = (-1 : ℤ) by simp]
      have (k : ℕ): (((n + 1).choose k : ℤ).toNat : R) = ((n + 1).choose k : ℤ) := by simp
      conv_lhs => enter [2]; ext k; rw [← Nat.cast_add, ← Nat.cast_pow,
        ← Int.toNat_natCast (n := (n + 1).choose k), this k, ← Int.cast_pow, ← Int.cast_mul]
      rw [← h]
      rw [fwdDiff_iter_eq_factorial]
    conv_lhs => enter [2, 2]; ext k; rw [mul_comm (a := a (n + 1)), ← mul_assoc]
    conv_rhs => enter [2, 2]; ext k; rw [mul_comm (a := a (n + 1)), ← mul_assoc]
    rw [← Finset.sum_mul, ← Finset.sum_mul, ih', ih, add_left_inj]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [Finset.mem_range] at hk
    conv_lhs => enter [2]; ext i ; rw [← smul_eq_mul, mul_comm (a := a k), smul_eq_mul,← mul_assoc]
    rw [← Finset.sum_mul]
    conv_rhs => enter [2]; ext i ; rw [← smul_eq_mul, mul_comm (a := a k), smul_eq_mul,← mul_assoc]
    rw [← Finset.sum_mul]
    nth_rw 2 [show (1 : R) = (1 : ℕ) by simp only [Nat.cast_one]]
    nth_rw 1 [show (-1 : R) = (-1 : ℤ) by simp]
    conv_lhs => enter [1, 2]; ext i; rw [← smul_eq_mul, add_assoc, add_comm (a := (i : R)),
      ← add_assoc,← Nat.cast_add, ← Nat.cast_add]
    conv_rhs => enter [1, 2]; ext i ; rw [← smul_eq_mul]
    obtain h := fwdDiff_iter_eq_sum_shift (n := n + 1) (y := x + 1)
      (f := (fun x => x ^ k : ℕ → R)) (h := 1)
    have (k : ℕ): (((n + 1).choose k : ℤ).toNat : R) = ((n + 1).choose k : ℤ) := by simp
    conv_lhs => enter [1, 2]; ext k; enter [1]; rw [← Int.cast_pow ,
      ← Int.toNat_natCast (n := (n + 1).choose k), this k, ← Int.cast_mul]
    conv at h =>
      enter [2, 2]; ext k; rw [smul_eq_mul]; rw [zsmul_eq_mul, mul_one, ← Nat.cast_pow]
    conv_lhs => enter [1, 2]; ext k; rw [smul_eq_mul, ← Nat.cast_pow]
    rw [← h]
    obtain h := fwdDiff_iter_eq_sum_shift (n := n + 1) (y := x)  (f := (fun x => x ^ k : ℕ → R)) (h := 1)
    conv at h =>
      enter [2, 2]; ext k; rw [smul_eq_mul]; rw [zsmul_eq_mul, mul_one, ← Nat.cast_pow]
    nth_rw 1 [show (-1 : R) = (-1 : ℤ) by simp]
    conv_rhs => enter [1, 2]; ext k; rw [← Nat.cast_add, ← Nat.cast_pow,
      ← Int.toNat_natCast (n := (n + 1).choose k), this k, ← Int.cast_pow, ← Int.cast_mul, smul_eq_mul]
    rw [← h]
    rw [fwdDiff_iter_pow_lt (by linarith), fwdDiff_iter_pow_lt (by linarith)]

open Polynomial

/--
**Newton's series** for a polynomial function.
Any function `f` defined by a polynomial can be expressed as a sum of its forward
differences at `0`, weighted by binomial coefficients.
`f(x) = ∑_{k=0..x} (x choose k) * (Δ^k f)(0)`.
-/
theorem fwdDiffTab_0th_diag_poly' {n x : ℕ} (a : ℕ → R[X]):
  (∑ k ∈ Finset.range (n + 1), a k • (x ^ k) : R[X]) =
    ∑ k ∈ Finset.range (x + 1), x.choose k • Δ_[1] ^[k]
    (fun x => ∑ k ∈ Finset.range (n + 1), a k • (x ^ k) : ℕ → R[X]) 0 := by
  simp
  obtain h := shift_eq_sum_fwdDiff_iter (n := x) (y := 0)
    (f := (fun x => ∑ i ∈ Finset.range (n + 1), a i • (x ^ i) : ℕ → R[X])) (h := 1)
  simp at h
  conv_rhs => enter [2]; ext k; enter [2]; rw [fwdDiff_iter_eq_sum_shift]; simp
  rw [h]
  conv_lhs => enter [2]; ext k; enter [2]; rw [fwdDiff_iter_eq_sum_shift]; simp

/--
A formula for the sum of a polynomial sequence, `∑_{i=0..p} P(i)`, expressed in
terms of the forward differences of `P` at `0`. This is a generalization of **Faulhaber's formula**.
-/
theorem sum_of_poly_sequence {p n : ℕ} (a : ℕ → R[X]) :
    ∑ i ∈ Finset.range (p + 1), (∑ k ∈ Finset.range (n + 1), a k • (i ^ k : R[X])) =
    ∑ k ∈ Finset.range (p + 1), ((p + 1).choose (k + 1) : R[X]) •
      (Δ_[1] ^[k] (fun (y : ℕ) => ∑ i ∈ Finset.range (n + 1), a i • (y ^ i : R[X])) 0) := by
    have h₁ : ∀ n m, ∑ k ∈ Finset.range (n + 1), k.choose m = (n + 1).choose (m + 1) := by
      intro n m
      induction' n with n IH
      · exact rfl
      · rw [Finset.sum_range_succ, Nat.choose_succ_succ', IH, add_comm]
    obtain sum_choose := h₁ p
    conv => enter [1, 2, x]; rw [fwdDiffTab_0th_diag_poly']; simp
    simp only [smul_eq_mul]
    have h₂ : ∑ x ∈ Finset.range (p + 1), ∑ x_1 ∈ Finset.range (x + 1),
      ↑(x.choose x_1) * Δ_[1] ^[x_1] (fun (x : ℕ) => ∑ x_2 ∈ Finset.range (n + 1), a x_2 * ↑x ^ x_2) 0 =
      ∑ x ∈ Finset.range (p + 1), ∑ x_1 ∈ Finset.range (p + 1),
      ↑(x.choose x_1) * Δ_[1] ^[x_1] (fun (x : ℕ) => ∑ x_2 ∈ Finset.range (n + 1), a x_2 * ↑x ^ x_2) 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      have h₁₁ : ∑ k ∈ Finset.Ico (x + 1) (p + 1), ↑(x.choose k) * Δ_[1] ^[k]
        (fun (x : ℕ) => ∑ x_2 ∈ Finset.range (n + 1), a x_2 * x ^ x_2) 0 = 0 := by
        rw [Finset.sum_Ico_eq_sum_range]
        simp
        simp at hx
        have : ∑ k ∈ Finset.range (p - x), 0 = (0 : R[X]) := by simp only [Finset.sum_const_zero]
        rw [← this]
        apply Finset.sum_congr rfl
        intro y hy
        simp at hy
        have : x + 1 + y > x := by omega
        rw [Nat.choose_eq_zero_of_lt this]
        simp
      nth_rw 1 3 [Finset.range_eq_Ico]
      have h₁₂ : ∑ x_1 ∈ Finset.Ico 0 (p + 1), ↑(x.choose x_1) * Δ_[1] ^[x_1]
          (fun (x : ℕ) => ∑ x_2 ∈ Finset.range (n + 1), a x_2 * x ^ x_2) 0 =
        ∑ x_1 ∈ Finset.Ico 0 (x + 1), ↑(x.choose x_1) * Δ_[1] ^[x_1]
          (fun (x : ℕ) => ∑ x_2 ∈ Finset.range (n + 1), a x_2 * x ^ x_2) 0 +
        ∑ x_1 ∈ Finset.Ico (x + 1) (p + 1), ↑(x.choose x_1) * Δ_[1] ^[x_1]
          (fun (x : ℕ) => ∑ x_2 ∈ Finset.range (n + 1), a x_2 * x ^ x_2) 0 := by
        rw [← Finset.sum_Ico_consecutive]
        · linarith
        · simp at hx
          linarith
      rw [h₁₂, h₁₁, add_zero]
    rw [h₂, Finset.sum_comm]
    simp_rw [← Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    simp at hk
    congr 1
    norm_cast
    rw [sum_choose]
