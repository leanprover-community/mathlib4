/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Caflisch, David Loeffler
-/
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Abel

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
