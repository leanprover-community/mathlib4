/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Sub-Probability mass functions

This file defines `SPMF α` as an extension of the existing `PMF α` construction,
representing them as probability mass functions with optional failure for the distirubiton gap.

## Tags

probability mass function, discrete probability measure
-/

@[expose] public noncomputable section

variable {α β : Type _}

open NNReal ENNReal MeasureTheory

/-- A subprobability mass function on `α`, represented as a `PMF α` with an optional failure value.
The resulting function has sum *at most* one over `some x` rather than `PMF`'s exact sum,
with `none` being used to store the additional mass of the underlying `PMF`. -/
def SPMF.{u} (α : Type u) : Type u := OptionT PMF α

/-- Convert a `PMF` to an `SPMF` by assigning no failure mass. -/
def PMF.toSPMF (p : PMF α) : SPMF α := OptionT.lift p

/-- Convert an `SPMF α` to a `PMF (Option α)`, such that `none` has the missing mass needed
to make the total sum over `α` be exactly `1`. -/
def SPMF.toPMF (p : SPMF α) : PMF (Option α) := OptionT.run p

/-- Convert an `SPMF α` from a `PMF` over `Option α`. -/
def SPMF.mk (p : PMF (Option α)) : SPMF α := OptionT.mk p

namespace SPMF

instance instFunLike : FunLike (SPMF α) α ℝ≥0∞ where
  coe p a := p.toPMF (some a)
  coe_injective' _ _ h := OptionT.ext (PMF.ext_forall_ne none fun | some x, _ => congr_fun h x)

lemma apply_eq_toPMF_some (p : SPMF α) (x : α) : p x = p.toPMF (some x) := rfl

/-- The difference between the sum of an `SPMF` and `1`. -/
def gap (p : SPMF α) : ℝ≥0∞ := p.toPMF none

lemma gap_eq_tsub_tsum (p : SPMF α) : p.gap = 1 - ∑' x, p x := by
  classical
  simp [gap, PMF.apply_eq_one_sub_tsum_ite p.toPMF none,
    ENNReal.summable.tsum_option_eq_add_tsum, apply_eq_toPMF_some]

lemma tsum_le_one (p : SPMF α) : ∑' x, p x ≤ 1 := by
  classical
  refine le_of_le_of_eq ?_ p.toPMF.tsum_coe
  simp [ENNReal.summable.tsum_option_eq_add_tsum, apply_eq_toPMF_some]

@[simp]
lemma tsum_add_gap (p : SPMF α) : (∑' x, p x) + p.gap = 1 := by
  rw [gap_eq_tsub_tsum]
  exact add_tsub_cancel_of_le p.tsum_le_one

@[simp]
lemma gap_add_tsum (p : SPMF α) : p.gap + (∑' x, p x) = 1 := by
  rw [gap_eq_tsub_tsum]
  exact tsub_add_cancel_of_le p.tsum_le_one

@[simp, grind =]
lemma mk_apply (p : PMF (Option α)) (x : α) : (SPMF.mk p) x = p (some x) := rfl

@[ext]
lemma ext {p q : SPMF α} (h : ∀ x : α, p x = q x) : p = q :=
  PMF.ext_forall_ne none fun | some x, _ => h x

/-- Expose the induced monad instance on `SPMF`, viewed as `PMF` augmented with `failure`.
See `SPMF.pure_apply` and `SPMF.bind_apply_eq_tsum` for explicit definitions. -/
instance : AlternativeMonad SPMF := OptionT.instAlternativeMonadOfMonad PMF
instance : LawfulAlternative SPMF := OptionT.instLawfulAlternativeOfLawfulMonad PMF
instance : LawfulMonad SPMF := OptionT.instLawfulMonad (m := PMF)

/-- Expose the lifting operations from `PMF` to `SPMF` given by `OptionT.lift`. -/
instance : MonadLift PMF SPMF := OptionT.instMonadLift (m := PMF)
instance : LawfulMonadLift PMF SPMF := OptionT.instLawfulMonadLift (m := PMF)

@[grind =]
lemma liftM_def (p : PMF α) : (liftM p : SPMF α) = PMF.toSPMF p := rfl

lemma to_PMF_liftM (p : SPMF α) : SPMF.toPMF (liftM p : SPMF α) = p := rfl

lemma toPMF_toSPMF (p : PMF α) : p.toSPMF.toPMF = p.map some := rfl

open Classical in
/-- Given a function `f : α → ℝ≥0∞` which has sum `hf : tsum f ≤ 1`,
`ofFn f hf` is the `SPMF` that has mass `f x` at `x : α`.
The underlying `PMF` asigns probability `1 - ∑' x, f x` to `none`. -/
def ofFn (f : α → ℝ≥0∞) (hf : ∑' x, f x ≤ 1) : SPMF α :=
  SPMF.mk (PMF.ofFn (Option.rec (1 - ∑' x, f x) f)
    (by simp [ENNReal.summable.tsum_option_eq_add_tsum, tsub_add_cancel_of_le hf]))

@[simp, grind =]
lemma ofFn_apply (f : α → ℝ≥0∞) (hf : ∑' x, f x ≤ 1) (x : α) :
    SPMF.ofFn f hf x = f x := rfl

section pure

lemma pure_eq_mk (x : α) : (pure x : SPMF α) = SPMF.mk (PMF.pure (some x)) := rfl

lemma pure_eq_toSPMF (x : α) : (pure x : SPMF α) = PMF.toSPMF (PMF.pure x) :=
  (PMF.pure_map some x).symm

@[simp]
lemma toPMF_pure (x : α) : SPMF.toPMF (pure x) = PMF.pure (some x) := by
  simp [pure_eq_toSPMF, toPMF_toSPMF]

open scoped Classical in
lemma pure_eq_ofFn (x : α) :
    (pure x : SPMF α) = SPMF.ofFn (Pi.single x 1) (le_of_eq (tsum_pi_single x 1)) := by
  ext y; grind [= pure_eq_mk, = PMF.pure_apply]

open scoped Classical in
@[simp, grind =]
lemma pure_apply (x y : α) :
    (pure x : SPMF α) y = if y = x then 1 else 0 := by
  grind [= pure_eq_ofFn]

@[simp, grind =]
lemma gap_pure (x : α) : SPMF.gap (pure x) = 0 := by
  simp [SPMF.gap_eq_tsub_tsum]

end pure

section bind

@[simp, grind =]
lemma toPMF_bind (p : SPMF α) (q : α → SPMF β) : (p >>= q).toPMF =
    Option.elimM p.toPMF (PMF.pure none) (fun x => (q x).toPMF) := OptionT.run_bind _

lemma bind_apply_eq_tsum (p : SPMF α) (q : α → SPMF β) (y : β) :
    (p >>= q) y = ∑' x : α, p x * q x y := by
  simp [apply_eq_toPMF_some]

lemma gap_bind (p : SPMF α) (q : α → SPMF β) :
    (p >>= q).gap = p.gap + ∑' x, p x * (q x).gap := by
  simp [gap, apply_eq_toPMF_some]

end bind

section zero

instance {α : Type _} : Zero (SPMF α) where
  zero := ofFn 0 (by simp)

@[simp, grind =]
lemma zero_apply (x : α) : (0 : SPMF α) x = 0 := rfl

@[simp, grind =]
lemma gap_zero : (0 : SPMF α).gap = 1 := by
  simp [gap_eq_tsub_tsum]

lemma zero_eq_mk : (0 : SPMF α) = SPMF.mk (PMF.pure none) := by simp [SPMF.ext_iff]

lemma failure_eq_mk : (failure : SPMF α) = SPMF.mk (PMF.pure none) := rfl

lemma failure_eq_zero : (failure : SPMF α) = (0 : SPMF α) := by
  rw [failure_eq_mk, zero_eq_mk]

@[simp, grind =]
lemma failure_apply (x : α) : (failure : SPMF α) x = 0 := by simp [failure_eq_zero]

end zero

end SPMF
