/-
Copyright (c) 2026 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash, Paul Cadman
-/
module

public import Mathlib.Algebra.Polynomial.RootsIn
public import Mathlib.Algebra.Polynomial.Sturm.Sequence
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Sign.Defs
public import Mathlib.Data.List.SignVariations

/-!
# The Sturm–Tarski theorem

This file states the Sturm–Tarski theorem on an open interval and Sturm's theorem on the whole
real line, for polynomials over `ℝ`. Neither statement is proved here; the docstring of each links
to its proof in lean-smt.

## Main definitions

* `Polynomial.signAtTop p` and `Polynomial.signAtBot p`: the signs of `p` at `∞` and at `-∞`.
* `Polynomial.signVariationsLine L`: the number of sign variations of the list `L` at `-∞`, minus
  the number at `∞`.

## Main statements

* `Polynomial.sturm_tarski`: the Sturm–Tarski theorem on an open interval.
* `Polynomial.sturm_R`: Sturm's theorem on the whole real line.
-/

noncomputable section

open List Set SignType

namespace Polynomial

section Sign

variable {R : Type*} [Ring R] [LinearOrder R]

/-- The sign of `p` at `∞`.

See:
[`sgn_pos_inf`](https://github.com/ufmg-smite/lean-smt/blob/8ce8a0d7e49bb999c9ad483c69999c791ba0c87b/Smt/Reconstruct/Real/CAD/Sturm/SeqDefs.lean#L56-L57). -/
public def signAtTop (p : R[X]) : SignType :=
  sign p.leadingCoeff

public theorem signAtTop_def (p : R[X]) : signAtTop p = sign p.leadingCoeff := by
  rw [signAtTop]

/-- The sign of `p` at `-∞`.

See:
[`sgn_neg_inf`](https://github.com/ufmg-smite/lean-smt/blob/8ce8a0d7e49bb999c9ad483c69999c791ba0c87b/Smt/Reconstruct/Real/CAD/Sturm/SeqDefs.lean#L59-L60). -/
public def signAtBot (p : R[X]) : SignType :=
  if Even p.natDegree then signAtTop p else -signAtTop p

public theorem signAtBot_def (p : R[X]) :
    signAtBot p = if Even p.natDegree then signAtTop p else -signAtTop p := by
  rw [signAtBot]

@[simp]
public theorem signAtTop_C_mul [IsStrictOrderedRing R] (c : R) (p : R[X]) :
    signAtTop (C c * p) = sign c * signAtTop p := by
  simp [signAtTop_def, sign_mul]

@[simp]
public theorem signAtBot_C_mul [IsStrictOrderedRing R] (c : R) (p : R[X]) :
    signAtBot (C c * p) = sign c * signAtBot p := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp [signAtBot_def, signAtTop_def]
  · simp only [signAtBot_def, natDegree_C_mul hc, signAtTop_C_mul]
    split_ifs <;> simp

/-- The number of sign variations of the list `L` at `-∞`, minus the number at `∞`.

See:
[`seqVarLine`](https://github.com/ufmg-smite/lean-smt/blob/8ce8a0d7e49bb999c9ad483c69999c791ba0c87b/Smt/Reconstruct/Real/CAD/Sturm/SeqDefs.lean#L105-L106). -/
public def signVariationsLine (L : List R[X]) : ℤ :=
  (L.map signAtBot).signVariations - (L.map signAtTop).signVariations

public theorem signVariationsLine_def (L : List R[X]) :
    signVariationsLine L = (L.map signAtBot).signVariations - (L.map signAtTop).signVariations := by
  rw [signVariationsLine]

end Sign

-- I'd like to generalise beyond the reals to:
-- `variable {k : Type*} [Field k] [IsRealClosed k] (p q : k[X])`
-- but unfortunately our theory of real closed fields is too thin to make this practical for now.
variable (p q : ℝ[X])

/-- The number of sign variations at `a` of the Sturm sequence of `p` and `p' * q`. -/
public def sturmSignVariations (a : ℝ) : ℕ :=
  signVariations <| (sturmSeq p (p.derivative * q)).map (sign ∘ eval a)

public theorem sturmSignVariations_def (a : ℝ) :
    sturmSignVariations p q a =
      signVariations ((sturmSeq p (p.derivative * q)).map (sign ∘ eval a)) := by
  rw [sturmSignVariations]

/-- The Sturm–Tarski theorem on an open interval.

See:
[`sturm_tarski_interval`](https://github.com/ufmg-smite/lean-smt/blob/8ce8a0d7e49bb999c9ad483c69999c791ba0c87b/Smt/Reconstruct/Real/CAD/Sturm/Theorem.lean#L9-L12). -/
public theorem sturm_tarski {a b : ℝ} (h : a < b) (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0) :
    (sturmSignVariations p q a : ℤ) - sturmSignVariations p q b =
      (p.rootsIn (Ioo a b ∩ {x | 0 < q.eval x})).card -
        (p.rootsIn (Ioo a b ∩ {x | q.eval x < 0})).card := by
  sorry

/-- Sturm's theorem on the whole real line.

See:
[`sturm_R`](https://github.com/ufmg-smite/lean-smt/blob/8ce8a0d7e49bb999c9ad483c69999c791ba0c87b/Smt/Reconstruct/Real/CAD/Sturm/Theorem.lean#L229-L233). -/
public theorem sturm_R :
    p.roots.toFinset.card = signVariationsLine (sturmSeq p (derivative p)) := by
  sorry

end Polynomial
