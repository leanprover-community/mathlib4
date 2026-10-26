/-
Copyright (c) 2026 Paul Cadman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Cadman
-/
module

public import Mathlib.Algebra.Polynomial.Sturm.Sequence
public import Mathlib.Data.List.SignVariations
public import Mathlib.Basic.Sign.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.FieldTheory.IsRealClosed.Basic

/-!
# The Sturm–Tarski theorem

Statement only: the proofs are `sorry` until the theorem lands. The `real_root_count` tactic is
built on `Polynomial.sturm_tarski`.
-/

@[expose] public section

noncomputable section

open List Set SignType
open scoped Finset

namespace Polynomial

-- I'd like to generalise beyond the reals to:
-- `variable {k : Type*} [Field k] [IsRealClosed k] (p q : k[X])`
-- but unfortunately our theory of real closed fields is too thin to make this practical for now.
variable (p q : ℝ[X])

-- This should probably be part of the public `Polynomial` API since its such a common operation.
open scoped Classical in
/-- The distinct roots of `p` in `s`. -/
def rootsIn (s : Set ℝ) : Finset ℝ :=
  p.roots.toFinset.filter (fun x ↦ x ∈ s)

/-- The number of sign variations at `a` of the Sturm sequence of `p` and `p' * q`. -/
def sturmSignVariations (a : ℝ) : ℕ :=
  signVariations <| (sturmSeq p (p.derivative * q)).map (sign ∘ eval a)

theorem sturm_tarski' (a : ℝ) (ha : p.eval a ≠ 0) :
    letI va : ℤ := sturmSignVariations p q a
    letI wa : ℤ :=
      (p.rootsIn (Ioi a ∩ {x | 0 < q.eval x})).card - (p.rootsIn (Ioi a ∩ {x | q.eval x < 0})).card
    letI const := signVariations <| (sturmSeq p (p.derivative * q)).map (sign ∘ leadingCoeff)
    va - wa = const := by
  sorry

-- I guess this is what you really want.
theorem sturm_tarski {a b : ℝ} (h : a < b) (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0) :
    (sturmSignVariations p q a : ℤ) - sturmSignVariations p q b =
      (p.rootsIn (Ioo a b ∩ {x | 0 < q.eval x})).card -
        (p.rootsIn (Ioo a b ∩ {x | q.eval x < 0})).card :=
  -- Easy consequence of `sturm_tarski'` (which I claim is the "true" result).
  sorry

end Polynomial
