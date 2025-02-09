/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
import Mathlib.Data.PNat.Basic

/-!
# `pnat_omega`

This file implements `pnat_omega`, a simple wrapper around `omega` for solving goals involving
`PNat`s.

## Implementation details
The implementation follows these steps:
1. For each `x : PNat` in the context, add the hypothesis `0 < (↑x : ℕ)`.
2. Translate arithmetic on `PNat` to `Nat` using the `pnat_omega_coe_simps` simp set.
3. Finish the proof using `omega`.

-/

namespace OmegaExtensions.PNat

open Lean Meta Elab Tactic Qq in
/-- For each `x : PNat` in the context, add the hypothesis `0 < (↑x : ℕ)`. -/
elab "omega_preprocess_pnat" : tactic => withMainContext do
  let result ← (← getLCtx).foldlM (init := ← getMainGoal) fun g decl => do
    let ⟨1, declType, declExpr⟩ ← inferTypeQ decl.toExpr | return g
    let ~q(PNat) := declType | return g
    let pf := q(PNat.pos $declExpr)
    let (_, mvarIdNew) ← g.let .anonymous pf q(0 < PNat.val $declExpr)
    return mvarIdNew
  setGoals [result]

@[pnat_omega_coe_simps]
lemma coe_inj (m n : PNat) : m = n ↔ (m : ℕ) = (n : ℕ) := by simp

@[pnat_omega_coe_simps]
lemma coe_le_coe (m n : PNat) : m ≤ n ↔ (m : ℕ) ≤ (n : ℕ) := by simp

@[pnat_omega_coe_simps]
lemma coe_lt_coe (m n : PNat) : m < n ↔ (m : ℕ) < (n : ℕ) := by simp

attribute [pnat_omega_coe_simps] PNat.add_coe PNat.mul_coe PNat.val_ofNat

@[pnat_omega_coe_simps]
lemma sub_coe (a b : PNat) : ((a - b : PNat) : Nat) = a.val - 1 - b.val + 1 := by
  cases a
  cases b
  simp only [PNat.mk_coe, _root_.PNat.sub_coe, ← _root_.PNat.coe_lt_coe]
  split_ifs <;> omega

/-- Simple wrapper around `omega` for solving goals involving `PNat`s. -/
macro "pnat_omega" : tactic => `(tactic| focus (
  omega_preprocess_pnat;
  simp only [pnat_omega_coe_simps] at *;
  omega)
)

end OmegaExtensions.PNat
