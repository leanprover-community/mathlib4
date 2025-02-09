/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
import Mathlib.Data.PNat.Basic

/-!
# `pnat_omega`

In this file we implement `enat_omega`: a simple wrapper around `omega` for solving goals involving
`PNat`s.

## Implementation details
It uses the following pipeline:
1. For each `x : PNat` in the context add the `0 < (↑x : ℕ)` hypothesis.
2. Translate the arithmetic on `PNat` to `Nat` using `pnat_omega_coe_simps` simp set.
3. Finish the goal using `omega`.

-/

namespace OmegaExtensions.PNat

open Qq in

/-- For each `x : PNat` in the context add the `0 < (↑x : ℕ)` hypothesis. -/
elab "omega_preprocess_pnat" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let ctx ← Lean.MonadLCtx.getLCtx
    let result : Lean.MVarId ← ctx.foldlM (init := goal) fun g decl => do
      let declExpr := decl.toExpr
      let declType ← Lean.Meta.inferType declExpr
      let isPNat ← Lean.Meta.isExprDefEq declType q(PNat)
      if isPNat then
        let p : Lean.Expr := Lean.Expr.app q(PNat.pos) declExpr
        let mvarIdNew ← g.define .anonymous (← Lean.Meta.inferType p) p
        let (_, mvarIdNew) ← mvarIdNew.intro1P
        return mvarIdNew
      else
        return g
    Lean.Elab.Tactic.setGoals [result]

@[pnat_omega_coe_simps]
lemma coe_inj' (m n : PNat) : m = n ↔ (m : ℕ) = (n : ℕ) := PNat.coe_inj.symm

@[pnat_omega_coe_simps]
lemma coe_le_coe' (m n : PNat) : m ≤ n ↔ (m : ℕ) ≤ (n : ℕ) := (PNat.coe_le_coe m n).symm

@[pnat_omega_coe_simps]
lemma coe_lt_coe' (m n : PNat) : m < n ↔ (m : ℕ) < (n : ℕ) := (PNat.coe_lt_coe m n).symm

attribute [pnat_omega_coe_simps] PNat.add_coe PNat.mul_coe PNat.val_ofNat

@[pnat_omega_coe_simps]
lemma sub_coe' (a b : PNat) : ((a - b : PNat) : Nat) = a.val - 1 - b.val + 1 := by
  cases a
  cases b
  simp only [PNat.mk_coe, PNat.sub_coe, ← PNat.coe_lt_coe]
  split_ifs <;> omega

/-- Simple wrapper around `omega` for solving goals involving `PNat`s. -/
macro "pnat_omega" : tactic => `(tactic| focus (
  omega_preprocess_pnat;
  simp only [pnat_omega_coe_simps] at *;
  omega)
)

end OmegaExtensions.PNat
