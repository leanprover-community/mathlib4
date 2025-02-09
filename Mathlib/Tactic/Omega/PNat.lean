import Mathlib.Data.PNat.Basic

namespace OmegaExtensions.PNat

open Qq in
/--  -/
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

macro "pnat_omega" : tactic => `(tactic| focus (
  omega_preprocess_pnat;
  simp only [pnat_omega_coe_simps] at *;
  omega)
)

end OmegaExtensions.PNat
