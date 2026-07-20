/-
Copyright (c) 2026 Paul Cadman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Cadman
-/
module

public import Mathlib.Tactic.Determinant.Bird.Cert

/-!
# `norm_det` simproc and `eval_det` tactic

A tactic for normalizing matrix determinants.
-/

public meta section

open Lean Meta Elab Tactic Simp
open Mathlib.Tactic.Determinant

/-- reify a `BirdDet` call and normalize it using the certificate-chain evaluator -/
def normalizeBirdDet (e : Expr) : MetaM Simp.Result := do
  let ⟨rα, ctx⟩ ← reifyBirdDet e
  let detNorm ← certBirdDet (rα := rα) |>.run' {} |>.run ctx |>.run .reducible
  Mathlib.Tactic.RingNF.cleanup {} {expr := detNorm.norm, proof? := some detNorm.proof}

/-- Normalize a literal `birdDet` call using the certificate-chain evaluator. -/
simproc_decl norm_det (BirdDet.birdDet _ _) := fun e => do
  return .done (← normalizeBirdDet e)

/-- Normalize `birdDet` calls in the target using the certificate-chain simproc. -/
macro (name := evalDet) "eval_det" : tactic => `(tactic| simp only [norm_det])

end
