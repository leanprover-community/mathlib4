/-
Copyright (c) 2023 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib.Tactic.SolveByElim

register_label_attr ineq_rules

register_label_attr unsafe_ineq_rules

register_label_attr ineq_extra

register_label_attr mod_rules

register_label_attr mod_extra

register_label_attr iff_rules

syntax (name := RelCongrSyntax) "rel_congr" : tactic
syntax (name := RelSyntax) "rel" " [" term,* "] " : tactic
syntax (name := ExtraSyntax) "extra" : tactic

open Lean Mathlib Tactic

def RelConfig : SolveByElim.Config :=
{ transparency := .instances
  -- On applying a lemma or hypothesis successfully, don't backtrack
  failAtMaxDepth := false
  maxDepth := 50 }

def Lean.MVarId.RelCongr (attr : Name) --(add : List Term)
    (disch : MVarId → MetaM (Option (List MVarId)) := fun _ => pure none)
    (proc : List MVarId → List MVarId → MetaM (Option (List MVarId)) := fun _ _ => pure none)
    (g : MVarId) :
    MetaM (List MVarId) := do
  let cfg : SolveByElim.Config := { RelConfig with discharge := disch, proc := proc }
  SolveByElim.solveByElim.processSyntax cfg false false [] [] #[mkIdent attr] [g]

def Lean.MVarId.Rel (attr : Array Name) (add : List Term) (m : MessageData)
    (disch : MVarId → MetaM (Option (List MVarId)) := fun _ => pure none)
    (proc : List MVarId → List MVarId → MetaM (Option (List MVarId)) := fun _ _ => pure none)
    (g : MVarId) :
    MetaM (List MVarId) := do
  let cfg : SolveByElim.Config := { RelConfig with discharge := disch, proc := proc }
  let [] ← SolveByElim.solveByElim.processSyntax cfg true false add [] (attr.map mkIdent) [g]
    | throwError m
  return []
