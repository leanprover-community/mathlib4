/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Init
import Lean.Meta.Match.MatcherInfo
import Lean.Meta.Tactic.Delta
import Std.Data.HashMap.Basic

/-!
# Additional functions on `Lean.Name`.

We provide `allNames` and `allNamesByModule`.
-/

open Lean Meta Elab

private def isBlackListed (declName : Name) : CoreM Bool := do
  if declName.toString.startsWith "Lean" then return true
  let env ← getEnv
  pure <| declName.isInternalDetail
   || isAuxRecursor env declName
   || isNoConfusion env declName
  <||> isRec declName <||> isMatcher declName

/--
Retrieve all names in the environment satisfying a predicate.
-/
def allNames (p : Name → Bool) : CoreM (Array Name) := do
  (← getEnv).constants.foldM (init := #[]) fun names n _ => do
    if p n && !(← isBlackListed n) then
      return names.push n
    else
      return names

/--
Retrieve all names in the environment satisfying a predicate,
gathered together into a `HashMap` according to the module they are defined in.
-/
def allNamesByModule (p : Name → Bool) : CoreM (Std.HashMap Name (Array Name)) := do
  (← getEnv).constants.foldM (init := ∅) fun names n _ => do
    if p n && !(← isBlackListed n) then
      let some m ← findModuleOf? n | return names
      -- TODO use `modify` and/or `alter` when available
      match names[m]? with
      | some others => return names.insert m (others.push n)
      | none => return names.insert m #[n]
    else
      return names

/-- Decapitalize the last component of a name. -/
def Lean.Name.decapitalize (n : Name) : Name :=
  n.modifyBase fun
    | .str p s => .str p s.decapitalize
    | n       => n

/-- Whether the lemma has a name of the form produced by `Lean.Meta.mkAuxLemma`. -/
def Lean.Name.isAuxLemma (n : Name) : Bool :=
  match n with
  -- `mkAuxLemma` generally allows for arbitrary prefixes but these are the ones produced by core.
  | .str _ s => "_proof_".isPrefixOf s || "_simp_".isPrefixOf s
  | _ => false

/-- Unfold all lemmas created by `Lean.Meta.mkAuxLemma`. -/
def Lean.Meta.unfoldAuxLemmas (e : Expr) : MetaM Expr := do
  deltaExpand e Lean.Name.isAuxLemma
