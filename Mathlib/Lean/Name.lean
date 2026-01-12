/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Init
public import Lean.Meta.Match.MatcherInfo
public import Lean.Meta.Tactic.Delta
public import Std.Data.HashMap.Basic

/-!
# Additional functions on `Lean.Name`.

We provide `allNames` and `allNamesByModule`.
-/

public section

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

/--
Determines if the pretty-printed version of the given name would parse as an
`ident` with an underlying name (via `getId`) equal to the original name.
The pretty-printer usually escapes unparsable components of a name with `«»`,
but makes exceptions for various names with special meaning, meaning that the result does not
round trip. We therefore re-check those conditions here.

This function is intended to be "safe" in that if it returns `true`,
the name will definitely round trip. (The converse is not guaranteed.) Any deviation from this
behavior is a bug which should be fixed.
-/
-- See also [Zulip](https://leanprover.zulipchat.com/#narrow/channel/239415-metaprogramming-.2F-tactics/topic/Check.20if.20a.20.60Lean.2EName.60.20is.20roundtrippable/with/565735560)
meta def Lean.Name.willRoundTrip (n : Name) : Bool :=
  !n.isAnonymous -- anonymous names do not roundtrip
    && !n.hasMacroScopes -- names with macroscopes do not roundtrip
    && !maybePseudoSyntax -- names which might be "pseudo-syntax" do not roundtrip
    && !n.isInaccessibleUserName -- names which satisfy `isInaccessibleUserName` may not roundtrip
    && go n
where
  go : Lean.Name → Bool
    | .str n s =>
        !s.contains (fun c =>
          /- names with newlines may not round trip; for convenience, we consider all names
          with newlines to be non-roundtrippable, though technically some might -/
          c == '\n'
          -- names containing the end escape character `»` do not roundtrip
          || isIdEndEscape c)
        && go n
    | .num .. => false -- names with any numeric components do not roundtrip
    | .anonymous => true -- we check that the entire name is not anonymous at the top level
  /-- This should be exactly the same as `toStringWithToken.maybePseudoSyntax`. -/
  maybePseudoSyntax :=
    if n == `_ then
      -- output hole as is
      true
    else if let .str _ s := n.getRoot then
      -- could be pseudo-syntax for loose bvar or universe mvar, output as is
      "#".isPrefixOf s || "?".isPrefixOf s
    else
      false
