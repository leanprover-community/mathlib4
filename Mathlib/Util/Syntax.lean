/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Thomas R. Murrills
-/
import Lean
import Std.Tactic.OpenPrivate

/-!
# Helper functions for working with typed syntaxes.
-/

set_option autoImplicit true

namespace Lean

/-- Acts on the raw `Syntax` underlying some `TSyntax ks` with `f : Syntax → Syntax`. -/
def TSyntax.map (f : Syntax → Syntax) {ks} : TSyntax ks → TSyntax ks
  | ⟨raw⟩ => ⟨f raw⟩

/-- Monadically acts on the raw `Syntax` underlying some `TSyntax ks` with `f : Syntax → m Syntax`-/
def TSyntax.mapM [Monad m] (f : Syntax → m Syntax) {ks} : TSyntax ks → m (TSyntax ks)
  | ⟨raw⟩ => return ⟨← f raw⟩

/--
Applies the given function to every subsyntax.

Like `Syntax.replaceM` but for typed syntax.
-/
def TSyntax.replaceM [Monad M] (f : Syntax → M (Option Syntax)) (stx : TSyntax k) : M (TSyntax k) :=
  stx.mapM (·.replaceM f)

/--
Constructs a typed separated array from elements.
The given array does not include the separators.

Like `Syntax.SepArray.ofElems` but for typed syntax.
-/
def Syntax.TSepArray.ofElems {sep} (elems : Array (TSyntax k)) : TSepArray k sep :=
  .mk (SepArray.ofElems (sep := sep) elems).1

/--
Determines if `lhs : Syntax` and `rhs : Syntax` have the same range. If either does not
have position info, returns `false`.

If `lhsCanonical` or `rhsCanonical` are `true` (default: `false`), only consider
`lhs` or `rhs` as having position info if they are canonical, respectively.
-/
def Syntax.isEqByRange (lhs rhs : Syntax) (lhsCanonical rhsCanonical := true) :=
  match lhs.getRange? lhsCanonical, rhs.getRange? rhsCanonical with
  | some r₁, some r₂ => r₁ == r₂
  | _, _ => false

/--
Determines if the range of `super : Syntax` includes the range of `sub : Syntax`. If either does
not have position info, returns `false`.

If `superCanonical` or `subCanonical` are `true` (default: `false`), only consider
`super` or `sub` as having position info if they are canonical, respectively.
-/
def Syntax.includes (super sub : Syntax) (superCanonical subCanonical := false) :=
  match super.getRange? superCanonical, sub.getRange? subCanonical with
  | some rSuper, some rSub => rSuper.includes rSub
  | _, _ => false

/--
Determines if the range of `super : TSyntax ks` includes the range of `sub : Syntax`. If either
does not have position info, returns `false`.

If `superCanonical` or `subCanonical` are `true` (default: `false`), only consider
`super` or `sub` as having position info if they are canonical, respectively.

Like `Syntax.includes`, but enables dot notation for `TSyntax` on its first argument.
-/
def TSyntax.includes {ks} (super : TSyntax ks) (sub : Syntax)
    (superCanonical subCanonical := false) :=
  super.raw.includes sub superCanonical subCanonical

open private updateLast from Init.Meta in
/-- Finds the rightmost, lowermost `info : SourceInfo` for which `f info` is `some newInfo`, and
replaces `info` with `newInfo`. If no such `SourceInfo` is found, returns `none`. -/
partial def Syntax.setTrailingInfoBy? (f : SourceInfo → Option SourceInfo) :
    Syntax → Option Syntax
  | .node info kind args => match updateLast args (setTrailingInfoBy? f) args.size with
    | some args => some <| .node info kind args
    | none => (f info).map (.node · kind args)
  | .ident info rv v pr => (f info).map (.ident · rv v pr)
  | .atom info val => (f info).map (.atom · val)
  | _ => none

@[inherit_doc Syntax.setTrailingInfoBy?]
def TSyntax.setTrailingInfoBy? (f : SourceInfo → Option SourceInfo) {ks} :
    TSyntax ks → Option (TSyntax ks) :=
  mapM (·.setTrailingInfoBy? f)

/-- Given some `SourceInfo.original ..`, replace its `trailing` argument with the empty string.
If the argument is not an `.original` `SourceInfo`, return `none`. -/
def SourceInfo.unsetOriginalTrailing? : SourceInfo → Option SourceInfo
  | .original l p _ e => some <| .original l p "".toSubstring e
  | _ => none

/-- Removes the trailing string of the rightmost, lowermost `.original .. : SourceInfo`. If no
`.original` `SourceInfo` is found, returns `none`. -/
def Syntax.unsetOriginalTrailing? : Syntax → Option Syntax :=
  setTrailingInfoBy? (·.unsetOriginalTrailing?)

/-- Removes the trailing string of the rightmost, lowermost `.original .. : SourceInfo`. If no
`.original` `SourceInfo` is found, leave the argument syntax unchanged.

Contrast with `unsetTrailing`, which, while it does unset `.original` source info, does so for the
rightmost, *uppermost* node, instead of the rightmost, lowermost node. -/
-- TODO: as of writing, a bug in `setTrailingInfo` means that `unsetTrailing` does not even
-- necessarily behave as described.
def Syntax.unsetOriginalTrailing (stx : Syntax) : Syntax :=
  stx.unsetOriginalTrailing?.getD stx

@[inherit_doc Syntax.unsetOriginalTrailing?]
def TSyntax.unsetOriginalTrailing? {ks} (stx : TSyntax ks) : Option (TSyntax ks) :=
  stx.mapM (·.unsetOriginalTrailing?)

@[inherit_doc Syntax.unsetOriginalTrailing]
def TSyntax.unsetOriginalTrailing {ks} (stx : TSyntax ks) : TSyntax ks :=
  stx.map (·.unsetOriginalTrailing)
