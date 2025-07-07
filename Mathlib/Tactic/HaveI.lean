/-
Copyright (c) 2023 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/

import Mathlib.Init
/-!
# Variants of `haveI`/`letI` for use in do-notation.

This files implements the `haveI'` and `letI'` macros which have the same semantics as
`haveI` and `letI`, but are `doElem`s and can be used inside do-notation.

They need an apostrophe after their name for disambiguation with the term variants.
This is necessary because the do-notation has a hardcoded list of keywords which can appear both
as term-mode and do-elem syntax (like for example `let` or `have`).
-/

namespace Mathlib.Tactic.HaveI

local syntax "haveIDummy" letDecl : term
macro_rules
  | `(assert! haveIDummy $hd:letDecl; $body) => `(haveI $hd:letDecl; $body)

/--
`haveI'` behaves like `have`, but inlines the value instead of producing a `have` term.

(This is the do-notation version of the term-mode `haveI`.)
-/
macro "haveI' " hd:letDecl : doElem =>
  `(doElem| assert! haveIDummy $hd:letDecl)

local syntax "letIDummy" letDecl : term
macro_rules
  | `(assert! letIDummy $hd:letDecl; $body) => `(letI $hd:letDecl; $body)

/--
`letI` behaves like `let`, but inlines the value instead of producing a `let` term.

(This is the do-notation version of the term-mode `haveI`.)
-/
macro "letI' " hd:letDecl : doElem =>
  `(doElem| assert! letIDummy $hd:letDecl)

end Mathlib.Tactic.HaveI
