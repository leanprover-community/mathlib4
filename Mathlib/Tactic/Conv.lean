/-
Copyright (c) 2021 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Gabriel Ebner
-/
import Mathlib.Tactic.RunTac

/-!
Additional `conv` tactics.
-/

namespace Mathlib.Tactic.Conv
open Lean Parser.Tactic Parser.Tactic.Conv

macro "try " t:convSeq : conv => `(conv| first | $t | skip)

macro (name := traceLHS) "traceLHS" : conv =>
  `(conv| trace_state) -- FIXME

syntax (name := convLHS) "convLHS" (" at " ident)? (" in " term)? " => " convSeq : tactic
macro_rules
  | `(tactic| convLHS $[at $id?]? $[in $pat?]? => $seq) =>
    `(tactic| conv $[at $id?]? $[in $pat?]? => lhs; ($seq:convSeq))

syntax (name := convRHS) "convRHS" (" at " ident)? (" in " term)? " => " convSeq : tactic
macro_rules
  | `(tactic| convRHS $[at $id?]? $[in $pat?]? => $seq) =>
    `(tactic| conv $[at $id?]? $[in $pat?]? => rhs; ($seq:convSeq))

macro "runConv" e:doSeq : conv => `(conv| tactic' => runTac $e)

macro (name := find) "find " pat:term " => " seq:convSeq : conv =>
  `(conv| conv => pattern $pat; ($seq:convSeq))
