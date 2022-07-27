/-
Copyright (c) 2021 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
import Mathlib.Tactic.RunTac

/-!
Additional `conv` tactics.
-/

namespace Mathlib.Tactic.Conv
open Lean Parser.Tactic Parser.Tactic.Conv

macro "try " t:convSeq : conv => `(conv| first | $t | skip)

macro (name := traceLHS) "trace_lhs" : conv =>
  `(conv| trace_state) -- FIXME

syntax (name := convLHS) "conv_lhs" (" at " ident)? (" in " term)? " => " convSeq : tactic
macro_rules
  | `(tactic| conv_lhs $[at $id?]? $[in $pat?]? => $seq) =>
    `(tactic| conv $[at $id?]? $[in $pat?]? => lhs; ($seq:convSeq))

syntax (name := convRHS) "conv_rhs" (" at " ident)? (" in " term)? " => " convSeq : tactic
macro_rules
  | `(tactic| conv_rhs $[at $id?]? $[in $pat?]? => $seq) =>
    `(tactic| conv $[at $id?]? $[in $pat?]? => rhs; ($seq:convSeq))

macro "run_conv" e:doSeq : conv => `(conv| tactic' => run_tac $e)

macro (name := find) "find " pat:term " => " seq:convSeq : conv =>
  `(conv| conv => pattern $pat; ($seq:convSeq))
