/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Lean
import Mathlib.Tactic.Lint.Basic

open Lean Parser

@[termParser default+1] def command.quot : Parser :=
  leading_parser "`(command|" >> incQuotDepth commandParser >> ")"

attribute [nolint docBlame] command.quot command.quot.parenthesizer command.quot.formatter

elab_stx_quot command.quot
