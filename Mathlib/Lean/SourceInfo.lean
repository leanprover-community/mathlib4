/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/

import Lean

/-!
# `SourceInfo`

Temporary file. Should be moved to core.
-/

namespace Lean


/--
Constructs a synthetic SourceInfo using a ref : Syntax for the span.

A variant of `SourceInfo.fromRef` in core; see also https://github.com/leanprover/lean4/pull/1620
-/
def SourceInfo.fromRef' (ref : Syntax) (synthetic := true) : SourceInfo :=
  match ref.getPos?, ref.getTailPos? with
  | some pos, some tailPos =>
    if synthetic then .synthetic pos tailPos
    else .original "".toSubstring pos "".toSubstring tailPos
  | _,        _            => .none
