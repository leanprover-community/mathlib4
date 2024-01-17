/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
import Lean.Syntax

/-!
# Helper functions for working with typed syntaxes.
-/

set_option autoImplicit true

namespace Lean

/--
Applies the given function to every subsyntax.

Like `Syntax.replaceM` but for typed syntax.
-/
def TSyntax.replaceM [Monad M] (f : Syntax → M (Option Syntax)) (stx : TSyntax k) : M (TSyntax k) :=
  .mk <$> stx.1.replaceM f

/--
Constructs a typed separated array from elements.
The given array does not include the separators.

Like `Syntax.SepArray.ofElems` but for typed syntax.
-/
def Syntax.TSepArray.ofElems {sep} (elems : Array (TSyntax k)) : TSepArray k sep :=
  .mk (SepArray.ofElems (sep := sep) elems).1
