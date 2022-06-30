/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
import Lean

namespace Lean

def TSyntax.replaceM [Monad M] (f : Syntax → M (Option Syntax)) (stx : TSyntax k) : M (TSyntax k) :=
  .mk <$> stx.1.replaceM f

def Syntax.TSepArray.ofElems (elems : Array (TSyntax k)) : TSepArray k sep :=
  .mk (SepArray.ofElems (sep := sep) elems).1
