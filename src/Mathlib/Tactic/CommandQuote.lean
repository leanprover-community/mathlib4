/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Lean

namespace Lean

@[termParser default+1] def Parser.Term.Command.quot : Parser :=
  leading_parser "`(command|" >> incQuotDepth commandParser >> ")"

@[termElab Command.quot] def Elab.Term.elabCommandQuot : TermElab :=
  adaptExpander Quotation.stxQuot.expand
