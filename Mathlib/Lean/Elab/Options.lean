/-
Copyright (c) 2026 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
module

public import Lean.Data.KVMap

/-! # Additional utilities for managing `Options` -/

public section

namespace Lean

/--
Converts a `DataValue` that may appear as the value of some `set_option` to appropriate `Syntax`.
This only returns `some _` on user-writable `set_option` `DataValue`s (`.ofBool`, `.ofNat`,
`.ofString`) and `none` on the rest.

Note that the parser responsible for the option values is
```
def Parser.Command.optionValue :=
  nonReservedSymbol "true" <|> nonReservedSymbol "false" <|> strLit <|> numLit
```
but this is not a `leading_parser`, and creates no corresponding syntax node. Instead, syntax
quotations constructing a `set_option` expect a ``TSyntax [`str, `num]``.
-/
def DataValue.toSetOptionValueSyntax? : DataValue → Option (TSyntax [`str, `num])
  | .ofNat n      => some ⟨Syntax.mkNumLit (toString n)⟩
  | .ofBool b     => some ⟨Syntax.atom .none (toString b)⟩
  | .ofString str => some ⟨Syntax.mkStrLit str⟩
  | _ => none
