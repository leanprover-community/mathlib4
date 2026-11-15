/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Runtian Zhou
-/
module

public import Mathlib.Init

/-!
# `Quote` instances for `Int` and `Rat`

Lean core provides `Quote Nat`, which turns a natural number into a numeral.
This file provides the analogous instances for `Int` and `Rat`,
so that tactics can turn a computed number into syntax, e.g. for a "Try this" suggestion.

Like `Quote Nat`, these instances produce numerals without a type ascription:
`quote (-7 / 2 : ℚ)` is the syntax `-7 / 2`, not `(-7 / 2 : ℚ)`.
The resulting term is therefore elaborated at the expected type (for example `ℝ`),
and denotes the original number in any field of characteristic zero. In other types it may
not: in `ℤ`, `/` is integer division, so `-7 / 2` denotes `-4`,
and in `ℕ` a negative numeral does not elaborate at all.
-/

public meta section

namespace Mathlib
open Lean

/-- Quote an integer as a numeral, e.g. `-7`. -/
instance instQuoteInt : Quote Int where
  quote
  | .ofNat n => quote n
  | .negSucc n => Unhygienic.run `(-$(quote (n + 1)))

/-- Quote a rational number as a numeral or a quotient of numerals, e.g. `-7 / 2`. -/
instance instQuoteRat : Quote Rat where
  quote q :=
    if q.den = 1 then quote q.num
    else Unhygienic.run `($(quote q.num) / $(quote q.den))

end Mathlib
