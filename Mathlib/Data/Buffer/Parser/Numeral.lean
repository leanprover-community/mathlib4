/-
Copyright (c) 2020 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky

! This file was ported from Lean 3 source module data.buffer.parser.numeral
! leanprover-community/mathlib commit 2220b0cbab795e73674b8191170b0cc68c6b54a8
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Buffer.Parser.Basic

/-!
# Numeral parsers

This file expands on the existing `nat : parser ℕ` to provide parsers into any type `α` that
can be represented by a numeral, which relies on `α` having a 0, 1, and addition operation.
There are also convenience parsers that ensure that the numeral parsed in is not larger than
the cardinality of the type `α` , if it is known that `fintype α`. Additionally, there are
convenience parsers that parse in starting from "1", which can be useful for positive ordinals;
or parser from a given character or character range.

## Main definitions

* `parser.numeral` : The parser which uses `nat.cast`
  to map the result of `parser.nat` to the desired `α`
* `parser.numeral.of_fintype` :  The parser which `guard`s to make sure the parsed
  numeral is within the cardinality of the target `fintype` type `α`.

## Implementation details

When the `parser.numeral` or related parsers are invoked, the desired type is provided explicitly.
In many cases, it can be inferred, so one can write, for example
```lean
def get_fin : string → fin 5 :=
sum.elim (λ _, 0) id ∘ parser.run_string (parser.numeral.of_fintype _)
```

In the definitions of the parsers (except for `parser.numeral`), there is an
explicit `nat.bin_cast` instead an explicit or implicit `nat.cast`.
-/


open Parser ParseResult

namespace Parser

variable (α : Type) [Zero α] [One α] [Add α]

/-- Parse a string of digits as a numeral while casting it to target type `α`.
-/
def numeral : Parser α :=
  Nat.binCast <$> nat
deriving Mono, Bounded, Prog
#align parser.numeral Parser.numeral

/-- Parse a string of digits as a numeral while casting it to target type `α`,
which has a `[fintype α]` constraint. The parser ensures that the numeral parsed in
is within the cardinality of the type `α`.
-/
def numeral.ofFintype [Fintype α] : Parser α := do
  let c ← nat
  decorate_error (s! "<numeral less than {toString (Fintype.card α)}>") (guard (c < Fintype.card α))
  pure <| Nat.binCast c
deriving Mono, Bounded, Prog
#align parser.numeral.of_fintype Parser.numeral.ofFintype

/-- Parse a string of digits as a numeral while casting it to target type `α`. The parsing starts
at "1", so `"1"` is parsed in as `nat.cast 0`. Providing `"0"` to the parser causes a failure.
-/
def numeral.fromOne : Parser α := do
  let c ← nat
  decorate_error "<positive numeral>" (guard (0 < c))
  pure <| Nat.binCast (c - 1)
deriving Mono, Bounded, Prog
#align parser.numeral.from_one Parser.numeral.fromOne

/-- Parse a string of digits as a numeral while casting it to target type `α`,
which has a `[fintype α]` constraint. The parser ensures that the numeral parsed in
is within the cardinality of the type `α`. The parsing starts
at "1", so `"1"` is parsed in as `nat.cast 0`. Providing `"0"` to the parser causes a failure.
-/
def numeral.fromOne.ofFintype [Fintype α] : Parser α := do
  let c ← nat
  decorate_error (s! "<positive numeral less than or equal to {toString (Fintype.card α)}>")
      (guard (0 < c ∧ c ≤ Fintype.card α))
  pure <| Nat.binCast (c - 1)
deriving Mono, Bounded, Prog
#align parser.numeral.from_one.of_fintype Parser.numeral.fromOne.ofFintype

/-- Parse a character as a numeral while casting it to target type `α`,
The parser ensures that the character parsed in is within the bounds set by `fromc` and `toc`,
and subtracts the value of `fromc` from the parsed in character.
-/
def numeral.char (fromc toc : Char) : Parser α := do
  let c ←
    decorateError (s! "<char between '{fromc.toString }' to '{toc.toString}' inclusively>")
        (sat fun c => fromc ≤ c ∧ c ≤ toc)
  pure <| Nat.binCast (c - fromc)
deriving Mono, Bounded, ErrStatic, Step
#align parser.numeral.char Parser.numeral.char

/-- Parse a character as a numeral while casting it to target type `α`,
which has a `[fintype α]` constraint.
The parser ensures that the character parsed in is greater or equal to `fromc` and
and subtracts the value of `fromc` from the parsed in character. There is also a check
that the resulting value is within the cardinality of the type `α`.
-/
def numeral.char.ofFintype [Fintype α] (fromc : Char) : Parser α := do
  let c ←
    decorateError
        (s! "<char from '{fromc.toString}' to '
              {(Char.ofNat (fromc.toNat + Fintype.card α - 1)).toString}' inclusively>")
        (sat fun c => fromc ≤ c ∧ c.toNat - Fintype.card α < fromc.toNat)
  pure <| Nat.binCast (c - fromc)
deriving Mono, Bounded, ErrStatic, Step
#align parser.numeral.char.of_fintype Parser.numeral.char.ofFintype

/-! ## Specific numeral types -/


/-- Matches an integer, like `43` or `-2`.
Large numbers may cause performance issues, so don't run this parser on untrusted input.
-/
def int : Parser Int :=
  coe <$> nat <|> ch '-' >> Neg.neg <$> coe <$> nat
#align parser.int Parser.int

/-- Matches an rational number, like `43/1` or `-2/3`.
Requires that the negation is in the numerator,
and that both a numerator and denominator are provided (e.g. will not match `43`).
Large numbers may cause performance issues, so don't run this parser on untrusted input.
-/
def rat : Parser Rat :=
  (fun x y => ↑x / ↑y) <$> int <*> (ch '/' >> nat)
#align parser.rat Parser.rat

end Parser

