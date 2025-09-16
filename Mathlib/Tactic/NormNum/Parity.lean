/-
Copyright (c) 2025 Concordance Inc. dba Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Tactic.NormNum.Core

/-!
# `norm_num` extensions for `Even` and `Odd`

In this file we provide `norm_num` extensions for `Even n` and `Odd n`,
where `n : ℕ` or `n : ℤ`.
-/

namespace Mathlib.Meta.NormNum

open Qq

/-- `norm_num` extension for `Even`.

Works for `ℕ` and `ℤ`. -/
@[norm_num Even _]
def evalEven : NormNumExt where eval {u αP} e := do
  match u, αP, e with
  | 0, ~q(Prop), ~q(@Even ℕ _ $a) =>
    assertInstancesCommute
    let ⟨b, r⟩ ← deriveBoolOfIff q($a % 2 = 0) q(Even $a) q((@Nat.even_iff $a).symm)
    return .ofBoolResult r
  | 0, ~q(Prop), ~q(@Even ℤ _ $a) =>
    assertInstancesCommute
    let ⟨b, r⟩ ← deriveBoolOfIff q($a % 2 = 0) q(Even $a) q((@Int.even_iff $a).symm)
    return .ofBoolResult r
  | _, _, _ => failure

/-- `norm_num` extension for `Odd`.

Works for `ℕ` and `ℤ`. -/
@[norm_num Odd _]
def evalOdd : NormNumExt where eval {u αP} e := do
  match u, αP, e with
  | 0, ~q(Prop), ~q(@Odd ℕ $inst $a) =>
    assertInstancesCommute
    let ⟨b, r⟩ ← deriveBoolOfIff q($a % 2 = 1) q(Odd $a) q((@Nat.odd_iff $a).symm)
    return .ofBoolResult r
  | 0, ~q(Prop), ~q(@Odd ℤ $inst $a) =>
    assertInstancesCommute
    let ⟨b, r⟩ ← deriveBoolOfIff q($a % 2 = 1) q(Odd $a) q((@Int.odd_iff $a).symm)
    return .ofBoolResult r
  | _ => failure

end Mathlib.Meta.NormNum
