/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Init
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

/-!

# Characteristic of intermediate fields

This file contains some convenient instances for determining the characteristic of
intermediate fields. Some char zero instances are not provided, since they are already
covered by `SubsemiringClass.instCharZero`.

-/

@[expose] public section

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

namespace IntermediateField

variable (L : IntermediateField F E) (p : ℕ)

instance charZero [CharZero F] : CharZero L :=
  charZero_of_injective_algebraMap (algebraMap F _).injective

instance charP [CharP F p] : CharP L p :=
  charP_of_injective_algebraMap (algebraMap F _).injective p

instance expChar [ExpChar F p] : ExpChar L p :=
  expChar_of_injective_algebraMap (algebraMap F _).injective p

instance charP' [CharP E p] : CharP L p := Subfield.charP L.toSubfield p

instance expChar' [ExpChar E p] : ExpChar L p := Subfield.expChar L.toSubfield p

end IntermediateField
