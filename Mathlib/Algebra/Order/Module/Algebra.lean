/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Order.Module.Defs
import Mathlib.Tactic.Positivity.Core

/-!
# Ordered algebras

This file proves properties of algebras where both rings are ordered compatibly.

## TODO

`positivity` extension for `algebraMap`
-/

variable {α β : Type*} [CommSemiring α] [PartialOrder α]

section OrderedSemiring
variable (β)
variable [Semiring β] [PartialOrder β] [IsOrderedRing β] [Algebra α β] [SMulPosMono α β] {a : α}

@[gcongr, mono] lemma algebraMap_mono : Monotone (algebraMap α β) :=
  fun a₁ a₂ ha ↦ by
    simpa only [Algebra.algebraMap_eq_smul_one] using smul_le_smul_of_nonneg_right ha zero_le_one

lemma algebraMap_nonneg (ha : 0 ≤ a) : 0 ≤ algebraMap α β a := by simpa using algebraMap_mono β ha

end OrderedSemiring

section StrictOrderedSemiring
variable [Semiring β] [PartialOrder β] [IsStrictOrderedRing β] [Algebra α β]

section SMulPosMono
variable [SMulPosMono α β] [SMulPosReflectLE α β] {a₁ a₂ : α}

@[simp] lemma algebraMap_le_algebraMap : algebraMap α β a₁ ≤ algebraMap α β a₂ ↔ a₁ ≤ a₂ := by
  simp [Algebra.algebraMap_eq_smul_one]

end SMulPosMono

section SMulPosStrictMono
variable [SMulPosStrictMono α β] {a a₁ a₂ : α}
variable (β)

@[gcongr, mono] lemma algebraMap_strictMono : StrictMono (algebraMap α β) :=
  fun a₁ a₂ ha ↦ by
    simpa only [Algebra.algebraMap_eq_smul_one] using smul_lt_smul_of_pos_right ha zero_lt_one

lemma algebraMap_pos (ha : 0 < a) : 0 < algebraMap α β a := by
  simpa using algebraMap_strictMono β ha

variable {β}
variable [SMulPosReflectLT α β]

@[simp] lemma algebraMap_lt_algebraMap : algebraMap α β a₁ < algebraMap α β a₂ ↔ a₁ < a₂ := by
  simp [Algebra.algebraMap_eq_smul_one]

end SMulPosStrictMono
end StrictOrderedSemiring

namespace Mathlib.Meta.Positivity
open Lean Meta Qq Function

/-- Extension for `algebraMap`. -/
@[positivity algebraMap _ _ _]
def evalAlgebraMap : PositivityExt where eval {u β} _zβ _pβ e := do
  let ~q(@algebraMap $α _ $instα $instβ $instαβ $a) := e | throwError "not `algebraMap`"
  let pα ← synthInstanceQ q(PartialOrder $α)
  match ← core q(inferInstance) pα a with
  | .positive pa =>
    let _instαSemiring ← synthInstanceQ q(Semiring $α)
    let _instαPartialOrder ← synthInstanceQ q(PartialOrder $α)
    try
      let _instβSemiring ← synthInstanceQ q(Semiring $β)
      let _instβPartialOrder  ← synthInstanceQ q(PartialOrder $β)
      let _instβIsStrictOrderedRing ← synthInstanceQ q(IsStrictOrderedRing $β)
      let _instαβsmul ← synthInstanceQ q(SMulPosStrictMono $α $β)
      assertInstancesCommute
      return .positive q(algebraMap_pos $β $pa)
    catch _ =>
      let _instβSemiring ← synthInstanceQ q(Semiring $β)
      let _instβPartialOrder  ← synthInstanceQ q(PartialOrder $β)
      let _instβIsOrderedRing ← synthInstanceQ q(IsOrderedRing $β)
      let _instαβsmul ← synthInstanceQ q(SMulPosMono $α $β)
      assertInstancesCommute
      return .nonnegative q(algebraMap_nonneg $β <| le_of_lt $pa)
  | .nonnegative pa =>
    let _instαSemiring ← synthInstanceQ q(CommSemiring $α)
    let _instαPartialOrder ← synthInstanceQ q(PartialOrder $α)
    let _instβSemiring ← synthInstanceQ q(Semiring $β)
    let _instβPartialOrder  ← synthInstanceQ q(PartialOrder $β)
    let _instβIsOrderedRing ← synthInstanceQ q(IsOrderedRing $β)
    let _instαβsmul ← synthInstanceQ q(SMulPosMono $α $β)
    assertInstancesCommute
    return .nonnegative q(algebraMap_nonneg $β $pa)
  | _ => pure .none

example [Semiring β] [PartialOrder β] [IsOrderedRing β] [Algebra α β] [SMulPosMono α β]
    {a : α} (ha : 0 ≤ a) :
    0 ≤ algebraMap α β a := by positivity

example [Semiring β] [PartialOrder β] [IsOrderedRing β] [Algebra α β] [SMulPosMono α β]
    {a : α} (ha : 0 < a) :
    0 ≤ algebraMap α β a := by positivity

example [Semiring β] [PartialOrder β] [IsStrictOrderedRing β] [Algebra α β] [SMulPosStrictMono α β]
    {a : α} (ha : 0 < a) :
    0 < algebraMap α β a := by positivity

end Mathlib.Meta.Positivity
