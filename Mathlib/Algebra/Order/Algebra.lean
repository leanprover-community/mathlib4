/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Kim Morrison
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Order.Module.Defs
public import Mathlib.Tactic.Positivity.Core

/-!
# Ordered algebras

An ordered algebra is an ordered semiring, which is an algebra over an ordered commutative semiring,
for which scalar multiplication is "compatible" with the two orders.

The prototypical example is 2x2 matrices over the reals or complexes (or indeed any C^* algebra)
where the ordering the one determined by the positive cone of positive operators,
i.e. `A ≤ B` iff `B - A = star R * R` for some `R`.
(We don't yet have this example in mathlib.)

## Implementation

Because the axioms for an ordered algebra are exactly the same as those for the underlying
module being ordered, we don't actually introduce a new class, but just use the `IsOrderedModule`
and `IsStrictOrderedModule` mixins.

## Tags

ordered algebra

## TODO

`positivity` extension for `algebraMap`
-/

public section

variable {α β : Type*} [CommSemiring α] [PartialOrder α] [Semiring β] [PartialOrder β] [Algebra α β]

theorem IsOrderedModule.of_algebraMap_mono [PosMulMono β] [MulPosMono β]
    (h : Monotone (algebraMap α β)) : IsOrderedModule α β :=
  .of_smul_one_mono (by simpa [Algebra.smul_def] using h)

section ZeroLEOneClass
variable [ZeroLEOneClass β]

section SMulPosMono
variable (β) [SMulPosMono α β]

@[gcongr, mono]
lemma algebraMap_mono : Monotone (algebraMap α β) := by
  simpa [Algebra.smul_def] using smul_one_mono (α := α) β

lemma algebraMap_nonneg {a : α} (ha : 0 ≤ a) : 0 ≤ algebraMap α β a := by
  simpa using algebraMap_mono β ha

end SMulPosMono

theorem isOrderedModule_iff_algebraMap_mono [PosMulMono β] [MulPosMono β] :
    IsOrderedModule α β ↔ Monotone (algebraMap α β) := by
  simp [isOrderedModule_iff_smul_one_mono, Algebra.smul_def]

section Nontrivial
variable [Nontrivial β]

@[simp]
lemma algebraMap_le_algebraMap [SMulPosMono α β] [SMulPosReflectLE α β] {a₁ a₂ : α} :
    algebraMap α β a₁ ≤ algebraMap α β a₂ ↔ a₁ ≤ a₂ := by
  simp [Algebra.algebraMap_eq_smul_one]

section SMulPosStrictMono
variable (β) [SMulPosStrictMono α β]

@[gcongr, mono]
lemma algebraMap_strictMono : StrictMono (algebraMap α β) := by
  simpa [Algebra.smul_def] using smul_one_strictMono (α := α) β

lemma algebraMap_pos {a : α} (ha : 0 < a) : 0 < algebraMap α β a := by
  simpa using algebraMap_strictMono β ha

variable {β} in
@[simp]
lemma algebraMap_lt_algebraMap [SMulPosReflectLT α β] {a₁ a₂ : α} :
    algebraMap α β a₁ < algebraMap α β a₂ ↔ a₁ < a₂ := by
  simp [Algebra.algebraMap_eq_smul_one]

end SMulPosStrictMono
end Nontrivial
end ZeroLEOneClass

namespace Mathlib.Meta.Positivity
open Lean Meta Qq Function

/-- Extension for `algebraMap`. -/
@[positivity algebraMap _ _ _]
meta def evalAlgebraMap : PositivityExt where eval {u β} _zβ pβ? e := do
  let ~q(@algebraMap $α _ $instα $instβ $instαβ $a) := e | throwError "not `algebraMap`"
  let pα ← try? <| synthInstanceQ q(PartialOrder $α)
  match ← core q(inferInstance) pα a with
  | .positive pa =>
    let some _ := pβ? | pure .none
    let _instαSemiring ← synthInstanceQ q(Semiring $α)
    let _instαPartialOrder ← synthInstanceQ q(PartialOrder $α)
    try
      let _instβSemiring ← synthInstanceQ q(Semiring $β)
      let _instβPartialOrder ← synthInstanceQ q(PartialOrder $β)
      let _instβIsStrictOrderedRing ← synthInstanceQ q(IsStrictOrderedRing $β)
      let _instαβsmul ← synthInstanceQ q(SMulPosStrictMono $α $β)
      assertInstancesCommute
      return .positive q(algebraMap_pos $β $pa)
    catch _ =>
      let _instβSemiring ← synthInstanceQ q(Semiring $β)
      let _instβPartialOrder ← synthInstanceQ q(PartialOrder $β)
      let _instβIsOrderedRing ← synthInstanceQ q(IsOrderedRing $β)
      let _instαβsmul ← synthInstanceQ q(SMulPosMono $α $β)
      assertInstancesCommute
      return .nonnegative q(algebraMap_nonneg $β <| le_of_lt $pa)
  | .nonnegative pa =>
    let some _ := pβ? | pure .none
    let _instαSemiring ← synthInstanceQ q(CommSemiring $α)
    let _instαPartialOrder ← synthInstanceQ q(PartialOrder $α)
    let _instβSemiring ← synthInstanceQ q(Semiring $β)
    let _instβPartialOrder ← synthInstanceQ q(PartialOrder $β)
    let _instβIsOrderedRing ← synthInstanceQ q(IsOrderedRing $β)
    let _instαβsmul ← synthInstanceQ q(SMulPosMono $α $β)
    assertInstancesCommute
    return .nonnegative q(algebraMap_nonneg $β $pa)
  | _ => pure .none

example [IsOrderedRing β] [SMulPosMono α β]
    {a : α} (ha : 0 ≤ a) :
    0 ≤ algebraMap α β a := by positivity

example [IsOrderedRing β] [SMulPosMono α β]
    {a : α} (ha : 0 < a) :
    0 ≤ algebraMap α β a := by positivity

example [IsStrictOrderedRing β] [SMulPosStrictMono α β]
    {a : α} (ha : 0 < a) :
    0 < algebraMap α β a := by positivity

end Mathlib.Meta.Positivity
