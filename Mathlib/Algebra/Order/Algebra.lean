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
    (h : Monotone (algebraMap α β)) : IsOrderedModule α β where
  smul_le_smul_of_nonneg_left _ ha _ _ hb := by
    simpa [Algebra.smul_def] using mul_le_mul_of_nonneg_left hb (by simpa using h ha)
  smul_le_smul_of_nonneg_right _ ha _ _ hb := by
    simpa [Algebra.smul_def] using mul_le_mul_of_nonneg_right (h hb) ha

section OrderedSemiring
variable (β) [IsOrderedRing β] [SMulPosMono α β] {a : α}

@[gcongr, mono] lemma algebraMap_mono : Monotone (algebraMap α β) :=
  fun a₁ a₂ ha ↦ by
    simpa only [Algebra.algebraMap_eq_smul_one] using smul_le_smul_of_nonneg_right ha zero_le_one

lemma algebraMap_nonneg (ha : 0 ≤ a) : 0 ≤ algebraMap α β a := by simpa using algebraMap_mono β ha

end OrderedSemiring

theorem isOrderedModule_iff_algebraMap_mono [IsOrderedRing α] [IsOrderedRing β] :
    IsOrderedModule α β ↔ Monotone (algebraMap α β) where
  mp _ := algebraMap_mono _
  mpr := IsOrderedModule.of_algebraMap_mono

section StrictOrderedSemiring
variable [IsStrictOrderedRing β]

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
meta def evalAlgebraMap : PositivityExt where eval {u β} _zβ _pβ e := do
  let ~q(@algebraMap $α _ $instα $instβ $instαβ $a) := e | throwError "not `algebraMap`"
  let pα ← synthInstanceQ q(PartialOrder $α)
  match ← core q(inferInstance) pα a with
  | .positive pa =>
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
