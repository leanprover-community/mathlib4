/-
Copyright (c) 2026 Justin Mu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justin Mu, Zhan Shi, Annie Yao, Niels Voss, Jasper van de Kreeke, Marco David
-/
module

public import Mathlib.Algebra.Module.End
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.ZMod.IntUnitsPower

/-!
# Gradings for A∞-categories

This file introduces the grading data needed to write down A∞-structures.

The grading `β` of an A∞-category is an abelian group of degrees. We need two pieces of
additional structure:

* a distinguished *degree one* `degOne : β`, the degree of the differential; a degree `d` is
  *shifted by* an integer `n` by adding `n • degOne`;
* a *Koszul sign character* `β →+ Additive ℤˣ`, read as the map d ↦ (-1)^d.

They are compatible in that degree `degOne` is odd (i.e. the degree of the
differential is odd).

## Main definitions

* `AInfinity.Grading β`: a grading structure on the abelian group `β`.

## Implementation notes

Integer shifts are written with the `ℤ`-action `n • degOne` rather than through a cast
`ℤ → β`, so that integer literals are never elaborated in `β`. Global instances are provided for
the standard gradings `ℤ` and `ZMod 2`.

`Grading β` is a mixin over `AddCommGroup β` rather than an extension of
`AddCommGroupWithOne β`. The degree one is a named element `degOne` instead of the numeral `1`
because it need not behave like a unit. On a product grading `β × γ` (e.g. a bigrading) the
natural choice is often `(degOne, 0)`, which shifts only the first cohomological degree,
rather than the `(1, 1)` that Mathlib's product instance would supply automatically.
-/

namespace AInfinity

universe v

variable (β : Type v)

/-- A grading on an abelian group of degrees `β` is a distinguished degree one `degOne : β`, the
degree of the differential, together with a Koszul sign character `sign : β →+ Additive ℤˣ` for
which `degOne` is odd. -/
public class Grading (β : Type*) [AddCommGroup β] where
  /-- The degree one. Integer degree shifts are its multiples `n • degOne`. -/
  degOne : β
  /-- The Koszul sign character, written additively. -/
  sign : β →+ Additive ℤˣ
  /-- The degree one is odd. -/
  sign_degOne : sign degOne = Additive.ofMul (-1)

export Grading (degOne sign)

variable {β}

section Grading

variable [AddCommGroup β] [Grading β]

/-- The sign of an integer degree shift is `Int.negOnePow`. -/
@[simp]
public lemma sign_zsmul_degOne (n : ℤ) : sign (n • degOne : β) = Int.negOnePow n := by
  rw [map_zsmul, Grading.sign_degOne, ← ofMul_zpow, Int.negOnePow_def]
  rfl

end Grading

namespace Grading

/-! ### Instances

Global instances for the two standard gradings `ℤ` and `ZMod 2`. -/

/-- The integers, graded by themselves: the degree one is `1` and the sign of `n` is
(-1)^n. -/
public instance : Grading ℤ where
  degOne := 1
  sign := zmultiplesHom (Additive ℤˣ) (Additive.ofMul (-1))
  sign_degOne := one_zsmul _

@[simp]
public lemma degOne_int : (degOne : ℤ) = 1 := rfl

/-- The parity grading `ZMod 2`: the degree one is `1` and the sign of a parity `p` is
(-1)^p, using the power operation on `ℤˣ` by `ZMod 2`. -/
public instance : Grading (ZMod 2) where
  degOne := 1
  sign := (smulAddHom (ZMod 2) (Additive ℤˣ)).flip (Additive.ofMul (-1))
  sign_degOne := by
    simp only [AddMonoidHom.flip_apply, smulAddHom_apply, one_smul]

@[simp]
public lemma degOne_zmod_two : (degOne : ZMod 2) = 1 := rfl

end Grading

/-! ### Koszul signs in the standard gradings -/

@[simp]
public lemma sign_int (n : ℤ) : sign n = Int.negOnePow n := rfl

/-- In the parity grading, `sign` is the power operation on `ℤˣ` by `ZMod 2`. -/
public lemma sign_zmod_two (p : ZMod 2) : sign p = (-1 : ℤˣ) ^ p := rfl

end AInfinity
