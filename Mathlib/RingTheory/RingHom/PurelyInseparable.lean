/-
Copyright (c) 2026 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.LocalProperties.Basic

/-!
# Purely inseparable ring homomorphisms

In this file we define purely inseparable ring homomorphisms and show their meta properties.

Since purely inseparable is mainly used for fields, we cannot prove many
general ring hom properties. E.g. we can't prove `StableUnderComposition IsPurelyInseparable`,
since `IsPurelyInseparable.trans` requires the involved rings to be fields.

-/

@[expose] public section

universe u v

/-- A ring homomorphism `f : F →+* E` is purely inseparable if `E` is purely inseparable as an
`F`-algebra. -/
@[algebraize IsPurelyInseparable]
protected def RingHom.IsPurelyInseparable
    {F : Type u} {E : Type v} [CommRing F] [CommRing E] (f : F →+* E) : Prop :=
  letI : Algebra F E := f.toAlgebra
  IsPurelyInseparable F E

lemma RingHom.isPurelyInseparable_algebraMap_iff
    {F : Type u} {E : Type v} [CommRing F] [CommRing E] [Algebra F E] :
    (algebraMap F E).IsPurelyInseparable ↔ IsPurelyInseparable F E := by
  rw [RingHom.IsPurelyInseparable, toAlgebra_algebraMap]

namespace RingHom.IsPurelyInseparable

variable {F E K : Type*}

variable (F) in
/-- The identity of a ring is purely inseparable. -/
lemma id [CommRing F] : RingHom.IsPurelyInseparable (RingHom.id F) :=
  isPurelyInseparable_self F

lemma containsIdentities : ContainsIdentities RingHom.IsPurelyInseparable := id

/-- Composition of purely inseparable ring homomorphisms between fields is purely inseparable. -/
lemma comp [Field F] [Field E] [Field K] {f : F →+* E} {g : E →+* K}
    (hf : f.IsPurelyInseparable) (hg : g.IsPurelyInseparable) :
    (g.comp f).IsPurelyInseparable := by
  algebraize [f, g, g.comp f]
  exact IsPurelyInseparable.trans F E K

end RingHom.IsPurelyInseparable
