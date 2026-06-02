/-
Copyright (c) 2026 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.LocalProperties.Basic

/-!
# Flat ring homomorphisms

In this file we define purely inseparable ring homomorphisms and show their meta properties.

-/

@[expose] public section

universe u v

/-- A ring homomorphism `f : R →+* S` is flat if `S` is flat as an `R` module. -/
@[algebraize IsPurelyInseparable]
def RingHom.IsPurelyInseparable
    {F : Type u} {E : Type v} [CommRing F] [CommRing E] (f : F →+* E) : Prop :=
  letI : Algebra F E := f.toAlgebra
  _root_.IsPurelyInseparable F E

lemma RingHom.isPurelyInseparable_algebraMap_iff
    {F : Type u} {E : Type v} [CommRing F] [CommRing E] [Algebra F E] :
    (algebraMap F E).IsPurelyInseparable ↔ _root_.IsPurelyInseparable F E := by
  rw [RingHom.IsPurelyInseparable, toAlgebra_algebraMap]

namespace RingHom.IsPurelyInseparable

variable {F E K : Type*}

variable (F) in
/-- The identity of a ring is flat. -/
lemma id [CommRing F] : RingHom.IsPurelyInseparable (RingHom.id F) :=
  isPurelyInseparable_self F

/-- Composition of flat ring homomorphisms is flat. -/
lemma comp [Field F] [Field E] [Field K] {f : F →+* E} {g : E →+* K}
    (hf : f.IsPurelyInseparable) (hg : g.IsPurelyInseparable) :
    IsPurelyInseparable (g.comp f) := by
  algebraize [f, g, (g.comp f)]
  exact _root_.IsPurelyInseparable.trans F E K

lemma containsIdentities : ContainsIdentities IsPurelyInseparable := id

/- lemma stableUnderComposition : StableUnderComposition IsPurelyInseparable := by -/
/-   introv R hf hg -/
/-   exact hf.comp hg -/

/- lemma respectsIso : RespectsIso IsPurelyInseparable := by -/
/-   apply stableUnderComposition.respectsIso -/
/-   introv -/
/-   exact of_bijective e.bijective -/

end RingHom.IsPurelyInseparable
