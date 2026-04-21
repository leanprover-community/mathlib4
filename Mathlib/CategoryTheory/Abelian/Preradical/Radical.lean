/-
Copyright (c) 2026 Blake Farman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Blake Farman
-/
module

public import Mathlib.CategoryTheory.Abelian.Preradical.Basic
public import Mathlib.CategoryTheory.Abelian.Preradical.Colon
public import Mathlib.CategoryTheory.Abelian.FunctorCategory

/-!
# Radicals

In this file we define what it means for a preradical `Φ : Preradical C` on an
abelian category `C` to be *radical*, and we define `Radical C` as the full
subcategory of `Preradical C` consisting of radicals.

Following Stenström, a preradical `Φ` is called radical if it coincides with its self colon.
We encode this as the property that the natural transformation `toColon Φ Φ : Φ ⟶ Φ.colon Φ`
is an isomorphism, and we prove a basic characterization of radicals in terms
of the vanishing of `Φ.r` on `Φ.quotient`.


## Main definitions

* `Preradical.IsRadical` :
  The property that a preradical `Φ` is radical, i.e. that `(Φ.colon Φ) ≅ Φ`.

* `Radical C` :
  The type of radicals on `C`, as a full subcategory of `Preradical C`.

## Main results

* `Preradical.isRadical_iff_isZero` :
  A preradical `Φ` is radical if and only if `Φ.quotient ⋙ Φ.r` is the zero object.

## References

* [Bo Stenström, Rings and Modules of Quotients][stenstrom1971]
* [Bo Stenström, *Rings of Quotients*][stenstrom1975]

## Tags

preradical, radical, torsion theory, abelian
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

namespace CategoryTheory.Abelian
open CategoryTheory.Limits

variable {C : Type*} [Category* C] [Abelian C]

namespace Preradical

variable (C)
/-- A preradical `Φ` is *radical* if `Φ.colon Φ ≅ Φ`. -/
def isRadical : ObjectProperty (Preradical C) :=
  fun Φ ↦ IsIso (toColon Φ Φ)

lemma isRadical_iff_isIso (Φ : Preradical C) :
    isRadical C Φ ↔ IsIso (toColon Φ Φ) :=
  Iff.rfl

/-- A preradical `Φ` is radical if and only if it `Φ` vanishes on the quotient `Φ.quotient`. -/
lemma isRadical_iff_isZero (Φ : Preradical C) :
    isRadical C Φ ↔ IsZero (Φ.quotient ⋙ Φ.r) := by
  rw [isRadical_iff_isIso, isIso_toColon_iff]

end Preradical

variable (C) in
/-- The category of radicals on `C`, defined as the full subcategory of
`Preradical C` consisting of preradicals `Φ` such that `toColon Φ Φ` is an isomorphism. -/
abbrev Radical := (Preradical.isRadical C).FullSubcategory

namespace Radical

instance (Φ : Radical C) : IsIso (Preradical.toColon Φ.obj Φ.obj) := Φ.property

lemma isZero (Φ : Radical C) : IsZero (Φ.obj.quotient ⋙ Φ.obj.r) := by
  rw [← Preradical.isRadical_iff_isZero, Preradical.isRadical_iff_isIso]
  infer_instance

end Radical

end CategoryTheory.Abelian
