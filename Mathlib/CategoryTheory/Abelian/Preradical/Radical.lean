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
# Radicals of preradicals

In this file we define what it means for a preradical `Φ : Preradical C` on an
abelian category `C` to be *radical*, and we introduce a bundled `Radical C`
structure.

Following Stenström, a preradical `Φ` is called radical if it coincides with its self colon.
We encode this as the existence of an isomorphism `Φ.colon Φ ≅ Φ`.  We then prove a basic
characterization of radicals in terms of the vanishing of `Φ.r` on `Φ.quotient`.

## Main definitions

* `Preradical.IsRadical Φ` :
  The proposition that a preradical `Φ` is radical, i.e. that `(Φ.colon Φ) ≅ Φ`.

* `Preradical.Radical C` :
  The type of radicals on `C`, given by a preradical together with a proof
  that it is radical.

## Main results

* `Preradical.isRadical_iff_isZero_whisker` :
  A preradical `Φ` is radical if and only if `Φ.quotient ⋙ Φ.r` is the zero object.

## References

* [Bo Stenström, Rings and Modules of Quotients][stenstrom1971]
* [Bo Stenström, *Rings of Quotients*][stenstrom1975]

## Tags

preradical, radical, torsion theory, abelian
-/
@[expose] public section

namespace CategoryTheory.Abelian
open CategoryTheory.Limits

namespace Preradical

variable {C : Type*} [Category C] [Abelian C]

/-- A preradical `Φ` is *radical* if `Φ.colon Φ ≅ Φ`. -/
class IsRadical (Φ : Preradical C) : Prop where
  iso_self_colon : Nonempty ((Preradical.colon Φ Φ) ≅ Φ)

/-- A *radical* on `C` is a preradical together with a proof that it is radical
in the sense of `IsRadical`. -/
abbrev Radical := { Φ : Preradical C // IsRadical Φ }

open Functor

/-- A preradical `Φ` is radical if and only if it `Φ` vanishes on the quotient `Φ.quotient`. -/
theorem isRadical_iff {Φ : Preradical C} :
    IsRadical Φ ↔ IsZero (Φ.quotient ⋙ Φ.r) := by
  let g := Φ.quotient.whiskerLeft Φ.ι ≫ (rightUnitor _).hom
  constructor
  · intro h
    obtain ⟨μ⟩ := h.iso_self_colon
    refine IsZero.of_mono_eq_zero
      (Φ.quotient.whiskerLeft Φ.ι ≫ (rightUnitor _).hom)
      (zero_of_epi_comp (colonπ Φ Φ) ?_)
    calc
        _ = (colon Φ Φ).ι ≫ Φ.π := by
          simp [colonπ, Preradical.ι, Preradical.colon, ← pullback.condition]
        _ = (μ.hom.hom.left ≫ Φ.ι) ≫ Φ.π := by
          rw [MonoOver.w μ.hom]
        _ = 0 := by
          rw [Category.assoc, Φ.ι_π, comp_zero]
  · intro h
    constructor
    haveI := (isIso_toColon_iff.mpr h : IsIso (Φ.toColon Φ))
    exact ⟨(asIso (Φ.toColon Φ)).symm⟩

end Preradical

end CategoryTheory.Abelian
