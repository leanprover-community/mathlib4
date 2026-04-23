/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.SpectralSequence.ComplexShape
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.CategoryTheory.Reassoc
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
# Spectral sequences

In this file, we define the category `SpectralSequence C c r₀` of spectral sequences
in an abelian category `C` with `Eᵣ`-pages defined from `r₀ : ℤ` having differentials
given by complex shapes `c : ℤ → ComplexShape κ`, where `κ` is the index type
for the objects on each page (e.g. `κ := ℤ × ℤ` or `κ := ℕ × ℕ`).
A spectral sequence is defined as the data of a sequence of homological complexes
(the pages) and a sequence of isomorphisms between the homology of a page and the
next page.

-/

@[expose] public section

namespace CategoryTheory

open Category Limits

variable (C : Type*) [Category C] [Abelian C]
  {κ : Type*} (c : ℤ → ComplexShape κ) (r₀ : ℤ)

/-- Given an abelian category `C`, a sequence of complex shapes `c : ℤ → ComplexShape κ`
and a starting page `r₀ : ℤ`, a spectral sequence involves pages which are homological
complexes and isomorphisms saying that the homology of a page identifies to the next page. -/
structure SpectralSequence where
  /-- the `r`th page of a spectral sequence is an homological complex -/
  page (r : ℤ) (hr : r₀ ≤ r := by lia) : HomologicalComplex C (c r)
  /-- the isomorphism between the homology of the `r`-th page at an object `pq : κ`
  and the corresponding object on the next page -/
  iso (r r' : ℤ) (pq : κ) (hrr' : r + 1 = r' := by lia) (hr : r₀ ≤ r := by lia) :
    (page r).homology pq ≅ (page r').X pq

namespace SpectralSequence

variable {C c r₀}

/-- A morphism of spectral sequences is a sequence of morphisms between the
pages which commutes with the isomorphisms in homology. -/
@[ext]
structure Hom (E E' : SpectralSequence C c r₀) where
  /-- the morphism of homological complexes between the `r`th pages -/
  hom (r : ℤ) (hr : r₀ ≤ r := by lia) : E.page r ⟶ E'.page r
  comm (r r' : ℤ) (pq : κ) (hrr' : r + 1 = r' := by lia) (hr : r₀ ≤ r := by lia) :
    HomologicalComplex.homologyMap (hom r) pq ≫ (E'.iso r r' pq).hom =
      (E.iso r r' pq).hom ≫ (hom r').f pq := by cat_disch

/-- If `E` is a spectral sequence, and `r = r'`, this is the
isomorphism `(E.page r).X pq ≅ (E.page r').X pq`. -/
def pageXIsoOfEq (E : SpectralSequence C c r₀) (pq : κ) (r r' : ℤ) (h : r = r' := by lia)
    (hr : r₀ ≤ r := by lia) :
    (E.page r).X pq ≅ (E.page r').X pq :=
  eqToIso (by subst h; rfl)

attribute [reassoc (attr := simp)] Hom.comm

@[simps! id_hom comp_hom]
instance : Category (SpectralSequence C c r₀) where
  Hom := Hom
  id _ := { hom _ _ := 𝟙 _ }
  comp f g :=
    { hom r hr := f.hom r ≫ g.hom r
      comm r r' hrr' pq hr := by
        simp [HomologicalComplex.homologyMap_comp, assoc, g.comm r r', f.comm_assoc r r'] }

@[ext]
lemma hom_ext {E E' : SpectralSequence C c r₀} {f f' : E ⟶ E'}
    (h : ∀ (r : ℤ) (hr : r₀ ≤ r), f.hom r = f'.hom r) :
    f = f' :=
  Hom.ext (by grind)

attribute [simp] id_hom
attribute [reassoc, simp] comp_hom

variable (C c r₀)

/-- The functor `SpectralSequence C c r₀ ⥤ HomologicalComplex C (c r)` which
sends a spectral sequence to its `r`th page. -/
@[simps]
def pageFunctor (r : ℤ) (hr : r₀ ≤ r := by lia) :
    SpectralSequence C c r₀ ⥤ HomologicalComplex C (c r) where
  obj E := E.page r
  map f := f.hom r

/-- The natural isomorphism between the homology of a spectral sequence on the
object `pq : κ` of the `r`th page and the corresponding object on the next page. -/
@[simps!]
noncomputable def pageHomologyNatIso
    (r r' : ℤ) (pq : κ) (hrr' : r + 1 = r' := by lia) (hr : r₀ ≤ r := by lia) :
    pageFunctor C c r₀ r ⋙ HomologicalComplex.homologyFunctor _ _ pq ≅
      pageFunctor C c r₀ r' ⋙ HomologicalComplex.eval _ _ pq :=
  NatIso.ofComponents (fun E ↦ E.iso r r' pq)

end SpectralSequence

/-- A cohomological spectral sequence has differentials given by the
vector `(r, 1 - r)` on the `r`th page. -/
abbrev CohomologicalSpectralSequence :=
  SpectralSequence C (fun r ↦ ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ))

/-- A `E₂`-cohomological spectral sequence has differentials given by the
vector `(r, 1 - r)` on the `r`th page for `2 ≤ r`. -/
abbrev E₂CohomologicalSpectralSequence := CohomologicalSpectralSequence C 2

/-- A first quadrant cohomological spectral sequence has differentials
given by the vector `(r, 1 - r)` on the `r`th page. -/
abbrev CohomologicalSpectralSequenceNat :=
  SpectralSequence C (fun r ↦ ComplexShape.spectralSequenceNat ⟨r, 1 - r⟩)

/-- A first quadrant `E₂`-cohomological spectral sequence has differentials
given by the vector `(r, 1 - r)` on the `r`th page for `2 ≤ r`. -/
abbrev E₂CohomologicalSpectralSequenceNat :=
  CohomologicalSpectralSequenceNat C 2

/-- A cohomological spectral sequence lying on finitely many rows
has differentials given by the vector `(r, 1 - r)` on the `r`th page. -/
abbrev CohomologicalSpectralSequenceFin (l : ℕ) :=
  SpectralSequence C (fun r ↦ ComplexShape.spectralSequenceFin l ⟨r, 1 - r⟩)

/-- A `E₂`-cohomological spectral sequence lying on finitely many rows
has differentials given by the vector `(r, 1 - r)` on the `r`th page for `2 ≤ r`. -/
abbrev E₂CohomologicalSpectralSequenceFin (l : ℕ) :=
  CohomologicalSpectralSequenceFin C 2 l

end CategoryTheory
