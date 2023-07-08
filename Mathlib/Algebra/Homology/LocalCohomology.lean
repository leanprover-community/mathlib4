/-
Copyright (c) 2023 Emily Witt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emily Witt, Scott Morrison, Jake Levinson, Sam van Gool

! This file was ported from Lean 3 source module algebra.homology.local_cohomology
! leanprover-community/mathlib commit 5a684ce82399d820475609907c6ef8dba5b1b97c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.RingTheory.Finiteness

/-!
# Local cohomology.

This file defines the `i`-th local cohomology module of an `R`-module `M` with support in an
ideal `I` of `R`, where `R` is a commutative ring, as the direct limit of Ext modules:

Given a collection of ideals cofinal with the powers of `I`, consider the directed system of
quotients of `R` by these ideals, and take the direct limit of the system induced on the `i`-th
Ext into `M`.  One can, of course, take the collection to simply be the integral powers of `I`.

## References

* [M. Hochster, *Local cohomology*][hochsterunpublished]
  <https://dept.math.lsa.umich.edu/~hochster/615W22/lcc.pdf>
* [R. Hartshorne, *Local cohomology: A seminar given by A. Grothendieck*][hartshorne61]
* [M. Brodmann and R. Sharp, *Local cohomology: An algebraic introduction with geometric
  applications*][brodmannsharp13]
* [S. Iyengar, G. Leuschke, A. Leykin, Anton, C. Miller, E. Miller, A. Singh, U. Walther,
  *Twenty-four hours of local cohomology*][iyengaretal13]

## Tags

local cohomology, local cohomology modules

## Future work

* Prove that this definition is equivalent to:
    * the right-derived functor definition
    * the characterization as the limit of Koszul homology
    * the characterization as the cohomology of a Cech-like complex
* Prove that local cohomology depends only on the radical of the ideal
* Establish long exact sequence(s) in local cohomology
-/


open Opposite

open CategoryTheory

open CategoryTheory.Limits

noncomputable section

universe u v

namespace localCohomology

-- We define local cohomology, implemented as a direct limit of `Ext(R/J, -)`.
section

variable {R : Type u} [CommRing R] {D : Type v} [SmallCategory D]

/-- The directed system of `R`-modules of the form `R/J`, where `J` is an ideal of `R`,
determined by the functor `I`  -/
def ringModIdeals (I : D ⥤ Ideal R) : D ⥤ ModuleCat.{u} R where
  obj t := ModuleCat.of R <| R ⧸ I.obj t
  map w := Submodule.mapQ _ _ LinearMap.id (I.map w).down.down
  -- Porting note: was 'obviously'
  map_comp f g := by apply Submodule.linearMap_qext; rfl
#align local_cohomology.ring_mod_ideals localCohomology.ringModIdeals

-- Porting note: TODO:  Once this file is ported, move this instance to the right location.
instance moduleCat_enoughProjectives' : EnoughProjectives (ModuleCat.{u} R) :=
  ModuleCat.moduleCat_enoughProjectives.{u}
set_option linter.uppercaseLean3 false in
#align local_cohomology.Module_enough_projectives' localCohomology.moduleCat_enoughProjectives'

/-- The diagram we will take the colimit of to define local cohomology, corresponding to the
directed system determined by the functor `I` -/
def diagram (I : D ⥤ Ideal R) (i : ℕ) : Dᵒᵖ ⥤ ModuleCat.{u} R ⥤ ModuleCat.{u} R :=
  (ringModIdeals I).op ⋙ Ext R (ModuleCat.{u} R) i
#align local_cohomology.diagram localCohomology.diagram

end

section

-- We momentarily need to work with a type inequality, as later we will take colimits
-- along diagrams either in Type, or in the same universe as the ring, and we need to cover both.
variable {R : Type max u v} [CommRing R] {D : Type v} [SmallCategory D]

/-
In this definition we do not assume any special property of the diagram `I`, but the relevant case
will be where `I` is (cofinal with) the diagram of powers of a single given ideal.

Below, we give two equivalent (to be shown) definitions of the usual local cohomology with support
in an ideal `J`, `localCohomology` and `localCohomology.ofSelfLERadical`.

TODO: Show that any functor cofinal with `I` gives the same result.
 -/
/-- `localCohomology.ofDiagram I i` is the functor sending a module `M` over a commutative
ring `R` to the direct limit of `Ext^i(R/J, M)`, where `J` ranges over a collection of ideals
of `R`, represented as a functor `I`. -/
def ofDiagram (I : D ⥤ Ideal R) (i : ℕ) : ModuleCat.{max u v} R ⥤ ModuleCat.{max u v} R :=
  colimit (diagram.{max u v, v} I i)
#align local_cohomology.of_diagram localCohomology.ofDiagram

end

section Diagrams

variable {R : Type u} [CommRing R]

/-- The functor sending a natural number `i` to the `i`-th power of the ideal `J` -/
def idealPowersDiagram (J : Ideal R) : ℕᵒᵖ ⥤ Ideal R where
  obj t := J ^ unop t
  map w := ⟨⟨Ideal.pow_le_pow w.unop.down.down⟩⟩
#align local_cohomology.ideal_powers_diagram localCohomology.idealPowersDiagram

/-- The full subcategory of all ideals with radical containing `J` -/
def SelfLERadical (J : Ideal R) : Type u :=
  FullSubcategory fun J' : Ideal R => J ≤ J'.radical
--deriving Category

-- Porting note: `deriving Category` is not able to derive this instance
instance (J : Ideal R) : Category (SelfLERadical J) :=
  (FullSubcategory.category _)

#align local_cohomology.self_le_radical localCohomology.SelfLERadical

instance SelfLERadical.inhabited (J : Ideal R) : Inhabited (SelfLERadical J)
    where default := ⟨J, Ideal.le_radical⟩
#align local_cohomology.self_le_radical.inhabited localCohomology.SelfLERadical.inhabited

/-- The diagram of all ideals with radical containing `J`, represented as a functor.
This is the "largest" diagram that computes local cohomology with support in `J`. -/
def selfLERadicalDiagram (J : Ideal R) : SelfLERadical J ⥤ Ideal R :=
  fullSubcategoryInclusion _
#align local_cohomology.self_le_radical_diagram localCohomology.selfLERadicalDiagram

end Diagrams

end localCohomology

/-! We give two models for the local cohomology with support in an ideal `J`: first in terms of
the powers of `J` (`local_cohomology`), then in terms of *all* ideals with radical
containing `J` (`local_cohomology.ofSelfLERadical`). -/


section ModelsForLocalCohomology

open localCohomology

variable {R : Type u} [CommRing R]

/-- `localCohomology J i` is `i`-th the local cohomology module of a module `M` over
a commutative ring `R` with support in the ideal `J` of `R`, defined as the direct limit
of `Ext^i(R/J^t, M)` over all powers `t : ℕ`. -/
def localCohomology (J : Ideal R) (i : ℕ) : ModuleCat.{u} R ⥤ ModuleCat.{u} R :=
  ofDiagram (idealPowersDiagram J) i
#align local_cohomology localCohomology

/-- Local cohomology as the direct limit of `Ext^i(R/J', M)` over *all* ideals `J'` with radical
containing `J`. -/
def localCohomology.ofSelfLERadical (J : Ideal R) (i : ℕ) : ModuleCat.{u} R ⥤ ModuleCat.{u} R :=
  ofDiagram.{u} (selfLERadicalDiagram.{u} J) i
#align local_cohomology.of_self_le_radical localCohomology.ofSelfLERadical

/- TODO: Construct `localCohomology J i ≅ localCohomology.ofSelfLERadical J i`. Use this to
show that local cohomology depends only on `J.radical`. -/
end ModelsForLocalCohomology

section LocalCohomologyEquiv

open localCohomology

variable {R : Type u} [CommRing R] (I J : Ideal R)

/-- Lifting `idealPowersDiagram J` from a diagram valued in `ideals R` to a diagram
valued in `SelfLERadical J`. -/
def localCohomology.idealPowersToSelfLERadical (J : Ideal R) : ℕᵒᵖ ⥤ SelfLERadical J :=
  FullSubcategory.lift _ (idealPowersDiagram J) fun k => by
    change _ ≤ (J ^ unop k).radical
    cases' unop k with n
    · simp [Ideal.radical_top, pow_zero, Ideal.one_eq_top, le_top, Nat.zero_eq]
    · simp only [J.radical_pow _ n.succ_pos, Ideal.le_radical]
#align local_cohomology.ideal_powers_to_self_le_radical localCohomology.idealPowersToSelfLERadical

/-- The composition with the inclusion into `ideals R` is isomorphic to `idealPowersDiagram J`. -/
def localCohomology.idealPowersToSelfLERadicalCompInclusion (J : Ideal R) :
    localCohomology.idealPowersToSelfLERadical J ⋙ selfLERadicalDiagram J ≅ idealPowersDiagram J :=
  FullSubcategory.lift_comp_inclusion _ _ _
#align local_cohomology.ideal_powers_to_self_le_radical_comp_inclusion localCohomology.idealPowersToSelfLERadicalCompInclusion

/-- The lemma below essentially says that `idealPowersToSelfLERadical I` is initial in
`selfLERadicalDiagram I`.

Porting note: This lemma should probably be moved to `Mathlib/RingTheory/Finiteness.lean`
to be near `Ideal.exists_radical_pow_le_of_fg`, which it generalizes. -/
theorem Ideal.exists_pow_le_of_le_radical_of_fg (hIJ : I ≤ J.radical) (hJ : J.radical.FG) :
    ∃ k : ℕ, I ^ k ≤ J := by
  obtain ⟨k, hk⟩ := J.exists_radical_pow_le_of_fg hJ
  use k
  calc
    I ^ k ≤ J.radical ^ k := Ideal.pow_mono hIJ _
    _ ≤ J := hk
#align ideal.exists_pow_le_of_le_radical_of_fg Ideal.exists_pow_le_of_le_radical_of_fg

end LocalCohomologyEquiv
