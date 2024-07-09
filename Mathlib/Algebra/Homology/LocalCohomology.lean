/-
Copyright (c) 2023 Emily Witt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emily Witt, Scott Morrison, Jake Levinson, Sam van Gool
-/
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.RingTheory.Finiteness
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.RingTheory.Noetherian

#align_import algebra.homology.local_cohomology from "leanprover-community/mathlib"@"893964fc28cefbcffc7cb784ed00a2895b4e65cf"


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
* Establish long exact sequence(s) in local cohomology
-/


open Opposite

open CategoryTheory

open CategoryTheory.Limits

noncomputable section

universe u v v'

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

-- Porting note (#11215): TODO:  Once this file is ported, move this instance to the right location.
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

lemma hasColimitDiagram (I : D ⥤ Ideal R) (i : ℕ) :
    HasColimit (diagram I i) := by
  have : HasColimitsOfShape Dᵒᵖ (AddCommGrpMax.{u, v}) := inferInstance
  infer_instance

/-
In this definition we do not assume any special property of the diagram `I`, but the relevant case
will be where `I` is (cofinal with) the diagram of powers of a single given ideal.

Below, we give two equivalent definitions of the usual local cohomology with support
in an ideal `J`, `localCohomology` and `localCohomology.ofSelfLERadical`.
 -/
/-- `localCohomology.ofDiagram I i` is the functor sending a module `M` over a commutative
ring `R` to the direct limit of `Ext^i(R/J, M)`, where `J` ranges over a collection of ideals
of `R`, represented as a functor `I`. -/
def ofDiagram (I : D ⥤ Ideal R) (i : ℕ) : ModuleCatMax.{u, v} R ⥤ ModuleCatMax.{u, v} R :=
  have := hasColimitDiagram.{u, v} I i
  colimit (diagram I i)
#align local_cohomology.of_diagram localCohomology.ofDiagram

end

section

variable {R : Type max u v v'} [CommRing R] {D : Type v} [SmallCategory D]
variable {E : Type v'} [SmallCategory E] (I' : E ⥤ D) (I : D ⥤ Ideal R)

/-- Local cohomology along a composition of diagrams. -/
def diagramComp (i : ℕ) : diagram (I' ⋙ I) i ≅ I'.op ⋙ diagram I i :=
  Iso.refl _
#align local_cohomology.diagram_comp localCohomology.diagramComp

/-- Local cohomology agrees along precomposition with a cofinal diagram. -/
@[nolint unusedHavesSuffices]
def isoOfFinal [Functor.Initial I'] (i : ℕ) :
    ofDiagram.{max u v, v'} (I' ⋙ I) i ≅ ofDiagram.{max u v', v} I i :=
  have := hasColimitDiagram.{max u v', v} I i
  have := hasColimitDiagram.{max u v, v'} (I' ⋙ I) i
  HasColimit.isoOfNatIso (diagramComp.{u} I' I i) ≪≫ Functor.Final.colimitIso _ _
#align local_cohomology.iso_of_final localCohomology.isoOfFinal

end

section Diagrams

variable {R : Type u} [CommRing R]

/-- The functor sending a natural number `i` to the `i`-th power of the ideal `J` -/
def idealPowersDiagram (J : Ideal R) : ℕᵒᵖ ⥤ Ideal R where
  obj t := J ^ unop t
  map w := ⟨⟨Ideal.pow_le_pow_right w.unop.down.down⟩⟩
#align local_cohomology.ideal_powers_diagram localCohomology.idealPowersDiagram

/-- The full subcategory of all ideals with radical containing `J` -/
def SelfLERadical (J : Ideal R) : Type u :=
  FullSubcategory fun J' : Ideal R => J ≤ J'.radical
#align local_cohomology.self_le_radical localCohomology.SelfLERadical

-- Porting note: `deriving Category` is not able to derive this instance
-- https://github.com/leanprover-community/mathlib4/issues/5020
instance (J : Ideal R) : Category (SelfLERadical J) :=
  (FullSubcategory.category _)

instance SelfLERadical.inhabited (J : Ideal R) : Inhabited (SelfLERadical J) where
  default := ⟨J, Ideal.le_radical⟩
#align local_cohomology.self_le_radical.inhabited localCohomology.SelfLERadical.inhabited

/-- The diagram of all ideals with radical containing `J`, represented as a functor.
This is the "largest" diagram that computes local cohomology with support in `J`. -/
def selfLERadicalDiagram (J : Ideal R) : SelfLERadical J ⥤ Ideal R :=
  fullSubcategoryInclusion _
#align local_cohomology.self_le_radical_diagram localCohomology.selfLERadicalDiagram

end Diagrams

end localCohomology

/-! We give two models for the local cohomology with support in an ideal `J`: first in terms of
the powers of `J` (`localCohomology`), then in terms of *all* ideals with radical
containing `J` (`localCohomology.ofSelfLERadical`). -/


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

end ModelsForLocalCohomology

namespace localCohomology

/-!
Showing equivalence of different definitions of local cohomology.
  * `localCohomology.isoSelfLERadical` gives the isomorphism
      `localCohomology J i ≅ localCohomology.ofSelfLERadical J i`
  * `localCohomology.isoOfSameRadical` gives the isomorphism
      `localCohomology J i ≅ localCohomology K i` when `J.radical = K.radical`.
-/

section LocalCohomologyEquiv

variable {R : Type u} [CommRing R]

/-- Lifting `idealPowersDiagram J` from a diagram valued in `ideals R` to a diagram
valued in `SelfLERadical J`. -/
def idealPowersToSelfLERadical (J : Ideal R) : ℕᵒᵖ ⥤ SelfLERadical J :=
  FullSubcategory.lift _ (idealPowersDiagram J) fun k => by
    change _ ≤ (J ^ unop k).radical
    cases' unop k with n
    · simp [Ideal.radical_top, pow_zero, Ideal.one_eq_top, le_top, Nat.zero_eq]
    · simp only [J.radical_pow n.succ_ne_zero, Ideal.le_radical]
#align local_cohomology.ideal_powers_to_self_le_radical localCohomology.idealPowersToSelfLERadical

variable {I J K : Ideal R}

/-- The lemma below essentially says that `idealPowersToSelfLERadical I` is initial in
`selfLERadicalDiagram I`.

Porting note: This lemma should probably be moved to `Mathlib/RingTheory/Finiteness`
to be near `Ideal.exists_radical_pow_le_of_fg`, which it generalizes. -/
theorem Ideal.exists_pow_le_of_le_radical_of_fG (hIJ : I ≤ J.radical) (hJ : J.radical.FG) :
    ∃ k : ℕ, I ^ k ≤ J := by
  obtain ⟨k, hk⟩ := J.exists_radical_pow_le_of_fg hJ
  use k
  calc
    I ^ k ≤ J.radical ^ k := Ideal.pow_right_mono hIJ _
    _ ≤ J := hk
#align local_cohomology.ideal.exists_pow_le_of_le_radical_of_fg localCohomology.Ideal.exists_pow_le_of_le_radical_of_fG

/-- The diagram of powers of `J` is initial in the diagram of all ideals with
radical containing `J`. This uses noetherianness. -/
instance ideal_powers_initial [hR : IsNoetherian R R] :
    Functor.Initial (idealPowersToSelfLERadical J) where
  out J' := by
    apply (config := {allowSynthFailures := true }) zigzag_isConnected
    · obtain ⟨k, hk⟩ := Ideal.exists_pow_le_of_le_radical_of_fG J'.2 (isNoetherian_def.mp hR _)
      exact ⟨CostructuredArrow.mk (⟨⟨hk⟩⟩ : (idealPowersToSelfLERadical J).obj (op k) ⟶ J')⟩
    · intro j1 j2
      apply Relation.ReflTransGen.single
      -- The inclusions `J^n1 ≤ J'` and `J^n2 ≤ J'` always form a triangle, based on
      -- which exponent is larger.
      rcases le_total (unop j1.left) (unop j2.left) with h | h
      · right; exact ⟨CostructuredArrow.homMk (homOfLE h).op (AsTrue.get trivial)⟩
      · left; exact ⟨CostructuredArrow.homMk (homOfLE h).op (AsTrue.get trivial)⟩
#align local_cohomology.ideal_powers_initial localCohomology.ideal_powers_initial

example : HasColimitsOfSize.{0, 0, u, u + 1} (ModuleCat.{u, u} R) := inferInstance
/-- Local cohomology (defined in terms of powers of `J`) agrees with local
cohomology computed over all ideals with radical containing `J`. -/
def isoSelfLERadical (J : Ideal.{u} R) [IsNoetherian.{u,u} R R] (i : ℕ) :
    localCohomology.ofSelfLERadical.{u} J i ≅ localCohomology.{u} J i :=
  (localCohomology.isoOfFinal.{u, u, 0} (idealPowersToSelfLERadical.{u} J)
    (selfLERadicalDiagram.{u} J) i).symm ≪≫
      HasColimit.isoOfNatIso.{0,0,u+1,u+1} (Iso.refl.{u+1,u+1} _)
#align local_cohomology.iso_self_le_radical localCohomology.isoSelfLERadical

/-- Casting from the full subcategory of ideals with radical containing `J` to the full
subcategory of ideals with radical containing `K`. -/
def SelfLERadical.cast (hJK : J.radical = K.radical) : SelfLERadical J ⥤ SelfLERadical K :=
  FullSubcategory.map fun L hL => by
    rw [← Ideal.radical_le_radical_iff] at hL ⊢
    exact hJK.symm.trans_le hL
#align local_cohomology.self_le_radical.cast localCohomology.SelfLERadical.cast

-- TODO generalize this to the equivalence of full categories for any `iff`.
/-- The equivalence of categories `SelfLERadical J ≌ SelfLERadical K`
when `J.radical = K.radical`. -/
def SelfLERadical.castEquivalence (hJK : J.radical = K.radical) :
    SelfLERadical J ≌ SelfLERadical K where
  functor := SelfLERadical.cast hJK
  inverse := SelfLERadical.cast hJK.symm
  unitIso := Iso.refl _
  counitIso := Iso.refl _

instance SelfLERadical.cast_isEquivalence (hJK : J.radical = K.radical) :
    (SelfLERadical.cast hJK).IsEquivalence :=
  (castEquivalence hJK).isEquivalence_functor
#align local_cohomology.self_le_radical.cast_is_equivalence localCohomology.SelfLERadical.cast_isEquivalence

/-- The natural isomorphism between local cohomology defined using the `of_self_le_radical`
diagram, assuming `J.radical = K.radical`. -/
def SelfLERadical.isoOfSameRadical (hJK : J.radical = K.radical) (i : ℕ) :
    ofSelfLERadical J i ≅ ofSelfLERadical K i :=
  (isoOfFinal.{u, u, u} (SelfLERadical.cast hJK.symm) _ _).symm
#align local_cohomology.self_le_radical.iso_of_same_radical localCohomology.SelfLERadical.isoOfSameRadical

/-- Local cohomology agrees on ideals with the same radical. -/
def isoOfSameRadical [IsNoetherian R R] (hJK : J.radical = K.radical) (i : ℕ) :
    localCohomology J i ≅ localCohomology K i :=
  (isoSelfLERadical J i).symm ≪≫ SelfLERadical.isoOfSameRadical hJK i ≪≫ isoSelfLERadical K i
#align local_cohomology.iso_of_same_radical localCohomology.isoOfSameRadical

end LocalCohomologyEquiv

end localCohomology
