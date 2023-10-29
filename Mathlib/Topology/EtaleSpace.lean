/-
Copyright (c) 2023 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.Topology.IsLocallyHomeomorph
import Mathlib.Topology.Sheaves.Sheafify
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# The category of étale spaces and the étale space of a presheaf

This file defines the category of étale spaces (namely, the local homeomorphisms
with a fixed target), the functor taking a presheaf to its étale space, and the sections
functor taking an étale space to its sheaf of sections; the composition of these two
functors is naturally isomorphic to sheafification.

## Main definitions


-/

universe u v

open CategoryTheory TopologicalSpace Opposite Set

section Sections

variable {X : Type v} [TopologicalSpace X] {B : TopCat.{u}}

/-- The continuous sections of a (not necessarily continuous) function between two
  topological spaces form a sheaf over the base space. -/
def TopCat.sheafOfSections (p : X → B) : B.Sheaf (Type max u v) where
  val :=
  { obj := fun U ↦ { f : C(U.unop, X) // p ∘ f = (↑) },
    map := fun i s ↦ ⟨s.1.comp ⟨_, continuous_inclusion i.unop.le⟩, funext fun _ ↦ congrFun s.2 _⟩,
    map_id := sorry,
    map_comp := sorry }
  cond := (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing_types _).mpr <| fun i U sf cpt ↦ by



-- Right adjoint is fully faithful iff the counit is an isomorphism  ...
-- "reflection", coreflection -- reflective


-- sections can be considered to be morphisms between certain objects of Top/B .. Yoneda?
-- use open set in B as "test objects"




end Sections

def EtaleSpaceOver (B : TopCat.{u}) : Type (u + 1) :=
  FullSubcategory fun f : Over B ↦ IsLocallyHomeomorph f.hom

namespace TopCat.Presheaf

variable {B : TopCat.{u}} (F : Presheaf (Type u) B)
/- TODO: generalize Type u to Type v with UnivLE.{u v}, both here and in Stalks.lean -/

/-- The étale space of a presheaf `F` of types over a topological space `B`
  is the disjoint union of stalks. -/
def EtaleSpace : Type u := Σ b : B, F.stalk b

namespace EtaleSpace

variable {F}

/-- Every section of a presheaf `F` on an open set `U` defines a function from `U`
  to the étale space of `F` by taking germs. -/
noncomputable def germMap {U : Opens B} (s : F.obj (op U)) : U → EtaleSpace F :=
  fun x ↦ ⟨x, F.germ x s⟩

/-- The étale space is endowed with the strongest topology making every germMap continuous. -/
instance : TopologicalSpace (EtaleSpace F) :=
  ⨆ (U : Opens B) (s : F.obj (op U)), coinduced (germMap s) inferInstance

lemma isOpen_iff {V : Set (EtaleSpace F)} :
    IsOpen V ↔ ∀ (U : Opens B) (s : F.obj (op U)), IsOpen (germMap s ⁻¹' V) := by
  simp_rw [isOpen_iSup_iff, isOpen_coinduced]

lemma continuous_iff {X} [TopologicalSpace X] {f : EtaleSpace F → X} :
    Continuous f ↔ ∀ (U : Opens B) (s : F.obj (op U)), Continuous (f ∘ germMap s) := by
  simp_rw [continuous_def, isOpen_iff, preimage_preimage]; exact forall₂_swap

lemma isOpen_range_germMap {U : Opens B} (s : F.obj (op U)) : IsOpen (range (germMap s)) :=
  isOpen_iff.mpr fun V t ↦ isOpen_iff_mem_nhds.mpr fun ⟨v, hv⟩ ⟨⟨u, hu⟩, he⟩ ↦ by
    simp_rw [germMap] at he; cases (Sigma.mk.inj_iff.mp he).1




    --isOpen_induced_eq.mpr <| by

    --⟨U ∩ V, U.isOpen.inter V.isOpen, _⟩


variable (F)

/-- The projection from the étale space down to the base is continuous. -/
def proj : C(EtaleSpace F, B) where
  toFun := Sigma.fst
  continuous_toFun := continuous_iff.mpr fun _ _ ↦ continuous_subtype_val

lemma isTopologicalBasis : IsTopologicalBasis
    {V | ∃ (U : Opens B) (s : F.obj (op U)), Set.range (germMap s) = V} :=
  isTopologicalBasis_of_open_of_nhds (fun V hV ↦ _) _


--isLocallyHomeomorph :



-- if it's a sheaf, the opens are exactly images of germMap ..
-- sheaf has same stalks .. so
-- many functors!
-- Presheaf B -EtaleSpace→ LocalHomeo/B -sections-> Sheaf B : composition NatIso to sheafification ..
-- Presheaf -sheafification→ Sheaf -forget→ Presheaf .. adjunction such that one composition is iso to identity ..

-- image of these actually forms a basis? for any presheaf or only for sheaves?

-- IsLocallyHomeomorph
-- characterization of continuous maps into EtaleSpace of a sheaf ..
-- isOpen_iff

end EtaleSpace

end TopCat.Presheaf
