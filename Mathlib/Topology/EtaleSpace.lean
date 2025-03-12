/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.Sheaves.Sheafify
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# The category of étale spaces and the étale space of a presheaf

This file defines the category of étale spaces over a base space (namely, the local homeomorphisms
with a fixed target), the functor taking a presheaf to its étale space, and the sections
functor taking an étale space to its sheaf of sections; the composition of these two
functors is naturally isomorphic to sheafification.

## Main definitions


-/

open CategoryTheory TopologicalSpace Opposite Set

namespace TopCat

variable {X : Type*} [TopologicalSpace X] {B : TopCat}

/-- The continuous sections of a (not necessarily continuous) function between two
  topological spaces form a sheaf over the base space. -/
def sheafOfSections (p : X → B) : B.Sheaf (Type _) :=
  B.subsheafToTypes <| (B.continuousLocal X).and <| B.isSection p

/-- The stalks of the sheaf of sections are in bijections with the fibers. -/
def stalkSectionsEquivFiber (p : X → B) (b : B) :
    (sheafOfSections p).presheaf.stalk b ≃ p ⁻¹' {b} where
  toFun := ⟨_, _⟩
  invFun := _
  left_inv := _
  right_inv := _


-- stalks of this sheaf is equiv to fibers of p?
-- should be the case since sheafification preserves stalks

-- Right adjoint is fully faithful iff the counit is an isomorphism  ...
-- "reflection", coreflection -- reflective
-- monadic adjunction

-- sections can be considered to be morphisms between certain objects of Top/B .. Yoneda?
-- use open set in B as "test objects"

-- separated maps <-> "identity theorem" (e.g. analytic functions)
-- covering maps <-> locally constant sheaves


def EtaleSpaceOver (B : TopCat) : Type _ :=
  FullSubcategory fun f : Over B ↦ IsLocalHomeomorph f.hom

namespace Presheaf

universe u v

variable {B : TopCat.{u}} (F : Presheaf (Type v) B)

/-- The étale space of a presheaf `F` of types over a topological space `B`
  is the disjoint union of stalks. -/
def EtaleSpace : Type max u v := Σ b : B, stalk (F ⋙ uliftFunctor.{u}) b

namespace EtaleSpace

variable {F}

/-- Every section of a presheaf `F` on an open set `U` defines a function from `U`
  to the étale space of `F` by taking germs. -/
noncomputable def germMap {U : Opens B} (s : F.obj (op U)) : U → F.EtaleSpace :=
  fun x ↦ ⟨x, germ (F ⋙ uliftFunctor) U x x.2 ⟨s⟩⟩

/-- The étale space is endowed with the strongest topology making every germMap continuous. -/
instance : TopologicalSpace F.EtaleSpace :=
  ⨆ (U : Opens B) (s : F.obj (op U)), coinduced (germMap s) inferInstance

lemma isOpen_iff {V : Set F.EtaleSpace} :
    IsOpen V ↔ ∀ (U : Opens B) (s : F.obj (op U)), IsOpen (germMap s ⁻¹' V) := by
  simp_rw [isOpen_iSup_iff, isOpen_coinduced]

lemma continuous_iff {X} [TopologicalSpace X] {f : F.EtaleSpace → X} :
    Continuous f ↔ ∀ (U : Opens B) (s : F.obj (op U)), Continuous (f ∘ germMap s) := by
  simp_rw [continuous_def, isOpen_iff, preimage_preimage]; exact forall₂_swap

lemma isOpen_range_germMap {U : Opens B} (s : F.obj (op U)) : IsOpen (range (germMap s)) :=
  isOpen_iff.mpr fun V t ↦ isOpen_iff_mem_nhds.mpr fun ⟨v, hv⟩ ⟨⟨u, hu⟩, he⟩ ↦ by
    simp_rw [germMap] at he; cases (Sigma.mk.inj_iff.mp he).1




    --isOpen_induced_eq.mpr <| by

    --⟨U ∩ V, U.isOpen.inter V.isOpen, _⟩

-- IsSheaf iff every continuous partial section is realized by a section of the presheaf

-- idempotent adjunction: reflective, coreflective

variable (F)

/-- The projection from the étale space down to the base is continuous. -/
def proj : C(F.EtaleSpace, B) where
  toFun := Sigma.fst
  continuous_toFun := continuous_iff.mpr fun _ _ ↦ continuous_subtype_val

lemma proj_isLocalHomeomorph : IsLocalHomeomorph (proj F) := sorry


lemma isTopologicalBasis : IsTopologicalBasis
    {V | ∃ (U : Opens B) (s : F.obj (op U)), Set.range (germMap s) = V} :=
  isTopologicalBasis_of_isOpen_of_nhds (fun V hV ↦ _) _

variable (X : Type*) [TopologicalSpace X] (p : C(X, B))

def adjunction : {f : C(F.EtaleSpace, X) // p.comp f = proj F} ≃
    {f : (Π U, F.obj U → (sheafOfSections p).1.obj U) //
      ∀ U V (i : U ⟶ V), (sheafOfSections p).1.map i ∘ f U = f V ∘ F.map i} where
  toFun := _
  invFun := _
  left_inv := _
  right_inv := _

-- if it's a sheaf, the opens are exactly images of germMap ..
-- sheaf has same stalks .. so
-- many functors!
-- Presheaf B -EtaleSpace→ LocalHomeo/B -sections-> Sheaf B : composition NatIso to sheafification ..
-- Presheaf -sheafification→ Sheaf -forget→ Presheaf .. adjunction such that one composition is iso to identity ..

-- image of these actually forms a basis? for any presheaf or only for sheaves?

-- characterization of continuous maps into EtaleSpace of a sheaf ..
-- isOpen_iff

end EtaleSpace

variable (F : Presheaf (Type u) B)
/- TODO: generalize `TopCat.Presheaf.Sheafify.isGerm` using `F ⋙ uliftFunctor` to allow an
  arbitrary universe instead of u (the universe of X) -/

/-- -/
def sheafOfSectionsEtaleSpaceIsoSheafify : sheafOfSections (EtaleSpace.proj F) ≅ F.sheafify where
  hom := _
  inv := _
  hom_inv_id := _
  inv_hom_id := _

end TopCat.Presheaf
