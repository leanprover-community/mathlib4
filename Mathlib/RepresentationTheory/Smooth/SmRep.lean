/-
Copyright (c) 2026 Jiaxi Mo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiaxi Mo
-/
module

public import Mathlib.RepresentationTheory.Smooth.Basic
public import Mathlib.RepresentationTheory.Rep.Basic
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Monoidal.Subcategory
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# Smooth representations

This file defines the category `SmoothRep k G` of smooth representations of a topological group `G`
and proves that it is a full, coreflexive, braided, closed, monoidal subcategory of `Rep k G`.

## Main definitions

* `Representation.Smooth.SmRep.SmoothRep`
* `Representation.Smooth.SmRep.smVec`
* `Representation.Smooth.SmRep.ihom`
* `Representation.Smooth.SmRep.dual`

## Main theorems

* `Representation.Smooth.SmRep.tensorHomAdjunction`

## Implementation notes

We use `ObjectProperty.FullSubcategory` to define the category of smooth representations.

To obtain the monoidal structure, we first show that taking smooth vectors `smVec` is right adjoint
to the canonical inclusion `ι`, and then we employ the categorical machinery to obtain the desired
categorical structures by restricting those structures in `Rep` along the fully faithful inclusion.

-/

@[expose] public section

open CategoryTheory Representation

namespace Representation.Smooth.SmRep

universe u v

section ring

variable (k : Type u) [Ring k]
variable (G : Type v) [TopologicalSpace G] [Group G]

def smoothProperty : ObjectProperty (Rep k G) := fun A ↦ (IsSmooth A.ρ)

/-- `SmoothRep` is the full subcategory of `Rep` consisting of smooth representations. -/
abbrev SmoothRep := (smoothProperty k G).FullSubcategory

variable {k G}

@[simp]
lemma smoothProperty_iff {A : Rep k G}
    : smoothProperty k G A ↔ IsSmooth A.ρ := by
  rfl

/-- The zero representation is smooth. -/
instance : Inhabited (SmoothRep k G) := ⟨(default : Rep k G), isSmooth_trivial⟩

/-- Smoothness is stable under isomorphisms. -/
lemma isSmooth_of_iso {A B : Rep k G} (f : A ≅ B) (h : IsSmooth A.ρ) : IsSmooth B.ρ := by
  simp_all only [isSmooth_iff]
  intro v
  specialize h (f.inv.hom v)
  simp only [← f.inv.hom.isIntertwining] at h
  have heq (g : G) : (Rep.Hom.hom f.inv) ((B.ρ g) v) = (Rep.Hom.hom f.inv) v ↔ (B.ρ g) v = v :=
  ⟨fun hv => by simpa [Rep.hom_inv_apply] using congrArg (Rep.Hom.hom f.hom) hv,
  fun hv => by rw [hv]⟩
  simpa [heq] using h

instance : (smoothProperty k G).IsClosedUnderIsomorphisms := ⟨by
  simp only [smoothProperty_iff]; exact fun f h => (isSmooth_of_iso f h)⟩

variable [IsTopologicalGroup G]

abbrev ι : SmoothRep k G ⥤ Rep k G := (smoothProperty k G).ι

/-- The functor of taking the maximal smooth subrepresentation. -/
def smVec : Rep k G ⥤ SmoothRep k G where
  obj := fun A ↦ ⟨Rep.of ((smoothVectors A.ρ).toRepresentation), by simp [isSmooth_smoothVectors]⟩
  map := fun f ↦ ObjectProperty.homMk (Rep.ofHom (IntertwiningMap.smoothVectors f.hom))

/-- `ι` is left adjoint to `smVec`. -/
def smVecAdjunction : ι ⊣ smVec (k := k) (G := G) where
  unit := { app A := ObjectProperty.homMk <| Rep.ofHom {
    toFun := fun v ↦ ⟨v, A.property.smooth v⟩
    map_add' x y := by rfl, map_smul' m x := by rfl, isIntertwining' g := by rfl }}
  counit := { app A := Rep.ofHom {
    toFun := fun ⟨v, hv⟩ ↦ v
    map_add' x y := by rfl, map_smul' m x := by rfl, isIntertwining' g :=  by rfl }}

/-- `SmoothRep` is a coreflexive full subcategory of `Rep`. -/
lemma isIso_smVecAdjunction_unit : IsIso (smVecAdjunction (k := k) (G := G)).unit :=
  smVecAdjunction.unit_isIso_of_L_fully_faithful

end ring

section commring

variable {k : Type u} [CommRing k]
variable {G : Type v} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]

section monoidal

open MonoidalCategory

/-- `SmoothRep` is a full monoidal subcategory of `Rep`. -/
instance : ObjectProperty.IsMonoidal (smoothProperty k G) where
  prop_unit := by simp [isSmooth_trivial]
  prop_tensor := by simp_all [isSmooth_tprod]

/-- The definition of internal `Hom` in the category of smooth representations. -/
noncomputable def ihom (A : SmoothRep k G) := ι ⋙ (ι.obj A).ihom ⋙ smVec

/-- The underlying representation of `ihom` is `smoothHom`. -/
lemma ihom_eq_RepOfSmoothHom (A B : SmoothRep k G)
    : ((ihom A).obj B).obj = Rep.of (smoothHom A.obj.ρ B.obj.ρ) := by
  rfl

noncomputable def tensorHomAdjunction' (A : SmoothRep k G)
    : ι ⋙ (tensorLeft (ι.obj A)) ⊣ (Rep.ihom (ι.obj A)) ⋙ smVec :=
  smVecAdjunction.comp (ihom.adjunction (ι.obj A))

/-- The adjunction between `A ⨂ _` and `ihom (A, _)` in the category `SmoothRep`. -/
noncomputable def tensorHomAdjunction (A : SmoothRep k G) : tensorLeft A ⊣ ihom A :=
  Adjunction.restrictFullyFaithful (tensorHomAdjunction' A)
  (Functor.FullyFaithful.id (SmoothRep k G)) ((smoothProperty k G).fullyFaithfulι)
  (Functor.Monoidal.commTensorLeft ι A) ((Functor.rightUnitor (ihom A)).symm)

/-- The explicit isomorphism between `A ⊗ B ⟶ C` and `B ⟶ ihom (A, C)`. -/
noncomputable def tensorHomEquiv (A B C : SmoothRep k G) : (A ⊗ B ⟶ C) ≃ (B ⟶ (SmRep.ihom A).obj C)
  := ((smoothProperty k G).fullyFaithfulι.homEquiv).trans <|
  (Rep.tensorHomEquiv (ι.obj A) (ι.obj B) (ι.obj C)).trans <|
  smVecAdjunction.homEquiv B ((Rep.ihom (ι.obj A)).obj (ι.obj C))

lemma tensorHomAdjunction_homEquiv_eq_tensorHomEquiv (A : SmoothRep k G)
    : (tensorHomAdjunction A).homEquiv = tensorHomEquiv A := by
  ext; rfl

/-- `SmoothRep` is a full closed monoidal subcategory of `Rep`. -/
noncomputable instance : MonoidalClosed (SmoothRep k G) where
  closed A := { rightAdj := ihom A, adj := tensorHomAdjunction A }

/-- `SmoothRep` is a full braided subcategory of `Rep`. -/
noncomputable instance : BraidedCategory (SmoothRep k G) := by
  infer_instance

open Opposite

/-- The dualizing functor in `SmoothRep`. -/
noncomputable def dual : SmoothRep k G ⥤ (SmoothRep k G)ᵒᵖ where
  obj A := op ((ihom A).obj (𝟙_ (SmoothRep k G)))
  map {A B} f := op ((MonoidalClosed.pre (C := SmoothRep k G) f).app (𝟙_ (SmoothRep k G)))

/-- The underlying construction of the dualizing functor is given by `contragredient`. -/
lemma unop_dualObj_eq_contragredient (A : SmoothRep k G)
    : (unop (dual.obj A)).obj.ρ = contragredient A.obj.ρ := by
  rfl

end monoidal

end commring
