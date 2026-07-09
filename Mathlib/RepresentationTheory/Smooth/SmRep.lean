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

This file defines the category `SmRep k G` of smooth representations of a topological group `G`
and proves that it is a full, coreflexive, braided, closed, monoidal subcategory of `Rep k G`.

## Main definitions

* `Representation.Smooth.SmRep.SmRep`
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

namespace Representation.Smooth

universe w u v

variable (k : Type u) [Ring k]
variable (G : Type v) [TopologicalSpace G] [Group G]

/-- Smoothness is an `ObjectProperty` of `Rep k G`. -/
def smoothProperty : ObjectProperty (Rep.{w} k G) := fun A ↦ (Smooth.IsSmooth A.ρ)

/-- `SmRep k G` is the full subcategory of `Rep k G` consisting of smooth representations. -/
abbrev SmRep := (smoothProperty.{w} k G).FullSubcategory

variable {k G}

@[simp]
lemma smoothProperty_iff {A : Rep.{w} k G}
    : smoothProperty k G A ↔ Smooth.IsSmooth A.ρ := by
  rfl

namespace SmRep

variable {V : Type w} [AddCommGroup V] [Module k V]

/-- The object in `SmRep k G` associated to a smooth representation. -/ 
abbrev of (ρ : Representation k G V) [h : IsSmooth ρ] : SmRep.{w} k G := ⟨Rep.of.{w} ρ, h⟩

/-- The zero representation is smooth. -/
instance : Inhabited (SmRep k G) := ⟨(default : Rep k G), isSmooth_trivial⟩

/-- Smoothness is stable under isomorphisms. -/
lemma isSmooth_of_iso {A B : Rep.{w} k G} (f : A ≅ B) (h : IsSmooth A.ρ) : IsSmooth B.ρ := by
  simp_all only [isSmooth_iff]
  intro v
  specialize h (f.inv.hom v)
  simp only [← f.inv.hom.isIntertwining] at h
  have heq (g : G) : (Rep.Hom.hom f.inv) ((B.ρ g) v) = (Rep.Hom.hom f.inv) v ↔ (B.ρ g) v = v :=
  ⟨fun hv => by simpa [Rep.hom_inv_apply] using congrArg (Rep.Hom.hom f.hom) hv,
  fun hv => by rw [hv]⟩
  simpa [heq] using h

instance : (smoothProperty.{w} k G).IsClosedUnderIsomorphisms := ⟨by
  simp only [smoothProperty_iff]; exact fun f h => (isSmooth_of_iso f h)⟩

variable [IsTopologicalGroup G]

/-- The canonical inclusion functor from `SmRep` to `Rep`. -/
abbrev ι : SmRep.{w} k G ⥤ Rep.{w} k G := (smoothProperty.{w} k G).ι

/-- The functor of taking the maximal smooth subrepresentation. -/
def smVec : Rep.{w} k G ⥤ SmRep.{w} k G where
  obj := fun A ↦ ⟨Rep.of ((smoothVectors A.ρ).toRepresentation), by simp [isSmooth_smoothVectors]⟩
  map := fun f ↦ ObjectProperty.homMk (Rep.ofHom (IntertwiningMap.smoothVectors f.hom))

/-- `ι` is left adjoint to `smVec`. -/
def smVecAdjunction : ι ⊣ smVec.{w} (k := k) (G := G) where
  unit := { app A := ObjectProperty.homMk <| Rep.ofHom {
    toFun v := ⟨v, A.property.smooth v⟩
    map_add' x y := by rfl, map_smul' m x := by rfl, isIntertwining' g := by rfl }}
  counit := { app A := Rep.ofHom {
    toFun v := v.1
    map_add' x y := by rfl, map_smul' m x := by rfl, isIntertwining' g :=  by rfl }}

/-- `SmRep` is a coreflexive full subcategory of `Rep`. -/
lemma isIso_smVecAdjunction_unit : IsIso (smVecAdjunction.{w} (k := k) (G := G)).unit :=
  smVecAdjunction.unit_isIso_of_L_fully_faithful

section monoidal

variable {k : Type u} [CommRing k]

open MonoidalCategory

/-- `SmRep` is a full monoidal subcategory of `Rep`. -/
instance : ObjectProperty.IsMonoidal (smoothProperty.{u} k G) where
  prop_unit := by simp [isSmooth_trivial]
  prop_tensor := by simp_all [isSmooth_tprod]

/-- The definition of internal `Hom` in the category of smooth representations. -/
noncomputable def ihom (A : SmRep.{w} k G) := ι ⋙ (ι.obj A).ihom ⋙ smVec

/-- The underlying representation of `ihom` is `smoothHom`. -/
lemma ihom_eq_RepOfSmoothHom (A B : SmRep.{w} k G)
    : ((ihom A).obj B).obj = Rep.of (smoothHom A.obj.ρ B.obj.ρ) := by
  rfl

/-- An auxiliary form of `tensorHomAdjunction`. -/
noncomputable def tensorHomAdjunction' (A : SmRep.{u} k G)
    : ι ⋙ (tensorLeft (ι.obj A)) ⊣ (Rep.ihom (ι.obj A)) ⋙ smVec :=
  smVecAdjunction.comp (ihom.adjunction (ι.obj A))

/-- The adjunction between `A ⨂ _` and `ihom (A, _)` in the category `SmRep`. -/
noncomputable def tensorHomAdjunction (A : SmRep.{u} k G) : tensorLeft A ⊣ ihom A :=
  Adjunction.restrictFullyFaithful
  (adj := tensorHomAdjunction' A)
  (hiC := Functor.FullyFaithful.id (SmRep k G))
  (hiD := (smoothProperty k G).fullyFaithfulι)
  (comm1 := Functor.Monoidal.commTensorLeft ι A)
  (comm2 := (Functor.rightUnitor (ihom A)).symm)

/-- The explicit isomorphism between `A ⊗ B ⟶ C` and `B ⟶ ihom (A, C)`. -/
noncomputable def tensorHomEquiv (A B C : SmRep.{u} k G) : (A ⊗ B ⟶ C) ≃ (B ⟶ (SmRep.ihom A).obj C)
  := ((smoothProperty k G).fullyFaithfulι.homEquiv).trans <|
  (Rep.tensorHomEquiv (ι.obj A) (ι.obj B) (ι.obj C)).trans <|
  smVecAdjunction.homEquiv B ((Rep.ihom (ι.obj A)).obj (ι.obj C))

lemma tensorHomAdjunction_homEquiv_eq_tensorHomEquiv (A : SmRep.{u} k G)
    : (tensorHomAdjunction A).homEquiv = tensorHomEquiv A := by
  ext; rfl

/-- `SmRep` is a full closed monoidal subcategory of `Rep`. -/
noncomputable instance : MonoidalClosed (SmRep.{u} k G) where
  closed A := { rightAdj := ihom A, adj := tensorHomAdjunction A }

/-- `SmRep` is a full braided subcategory of `Rep`. -/
noncomputable instance : BraidedCategory (SmRep.{u} k G) := by
  infer_instance

open Opposite

/-- The dualizing functor in `SmRep`. -/
noncomputable def dualFunctor : SmRep.{u} k G ⥤ (SmRep.{u} k G)ᵒᵖ where
  obj A := op ((ihom A).obj (𝟙_ (SmRep.{u} k G)))
  map {A B} f := op ((MonoidalClosed.pre (C := SmRep.{u} k G) f).app (𝟙_ (SmRep.{u} k G)))

/-- The smooth dual representation. -/
noncomputable abbrev dual (A : SmRep.{u} k G) := unop (dualFunctor.obj A)

/-- The underlying construction of the dualizing functor is given by `contragredient`. -/
lemma unop_dualObj_eq_contragredient (A : SmRep.{u} k G)
    : (dual A).obj.ρ = contragredient A.obj.ρ := by
  rfl

end monoidal

end SmRep

end Representation.Smooth
