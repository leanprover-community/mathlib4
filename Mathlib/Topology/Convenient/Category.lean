/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Adjunction.Reflective
public import Mathlib.CategoryTheory.Monad.Limits
public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.Topology.Convenient.ContinuousMapGeneratedBy

/-!
# The category of `X`-generated spaces

Let `X i` be a family of topological spaces. In this file, we define
the category `GeneratedByTopCat X` of `X`-generated spaces: this is
defined as a full subcategory of `TopCat`.

We also introduce an equivalent category `ContinuousGeneratedByCat X` whose
objects are all topological spaces, but morphisms from `Y` to `Z` identify
to the type `ContinuousMapGeneratedBy X Y Z` of `X`-continuous maps from
`Y` to `Z`. While `GeneratedByTopCat X` is defined as a full subcategory
of `TopCat`, `ContinuousGeneratedByCat X` should be thought of as
a localization of the category `TopCat`. This alternative point of view
from the article by Martín Escardó, Jimmie Lawson and Alex Simpson
shall allow a very nice construction of a cartesian monoidal closed
structure on `GeneratedByTopCat X` under suitable assumptions (TODO @joelriou).

## References
* [Martín Escardó, Jimmie Lawson and Alex Simpson, *Comparing Cartesian closed
  categories of (core) compactly generated spaces*][escardo-lawson-simpson-2004]

-/

@[expose] public section

universe v t u

open CategoryTheory Topology Limits

variable {ι : Type t} (X : ι → Type u) [∀ i, TopologicalSpace (X i)]

/-- The property of objects of `TopCat` which is satisfied by `X`-generated spaces. -/
abbrev TopCat.generatedBy : ObjectProperty TopCat.{v} :=
  fun Y ↦ IsGeneratedBy X Y

lemma TopCat.generatedBy_def (Y : TopCat.{v}) :
    generatedBy X Y ↔ IsGeneratedBy X Y := Iff.rfl

/-- The full subcategory of `TopCat` consisting of `X`-generated spaces. -/
abbrev GeneratedByTopCat := (TopCat.generatedBy.{v} X).FullSubcategory

namespace GeneratedByTopCat

variable {X} in
/-- The inclusion functor `GeneratedByTopCat X ⥤ TopCat`. -/
abbrev toTopCat : GeneratedByTopCat.{v} X ⥤ TopCat.{v} := ObjectProperty.ι _

instance (Y : GeneratedByTopCat.{v} X) : IsGeneratedBy X (toTopCat.obj Y) := Y.property

/-- The inclusion functor `toTopCat : GeneratedByTopCat X ⥤ TopCat`
is fully faithful. -/
abbrev fullyFaithfulToTopCat : (toTopCat.{v} (X := X)).FullyFaithful :=
  ObjectProperty.fullyFaithfulι _

variable {X} in
/-- Constructor for objects in the category of `X`-generated spaces. -/
abbrev of (Y : Type v) [TopologicalSpace Y] [IsGeneratedBy X Y] :
    GeneratedByTopCat.{v} X where
  obj := TopCat.of Y
  property := by assumption

instance : CoeSort (GeneratedByTopCat.{v} X) (Type v) where
  coe Y := (Y.obj : Type v)

instance (Y : GeneratedByTopCat.{v} X) : IsGeneratedBy X Y := Y.property

end GeneratedByTopCat

/-- Let `X i` be a family of topological spaces. This is the type of objects
in a category ` ContinuousGeneratedByCat X` where:
* objects are topological spaces;
* morphisms are `X`-continuous maps. -/
structure ContinuousGeneratedByCat (X : ι → Type u) [∀ i, TopologicalSpace (X i)] where
  /-- Constructor for objects in `ContinuousGeneratedByCat X`. -/
  of ::
  /-- The underlying type of an object in `ContinuousGeneratedByCat X`. -/
  carrier : Type v
  [str : TopologicalSpace carrier]

namespace ContinuousGeneratedByCat

variable {X}

instance : CoeSort (ContinuousGeneratedByCat.{v} X) (Type v) :=
  ⟨carrier⟩

attribute [coe] carrier

attribute [instance] str

lemma coe_of (Y : Type v) [TopologicalSpace Y] : (of (X := X) Y : Type v) = Y := rfl

lemma of_carrier (Y : ContinuousGeneratedByCat.{v} X) : of (X := X) Y = Y := rfl

/-- The type of morphisms in the category `ContinuousGeneratedByCat X` is
a one-field structure containing a field of type `ContinuousMapGeneratedBy`,
i.e. `X`-continuous maps. -/
structure Hom (Y Z : ContinuousGeneratedByCat.{v} X) where
  /-- the underlying `X`-continuous map of a morphism in `ContinuousGeneratedByCat X`. -/
  hom : ContinuousMapGeneratedBy X Y Z

instance : Category (ContinuousGeneratedByCat.{v} X) where
  Hom := Hom
  id X := { hom := .id }
  comp f g := {hom := g.hom.comp f.hom }

instance : ConcreteCategory.{v} (ContinuousGeneratedByCat.{v} X)
    (fun Y Z ↦ ContinuousMapGeneratedBy X Y Z) where
  hom := Hom.hom
  ofHom := Hom.mk

/-- Constructor for morphisms in `ContinuousGeneratedByCat X`. -/
@[simps]
def homMk {Y Z : ContinuousGeneratedByCat.{v} X} (f : Y → Z) (hf : ContinuousGeneratedBy X f) :
    Y ⟶ Z where
  hom.toFun := f
  hom.prop := hf

/-- Use the abbreviation `TopCat.toContinuousGeneratedByCat` for the faithful
functor `TopCat ⥤ ContinuousGeneratedByCat X` which sends
a topological space `Y` to the same type `Y`, with the same topology, but
considered as an object of `ContinuousGeneratedByCat X`. -/
@[simps! +dsimpLhs forget₂_obj forget₂_map_hom_apply]
instance : HasForget₂ TopCat.{v} (ContinuousGeneratedByCat.{v} X) where
  forget₂.obj Y := .of Y
  forget₂.map f := ContinuousGeneratedByCat.homMk f (f.hom.continuous.continuousGeneratedBy)

end ContinuousGeneratedByCat

/-- The faithful functor `TopCat ⥤ ContinuousGeneratedByCat X` which sends
a topological space `Y` to the same type `Y`, with the same topology, but
considered as an object of `ContinuousGeneratedByCat X`. -/
abbrev TopCat.toContinuousGeneratedByCat :
    TopCat.{v} ⥤ ContinuousGeneratedByCat.{v} X := forget₂ _ _

instance : (TopCat.toContinuousGeneratedByCat.{v} X).Faithful := inferInstance

namespace ContinuousGeneratedByCat

/-- The functor `ContinuousGeneratedByCat X ⥤ TopCat` which sends a
topological space `Y` in the category `ContinuousGeneratedByCat X` to
the topological space `WithGeneratedByTopology X Y`. -/
@[simps obj]
def toTopCat : ContinuousGeneratedByCat.{v} X ⥤ TopCat where
  obj Y := TopCat.of (WithGeneratedByTopology X Y)
  map f := TopCat.ofHom (f.hom.prop.continuousMap)

variable {X} in
lemma toTopCat_map_apply {Y Z : ContinuousGeneratedByCat.{v} X}
    (f : Y ⟶ Z) (y : WithGeneratedByTopology X ↑Y) :
    dsimp% (toTopCat X).map f y =
      (WithGeneratedByTopology.equiv (X := X)).symm
        (f (WithGeneratedByTopology.equiv y)) :=
  rfl

/-- The functor `ContinuousGeneratedByCat.toTopCat : ContinuousGeneratedByCat X ⥤ TopCat`
is fully faithful. -/
def fullyFaithfulToTopCat : (toTopCat.{v} X).FullyFaithful where
  preimage {Y Z} g :=
    homMk (WithGeneratedByTopology.equiv (X := X) ∘ g.hom ∘
      (WithGeneratedByTopology.equiv (X := X)).symm) (by
      rw [continuousGeneratedBy_iff]
      exact g.hom.continuous)

variable {X}

/-- The unit (isomorphism) of the adjunction `ContinuousGeneratedByCat.adj` between
the categories `ContinuousGeneratedByCat X` and `TopCat`. -/
def adjUnitIso :
    𝟭 (ContinuousGeneratedByCat.{v} X) ≅ toTopCat X ⋙ TopCat.toContinuousGeneratedByCat X :=
  NatIso.ofComponents (fun Y ↦
    { hom := { hom := WithGeneratedByTopology.equivSymmAsContinuousMapGeneratedBy X Y }
      inv := { hom := WithGeneratedByTopology.equivAsContinuousMapGeneratedBy X Y }})

/-- The counit of the adjunction `ContinuousGeneratedByCat.adj` between
the categories `ContinuousGeneratedByCat X` and `TopCat`. -/
def adjCounit : TopCat.toContinuousGeneratedByCat.{v} X ⋙ toTopCat X ⟶ 𝟭 TopCat where
  app Z := TopCat.ofHom (⟨_,  WithGeneratedByTopology.continuous_equiv⟩)

/-- The adjunction between the categories `ContinuousGeneratedByCat X` and `TopCat`. -/
@[simps]
def adj : toTopCat.{v} X ⊣ TopCat.toContinuousGeneratedByCat X where
  unit := adjUnitIso.hom
  counit := adjCounit

instance : (toTopCat.{v} X).IsLeftAdjoint := adj.isLeftAdjoint

instance : (TopCat.toContinuousGeneratedByCat.{v} X).IsRightAdjoint := adj.isRightAdjoint

instance : (TopCat.toContinuousGeneratedByCat.{v} X).Faithful where
  map_injective h := by ext x; exact ConcreteCategory.congr_hom h x

instance : IsIso (adj.{v} (X := X)).unit := by dsimp; infer_instance

/-- The functor `GeneratedByTopCat X ⥤ ContinuousGeneratedByCat X` which is
part of the equivalence `ContinuousGeneratedByCat.equivalence`. It sends
an `X`-generated topological space `Y` to the topological space `Y`, considered as
an object of `ContinuousGeneratedByCat X`. -/
@[simps +dsimpLhs obj map_hom_apply]
def fromGeneratedByTopCat : GeneratedByTopCat.{v} X ⥤ ContinuousGeneratedByCat.{v} X where
  obj Y := .of Y.obj
  map f := ⟨f, f.hom.hom.continuous.continuousGeneratedBy⟩

/-- The isomorphism between
`fromGeneratedByTopCat ⋙ toTopCat X ≅ GeneratedByTopCat.toTopCat`. -/
def equivalenceFunctorIso :
    fromGeneratedByTopCat ⋙ toTopCat X ≅ GeneratedByTopCat.toTopCat :=
  NatIso.ofComponents (fun Y ↦ TopCat.isoOfHomeo
    (IsGeneratedBy.homeomorph (Y := GeneratedByTopCat.toTopCat.obj Y)))

/-- The functor `ContinuousGeneratedByCat X ⥤ GeneratedByTopCat X` which is
part of the equivalence `ContinuousGeneratedByCat.equivalence`. -/
@[simps! obj]
def toGeneratedByTopCat : ContinuousGeneratedByCat.{v} X ⥤ GeneratedByTopCat.{v} X :=
  ObjectProperty.lift _ (toTopCat X) (fun Y ↦ by
    rw [TopCat.generatedBy_def]
    dsimp +instances
    infer_instance)

lemma toGeneratedByTopCat_map_apply {Y Z : ContinuousGeneratedByCat.{v} X} (f : Y ⟶ Z)
    (y : WithGeneratedByTopology X Y) :
    dsimp% toGeneratedByTopCat.map f y =
      (WithGeneratedByTopology.equiv (X := X)).symm
        (f (WithGeneratedByTopology.equiv y)) := rfl

/-- The unit isomorphism of the equivalence `ContinuousGeneratedByCat.equivalence`. -/
def equivalenceUnitIso :
    𝟭 (GeneratedByTopCat.{v} X) ≅ fromGeneratedByTopCat ⋙ toGeneratedByTopCat :=
  NatIso.ofComponents (fun Y ↦
    (GeneratedByTopCat.fullyFaithfulToTopCat X).preimageIso
      (TopCat.isoOfHomeo IsGeneratedBy.homeomorph.symm))

/-- The counit isomorphism of the equivalence `ContinuousGeneratedByCat.equivalence`. -/
abbrev equivalenceCounitIso :
    toGeneratedByTopCat ⋙ fromGeneratedByTopCat ≅ 𝟭 (ContinuousGeneratedByCat X) :=
  adjUnitIso.symm

/-- The equivalence of categories `GeneratedByTopCat X ≌ ContinuousGeneratedByCat X`. -/
@[simps]
def equivalence : GeneratedByTopCat.{v} X ≌ ContinuousGeneratedByCat.{v} X where
  functor := fromGeneratedByTopCat
  inverse := toGeneratedByTopCat
  unitIso := equivalenceUnitIso
  counitIso := equivalenceCounitIso

instance : (fromGeneratedByTopCat.{v} (X := X)).IsEquivalence :=
  equivalence.isEquivalence_functor

instance : (toGeneratedByTopCat.{v} (X := X)).IsEquivalence :=
  equivalence.isEquivalence_inverse

end ContinuousGeneratedByCat

variable {X}

/-- The functor `TopCat.{v} ⥤ GeneratedByTopCat X`. -/
def TopCat.toGeneratedByTopCat : TopCat.{v} ⥤ GeneratedByTopCat X :=
  TopCat.toContinuousGeneratedByCat X ⋙ ContinuousGeneratedByCat.toGeneratedByTopCat

namespace GeneratedByTopCat

/-- The unit (isomorphism) of the adjunction `GeneratedByTopCat.adj` between
the categories `GeneratedByTopCat X` and `TopCat`. -/
def adjUnitIso : 𝟭 (GeneratedByTopCat.{v} X) ≅ toTopCat ⋙ TopCat.toGeneratedByTopCat :=
  ContinuousGeneratedByCat.equivalenceUnitIso

/-- The counit of the adjunction `GeneratedByTopCat.adj` between
the categories `GeneratedByTopCat X` and `TopCat`. -/
def adjCounit : TopCat.toGeneratedByTopCat.{v} (X := X) ⋙ toTopCat ⟶ 𝟭 TopCat :=
  ContinuousGeneratedByCat.adjCounit

/-- The adjunction between the categories `GeneratedByTopCat X` and `TopCat`.
The left adjoint is the inclusion functor, and the right adjoint sends
a topological space `Y` to the underlying type of `Y` endowed with
the `X`-generated topology. -/
@[simps]
def adj : toTopCat.{v} (X := X) ⊣ TopCat.toGeneratedByTopCat where
  unit := adjUnitIso.hom
  counit := adjCounit

instance : IsIso (adj.{v} (X := X)).unit := by dsimp; infer_instance

instance : (toTopCat.{v} (X := X)).IsLeftAdjoint := adj.isLeftAdjoint

instance : (TopCat.toGeneratedByTopCat.{v} (X := X)).IsRightAdjoint := adj.isRightAdjoint

instance : (TopCat.toGeneratedByTopCat.{v} (X := X)).Faithful where
  map_injective h := by ext x; exact ConcreteCategory.congr_hom h x

/-- The category of `X`-generated spaces is coreflective in the category of topological spaces. -/
instance : Coreflective (toTopCat.{v} (X := X)) where
  R := TopCat.toGeneratedByTopCat
  adj := adj

noncomputable instance : CreatesColimits (toTopCat.{v} (X := X)) :=
  comonadicCreatesColimits _

instance : HasLimits (GeneratedByTopCat X) :=
  hasLimits_of_coreflective toTopCat

instance : HasColimits (GeneratedByTopCat X) :=
  hasColimits_of_hasColimits_createsColimits toTopCat

end GeneratedByTopCat
