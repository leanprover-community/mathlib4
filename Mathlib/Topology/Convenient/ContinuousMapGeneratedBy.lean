/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Topology.Convenient.GeneratedBy

/-!
# `X`-continuous maps

Given a family `X i` of topological spaces, we introduce a predicate
`ContinuousGeneratedBy X` on maps `g : Y ⟶ Z` saying that
`g` is `X`-continuous, i.e. for any continuous map `f : X i → Y`,
the composition `g ∘ f` is continuous.

## References
* [Martín Escardó, Jimmie Lawson and Alex Simpson, *Comparing Cartesian closed
  categories of (core) compactly generated spaces*][escardo-lawson-simpson-2004]

-/

universe v v' t u

@[expose] public section

open Topology

variable {ι : Type t} {X : ι → Type u} [∀ i, TopologicalSpace (X i)]
  {Y : Type v} [TopologicalSpace Y] {Z : Type v'} [TopologicalSpace Z]

namespace Topology

variable (X) in
/-- Given a family `X i` of topological space, this is a predicate
on maps `g : Y → Z` between topological spaces saying that for any
continuous map `f : X i → Y`, the composition `g ∘ f` is continuous.
We say that `g` is `X`-continuous. -/
def ContinuousGeneratedBy (g : Y → Z) : Prop :=
  ∀ ⦃i : ι⦄ (f : C(X i, Y)), Continuous (g ∘ f)

lemma continuousGeneratedBy_def (g : Y → Z) :
    ContinuousGeneratedBy X g ↔
      ∀ ⦃i : ι⦄ (f : C(X i, Y)), Continuous (g ∘ f) := Iff.rfl

lemma continuousGeneratedBy_iff (g : Y → Z) :
    ContinuousGeneratedBy X g ↔
      Continuous ((WithGeneratedByTopology.equiv (X := X)).symm ∘ g ∘
        WithGeneratedByTopology.equiv (X := X)) := by
  rw [IsGeneratedBy.equiv_symm_comp_continuous_iff,
    WithGeneratedByTopology.continuous_from_iff]
  rfl

/-- A `X`-continuous map `g : Y → Z` induces a continuous map
between the types `Y` and `Z` equipped with the `X`-generated topology. -/
def ContinuousGeneratedBy.continuousMap {g : Y → Z}
    (hg : ContinuousGeneratedBy X g) :
    C(WithGeneratedByTopology X Y, WithGeneratedByTopology X Z) :=
  ⟨WithGeneratedByTopology.equiv.symm ∘ g ∘ WithGeneratedByTopology.equiv, by
    rwa [← continuousGeneratedBy_iff]⟩

@[simp]
lemma ContinuousGeneratedBy.continuousMap_coe {g : Y → Z}
    (hg : ContinuousGeneratedBy X g) :
    ⇑hg.continuousMap = WithGeneratedByTopology.equiv.symm ∘ g ∘ WithGeneratedByTopology.equiv :=
  rfl

@[simp]
lemma ContinuousGeneratedBy.id :
    ContinuousGeneratedBy X (id : Y → Y) := by
  simpa [continuousGeneratedBy_iff] using continuous_id

lemma ContinuousGeneratedBy.comp {g : Y → Z} (hg : ContinuousGeneratedBy X g)
    {T : Type*} [TopologicalSpace T] {f : T → Y} (hf : ContinuousGeneratedBy X f) :
    ContinuousGeneratedBy X (g ∘ f) := by
  rw [continuousGeneratedBy_iff]
  exact (hg.continuousMap.comp hf.continuousMap).continuous

end Topology

lemma Continuous.continuousGeneratedBy {g : Y → Z}
    (hg : Continuous g) : ContinuousGeneratedBy X g := by
  rw [continuousGeneratedBy_def]
  exact fun _ f ↦ hg.comp f.continuous

namespace Topology

variable (X Y Z) in
/-- The (bundled) type of `X`-continuous maps `Y → Z`. -/
@[ext]
structure ContinuousMapGeneratedBy where
  /-- the underlying map of a `X`-continuous map -/
  toFun : Y → Z
  prop : ContinuousGeneratedBy X toFun

instance : FunLike (ContinuousMapGeneratedBy X Y Z) Y Z where
  coe f := f.toFun
  coe_injective' _ _ _ := by aesop

/-- The identity, as a `X`-continous map. -/
@[simps]
def ContinuousMapGeneratedBy.id : ContinuousMapGeneratedBy X Y Y where
  toFun := _root_.id
  prop := continuous_id.continuousGeneratedBy

/-- The composition of `X`-continuous maps. -/
@[simps]
def ContinuousMapGeneratedBy.comp
    {Z : Type*} [TopologicalSpace Z]
    {T : Type*} [TopologicalSpace T]
    (g : ContinuousMapGeneratedBy X Y Z)
    (f : ContinuousMapGeneratedBy X T Y) :
    ContinuousMapGeneratedBy X T Z where
  toFun := g.toFun.comp f.toFun
  prop := g.prop.comp f.prop

namespace WithGeneratedByTopology

variable (X Y)

/-- The identity `WithGeneratedByTopology.equiv.symm : Y → WithGeneratedByTopology X Y`
as a `X`-continuous map. -/
def equivSymmAsContinuousMapGeneratedBy :
    ContinuousMapGeneratedBy X Y (WithGeneratedByTopology X Y) where
  toFun := equiv.symm
  prop := by
    rw [continuousGeneratedBy_def]
    intro i f
    rw [IsGeneratedBy.equiv_symm_comp_continuous_iff]
    continuity

@[simp]
lemma equivSymmAsContinuousMapGeneratedBy_coe :
    ⇑(equivSymmAsContinuousMapGeneratedBy X Y) = equiv.symm := rfl

/-- The identity `WithGeneratedByTopology.equiv : WithGeneratedByTopology X Y → Y`
as a `X`-continuous map. -/
def equivAsContinuousMapGeneratedBy :
    ContinuousMapGeneratedBy X (WithGeneratedByTopology X Y) Y where
  toFun := equiv
  prop := continuous_equiv.continuousGeneratedBy

@[simp]
lemma equivAsContinuousMapGeneratedBy_coe :
    ⇑(equivAsContinuousMapGeneratedBy X Y) = equiv := rfl

end WithGeneratedByTopology

end Topology
