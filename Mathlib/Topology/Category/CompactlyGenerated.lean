/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Topology.Category.CompHaus.Basic
import Mathlib.CategoryTheory.Elementwise
/-!

# Compactly generated topological spaces

This file defines the category of compactly generated topological spaces. These are spaces `X` such
that a map `f : X → Y` is continuous whenever the composition `S → X → Y` is continuous for all
compact Hausdorff spaces `S` mapping continuously to `X`.

## TODO

* `CompactlyGenerated` is a reflective subcategory of `TopCat`.
* `CompactlyGenerated` is cartesian closed.
* Every first-countable space is `u`-compactly generated for every universe `u`.
-/

attribute [local instance] CategoryTheory.ConcreteCategory.instFunLike

universe u w

open CategoryTheory Topology TopologicalSpace

/--
The compactly generated topology on a topological space `X`. This is the finest topology
which makes all maps from compact Hausdorff spaces to `X`, which are continuous for the original
topology, continuous.

Note: this definition should be used with an explicit universe parameter `u` for the size of the
compact Hausdorff spaces mapping to `X`.
-/
def TopologicalSpace.compactlyGenerated (X : Type w) [TopologicalSpace X] : TopologicalSpace X :=
  let f : (Σ (i : (S : CompHaus.{u}) × C(S, X)), i.fst) → X := fun ⟨⟨_, i⟩, s⟩ ↦ i s
  coinduced f inferInstance

lemma continuous_from_compactlyGenerated {X : Type w} [TopologicalSpace X]
    {Y : Type*} [t : TopologicalSpace Y] (f : X → Y)
      (h : ∀ (S : CompHaus.{u}) (g : C(S, X)), Continuous (f ∘ g)) :
        Continuous[compactlyGenerated.{u} X, t] f := by
  rw [continuous_coinduced_dom]
  continuity

/--
A topological space `X` is compactly generated if its topology is finer than (and thus equal to)
the compactly generated topology, i.e. it is coinduced by the continuous maps from compact
Hausdorff spaces to `X`.
-/
class UCompactlyGeneratedSpace (X : Type w) [t : TopologicalSpace X] : Prop where
  /-- The topology of `X` is finer than the compactly generated topology. -/
  le_compactlyGenerated : t ≤ compactlyGenerated.{u} X

lemma eq_compactlyGenerated {X : Type w} [t : TopologicalSpace X] [UCompactlyGeneratedSpace.{u} X] :
    t = compactlyGenerated.{u} X := by
  apply le_antisymm
  · exact UCompactlyGeneratedSpace.le_compactlyGenerated
  · simp only [compactlyGenerated, ← continuous_iff_coinduced_le, continuous_sigma_iff,
      Sigma.forall]
    exact fun S f ↦ f.2

instance (X : Type w) [t : TopologicalSpace X] [DiscreteTopology X] :
    UCompactlyGeneratedSpace.{u} X where
  le_compactlyGenerated := by
    rw [DiscreteTopology.eq_bot (t := t)]
    exact bot_le

lemma continuous_from_uCompactlyGeneratedSpace {X : Type w} [TopologicalSpace X]
    [UCompactlyGeneratedSpace.{u} X] {Y : Type*} [TopologicalSpace Y] (f : X → Y)
      (h : ∀ (S : CompHaus.{u}) (g : C(S, X)), Continuous (f ∘ g)) : Continuous f := by
  apply continuous_le_dom UCompactlyGeneratedSpace.le_compactlyGenerated
  exact continuous_from_compactlyGenerated f h

lemma uCompactlyGeneratedSpace_of_continuous_maps {X : Type w} [t : TopologicalSpace X]
    (h : ∀ {Y : Type w} [tY : TopologicalSpace Y] (f : X → Y),
      (∀ (S : CompHaus.{u}) (g : C(S, X)), Continuous (f ∘ g)) → Continuous f) :
        UCompactlyGeneratedSpace.{u} X where
  le_compactlyGenerated := by
    suffices Continuous[t, compactlyGenerated.{u} X] (id : X → X) by
      rwa [← continuous_id_iff_le]
    apply h (tY := compactlyGenerated.{u} X)
    intro S g
    let f : (Σ (i : (T : CompHaus.{u}) × C(T, X)), i.fst) → X := fun ⟨⟨_, i⟩, s⟩ ↦ i s
    suffices ∀ (i : (T : CompHaus.{u}) × C(T, X)),
      Continuous[inferInstance, compactlyGenerated X] (fun (a : i.fst) ↦ f ⟨i, a⟩) from this ⟨S, g⟩
    rw [← @continuous_sigma_iff]
    apply continuous_coinduced_rng

/-- The type of `u`-compactly generated `w`-small topological spaces. -/
structure CompactlyGenerated where
  /-- The underlying topological space of an object of `CompactlyGenerated`. -/
  toTop : TopCat.{w}
  /-- The underlying topological space is compactly generated. -/
  [is_compactly_generated : UCompactlyGeneratedSpace.{u} toTop]

namespace CompactlyGenerated

instance : Inhabited CompactlyGenerated.{u, w} :=
  ⟨{ toTop := { α := ULift (Fin 37) } }⟩

instance : CoeSort CompactlyGenerated Type* :=
  ⟨fun X => X.toTop⟩

attribute [instance] is_compactly_generated

instance : Category.{w, w+1} CompactlyGenerated.{u, w} :=
  InducedCategory.category toTop

instance : ConcreteCategory.{w} CompactlyGenerated.{u, w} :=
  InducedCategory.concreteCategory _

variable (X : Type w) [TopologicalSpace X] [UCompactlyGeneratedSpace.{u} X]

/-- Constructor for objects of the category `CompactlyGenerated`. -/
def of : CompactlyGenerated.{u, w} where
  toTop := TopCat.of X
  is_compactly_generated := ‹_›

/-- The fully faithful embedding of `CompactlyGenerated` in `TopCat`. -/
@[simps!]
def compactlyGeneratedToTop : CompactlyGenerated.{u, w} ⥤ TopCat.{w} :=
  inducedFunctor _

/-- `compactlyGeneratedToTop` is fully faithful. -/
def fullyFaithfulCompactlyGeneratedToTop : compactlyGeneratedToTop.{u, w}.FullyFaithful :=
  fullyFaithfulInducedFunctor _

instance : compactlyGeneratedToTop.{u, w}.Full := fullyFaithfulCompactlyGeneratedToTop.full

instance : compactlyGeneratedToTop.{u, w}.Faithful := fullyFaithfulCompactlyGeneratedToTop.faithful

/-- Construct an isomorphism from a homeomorphism. -/
@[simps hom inv]
def isoOfHomeo {X Y : CompactlyGenerated.{u, w}} (f : X ≃ₜ Y) : X ≅ Y where
  hom := ⟨f, f.continuous⟩
  inv := ⟨f.symm, f.symm.continuous⟩
  hom_inv_id := by
    ext x
    exact f.symm_apply_apply x
  inv_hom_id := by
    ext x
    exact f.apply_symm_apply x

/-- Construct a homeomorphism from an isomorphism. -/
@[simps]
def homeoOfIso {X Y : CompactlyGenerated.{u, w}} (f : X ≅ Y) : X ≃ₜ Y where
  toFun := f.hom
  invFun := f.inv
  left_inv x := by simp
  right_inv x := by simp
  continuous_toFun := f.hom.continuous
  continuous_invFun := f.inv.continuous

/-- The equivalence between isomorphisms in `CompactlyGenerated` and homeomorphisms
of topological spaces. -/
@[simps]
def isoEquivHomeo {X Y : CompactlyGenerated.{u, w}} : (X ≅ Y) ≃ (X ≃ₜ Y) where
  toFun := homeoOfIso
  invFun := isoOfHomeo
  left_inv f := by
    ext
    rfl
  right_inv f := by
    ext
    rfl

end CompactlyGenerated
