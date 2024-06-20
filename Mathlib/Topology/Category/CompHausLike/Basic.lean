/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Dagur Asgeirsson, Filippo A. E. Nuccio, Riccardo Brasca
-/
import Mathlib.CategoryTheory.Functor.ReflectsIso
import Mathlib.Topology.Category.TopCat.Basic
/-!

# Categories of Compact Hausdorff Spaces

We construct the category of compact Hausdorff spaces satisfying an additional property `P`.
-/

universe u

open CategoryTheory

attribute [local instance] ConcreteCategory.instFunLike

variable (P : TopCat.{u} → Prop)

/-- The type of Compact Hausdorff topological spaces satisfying an additional property `P`. -/
structure CompHausLike where
  /-- The underlying topological space of an object of `CompHausLike P`. -/
  toTop : TopCat
  /-- The underlying topological space is compact. -/
  [is_compact : CompactSpace toTop]
  /-- The underlying topological space is T2. -/
  [is_hausdorff : T2Space toTop]
  /-- The underlying topological space satisfies P. -/
  prop : P toTop

namespace CompHausLike

attribute [instance] is_compact is_hausdorff

instance : CoeSort (CompHausLike P) (Type u) :=
  ⟨fun X => X.toTop⟩

instance category : Category (CompHausLike P) :=
  InducedCategory.category toTop

instance concreteCategory : ConcreteCategory (CompHausLike P) :=
  InducedCategory.concreteCategory _

instance hasForget₂ : HasForget₂ (CompHausLike P) TopCat :=
  InducedCategory.hasForget₂ _

variable (X : Type u) [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-- This wraps the predicate `P : TopCat → Prop` in a typeclass. -/
class HasProp : Prop where
  hasProp : P (TopCat.of X)

variable [HasProp P X]

/-- A constructor for objects of the category `CompHausLike P`,
taking a type, and bundling the compact Hausdorff topology
found by typeclass inference. -/
def of : CompHausLike P where
  toTop := TopCat.of X
  is_compact := ‹_›
  is_hausdorff := ‹_›
  prop := HasProp.hasProp

@[simp]
theorem coe_of : (CompHausLike.of P X : Type _) = X :=
  rfl

@[simp]
theorem coe_id (X : CompHausLike P) : (𝟙 ((forget (CompHausLike P)).obj X)) = id :=
  rfl

@[simp]
theorem coe_comp {X Y Z : CompHausLike P} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((forget (CompHausLike P)).map f ≫ (forget (CompHausLike P)).map g) = g ∘ f :=
  rfl

-- Note (#10754): Lean does not see through the forgetful functor here
instance (X : CompHausLike.{u} P) : TopologicalSpace ((forget (CompHausLike P)).obj X) :=
  inferInstanceAs (TopologicalSpace X.toTop)

-- Note (#10754): Lean does not see through the forgetful functor here
instance (X : CompHausLike.{u} P) : CompactSpace ((forget (CompHausLike P)).obj X) :=
  inferInstanceAs (CompactSpace X.toTop)

-- Note (#10754): Lean does not see through the forgetful functor here
instance (X : CompHausLike.{u} P) : T2Space ((forget (CompHausLike P)).obj X) :=
  inferInstanceAs (T2Space X.toTop)

variable {P}

/-- If `P` imples `P'`, then there is a functor from `CompHausLike P` to `CompHausLike P'`. -/
@[simps]
def toCompHausLike {P P' : TopCat → Prop} (h : ∀ (X : CompHausLike P), P X.toTop → P' X.toTop) :
    CompHausLike P ⥤ CompHausLike P' where
  obj X :=
    have : HasProp P' X := ⟨(h _ X.prop)⟩
    CompHausLike.of _ X
  map f := f

section

variable {P P' : TopCat → Prop} (h : ∀ (X : CompHausLike P), P X.toTop → P' X.toTop)

/-- If `P` imples `P'`, then the functor from `CompHausLike P` to `CompHausLike P'` is fully
faithful. -/
def fullyFaithfulToCompHausLike : (toCompHausLike h).FullyFaithful :=
  fullyFaithfulInducedFunctor _

instance : (toCompHausLike h).Full := (fullyFaithfulToCompHausLike h).full

instance : (toCompHausLike h).Faithful := (fullyFaithfulToCompHausLike h).faithful

end

variable (P)

/-- The fully faithful embedding of `CompHausLike P` in `TopCat`. -/
@[simps!]
def compHausLikeToTop : CompHausLike.{u} P ⥤ TopCat.{u} :=
  inducedFunctor _ -- deriving Full, Faithful -- Porting note: deriving fails, adding manually.

example {P P' : TopCat → Prop} (h : ∀ (X : CompHausLike P), P X.toTop → P' X.toTop) :
    toCompHausLike h ⋙ compHausLikeToTop P' = compHausLikeToTop P := rfl

/-- The functor from `CompHausLike P` to `TopCat` is fully faithful. -/
def fullyFaithfulCompHausLikeToTop : (compHausLikeToTop P).FullyFaithful :=
  fullyFaithfulInducedFunctor _

instance : (compHausLikeToTop P).Full  :=
  inferInstanceAs (inducedFunctor _).Full

instance : (compHausLikeToTop P).Faithful :=
  inferInstanceAs (inducedFunctor _).Faithful

instance (X : CompHausLike P) : CompactSpace ((compHausLikeToTop P).obj X) :=
  inferInstanceAs (CompactSpace X.toTop)

instance (X : CompHausLike P) : T2Space ((compHausLikeToTop P).obj X) :=
  inferInstanceAs (T2Space X.toTop)

variable {P}

theorem epi_of_surjective {X Y : CompHausLike.{u} P} (f : X ⟶ Y) (hf : Function.Surjective f) :
    Epi f := by
  rw [← CategoryTheory.epi_iff_surjective] at hf
  exact (forget (CompHausLike P)).epi_of_epi_map hf

theorem mono_iff_injective {X Y : CompHausLike.{u} P} (f : X ⟶ Y) :
    Mono f ↔ Function.Injective f := by
  constructor
  · intro hf x₁ x₂ h
    let g₁ : X ⟶ X := ⟨fun _ => x₁, continuous_const⟩
    let g₂ : X ⟶ X := ⟨fun _ => x₂, continuous_const⟩
    have : g₁ ≫ f = g₂ ≫ f := by ext; exact h
    exact ContinuousMap.congr_fun ((cancel_mono _).mp this) x₁
  · rw [← CategoryTheory.mono_iff_injective]
    apply (forget (CompHausLike P)).mono_of_mono_map

/-- Any continuous function on compact Hausdorff spaces is a closed map. -/
theorem isClosedMap {X Y : CompHausLike.{u} P} (f : X ⟶ Y) : IsClosedMap f := fun _ hC =>
  (hC.isCompact.image f.continuous).isClosed

/-- Any continuous bijection of compact Hausdorff spaces is an isomorphism. -/
theorem isIso_of_bijective {X Y : CompHausLike.{u} P} (f : X ⟶ Y) (bij : Function.Bijective f) :
    IsIso f := by
  let E := Equiv.ofBijective _ bij
  have hE : Continuous E.symm := by
    rw [continuous_iff_isClosed]
    intro S hS
    rw [← E.image_eq_preimage]
    exact isClosedMap f S hS
  refine ⟨⟨⟨E.symm, hE⟩, ?_, ?_⟩⟩
  · ext x
    apply E.symm_apply_apply
  · ext x
    apply E.apply_symm_apply

instance forget_reflectsIsomorphisms :
    (forget (CompHausLike.{u} P)).ReflectsIsomorphisms :=
  ⟨by intro A B f hf; exact isIso_of_bijective _ ((isIso_iff_bijective f).mp hf)⟩

/-- Any continuous bijection of compact Hausdorff spaces induces an isomorphism. -/
noncomputable def isoOfBijective {X Y : CompHausLike.{u} P} (f : X ⟶ Y)
    (bij : Function.Bijective f) : X ≅ Y :=
  letI := isIso_of_bijective _ bij
  asIso f

/-- Construct an isomorphism from a homeomorphism. -/
@[simps!]
def isoOfHomeo {X Y : CompHausLike.{u} P} (f : X ≃ₜ Y) : X ≅ Y :=
  (fullyFaithfulCompHausLikeToTop P).preimageIso (TopCat.isoOfHomeo f)

/-- Construct a homeomorphism from an isomorphism. -/
@[simps!]
def homeoOfIso {X Y : CompHausLike.{u} P} (f : X ≅ Y) : X ≃ₜ Y :=
  TopCat.homeoOfIso <| (compHausLikeToTop P).mapIso f

/-- The equivalence between isomorphisms in `CompHaus` and homeomorphisms
of topological spaces. -/
@[simps]
def isoEquivHomeo {X Y : CompHausLike.{u} P} : (X ≅ Y) ≃ (X ≃ₜ Y) where
  toFun := homeoOfIso
  invFun := isoOfHomeo
  left_inv _ := rfl
  right_inv _ := rfl

end CompHausLike

