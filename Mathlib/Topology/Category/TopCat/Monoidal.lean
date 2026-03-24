/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Topology.Category.TopCat.Limits.Products
public import Mathlib.Topology.UnitInterval
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

/-!
# The cartesian monoidal structure on `TopCat`

We define the cartesian monoidal category structure on `TopCat`.
We also introduce the unit interval as an object `TopCat.I` of `TopCat`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace TopCat

instance : CartesianMonoidalCategory TopCat.{u} :=
  .ofChosenFiniteProducts ⟨_, isTerminalPUnit⟩
    (fun X Y ↦ ⟨prodBinaryFan X Y, X.prodBinaryFanIsLimit Y⟩)

instance : BraidedCategory TopCat.{u} := .ofCartesianMonoidalCategory

@[simp]
theorem tensor_apply {W X Y Z : TopCat.{u}} (f : W ⟶ X) (g : Y ⟶ Z) (p : ↑(W ⊗ Y)) :
    (f ⊗ₘ g).hom p = (f p.1, g p.2) :=
  rfl

@[simp]
theorem whiskerLeft_apply (X : TopCat.{u}) {Y Z : TopCat.{u}} (f : Y ⟶ Z) (p : ↑(X ⊗ Y)) :
    (X ◁ f) p = (p.1, f p.2) :=
  rfl

@[simp]
theorem whiskerRight_apply {Y Z : TopCat.{u}} (f : Y ⟶ Z) (X : TopCat.{u}) (p : ↑(Y ⊗ X)) :
    (f ▷ X) p = (f p.1, p.2) :=
  rfl

@[simp]
theorem leftUnitor_hom_apply {X : TopCat.{u}} {x : X} {p : PUnit.{u + 1}} :
    (λ_ X).hom (p, x) = x :=
  rfl

@[simp]
theorem leftUnitor_inv_apply {X : TopCat.{u}} {x : X} :
    (λ_ X).inv x = (PUnit.unit, x) :=
  rfl

@[simp]
theorem rightUnitor_hom_apply {X : TopCat.{u}} {x : X} {p : PUnit.{u + 1}} :
    (ρ_ X).hom (x, p) = x :=
  rfl

@[simp]
theorem rightUnitor_inv_apply {X : TopCat.{u}} {x : X} :
    (ρ_ X).inv x = (x, .unit) :=
  rfl

@[simp]
theorem associator_hom_apply {X Y Z : TopCat.{u}} {x : X} {y : Y} {z : Z} :
    (α_ X Y Z).hom ((x, y), z) = (x, (y, z)) :=
  rfl

@[simp]
theorem associator_inv_apply {X Y Z : TopCat.{u}} {x : X} {y : Y} {z : Z} :
    (α_ X Y Z).inv (x, (y, z)) = ((x, y), z) :=
  rfl

@[simp] theorem associator_hom_apply_1 {X Y Z : TopCat.{u}} {x} :
    ((α_ X Y Z).hom x).1 = x.1.1 :=
  rfl

@[simp] theorem associator_hom_apply_2_1 {X Y Z : TopCat.{u}} {x} :
    ((α_ X Y Z).hom x).2.1 = x.1.2 :=
  rfl

@[simp] theorem associator_hom_apply_2_2 {X Y Z : TopCat.{u}} {x} :
    ((α_ X Y Z).hom x).2.2 = x.2 :=
  rfl

@[simp] theorem associator_inv_apply_1_1 {X Y Z : TopCat.{u}} {x} :
    ((α_ X Y Z).inv x).1.1 = x.1 :=
  rfl

@[simp] theorem associator_inv_apply_1_2 {X Y Z : TopCat.{u}} {x} :
    ((α_ X Y Z).inv x).1.2 = x.2.1 :=
  rfl

@[simp] theorem associator_inv_apply_2 {X Y Z : TopCat.{u}} {x} :
    ((α_ X Y Z).inv x).2 = x.2.2 :=
  rfl

@[simp]
theorem braiding_hom_apply {X Y : TopCat.{u}} {x : X} {y : Y} :
    (β_ X Y).hom (x, y) = (y, x) :=
  rfl

@[simp]
theorem braiding_inv_apply {X Y : TopCat.{u}} {x : X} {y : Y} :
    (β_ X Y).inv (y, x) = (x, y) :=
  rfl

@[simp]
protected theorem lift_apply {X Y Z : TopCat.{u}} {f : X ⟶ Y} {g : X ⟶ Z} {x : X} :
    CartesianMonoidalCategory.lift f g x = (f x, g x) :=
  rfl

/-- The unit interval, as an object of `TopCat`. -/
def I : TopCat.{u} := TopCat.of (ULift unitInterval)

instance : LocallyCompactSpace I :=
  inferInstanceAs (LocallyCompactSpace (ULift unitInterval))

/-- The unit interval `TopCat.I` is homeomorphic to `unitInterval`. -/
def homeomorphI : I ≃ₜ unitInterval := Homeomorph.ulift

/-- Constructor for elements in `TopCat.I`. -/
def I.mk (t : unitInterval) : I := ULift.up t

@[continuity]
lemma I.continuous_mk : Continuous I.mk.{u} := continuous_uliftUp

/-- The symmetrization map `TopCat.I ⟶ TopCat.I`. -/
def I.symm : I.{u} → I := fun t ↦ I.mk (unitInterval.symm t.down)

@[continuity]
lemma I.continuous_symm : Continuous I.symm.{u} := by
  change Continuous ((I.mk.comp unitInterval.symm).comp ULift.down)
  continuity

instance : OfNat I 0 := ⟨I.mk 0⟩
instance : OfNat I 1 := ⟨I.mk 1⟩

set_option backward.isDefEq.respectTransparency false in
@[simp] lemma I.symm_one : I.symm 1 = 0 := by simp [I.symm]; rfl
set_option backward.isDefEq.respectTransparency false in
@[simp] lemma I.symm_zero : I.symm 0 = 1 := by simp [I.symm]; rfl

open CartesianMonoidalCategory

/-- The inclusion `X ⟶ X ⊗ I` given by `0 : I` for `X : TopCat`. -/
noncomputable def ι₀ {X : TopCat.{u}} : X ⟶ X ⊗ I :=
  lift (𝟙 X) (const 0)

@[reassoc (attr := simp)]
lemma ι₀_comp {X Y : TopCat.{u}} (f : X ⟶ Y) : ι₀ ≫ f ▷ _ = f ≫ ι₀ := rfl

@[reassoc (attr := simp)]
lemma ι₀_fst (X : TopCat.{u}) : ι₀ ≫ fst X _ = 𝟙 X := rfl

@[reassoc (attr := simp)]
lemma ι₀_snd (X : TopCat.{u}) : ι₀ ≫ snd X _ = TopCat.const 0 := rfl

@[simp] lemma ι₀_apply {X : TopCat.{u}} (x : X) : ι₀ x = ⟨x, 0⟩ := rfl

/-- The inclusion `X ⟶ X ⊗ I` given by `1 : I` for `X : TopCat`. -/
noncomputable def ι₁ {X : TopCat.{u}} : X ⟶ X ⊗ I :=
  lift (𝟙 X) (const 1)

@[reassoc (attr := simp)]
lemma ι₁_comp {X Y : TopCat.{u}} (f : X ⟶ Y) : ι₁ ≫ f ▷ _ = f ≫ ι₁ := rfl

@[reassoc (attr := simp)]
lemma ι₁_fst (X : TopCat.{u}) : ι₁ ≫ fst X _ = 𝟙 X := rfl

@[reassoc (attr := simp)]
lemma ι₁_snd (X : TopCat.{u}) : ι₁ ≫ snd X _ = const 1 := rfl

@[simp]
lemma ι₁_apply {X : TopCat.{u}} (x : X) : ι₁ x = ⟨x, 1⟩ := rfl

end TopCat
