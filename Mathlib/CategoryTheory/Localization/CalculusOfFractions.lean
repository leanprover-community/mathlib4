/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Localization.Opposite

/-!
# Calculus of fractions

Following the definitions by [Gabriel and Zisman][gabriel-zisman-1967],
given a morphism property `W : MorphismProperty C` on a category `C`,
we introduce the class `W.HasLeftCalculusOfFractions`. The main
result (TODO) is that if `L : C ⥤ D` is a localization functor for `W`,
then for any morphism `L.obj X ⟶ L.obj Y` in `D`, there exists an auxiliary
object `Y' : C` and morphisms `g : X ⟶ Y'` and `s : Y ⟶ Y'`, with `W s`, such
that the given morphism is a sort of fraction `g / s`, or more precisely of
the form `L.map g ≫ (Localization.isoOfHom L W s hs).inv`.

## References

* [P. Gabriel, M. Zisman, *Calculus of fractions and homotopy theory*][gabriel-zisman-1967]

-/

namespace CategoryTheory

open Category

namespace Functor

lemma congr_map_conjugate {C D : Type _} [Category C] [Category D] {F₁ F₂ : C ⥤ D}
    (h : F₁ = F₂) {X Y : C} (f : X ⟶ Y) :
    F₁.map f = eqToHom (by congr) ≫ F₂.map f ≫ eqToHom (by symm; congr) := by
  subst h
  simp

end Functor

namespace MorphismProperty

variable {C D : Type _} [Category C] [Category D]

/-- A left fraction from `X : C` to `Y : C` for `W : MorphismProperty C` consists of the
datum of an object `Y' : C` and maps `f : X ⟶ Y'` and `s : Y ⟶ Y'` such that `W s`. -/
structure LeftFraction (W : MorphismProperty C) (X Y : C) where
  /-- the auxiliary object of a left fraction -/
  {Y' : C}
  /-- the numerator of a left fraction -/
  f : X ⟶ Y'
  /-- the denominator of a left fraction -/
  s : Y ⟶ Y'
  /-- the condition that the denominator belongs to the given morphism property -/
  hs : W s

namespace LeftFraction

variable (W : MorphismProperty C) {X Y : C}

/-- The left fraction from `X` to `Y` given by a morphism `f : X ⟶ Y`. -/
@[simps]
def ofHom (f : X ⟶ Y) [W.ContainsIdentities] :
  W.LeftFraction X Y := mk f (𝟙 Y) (W.id_mem Y)

variable {W}

/-- The left fraction from `X` to `Y` given by a morphism `s : Y ⟶ X` such that `W s`. -/
@[simps]
def ofInv (s : Y ⟶ X) (hs : W s) :
  W.LeftFraction X Y := mk (𝟙 X) s hs

/-- If `φ : W.LeftFraction X Y` and `L` is a functor which inverts `W`, this is the
induced morphism `L.obj X ⟶ L.obj Y`  -/
noncomputable def map (φ : W.LeftFraction X Y) (L : C ⥤ D) (hL : W.IsInvertedBy L) :
    L.obj X ⟶ L.obj Y :=
  have := hL _ φ.hs
  L.map φ.f ≫ inv (L.map φ.s)

@[reassoc (attr := simp, nolint unusedHavesSuffices)]
lemma map_comp_map_s (φ : W.LeftFraction X Y) (L : C ⥤ D) (hL : W.IsInvertedBy L) :
    φ.map L hL ≫ L.map φ.s = L.map φ.f := by
  have := hL _ φ.hs
  simp [map]

variable (W)

lemma map_ofHom (f : X ⟶ Y) (L : C ⥤ D) (hL : W.IsInvertedBy L) [W.ContainsIdentities] :
    (ofHom W f).map L hL = L.map f := by
  simp [map]

@[reassoc (attr := simp, nolint unusedHavesSuffices)]
lemma map_ofInv_hom_id (s : Y ⟶ X) (hs : W s) (L : C ⥤ D) (hL : W.IsInvertedBy L) :
    (ofInv s hs).map L hL ≫ L.map s = 𝟙 _ := by
  have := hL _ hs
  simp [map]

@[reassoc (attr := simp, nolint unusedHavesSuffices)]
lemma map_hom_ofInv_id (s : Y ⟶ X) (hs : W s) (L : C ⥤ D) (hL : W.IsInvertedBy L) :
    L.map s ≫ (ofInv s hs).map L hL = 𝟙 _ := by
  have := hL _ hs
  simp [map]

variable {W}

lemma cases (α : W.LeftFraction X Y) :
    ∃ (Y' : C) (f : X ⟶ Y') (s : Y ⟶ Y') (hs : W s), α = LeftFraction.mk f s hs :=
  ⟨_, _, _, _, rfl⟩

end LeftFraction

/-- A right fraction from `X : C` to `Y : C` for `W : MorphismProperty C` consists of the
datum of an object `X' : C` and maps `s : X' ⟶ X` and `f : X' ⟶ Y` such that `W s`. -/
structure RightFraction (W : MorphismProperty C) (X Y : C) where
  /-- the auxiliary object of a right fraction -/
  {X' : C}
  /-- the denominator of a right fraction -/
  s : X' ⟶ X
  /-- the condition that the denominator belongs to the given morphism property -/
  hs : W s
  /-- the numerator of a right fraction -/
  f : X' ⟶ Y

namespace RightFraction

variable (W : MorphismProperty C)

variable {X Y : C}

/-- The right fraction from `X` to `Y` given by a morphism `f : X ⟶ Y`. -/
@[simps]
def ofHom (f : X ⟶ Y) [W.ContainsIdentities] :
  W.RightFraction X Y := mk (𝟙 X) (W.id_mem X) f

variable {W}

/-- The right fraction from `X` to `Y` given by a morphism `s : Y ⟶ X` such that `W s`. -/
@[simps]
def ofInv (s : Y ⟶ X) (hs : W s) :
  W.RightFraction X Y := mk s hs (𝟙 Y)

/-- If `φ : W.RightFraction X Y` and `L` is a functor which inverts `W`, this is the
induced morphism `L.obj X ⟶ L.obj Y`  -/
noncomputable def map (φ : W.RightFraction X Y) (L : C ⥤ D) (hL : W.IsInvertedBy L) :
    L.obj X ⟶ L.obj Y :=
  have := hL _ φ.hs
  inv (L.map φ.s) ≫ L.map φ.f

@[reassoc (attr := simp, nolint unusedHavesSuffices)]
lemma map_s_comp_map (φ : W.RightFraction X Y) (L : C ⥤ D) (hL : W.IsInvertedBy L) :
    L.map φ.s ≫ φ.map L hL = L.map φ.f := by
  have := hL _ φ.hs
  simp [map]

variable (W)

@[simp]
lemma map_ofHom (f : X ⟶ Y) (L : C ⥤ D) (hL : W.IsInvertedBy L) [W.ContainsIdentities] :
    (ofHom W f).map L hL = L.map f := by
  simp [map]

@[reassoc (attr := simp, nolint unusedHavesSuffices)]
lemma map_ofInv_hom_id (s : Y ⟶ X) (hs : W s) (L : C ⥤ D) (hL : W.IsInvertedBy L) :
    (ofInv s hs).map L hL ≫ L.map s = 𝟙 _ := by
  have := hL _ hs
  simp [map]

@[reassoc (attr := simp, nolint unusedHavesSuffices)]
lemma map_hom_ofInv_id (s : Y ⟶ X) (hs : W s) (L : C ⥤ D) (hL : W.IsInvertedBy L) :
    L.map s ≫ (ofInv s hs).map L hL = 𝟙 _ := by
  have := hL _ hs
  simp [map]

variable {W}

lemma cases (α : W.RightFraction X Y) :
    ∃ (X' : C) (s : X' ⟶ X) (hs : W s) (f : X' ⟶ Y) , α = RightFraction.mk s hs f :=
  ⟨_, _, _, _, rfl⟩

end RightFraction

variable (W : MorphismProperty C)

class HasLeftCalculusOfFractions extends W.IsMultiplicative : Prop where
  exists_leftFraction ⦃X Y : C⦄ (φ : W.RightFraction X Y) :
    ∃ (ψ : W.LeftFraction X Y), φ.f ≫ ψ.s = φ.s ≫ ψ.f
  ext : ∀ ⦃X' X Y : C⦄ (f₁ f₂ : X ⟶ Y) (s : X' ⟶ X) (_ : W s)
    (_ : s ≫ f₁ = s ≫ f₂), ∃ (Y' : C) (t : Y ⟶ Y') (_ : W t), f₁ ≫ t = f₂ ≫ t

class HasRightCalculusOfFractions extends W.IsMultiplicative : Prop where
  exists_rightFraction ⦃X Y : C⦄ (φ : W.LeftFraction X Y) :
    ∃ (ψ : W.RightFraction X Y), ψ.s ≫ φ.f = ψ.f ≫ φ.s
  ext : ∀ ⦃X Y Y' : C⦄ (f₁ f₂ : X ⟶ Y) (s : Y ⟶ Y') (_ : W s)
    (_ : f₁ ≫ s = f₂ ≫ s), ∃ (X' : C) (t : X' ⟶ X) (_ : W t), t ≫ f₁ = t ≫ f₂

end MorphismProperty

end CategoryTheory
