/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.SpectralObject.Basic
public import Mathlib.CategoryTheory.Triangulated.Triangulated
public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
public import Mathlib.CategoryTheory.ComposableArrows.One
public import Mathlib.CategoryTheory.ComposableArrows.Two
public import Mathlib.CategoryTheory.Triangulated.Functor

/-!
# Spectral objects in triangulated categories

In this file, we introduce the category `SpectralObject C ι` of spectral
objects in a pretriangulated category `C` indexed by the category `ι`.

## References
* [Jean-Louis Verdier, *Des catégories dérivées des catégories abéliennes*, II.4][verdier1996]

-/

@[expose] public section

namespace CategoryTheory

open Limits Pretriangulated ComposableArrows

variable (C ι : Type*) [Category* C] [Category* ι] [HasZeroObject C]
  [HasShift C ℤ] [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]
  {D : Type*} [Category* D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D]

namespace Triangulated

/-- A spectral object in a pretriangulated category `C` indexed by a category `ι` consists
of a functor `ω₁ : ComposableArrows ι 1 ⥤ C`, and a functorial distinguished triangle
from the category `ComposableArrows ι 2`, which must be of the form
`ω₁.obj (mk₁ f) ⟶ ω₁.obj (mk₁ (f ≫ g)) ⟶ ω₁.obj (mk₁ g) ⟶ ...` when evaluated
on `mk₂ f g : ComposableArrows ι 2`. -/
structure SpectralObject where
  /-- A functor from `ComposableArrows ι 1` to the pretriangulated category. -/
  ω₁ : ComposableArrows ι 1 ⥤ C
  /-- The connecting homomorphism of the spectral object. -/
  δ' : functorArrows ι 1 2 2 ⋙ ω₁ ⟶ functorArrows ι 0 1 2 ⋙ ω₁ ⋙ shiftFunctor C (1 : ℤ)
  distinguished' (D : ComposableArrows ι 2) :
    Triangle.mk (ω₁.map ((mapFunctorArrows ι 0 1 0 2 2).app D))
      (ω₁.map ((mapFunctorArrows ι 0 2 1 2 2).app D)) (δ'.app D) ∈ distTriang C

namespace SpectralObject

variable {C ι} (X : SpectralObject C ι)

/-- The functorial (distinguished) triangle attached to a spectral object in
a pretriangulated category. -/
@[simps!]
noncomputable def ω₂ : ComposableArrows ι 2 ⥤ Triangle C :=
  Triangle.functorMk (Functor.whiskerRight (mapFunctorArrows ι 0 1 0 2 2) X.ω₁)
    (Functor.whiskerRight (mapFunctorArrows ι 0 2 1 2 2) X.ω₁) X.δ'

lemma ω₂_obj_distinguished (D : ComposableArrows ι 2) :
    X.ω₂.obj D ∈ distTriang C :=
  X.distinguished' D

section

variable {i j k : ι} (f : i ⟶ j) (g : j ⟶ k)

/-- The connecting homomorphism `X.ω₁.obj (mk₁ g) ⟶ (X.ω₁.obj (mk₁ f))⟦(1 : ℤ)⟧`
of a spectral object `X` in a pretriangulated category when `f : i ⟶ j` and `g : j ⟶ k`
are composable. -/
def δ : X.ω₁.obj (mk₁ g) ⟶ (X.ω₁.obj (mk₁ f))⟦(1 : ℤ)⟧ :=
  X.δ'.app (mk₂ f g)

@[reassoc]
lemma δ_naturality {i' j' k' : ι} (f' : i' ⟶ j') (g' : j' ⟶ k')
    (α : mk₁ f ⟶ mk₁ f') (β : mk₁ g ⟶ mk₁ g') (hαβ : α.app 1 = β.app 0) :
    X.ω₁.map β ≫ X.δ f' g' = X.δ f g ≫ (X.ω₁.map α)⟦(1 : ℤ)⟧' := by
  let φ : mk₂ f g ⟶ mk₂ f' g' := homMk₂ (α.app 0) (α.app 1) (β.app 1) (naturality' α 0 1)
    (by simpa only [hαβ] using naturality' β 0 1)
  have h := X.δ'.naturality φ
  dsimp at h
  simp only [φ, hαβ] at h
  convert h <;> aesop_cat


/-- The distinguished triangle attached to a spectral object `E : SpectralObjet C ι`
and composable morphisms `f : i ⟶ j` and `g : j ⟶ k` in `ι`. -/
@[simps!]
def triangle : Triangle C :=
  Triangle.mk (X.ω₁.map (twoδ₂Toδ₁ f g _ rfl))
    (X.ω₁.map (twoδ₁Toδ₀ f g _ rfl)) (X.δ f g)

lemma triangle_distinguished : X.triangle f g ∈ distTriang C :=
  X.ω₂_obj_distinguished (mk₂ f g)

section

variable {f g}
variable {i' j' k' : ι} {f' : i' ⟶ j'} {g' : j' ⟶ k'}

noncomputable def mapTriangle (φ : mk₂ f g ⟶ mk₂ f' g') :
    X.triangle f g ⟶ X.triangle f' g' where
  hom₁ := X.ω₁.map ((functorArrows ι 0 1 2).map φ)
  hom₂ := X.ω₁.map ((functorArrows ι 0 2 2).map φ)
  hom₃ := X.ω₁.map ((functorArrows ι 1 2 2).map φ)
  comm₁ := by
    dsimp
    simp only [← X.ω₁.map_comp]
    congr 1
    ext
    · simp
    · exact naturality' φ 1 2
  comm₂ := by
    dsimp
    simp only [← X.ω₁.map_comp]
    congr 1
    ext
    · exact naturality' φ 0 1
    · simp
  comm₃ := by
    symm
    apply X.δ_naturality
    rfl

end

end
variable {ι' : Type*} [Category ι'] (F : ι' ⥤ ι)

attribute [local simp] Precomp.map Precomp.obj δ in
/-- The precomposition of a spectral object with a functor. -/
def precomp : SpectralObject C ι' where
  ω₁ := F.mapComposableArrows 1 ⋙ X.ω₁
  δ'.app D := X.ω₁.map (F.mapComposableArrowsObjMk₁Iso _).hom ≫
      X.δ'.app ((F.mapComposableArrows 2).obj D) ≫
      (X.ω₁.map (F.mapComposableArrowsObjMk₁Iso _).inv)⟦1⟧'
  δ'.naturality D₁ D₂ f := by
    have := X.δ'.naturality ((F.mapComposableArrows 2).map f)
    rw [← cancel_epi (X.ω₁.map (F.mapComposableArrowsObjMk₁Iso _).hom)] at this
    rw [← cancel_mono ((X.ω₁.map (F.mapComposableArrowsObjMk₁Iso _).hom)⟦(1 : ℤ)⟧')]
    dsimp at this ⊢
    simp only [← Functor.map_comp_assoc, ← Functor.map_comp, Category.assoc,
      Iso.inv_hom_id, Functor.map_id, Category.comp_id] at this ⊢
    convert this using 3
    · cat_disch
    · congr 2; cat_disch
  distinguished' D := by
    obtain ⟨_, _, _, f, g, rfl⟩ := ComposableArrows.mk₂_surjective D
    refine isomorphic_distinguished _ (X.triangle_distinguished (F.map f) (F.map g)) _ ?_
    refine Triangle.isoMk _ _ (X.ω₁.mapIso (ComposableArrows.isoMk₁ (Iso.refl _) (Iso.refl _)))
      (X.ω₁.mapIso (ComposableArrows.isoMk₁ (Iso.refl _) (Iso.refl _)))
      (X.ω₁.mapIso (ComposableArrows.isoMk₁ (Iso.refl _) (Iso.refl _))) ?_ ?_ ?_
    · dsimp
      simp only [← Functor.map_comp]
      congr 1
      cat_disch
    · dsimp
      simp only [← Functor.map_comp]
      congr 1
      cat_disch
    · have := X.δ'.naturality (F.mapComposableArrowsObjMk₂Iso f g).hom
      dsimp at this ⊢
      rw [← cancel_epi (X.ω₁.map (F.mapComposableArrowsObjMk₁Iso _).inv)]
      simp only [← Functor.map_comp_assoc, ← Functor.map_comp, Category.assoc,
        Iso.inv_hom_id, Functor.map_id, Category.id_comp] at this ⊢
      convert this.symm using 3
      · congr; cat_disch
      · cat_disch

section

variable (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]

/-- The image of a spectral by a triangulated functor. -/
@[simps]
def mapTriangulatedFunctor :
    SpectralObject D ι where
  ω₁ := X.ω₁ ⋙ F
  δ' := Functor.whiskerRight X.δ' F ≫
      Functor.whiskerLeft (functorArrows ι 0 1 2 ⋙ X.ω₁) (F.commShiftIso (1 : ℤ)).hom
  distinguished' D := F.map_distinguished _ (X.distinguished' D)

@[simp]
lemma mapTriangulatedFunctor_δ {i j k : ι} (f : i ⟶ j) (g : j ⟶ k) :
    (X.mapTriangulatedFunctor F).δ f g = F.map (X.δ f g) ≫ (F.commShiftIso 1).hom.app _ := rfl

end

/-- The type of morphisms between spectral objects in pretriangulated categories. -/
@[ext]
structure Hom (Y : SpectralObject C ι) where
  /-- The natural transformation that is part of a morphism between spectral objects. -/
  hom : X.ω₁ ⟶ Y.ω₁
  comm {i j k : ι} (f : i ⟶ j) (g : j ⟶ k) :
    X.δ f g ≫ (hom.app (mk₁ f))⟦(1 : ℤ)⟧' = hom.app (mk₁ g) ≫ Y.δ f g := by cat_disch

attribute [reassoc (attr := simp)] Hom.comm

@[simps id_hom comp_hom]
instance : Category (SpectralObject C ι) where
  Hom := Hom
  id X := { hom := 𝟙 _ }
  comp f g :=
    { hom := f.hom ≫ g.hom }

attribute [simp] id_hom
attribute [reassoc (attr := simp)] comp_hom

variable {X} in
@[ext]
lemma hom_ext {Y : SpectralObject C ι} {α β : X ⟶ Y} (h : α.hom = β.hom) : α = β := Hom.ext h

section

variable {A : Type*} [Category A] [Abelian A]
  (F : C ⥤ A) [F.IsHomological] [F.ShiftSequence ℤ]

@[simps]
noncomputable def mapHomologicalFunctor : Abelian.SpectralObject A ι where
  H n := X.ω₁ ⋙ F.shift n
  δ' n₀ n₁ h :=
    { app D := F.homologySequenceδ (X.triangle (D.map' 0 1) (D.map' 1 2)) n₀ n₁ h
      naturality D₁ D₂ φ := by
        obtain ⟨_, _, _, f, g, rfl⟩ := mk₂_surjective D₁
        obtain ⟨_, _, _, f', g', rfl⟩ := mk₂_surjective D₂
        exact F.homologySequenceδ_naturality (X.mapTriangle φ) n₀ n₁ h }
  exact₁' n₀ n₁ h D := by
    obtain ⟨_, _, _, f, g, rfl⟩ := mk₂_surjective D
    exact (F.homologySequence_exact₁ _
      (X.triangle_distinguished f g) n₀ n₁ h).exact_toComposableArrows
  exact₂' n D := by
    obtain ⟨_, _, _, f, g, rfl⟩ := mk₂_surjective D
    exact (F.homologySequence_exact₂ _ (X.triangle_distinguished f g) n).exact_toComposableArrows
  exact₃' n₀ n₁ h D := by
    obtain ⟨_, _, _, f, g, rfl⟩ := mk₂_surjective D
    exact (F.homologySequence_exact₃ _
      (X.triangle_distinguished f g) n₀ n₁ h).exact_toComposableArrows

@[simp]
lemma mapHomologicalFunctor_δ (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) {i j k : ι} (f : i ⟶ j) (g : j ⟶ k) :
    (X.mapHomologicalFunctor F).δ n₀ n₁ h f g =
      F.homologySequenceδ (X.triangle f g) n₀ n₁ h := by
  rfl

end

end SpectralObject

end Triangulated

namespace Functor

variable {C}

/-- The functor between categories of spectral objects that is induced by
a triangulated functor. -/
def mapTriangulatedSpectralObject (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    (ι : Type*) [Category* ι] :
    Triangulated.SpectralObject C ι ⥤ Triangulated.SpectralObject D ι where
  obj X := X.mapTriangulatedFunctor F
  map α :=
    { hom := Functor.whiskerRight α.hom _
      comm f g := by
        have hf := (F.commShiftIso (1 : ℤ)).hom.naturality (α.hom.app (mk₁ f))
        dsimp at hf ⊢
        rw [Category.assoc, ← hf, ← F.map_comp_assoc, α.comm, F.map_comp_assoc] }

end Functor

end CategoryTheory
