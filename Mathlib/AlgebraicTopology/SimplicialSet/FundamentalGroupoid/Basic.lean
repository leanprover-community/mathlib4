/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.HomotopyCat
public import Mathlib.CategoryTheory.Groupoid.FreeGroupoidOfCategory
public import Mathlib.CategoryTheory.IsoCat

/-!
# The fundamental groupoid of a simplicial set

-/

@[expose] public section

universe u

open CategoryTheory Simplicial SimplicialObject.Truncated

namespace SSet.Truncated

open Simplicial

/-- The fundamental groupoid of a `2`-truncated simpicial set. -/
def FundamentalGroupoid (X : SSet.Truncated.{u} 2) : Type u :=
  FreeGroupoid X.HomotopyCategory
deriving Groupoid

namespace FundamentalGroupoid

variable {X : SSet.Truncated.{u} 2}

def mk (x : X _⦋0⦌₂) : FundamentalGroupoid X := FreeGroupoid.mk (.mk x)

def homMk {x y : X _⦋0⦌₂} (e : Edge x y) : mk x ⟶ mk y :=
  FreeGroupoid.homMk (HomotopyCategory.homMk e)

@[simp]
lemma homMk_id (x : X _⦋0⦌₂) : homMk (Edge.id x) = 𝟙 (mk x) :=
  ((FreeGroupoid.of X.HomotopyCategory).congr_map (by simp)).trans
    ((FreeGroupoid.of X.HomotopyCategory).map_id _)

@[reassoc]
lemma homMk_comp {x₀ x₁ x₂ : X _⦋0⦌₂} {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂}
    {e₀₂ : Edge x₀ x₂} (h : Edge.CompStruct e₀₁ e₁₂ e₀₂) :
    homMk e₀₁ ≫ homMk e₁₂ = homMk e₀₂ := by
  simpa using! (FreeGroupoid.of X.HomotopyCategory).congr_map
    (HomotopyCategory.homMk_comp_homMk h)

end FundamentalGroupoid

def mapFundamentalGroupoid {X Y : SSet.Truncated.{u} 2} (f : X ⟶ Y) :
    FundamentalGroupoid X ⥤ FundamentalGroupoid Y :=
  FreeGroupoid.map (mapHomotopyCategory f)

lemma mapFundamentalGroupoid_id (X : SSet.Truncated.{u} 2) :
    mapFundamentalGroupoid (𝟙 X) = 𝟭 _ := by
  dsimp [mapFundamentalGroupoid]
  rw [mapHomotopyCategory_id, FreeGroupoid.map_id]
  rfl

lemma mapFundamentalGroupoid_comp {X Y Z : SSet.Truncated.{u} 2} (f : X ⟶ Y) (g : Y ⟶ Z) :
    mapFundamentalGroupoid (f ≫ g) = mapFundamentalGroupoid f ⋙ mapFundamentalGroupoid g := by
  dsimp [mapFundamentalGroupoid]
  rw [mapHomotopyCategory_comp, FreeGroupoid.map_comp]
  rfl

def mapIsoFundamentalGroupoid {X Y : SSet.Truncated.{u} 2} (e : X ≅ Y) :
    IsoCat (FundamentalGroupoid X) (FundamentalGroupoid Y) where
  functor := mapFundamentalGroupoid e.hom
  inverse := mapFundamentalGroupoid e.inv
  unit_eq := by rw [← mapFundamentalGroupoid_comp, e.hom_inv_id, mapFundamentalGroupoid_id]
  counit_eq := by rw [← mapFundamentalGroupoid_comp, e.inv_hom_id, mapFundamentalGroupoid_id]

instance {X Y : SSet.Truncated.{u} 2} (f : X ⟶ Y) [IsIso f] :
    (mapFundamentalGroupoid f).IsEquivalence :=
  (mapIsoFundamentalGroupoid (asIso f)).toEquivalence.isEquivalence_functor

end SSet.Truncated

namespace SSet

variable {X Y : SSet.{u}}

variable (X) in
def FundamentalGroupoid : Type u :=
  ((truncation 2).obj X).FundamentalGroupoid
deriving Groupoid

def mk (x : X _⦋0⦌) : FundamentalGroupoid X :=
  Truncated.FundamentalGroupoid.mk x

lemma mk_surjective : Function.Surjective (mk (X := X)) :=
  fun ⟨⟨⟨⟨x⟩⟩⟩⟩ ↦ ⟨x, rfl⟩

@[elab_as_elim, cases_eliminator, induction_eliminator]
def rec {motive : FundamentalGroupoid X → Sort*}
    (mk : ∀ (x : X _⦋0⦌), motive (mk x)) (x : FundamentalGroupoid X) :
    motive x :=
  mk _

def homMk {x y : X _⦋0⦌} (e : Edge x y) : mk x ⟶ mk y :=
  Truncated.FundamentalGroupoid.homMk e

@[simp]
lemma homMk_id (x : X _⦋0⦌) : homMk (Edge.id x) = 𝟙 (mk x) :=
  Truncated.FundamentalGroupoid.homMk_id _

@[elab_as_elim, cases_eliminator, induction_eliminator]
lemma hom_rec {motive : ∀ ⦃x y : FundamentalGroupoid X⦄ (f : x ⟶ y), Prop}
    (homMk : ∀ ⦃x y : X _⦋0⦌⦄ (e : Edge x y), motive (homMk e))
    (inv : ∀ ⦃x y : FundamentalGroupoid X⦄ (f : x ⟶ y), motive f → motive (inv f))
    (comp : ∀ ⦃x y z : FundamentalGroupoid X⦄ (f : x ⟶ y) (g : y ⟶ z),
      motive f → motive g → motive (f ≫ g))
    {x y : FundamentalGroupoid X} (f : x ⟶ y) :
    motive f := sorry

@[reassoc]
lemma homMk_comp {x₀ x₁ x₂ : X _⦋0⦌} {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂}
    {e₀₂ : Edge x₀ x₂} (h : Edge.CompStruct e₀₁ e₁₂ e₀₂) :
    homMk e₀₁ ≫ homMk e₁₂ = homMk e₀₂ :=
  Truncated.FundamentalGroupoid.homMk_comp h

def mapFundamentalGroupoid (f : X ⟶ Y) :
    FundamentalGroupoid X ⥤ FundamentalGroupoid Y :=
  SSet.Truncated.mapFundamentalGroupoid ((truncation 2).map f)

noncomputable def isoCatMapFundamentalGroupoid (f : X ⟶ Y)
    (hf : IsIso ((truncation 2).map f) := by infer_instance) :
    IsoCat (FundamentalGroupoid X) (FundamentalGroupoid Y) :=
  Truncated.mapIsoFundamentalGroupoid (asIso ((truncation 2).map f))

lemma isEquivalence_mapFundamentalGroupoid (f : X ⟶ Y)
    (hf : IsIso ((truncation 2).map f) := by infer_instance) :
    (mapFundamentalGroupoid f).IsEquivalence :=
  (isoCatMapFundamentalGroupoid f).toEquivalence.isEquivalence_functor

end SSet
