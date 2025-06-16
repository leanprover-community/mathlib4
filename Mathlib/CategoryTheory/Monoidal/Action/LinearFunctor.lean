/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
import Mathlib.CategoryTheory.Monoidal.Action.Basic

/-! # Functors that are linear with respect to an action

Given a monoidal category `C` acting on the left or on the right on categories
`D` and `D'`, we introduce the following typeclasses on functors `F : D ⥤ D` to
express compatibility of `F` with the action of `C`:
* `F.LaxLeftLinear C` bundles the "μₗ" as a morphism
  `c ⊙ₗ F.obj d ⟶ F.obj (c ⊙ₗ d)`.
* `F.LaxRightLinear` bundles the "μₗ" as a morphism
  `F.obj d ᵣ⊙ c ⟶ F.obj (d ᵣ⊙ c)`.
* `F.OplaxLeftLinear`.
* `F.OplaxRightLinear`.

-/

namespace CategoryTheory.Functor

variable {D D' : Type*} [Category D] [Category D']

open MonoidalCategory

section leftAction

open MonoidalLeftAction

/-- `F.LaxLinear C` equips `F : D ⥤ D'` with a family of morphisms
`μₗ F : ∀ (c : C) (d : D), c ⊙ₗ F.obj d ⟶ F.obj (c ⊙ₗ d)`
that is natural in each variable and coherent with respect to left actions
of `C` on `D` and `D'`. -/
class LaxLeftLinear
    (F : D ⥤ D') (C : Type*) [Category C] [MonoidalCategory C]
    [MonoidalLeftAction C D] [MonoidalLeftAction C D'] where
  /-- The "μₗ" morphism. -/
  μₗ (F) (c : C) (d : D) : c ⊙ₗ F.obj d ⟶ F.obj (c ⊙ₗ d)
  μₗ_naturality_left (F) {c c': C} (f : c ⟶ c') (d : D) :
    f ⊵ₗ F.obj d ≫ μₗ c' d = μₗ c d ≫ F.map (f ⊵ₗ d) := by aesop_cat
  μₗ_naturality_right (F) (c : C) {d d' : D} (f : d ⟶ d') :
    c ⊴ₗ F.map f ≫ μₗ c d' = μₗ c d ≫ F.map (c ⊴ₗ f) := by aesop_cat
  μₗ_associativity (F) (c c' : C) (d : D) :
    μₗ (c ⊗ c') d ≫ F.map (αₗ _ _ _).hom =
    (αₗ c c' (F.obj d)).hom ≫ c ⊴ₗ μₗ c' d ≫
      μₗ c (c' ⊙ₗ d) := by aesop_cat
  μₗ_unitality (F) (d : D) :
    (λₗ (F.obj d)).hom = μₗ (𝟙_ C) d ≫ F.map (λₗ d).hom := by aesop_cat

namespace LaxLeftLinear

-- These are [reassoc (attr := simp)] on the basis that analog lemmas for
-- lax monoidal functors are also [reassoc (attr := simp)].
attribute [reassoc (attr := simp)] μₗ_naturality_right
attribute [reassoc (attr := simp)] μₗ_naturality_left
attribute [reassoc (attr := simp)] μₗ_associativity
attribute [simp, reassoc] μₗ_unitality

variable
  (F : D ⥤ D') {C : Type*} [Category C] [MonoidalCategory C]
  [MonoidalLeftAction C D] [MonoidalLeftAction C D']
  [F.LaxLeftLinear C]

@[reassoc (attr := simp)]
lemma μₗ_associativity_inv (c c' : C) (d : D) :
    c ⊴ₗ μₗ F c' d ≫ μₗ F c (c' ⊙ₗ d) ≫ F.map (αₗ _ _ _).inv =
    (αₗ c c' (F.obj d)).inv ≫ μₗ F (c ⊗ c') d := by
  simpa [-μₗ_associativity, -μₗ_associativity_assoc] using
    (αₗ _ _ _).inv ≫=
      (μₗ_associativity F c c' d).symm =≫
      F.map (αₗ _ _ _).inv

@[reassoc (attr := simp)]
lemma μₗ_unitality_inv (d : D) :
     (λₗ (F.obj d)).inv ≫ μₗ F (𝟙_ C) d = F.map (λₗ d).inv := by
  simpa [-μₗ_unitality] using
    (λₗ[C] (F.obj d)).inv ≫=
      (μₗ_unitality F d).symm =≫
      F.map (λₗ[C] d).inv

end LaxLeftLinear

/-- `F.OplaxLinear C` equips `F : D ⥤ D'` with a family of morphisms
`δₗ F : ∀ (c : C) (d : D), c ⊙ₗ F.obj d ⟶ F.obj (c ⊙ₗ d)`
that is natural in each variable and coherent with respect to left actions
of `C` on `D` and `D'`. -/
class OplaxLeftLinear
    (F : D ⥤ D') (C : Type*) [Category C] [MonoidalCategory C]
    [MonoidalLeftAction C D] [MonoidalLeftAction C D'] where
  /-- The oplax lineator morphism morphism. -/
  δₗ (F) (c : C) (d : D) : F.obj (c ⊙ₗ d) ⟶ c ⊙ₗ F.obj d
  δₗ_naturality_left (F) {c c': C} (f : c ⟶ c') (d : D) :
    F.map (f ⊵ₗ d) ≫ δₗ c' d =
    δₗ c d ≫ f ⊵ₗ F.obj d := by aesop_cat
  δₗ_naturality_right (F) (c : C) {d d' : D} (f : d ⟶ d') :
    F.map (c ⊴ₗ f) ≫ δₗ c d' =
    δₗ c d ≫ c ⊴ₗ F.map f := by aesop_cat
  δₗ_associativity (F) (c c' : C) (d : D) :
    δₗ (c ⊗ c') d ≫ (αₗ _ _ _).hom =
    F.map (αₗ _ _ _).hom ≫ δₗ c (c' ⊙ₗ d) ≫
      c ⊴ₗ δₗ c' d := by aesop_cat
  δₗ_unitality_inv (F) (d : D) :
    (λₗ (F.obj d)).inv =
    F.map (λₗ d).inv ≫ δₗ (𝟙_ C) d := by aesop_cat

namespace OplaxLeftLinear

-- These are [reassoc (attr := simp)] on the basis that analog lemmas for
-- oplax monoidal functors are also [reassoc (attr := simp)].
attribute [reassoc (attr := simp)] δₗ_naturality_right
attribute [reassoc (attr := simp)] δₗ_naturality_left
attribute [reassoc (attr := simp)] δₗ_associativity
attribute [simp, reassoc] δₗ_unitality_inv

variable
  (F : D ⥤ D') {C : Type*} [Category C] [MonoidalCategory C]
  [MonoidalLeftAction C D] [MonoidalLeftAction C D']
  [F.OplaxLeftLinear C]

@[reassoc (attr := simp)]
lemma δₗ_associativity_inv (c c' : C) (d : D) :
    δₗ F c (c' ⊙ₗ d) ≫
      c ⊴ₗ δₗ F c' d ≫ (αₗ _ _ _).inv =
    F.map (αₗ _ _ _).inv ≫ δₗ F (c ⊗ c' : C) d := by
  simpa [-δₗ_associativity, -δₗ_associativity_assoc] using
    F.map (αₗ _ _ _).inv ≫=
      (δₗ_associativity F c c' d).symm =≫
      (αₗ _ _ _).inv

@[reassoc (attr := simp)]
lemma δₗ_unitality_hom (d : D) :
    δₗ F (𝟙_ C) d ≫ (λₗ (F.obj d)).hom = F.map (λₗ d).hom := by
  simpa [-δₗ_unitality_inv] using
    F.map (λₗ[C] d).hom ≫=
      (δₗ_unitality_inv F d).symm =≫
      (λₗ[C] (F.obj d)).hom

end OplaxLeftLinear

/-- `F.LeftLinear C` asserts that `F` is both lax and oplax left-linear,
in a compatible way, i.e that `μₗ` is inverse to `δₗ`. -/
class LeftLinear
    (F : D ⥤ D') (C : Type*) [Category C] [MonoidalCategory C]
    [MonoidalLeftAction C D] [MonoidalLeftAction C D'] extends
    F.LaxLeftLinear C, F.OplaxLeftLinear C where
  μₗ_comp_δₗ (F) (c : C) (d : D) :
    LaxLeftLinear.μₗ F c d ≫ OplaxLeftLinear.δₗ F c d = 𝟙 _
  δₗ_comp_μₗ (F) (c : C) (d : D) :
    OplaxLeftLinear.δₗ F c d ≫ LaxLeftLinear.μₗ F c d = 𝟙 _

namespace LeftLinear

open LaxLeftLinear OplaxLeftLinear

variable
  (F : D ⥤ D') {C : Type*} [Category C] [MonoidalCategory C]
  [MonoidalLeftAction C D] [MonoidalLeftAction C D']
  [F.LeftLinear C]

attribute [reassoc (attr := simp)] μₗ_comp_δₗ
attribute [reassoc (attr := simp)] δₗ_comp_μₗ

/-- A shorthand to bundle the μₗ as an isomorphism -/
abbrev ℓ_ (c : C) (d : D) : c ⊙ₗ F.obj d ≅ F.obj (c ⊙ₗ d) where
  hom := LaxLeftLinear.μₗ F c d
  inv := OplaxLeftLinear.δₗ F c d

variable (c : C) (d : D)

instance : IsIso (μₗ F c d) := Iso.isIso_hom (ℓ_ F c d)

instance : IsIso (δₗ F c d) := Iso.isIso_inv (ℓ_ F c d)

@[simp]
lemma inv_μₗ :
    CategoryTheory.inv (μₗ F c d) = δₗ F c d :=
  Eq.symm <| IsIso.eq_inv_of_hom_inv_id <| μₗ_comp_δₗ F c d

@[simp]
lemma inv_δₗ :
    CategoryTheory.inv (δₗ F c d) = μₗ F c d :=
  Eq.symm <| IsIso.eq_inv_of_hom_inv_id <| δₗ_comp_μₗ F c d

end LeftLinear

end leftAction


end CategoryTheory.Functor
