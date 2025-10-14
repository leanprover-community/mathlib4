/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
import Mathlib.CategoryTheory.Monoidal.Action.Basic

/-! # Functors that are linear with respect to an action

Given a monoidal category `C` acting on the left or on the right on categories
`D` and `D'`, we introduce the following typeclasses on functors `F : D ⥤ D'` to
express compatibility of `F` with the action of `C`:
* `F.LaxLeftLinear C` bundles the "lineator" as a morphism
  `μₗ : c ⊙ₗ F.obj d ⟶ F.obj (c ⊙ₗ d)`.
* `F.LaxRightLinear C` bundles the "lineator" as a morphism
  `μᵣ : F.obj d ⊙ᵣ c ⟶ F.obj (d ⊙ᵣ c)`.
* `F.OplaxLeftLinear C` bundles the "lineator" as a morphism
  `δₗ : F.obj (c ⊙ₗ d) ⟶ c ⊙ₗ F.obj d `.
* `F.OplaxRightLinear C` bundles the "lineator" as a morphism
  `δᵣ : F.obj (d ⊙ᵣ d) ⟶ F.obj d ⊙ᵣ c`.
* `F.LeftLinear C` expresses that `F` has both a `LaxLeftLinear C` and
  an `F.OplaxLeftLinear C` structure, and that they are compatible, i.e
  `δₗ F` is a left and right inverse to `μₗ`.
* `F.RightLinear C` expresses that `F` has both a `LaxRightLinear C` and
  an `F.OplaxRightLinear C` structure, and that they are compatible, i.e
  `δᵣ F` is a left and right inverse to `μᵣ`.

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
    f ⊵ₗ F.obj d ≫ μₗ c' d = μₗ c d ≫ F.map (f ⊵ₗ d) := by cat_disch
  μₗ_naturality_right (F) (c : C) {d d' : D} (f : d ⟶ d') :
    c ⊴ₗ F.map f ≫ μₗ c d' = μₗ c d ≫ F.map (c ⊴ₗ f) := by cat_disch
  μₗ_associativity (F) (c c' : C) (d : D) :
    μₗ (c ⊗ c') d ≫ F.map (αₗ _ _ _).hom =
    (αₗ c c' (F.obj d)).hom ≫ c ⊴ₗ μₗ c' d ≫
      μₗ c (c' ⊙ₗ d) := by cat_disch
  μₗ_unitality (F) (d : D) :
    (λₗ (F.obj d)).hom = μₗ (𝟙_ C) d ≫ F.map (λₗ d).hom := by cat_disch

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
  /-- The oplax lineator morphism. -/
  δₗ (F) (c : C) (d : D) : F.obj (c ⊙ₗ d) ⟶ c ⊙ₗ F.obj d
  δₗ_naturality_left (F) {c c': C} (f : c ⟶ c') (d : D) :
    F.map (f ⊵ₗ d) ≫ δₗ c' d =
    δₗ c d ≫ f ⊵ₗ F.obj d := by cat_disch
  δₗ_naturality_right (F) (c : C) {d d' : D} (f : d ⟶ d') :
    F.map (c ⊴ₗ f) ≫ δₗ c d' =
    δₗ c d ≫ c ⊴ₗ F.map f := by cat_disch
  δₗ_associativity (F) (c c' : C) (d : D) :
    δₗ (c ⊗ c') d ≫ (αₗ _ _ _).hom =
    F.map (αₗ _ _ _).hom ≫ δₗ c (c' ⊙ₗ d) ≫
      c ⊴ₗ δₗ c' d := by cat_disch
  δₗ_unitality_inv (F) (d : D) :
    (λₗ (F.obj d)).inv =
    F.map (λₗ d).inv ≫ δₗ (𝟙_ C) d := by cat_disch

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
abbrev μₗIso (c : C) (d : D) : c ⊙ₗ F.obj d ≅ F.obj (c ⊙ₗ d) where
  hom := LaxLeftLinear.μₗ F c d
  inv := OplaxLeftLinear.δₗ F c d

variable (c : C) (d : D)

instance : IsIso (μₗ F c d) := Iso.isIso_hom (μₗIso F c d)

instance : IsIso (δₗ F c d) := Iso.isIso_inv (μₗIso F c d)

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

section rightAction

open MonoidalRightAction

/-- `F.LaxLinear C` equips `F : D ⥤ D'` with a family of morphisms
`μₗ F : ∀ (c : C) (d : D), c ⊙ₗ F.obj d ⟶ F.obj (c ⊙ₗ d)`
that is natural in each variable and coherent with respect to left actions
of `C` on `D` and `D'`. -/
class LaxRightLinear
    (F : D ⥤ D') (C : Type*) [Category C] [MonoidalCategory C]
    [MonoidalRightAction C D] [MonoidalRightAction C D'] where
  /-- The "μᵣ" morphism. -/
  μᵣ (F) (d : D) (c : C) : F.obj d ⊙ᵣ c ⟶ F.obj (d ⊙ᵣ c)
  μᵣ_naturality_right (F) (d : D) {c c': C} (f : c ⟶ c') :
    F.obj d ⊴ᵣ f ≫ μᵣ d c' = μᵣ d c ≫ F.map (d ⊴ᵣ f) := by cat_disch
  μᵣ_naturality_left (F) {d d' : D} (f : d ⟶ d') (c : C) :
    F.map f ⊵ᵣ c ≫ μᵣ d' c = μᵣ d c ≫ F.map (f ⊵ᵣ c) := by cat_disch
  μᵣ_associativity (F) (d : D) (c c' : C) :
    μᵣ d (c ⊗ c') ≫ F.map (αᵣ _ _ _).hom =
    (αᵣ (F.obj d) c c').hom ≫ (μᵣ d c) ⊵ᵣ c' ≫
      μᵣ (d ⊙ᵣ c) c' := by cat_disch
  μᵣ_unitality (F) (d : D) :
    (ρᵣ (F.obj d)).hom = μᵣ d (𝟙_ C) ≫ F.map (ρᵣ d).hom := by cat_disch

namespace LaxRightLinear

-- These are [reassoc (attr := simp)] on the basis that analog lemmas for
-- lax monoidal functors are also [reassoc (attr := simp)].
attribute [reassoc (attr := simp)] μᵣ_naturality_right
attribute [reassoc (attr := simp)] μᵣ_naturality_left
attribute [reassoc (attr := simp)] μᵣ_associativity
attribute [simp, reassoc] μᵣ_unitality

variable
  (F : D ⥤ D') {C : Type*} [Category C] [MonoidalCategory C]
  [MonoidalRightAction C D] [MonoidalRightAction C D']
  [F.LaxRightLinear C]

@[reassoc (attr := simp)]
lemma μᵣ_associativity_inv (d : D) (c c' : C) :
    μᵣ F d c ⊵ᵣ c' ≫ μᵣ F (d ⊙ᵣ c) c' ≫ F.map (αᵣ _ _ _).inv =
    (αᵣ (F.obj d) c c' ).inv ≫ μᵣ F d (c ⊗ c') := by
  simpa [-μᵣ_associativity, -μᵣ_associativity_assoc] using
    (αᵣ _ _ _).inv ≫=
      (μᵣ_associativity F d c c').symm =≫
      F.map (αᵣ _ _ _).inv

@[reassoc (attr := simp)]
lemma μᵣ_unitality_inv (d : D) :
     (ρᵣ (F.obj d)).inv ≫ μᵣ F d (𝟙_ C) = F.map (ρᵣ d).inv := by
  simpa [-μᵣ_unitality] using
    (ρᵣ[C] (F.obj d)).inv ≫=
      (μᵣ_unitality F d).symm =≫
      F.map (ρᵣ[C] d).inv

end LaxRightLinear

/-- `F.OplaxLinear C` equips `F : D ⥤ D'` with a family of morphisms
`δₗ F : ∀ (c : C) (d : D), c ⊙ₗ F.obj d ⟶ F.obj (c ⊙ₗ d)`
that is natural in each variable and coherent with respect to left actions
of `C` on `D` and `D'`. -/
class OplaxRightLinear
    (F : D ⥤ D') (C : Type*) [Category C] [MonoidalCategory C]
    [MonoidalRightAction C D] [MonoidalRightAction C D'] where
  /-- The oplax lineator morphism. -/
  δᵣ (F) (d : D) (c : C) : F.obj (d ⊙ᵣ c) ⟶ (F.obj d) ⊙ᵣ c
  δᵣ_naturality_right (F) (d : D) {c c': C} (f : c ⟶ c') :
    F.map (d ⊴ᵣ f) ≫ δᵣ d c' =
    δᵣ d c ≫ F.obj d ⊴ᵣ f := by cat_disch
  δᵣ_naturality_left (F) {d d' : D} (f : d ⟶ d') (c : C) :
    F.map (f ⊵ᵣ c) ≫ δᵣ d' c =
    δᵣ d c ≫ F.map f ⊵ᵣ c := by cat_disch
  δᵣ_associativity (F) (d : D) (c c' : C) :
    δᵣ d (c ⊗ c') ≫ (αᵣ _ _ _).hom =
    F.map (αᵣ _ _ _).hom ≫ δᵣ (d ⊙ᵣ c) c' ≫
      δᵣ d c ⊵ᵣ c' := by cat_disch
  δᵣ_unitality_inv (F) (d : D) :
    (ρᵣ (F.obj d)).inv =
    F.map (ρᵣ d).inv ≫ δᵣ d (𝟙_ C) := by cat_disch

namespace OplaxRightLinear

-- These are [reassoc (attr := simp)] on the basis that analog lemmas for
-- oplax monoidal functors are also [reassoc (attr := simp)].
attribute [reassoc (attr := simp)] δᵣ_naturality_right
attribute [reassoc (attr := simp)] δᵣ_naturality_left
attribute [reassoc (attr := simp)] δᵣ_associativity
attribute [simp, reassoc] δᵣ_unitality_inv

variable
  (F : D ⥤ D') {C : Type*} [Category C] [MonoidalCategory C]
  [MonoidalRightAction C D] [MonoidalRightAction C D']
  [F.OplaxRightLinear C]

@[reassoc (attr := simp)]
lemma δᵣ_associativity_inv (d : D) (c c' : C) :
    δᵣ F (d ⊙ᵣ c) c' ≫
      δᵣ F d c ⊵ᵣ c' ≫ (αᵣ _ _ _).inv =
    F.map (αᵣ _ _ _).inv ≫ δᵣ F d (c ⊗ c' : C) := by
  simpa [-δᵣ_associativity, -δᵣ_associativity_assoc] using
    F.map (αᵣ _ _ _).inv ≫=
      (δᵣ_associativity F d c c').symm =≫
      (αᵣ _ _ _).inv

@[reassoc (attr := simp)]
lemma δᵣ_unitality_hom (d : D) :
    δᵣ F d (𝟙_ C) ≫ (ρᵣ (F.obj d)).hom = F.map (ρᵣ d).hom := by
  simpa [-δᵣ_unitality_inv] using
    F.map (ρᵣ[C] d).hom ≫=
      (δᵣ_unitality_inv F d).symm =≫
      (ρᵣ[C] (F.obj d)).hom

end OplaxRightLinear

/-- `F.RightLinear C` asserts that `F` is both lax and oplax left-linear,
in a compatible way, i.e that `μᵣ` is inverse to `δᵣ`. -/
class RightLinear
    (F : D ⥤ D') (C : Type*) [Category C] [MonoidalCategory C]
    [MonoidalRightAction C D] [MonoidalRightAction C D'] extends
    F.LaxRightLinear C, F.OplaxRightLinear C where
  μᵣ_comp_δᵣ (F) (d : D) (c : C) :
    LaxRightLinear.μᵣ F d c ≫ OplaxRightLinear.δᵣ F d c = 𝟙 _
  δᵣ_comp_μᵣ (F) (d : D) (c : C) :
    OplaxRightLinear.δᵣ F d c ≫ LaxRightLinear.μᵣ F d c = 𝟙 _

namespace RightLinear

open LaxRightLinear OplaxRightLinear

variable
  (F : D ⥤ D') {C : Type*} [Category C] [MonoidalCategory C]
  [MonoidalRightAction C D] [MonoidalRightAction C D']
  [F.RightLinear C]

attribute [reassoc (attr := simp)] μᵣ_comp_δᵣ
attribute [reassoc (attr := simp)] δᵣ_comp_μᵣ

/-- A shorthand to bundle the μᵣ as an isomorphism -/
abbrev μᵣIso (d : D) (c : C) : F.obj d ⊙ᵣ c ≅ F.obj (d ⊙ᵣ c) where
  hom := LaxRightLinear.μᵣ F d c
  inv := OplaxRightLinear.δᵣ F d c

variable (c : C) (d : D)

instance : IsIso (μᵣ F d c) := Iso.isIso_hom (μᵣIso F d c)

instance : IsIso (δᵣ F d c) := Iso.isIso_inv (μᵣIso F d c)

@[simp]
lemma inv_μᵣ :
    CategoryTheory.inv (μᵣ F d c) = δᵣ F d c :=
  Eq.symm <| IsIso.eq_inv_of_hom_inv_id <| μᵣ_comp_δᵣ F d c

@[simp]
lemma inv_δᵣ :
    CategoryTheory.inv (δᵣ F d c) = μᵣ F d c :=
  Eq.symm <| IsIso.eq_inv_of_hom_inv_id <| δᵣ_comp_μᵣ F d c

end RightLinear

end rightAction

end CategoryTheory.Functor
