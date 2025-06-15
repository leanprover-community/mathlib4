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
* `F.LaxLeftLinear C` bundles the "lineator" as a morphism
  `c ⊙ₗ F.obj d ⟶ F.obj (c ⊙ₗ d)`.
* `F.LaxRightLinear` bundles the "lineator" as a morphism
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
`lineator F : ∀ (c : C) (d : D), c ⊙ₗ F.obj d ⟶ F.obj (c ⊙ₗ d)`
that is natural in each variable and coherent with respect to left actions
of `C` on `D` and `D'`. -/
class LaxLeftLinear
    (F : D ⥤ D') (C : Type*) [Category C] [MonoidalCategory C]
    [MonoidalLeftAction C D] [MonoidalLeftAction C D'] where
  /-- The "lineator" morphism. -/
  lineator (F) (c : C) (d : D) : c ⊙ₗ F.obj d ⟶ F.obj (c ⊙ₗ d)
  lineator_naturality_left (F) {c c': C} (f : c ⟶ c') (d : D) :
    f ⊵ₗ F.obj d ≫ lineator c' d = lineator c d ≫ F.map (f ⊵ₗ d) := by aesop_cat
  lineator_naturality_right (F) (c : C) {d d' : D} (f : d ⟶ d') :
    c ⊴ₗ F.map f ≫ lineator c d' = lineator c d ≫ F.map (c ⊴ₗ f) := by aesop_cat
  lineator_associativity (F) (c c' : C) (d : D) :
    lineator (c ⊗ c') d ≫ F.map (σ_ₗ _ _ _).hom =
    (σ_ₗ c c' (F.obj d)).hom ≫ c ⊴ₗ lineator c' d ≫
      lineator c (c' ⊙ₗ d) := by aesop_cat
  lineator_unitality (F) (d : D) :
    (υ_ₗ (F.obj d)).hom = lineator (𝟙_ C) d ≫ F.map (υ_ₗ d).hom := by aesop_cat

namespace LaxLeftLinear

-- These are [reassoc (attr := simp)] on the basis that analog lemmas for
-- lax monoidal functors are also [reassoc (attr := simp)].
attribute [reassoc (attr := simp)] lineator_naturality_right
attribute [reassoc (attr := simp)] lineator_naturality_left
attribute [reassoc (attr := simp)] lineator_associativity
attribute [reassoc (attr := simp)] lineator_unitality

variable
  (F : D ⥤ D') {C : Type*} [Category C] [MonoidalCategory C]
  [MonoidalLeftAction C D] [MonoidalLeftAction C D']
  [F.LaxLeftLinear C]

@[reassoc (attr := simp)]
lemma lineator_associativity_inv (c c' : C) (d : D) :
    lineator F c (c' ⊙ₗ d) ≫
      c ⊴ₗ oplaxLineator F c' d ≫ (σ_ₗ _ _ _).inv =
    F.map (σ_ₗ _ _ _).inv ≫ oplaxLineator F (c ⊗ c' : C) d := by
  simpa [-oplaxLineator_associativity, -oplaxLineator_associativity_assoc] using
    F.map (σ_ₗ _ _ _).inv ≫=
      (oplaxLineator_associativity F c c' d).symm =≫
      (σ_ₗ _ _ _).inv

end LaxLeftLinear

/-- `F.OplaxLinear C` equips `F : D ⥤ D'` with a family of morphisms
`oplaxLineator F : ∀ (c : C) (d : D), c ⊙ₗ F.obj d ⟶ F.obj (c ⊙ₗ d)`
that is natural in each variable and coherent with respect to left actions
of `C` on `D` and `D'`. -/
class OplaxLeftLinear
    (F : D ⥤ D') (C : Type*) [Category C] [MonoidalCategory C]
    [MonoidalLeftAction C D] [MonoidalLeftAction C D'] where
  /-- The "lineator" morphism. -/
  oplaxLineator (F) (c : C) (d : D) : F.obj (c ⊙ₗ d) ⟶ c ⊙ₗ F.obj d
  oplaxLineator_naturality_left (F) {c c': C} (f : c ⟶ c') (d : D) :
    F.map (f ⊵ₗ d) ≫ oplaxLineator c' d =
    oplaxLineator c d ≫ f ⊵ₗ F.obj d := by aesop_cat
  oplaxLineator_naturality_right (F) (c : C) {d d' : D} (f : d ⟶ d') :
    F.map (c ⊴ₗ f) ≫ oplaxLineator c d' =
    oplaxLineator c d ≫ c ⊴ₗ F.map f := by aesop_cat
  oplaxLineator_associativity (F) (c c' : C) (d : D) :
    oplaxLineator (c ⊗ c') d ≫ (σ_ₗ _ _ _).hom =
    F.map (σ_ₗ _ _ _).hom ≫ oplaxLineator c (c' ⊙ₗ d) ≫
      c ⊴ₗ oplaxLineator c' d := by aesop_cat
  oplaxLineator_unitality (F) (d : D) :
    (υ_ₗ (F.obj d)).inv =
    F.map (υ_ₗ d).inv ≫ oplaxLineator (𝟙_ C) d := by aesop_cat

namespace OplaxLeftLinear

-- These are [reassoc (attr := simp)] on the basis that analog lemmas for
-- oplax monoidal functors are also [reassoc (attr := simp)].
attribute [reassoc (attr := simp)] oplaxLineator_naturality_right
attribute [reassoc (attr := simp)] oplaxLineator_naturality_left
attribute [reassoc (attr := simp)] oplaxLineator_associativity
attribute [reassoc (attr := simp)] oplaxLineator_unitality

variable
  (F : D ⥤ D') {C : Type*} [Category C] [MonoidalCategory C]
  [MonoidalLeftAction C D] [MonoidalLeftAction C D']
  [F.OplaxLeftLinear C]

@[reassoc (attr := simp)]
lemma oplaxLineator_associativity_inv (c c' : C) (d : D) :
    oplaxLineator F c (c' ⊙ₗ d) ≫
      c ⊴ₗ oplaxLineator F c' d ≫ (σ_ₗ _ _ _).inv =
    F.map (σ_ₗ _ _ _).inv ≫ oplaxLineator F (c ⊗ c' : C) d := by
  simpa [-oplaxLineator_associativity, -oplaxLineator_associativity_assoc] using
    F.map (σ_ₗ _ _ _).inv ≫=
      (oplaxLineator_associativity F c c' d).symm =≫
      (σ_ₗ _ _ _).inv

end OplaxLeftLinear

/-- `F.LeftLinear C` asserts that `F` is both lax and oplax left-linear,
in a compatible way, i.e that `lineator` is inverse to `oplaxLineator`. -/
class LeftLinear
    (F : D ⥤ D') (C : Type*) [Category C] [MonoidalCategory C]
    [MonoidalLeftAction C D] [MonoidalLeftAction C D'] extends
    F.LaxLeftLinear C, F.OplaxLeftLinear C where
  lineator_comp_oplaxLineator (F) (c : C) (d : D) :
    LaxLeftLinear.lineator F c d ≫ OplaxLeftLinear.oplaxLineator F c d = 𝟙 _
  oplaxLineator_comp_lineator (F) (c : C) (d : D) :
    OplaxLeftLinear.oplaxLineator F c d ≫ LaxLeftLinear.lineator F c d = 𝟙 _

namespace LeftLinear

open LaxLeftLinear OplaxLeftLinear

variable
  (F : D ⥤ D') {C : Type*} [Category C] [MonoidalCategory C]
  [MonoidalLeftAction C D] [MonoidalLeftAction C D']
  [F.LeftLinear C]

attribute [reassoc (attr := simp)] lineator_comp_oplaxLineator
attribute [reassoc (attr := simp)] oplaxLineator_comp_lineator

/-- A shorthand to bundle the lineator as an isomorphism -/
abbrev ℓ_ (c : C) (d : D) : c ⊙ₗ F.obj d ≅ F.obj (c ⊙ₗ d) where
  hom := LaxLeftLinear.lineator F c d
  inv := OplaxLeftLinear.oplaxLineator F c d

variable (c : C) (d : D)

instance : IsIso (lineator F c d) := Iso.isIso_hom (ℓ_ F c d)

instance : IsIso (oplaxLineator F c d) := Iso.isIso_inv (ℓ_ F c d)

@[simp]
lemma inv_lineator :
    CategoryTheory.inv (lineator F c d) = oplaxLineator F c d :=
  Eq.symm <| IsIso.eq_inv_of_hom_inv_id <| lineator_comp_oplaxLineator F c d

@[simp]
lemma inv_oplaxLineator :
    CategoryTheory.inv (oplaxLineator F c d) = lineator F c d :=
  Eq.symm <| IsIso.eq_inv_of_hom_inv_id <| oplaxLineator_comp_lineator F c d

end LeftLinear

section rightAction

open MonoidalRightAction

-- variable [MonoidalRightAction C D] [MonoidalRightAction C D']

-- class respectsRightAction (F : D ⥤ D') where
--   τ_ (d : D) (c : C) : F.obj (d ᵣ⊙ c) ≅ F.obj d ᵣ⊙ c

end rightAction

end CategoryTheory.Functor
