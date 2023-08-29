/-
Copyright (c) 2022 Praneeth Kolichala. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Praneeth Kolichala
-/
import Mathlib.CategoryTheory.Groupoid
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
import Mathlib.Topology.Category.TopCat.Limits.Products
import Mathlib.Topology.Homotopy.Product

#align_import algebraic_topology.fundamental_groupoid.product from "leanprover-community/mathlib"@"178a32653e369dce2da68dc6b2694e385d484ef1"

/-!
# Fundamental groupoid preserves products
In this file, we give the following definitions/theorems:

  - `FundamentalGroupoidFunctor.piIso` An isomorphism between Π i, (π Xᵢ) and π (Πi, Xᵢ), whose
    inverse is precisely the product of the maps π (Π i, Xᵢ) → π (Xᵢ), each induced by
    the projection in `Top` Π i, Xᵢ → Xᵢ.

  - `FundamentalGroupoidFunctor.prodIso` An isomorphism between πX × πY and π (X × Y), whose
    inverse is precisely the product of the maps π (X × Y) → πX and π (X × Y) → Y, each induced by
    the projections X × Y → X and X × Y → Y

  - `FundamentalGroupoidFunctor.preservesProduct` A proof that the fundamental groupoid functor
    preserves all products.
-/

-- Porting note: Plenty declarations in this file already used uppercase in mathlib 3 names
set_option linter.uppercaseLean3 false

noncomputable section

open scoped FundamentalGroupoid CategoryTheory

namespace FundamentalGroupoidFunctor

universe u

section Pi

variable {I : Type u} (X : I → TopCat.{u})

/-- The projection map Π i, X i → X i induces a map π(Π i, X i) ⟶ π(X i).
-/
def proj (i : I) : πₓ (TopCat.of (∀ i, X i)) ⥤ πₓ (X i) :=
  πₘ ⟨_, continuous_apply i⟩
#align fundamental_groupoid_functor.proj FundamentalGroupoidFunctor.proj

/-- The projection map is precisely path.homotopic.proj interpreted as a functor -/
@[simp]
theorem proj_map (i : I) (x₀ x₁ : πₓ (TopCat.of (∀ i, X i))) (p : x₀ ⟶ x₁) :
    (proj X i).map p = @Path.Homotopic.proj _ _ _ _ _ i p :=
  rfl
#align fundamental_groupoid_functor.proj_map FundamentalGroupoidFunctor.proj_map

-- Porting note: losing the instance with a concrete category again
instance : (i : I) → TopologicalSpace (πₓ (X i)).α := fun i => TopCat.topologicalSpace_coe (X i)

/-- The map taking the pi product of a family of fundamental groupoids to the fundamental
groupoid of the pi product. This is actually an isomorphism (see `piIso`)
-/
@[simps]
def piToPiTop : (∀ i, πₓ (X i)) ⥤ πₓ (TopCat.of (∀ i, X i)) where
  obj g := g
  map p := Path.Homotopic.pi p
  map_id x := by
    change (Path.Homotopic.pi fun i => 𝟙 (x i)) = _
    -- ⊢ (Path.Homotopic.pi fun i => 𝟙 (x i)) = 𝟙 ({ obj := fun g => g, map := fun {X …
    simp only [FundamentalGroupoid.id_eq_path_refl, Path.Homotopic.pi_lift]
    -- ⊢ Quotient.mk (Path.Homotopic.setoid (fun i => x i) fun i => x i) (Path.pi fun …
    rfl
    -- 🎉 no goals
  map_comp f g := (Path.Homotopic.comp_pi_eq_pi_comp f g).symm
#align fundamental_groupoid_functor.pi_to_pi_Top FundamentalGroupoidFunctor.piToPiTop

/-- Shows `piToPiTop` is an isomorphism, whose inverse is precisely the pi product
of the induced projections. This shows that `fundamentalGroupoidFunctor` preserves products.
-/
@[simps]
def piIso : CategoryTheory.Grpd.of (∀ i : I, πₓ (X i)) ≅ πₓ (TopCat.of (∀ i, X i)) where
  hom := piToPiTop X
  inv := CategoryTheory.Functor.pi' (proj X)
  hom_inv_id := by
    change piToPiTop X ⋙ CategoryTheory.Functor.pi' (proj X) = 𝟭 _
    -- ⊢ piToPiTop X ⋙ CategoryTheory.Functor.pi' (proj X) = 𝟭 ((i : I) → ↑(π.obj (X  …
    apply CategoryTheory.Functor.ext ?_ ?_
    -- ⊢ ∀ (X_1 : (i : I) → ↑(π.obj (X i))), (piToPiTop X ⋙ CategoryTheory.Functor.pi …
    · intros; rfl
      -- ⊢ (piToPiTop X ⋙ CategoryTheory.Functor.pi' (proj X)).obj X✝ = (𝟭 ((i : I) → ↑ …
              -- 🎉 no goals
    · intros; ext; simp
      -- ⊢ (piToPiTop X ⋙ CategoryTheory.Functor.pi' (proj X)).map f✝ = CategoryTheory. …
              -- ⊢ (piToPiTop X ⋙ CategoryTheory.Functor.pi' (proj X)).map f✝ i✝ = (CategoryThe …
                   -- 🎉 no goals
  inv_hom_id := by
    change CategoryTheory.Functor.pi' (proj X) ⋙ piToPiTop X = 𝟭 _
    -- ⊢ CategoryTheory.Functor.pi' (proj X) ⋙ piToPiTop X = 𝟭 ↑(π.obj (TopCat.of ((i …
    apply CategoryTheory.Functor.ext
    -- ⊢ autoParam (∀ (X_1 Y : ↑(π.obj (TopCat.of ((i : I) → ↑(X i))))) (f : X_1 ⟶ Y) …
    · intro _ _ f
      -- ⊢ (CategoryTheory.Functor.pi' (proj X) ⋙ piToPiTop X).map f = CategoryTheory.e …
      suffices Path.Homotopic.pi ((CategoryTheory.Functor.pi' (proj X)).map f) = f by simpa
      -- ⊢ Path.Homotopic.pi ((CategoryTheory.Functor.pi' (proj X)).map f) = f
      change Path.Homotopic.pi (fun i => (CategoryTheory.Functor.pi' (proj X)).map f i) = _
      -- ⊢ (Path.Homotopic.pi fun i => (CategoryTheory.Functor.pi' (proj X)).map f i) = f
      simp
      -- 🎉 no goals
    · intros; rfl
      -- ⊢ (CategoryTheory.Functor.pi' (proj X) ⋙ piToPiTop X).obj X✝ = (𝟭 ↑(π.obj (Top …
              -- 🎉 no goals
#align fundamental_groupoid_functor.pi_iso FundamentalGroupoidFunctor.piIso

section Preserves

open CategoryTheory

/-- Equivalence between the categories of cones over the objects `π Xᵢ` written in two ways -/
def coneDiscreteComp :
    Limits.Cone (Discrete.functor X ⋙ π) ≌ Limits.Cone (Discrete.functor fun i => πₓ (X i)) :=
  Limits.Cones.postcomposeEquivalence (Discrete.compNatIsoDiscrete X π)
#align fundamental_groupoid_functor.cone_discrete_comp FundamentalGroupoidFunctor.coneDiscreteComp

theorem coneDiscreteComp_obj_mapCone :
    -- Porting note: check universe parameters here
    (coneDiscreteComp X).functor.obj (Functor.mapCone π (TopCat.piFan.{u,u} X)) =
      Limits.Fan.mk (πₓ (TopCat.of (∀ i, X i))) (proj X) :=
  rfl
#align fundamental_groupoid_functor.cone_discrete_comp_obj_map_cone FundamentalGroupoidFunctor.coneDiscreteComp_obj_mapCone

/-- This is `piIso.inv` as a cone morphism (in fact, isomorphism) -/
def piTopToPiCone :
    Limits.Fan.mk (πₓ (TopCat.of (∀ i, X i))) (proj X) ⟶ Grpd.piLimitFan fun i : I => πₓ (X i)
    where Hom := CategoryTheory.Functor.pi' (proj X)
#align fundamental_groupoid_functor.pi_Top_to_pi_cone FundamentalGroupoidFunctor.piTopToPiCone

instance : IsIso (piTopToPiCone X) :=
  haveI : IsIso (piTopToPiCone X).Hom := (inferInstance : IsIso (piIso X).inv)
  Limits.Cones.cone_iso_of_hom_iso (piTopToPiCone X)

/-- The fundamental groupoid functor preserves products -/
def preservesProduct : Limits.PreservesLimit (Discrete.functor X) π := by
  -- Porting note: check universe parameters here
  apply Limits.preservesLimitOfPreservesLimitCone (TopCat.piFanIsLimit.{u,u} X)
  -- ⊢ Limits.IsLimit (π.mapCone (TopCat.piFan X))
  apply (Limits.IsLimit.ofConeEquiv (coneDiscreteComp X)).toFun
  -- ⊢ Limits.IsLimit ((coneDiscreteComp X).functor.obj (π.mapCone (TopCat.piFan X)))
  simp only [coneDiscreteComp_obj_mapCone]
  -- ⊢ Limits.IsLimit (Limits.Fan.mk (π.obj (TopCat.of ((i : I) → ↑(X i)))) (proj X))
  apply Limits.IsLimit.ofIsoLimit _ (asIso (piTopToPiCone X)).symm
  -- ⊢ Limits.IsLimit (Grpd.piLimitFan fun i => π.obj (X i))
  exact Grpd.piLimitFanIsLimit _
  -- 🎉 no goals
#align fundamental_groupoid_functor.preserves_product FundamentalGroupoidFunctor.preservesProduct

end Preserves

end Pi

section Prod

variable (A B : TopCat.{u})

/-- The induced map of the left projection map X × Y → X -/
def projLeft : πₓ (TopCat.of (A × B)) ⥤ πₓ A :=
  πₘ ⟨_, continuous_fst⟩
#align fundamental_groupoid_functor.proj_left FundamentalGroupoidFunctor.projLeft

/-- The induced map of the right projection map X × Y → Y -/
def projRight : πₓ (TopCat.of (A × B)) ⥤ πₓ B :=
  πₘ ⟨_, continuous_snd⟩
#align fundamental_groupoid_functor.proj_right FundamentalGroupoidFunctor.projRight

@[simp]
theorem projLeft_map (x₀ x₁ : πₓ (TopCat.of (A × B))) (p : x₀ ⟶ x₁) :
    (projLeft A B).map p = Path.Homotopic.projLeft p :=
  rfl
#align fundamental_groupoid_functor.proj_left_map FundamentalGroupoidFunctor.projLeft_map

@[simp]
theorem projRight_map (x₀ x₁ : πₓ (TopCat.of (A × B))) (p : x₀ ⟶ x₁) :
    (projRight A B).map p = Path.Homotopic.projRight p :=
  rfl
#align fundamental_groupoid_functor.proj_right_map FundamentalGroupoidFunctor.projRight_map

/--
The map taking the product of two fundamental groupoids to the fundamental groupoid of the product
of the two topological spaces. This is in fact an isomorphism (see `prodIso`).
-/
@[simps obj]
def prodToProdTop : πₓ A × πₓ B ⥤ πₓ (TopCat.of (A × B)) where
  obj g := g
  map {x y} p :=
    match x, y, p with
    | (x₀, x₁), (y₀, y₁), (p₀, p₁) => @Path.Homotopic.prod _ _ (_) (_) _ _ _ _ p₀ p₁
  map_id := by
    rintro ⟨x₀, x₁⟩
    -- ⊢ { obj := fun g => g,
    simp only [CategoryTheory.prod_id, FundamentalGroupoid.id_eq_path_refl]
    -- ⊢ Path.Homotopic.prod (𝟙 x₀) (𝟙 x₁) = 𝟙 (x₀, x₁)
    rfl
    -- 🎉 no goals
  map_comp {x y z} f g :=
    match x, y, z, f, g with
    | (x₀, x₁), (y₀, y₁), (z₀, z₁), (f₀, f₁), (g₀, g₁) =>
      (Path.Homotopic.comp_prod_eq_prod_comp f₀ f₁ g₀ g₁).symm
#align fundamental_groupoid_functor.prod_to_prod_Top FundamentalGroupoidFunctor.prodToProdTop

theorem prodToProdTop_map {x₀ x₁ : πₓ A} {y₀ y₁ : πₓ B} (p₀ : x₀ ⟶ x₁) (p₁ : y₀ ⟶ y₁) :
    (prodToProdTop A B).map (X := (x₀, y₀)) (Y := (x₁, y₁)) (p₀, p₁) =
      Path.Homotopic.prod p₀ p₁ :=
  rfl
#align fundamental_groupoid_functor.prod_to_prod_Top_map FundamentalGroupoidFunctor.prodToProdTop_map

/-- Shows `prodToProdTop` is an isomorphism, whose inverse is precisely the product
of the induced left and right projections.
-/
@[simps]
def prodIso : CategoryTheory.Grpd.of (πₓ A × πₓ B) ≅ πₓ (TopCat.of (A × B)) where
  hom := prodToProdTop A B
  inv := (projLeft A B).prod' (projRight A B)
  hom_inv_id := by
    change prodToProdTop A B ⋙ (projLeft A B).prod' (projRight A B) = 𝟭 _
    -- ⊢ prodToProdTop A B ⋙ CategoryTheory.Functor.prod' (projLeft A B) (projRight A …
    apply CategoryTheory.Functor.hext; · intros; ext <;> simp <;> rfl
    -- ⊢ ∀ (X : ↑(π.obj A) × ↑(π.obj B)), (prodToProdTop A B ⋙ CategoryTheory.Functor …
                                         -- ⊢ (prodToProdTop A B ⋙ CategoryTheory.Functor.prod' (projLeft A B) (projRight  …
                                                 -- ⊢ ((prodToProdTop A B ⋙ CategoryTheory.Functor.prod' (projLeft A B) (projRight …
                                                         -- ⊢ (projLeft A B).obj X✝ = X✝.fst
                                                         -- ⊢ (projRight A B).obj X✝ = X✝.snd
                                                                  -- 🎉 no goals
                                                                  -- 🎉 no goals
    rintro ⟨x₀, x₁⟩ ⟨y₀, y₁⟩ ⟨f₀, f₁⟩
    -- ⊢ HEq ((prodToProdTop A B ⋙ CategoryTheory.Functor.prod' (projLeft A B) (projR …
    have : Path.Homotopic.projLeft ((prodToProdTop A B).map (f₀, f₁)) = f₀ ∧
      Path.Homotopic.projRight ((prodToProdTop A B).map (f₀, f₁)) = f₁ :=
        And.intro (Path.Homotopic.projLeft_prod f₀ f₁) (Path.Homotopic.projRight_prod f₀ f₁)
    simpa
    -- 🎉 no goals
  inv_hom_id := by
    change (projLeft A B).prod' (projRight A B) ⋙ prodToProdTop A B = 𝟭 _
    -- ⊢ CategoryTheory.Functor.prod' (projLeft A B) (projRight A B) ⋙ prodToProdTop  …
    apply CategoryTheory.Functor.hext
    -- ⊢ ∀ (X : ↑(π.obj (TopCat.of (↑A × ↑B)))), (CategoryTheory.Functor.prod' (projL …
    · intros; apply Prod.ext <;> simp <;> rfl
      -- ⊢ (CategoryTheory.Functor.prod' (projLeft A B) (projRight A B) ⋙ prodToProdTop …
              -- ⊢ ((CategoryTheory.Functor.prod' (projLeft A B) (projRight A B) ⋙ prodToProdTo …
                                 -- ⊢ (projLeft A B).obj X✝ = X✝.fst
                                 -- ⊢ (projRight A B).obj X✝ = X✝.snd
                                          -- 🎉 no goals
                                          -- 🎉 no goals
    rintro ⟨x₀, x₁⟩ ⟨y₀, y₁⟩ f
    -- ⊢ HEq ((CategoryTheory.Functor.prod' (projLeft A B) (projRight A B) ⋙ prodToPr …
    have := Path.Homotopic.prod_projLeft_projRight f
    -- ⊢ HEq ((CategoryTheory.Functor.prod' (projLeft A B) (projRight A B) ⋙ prodToPr …
    -- Porting note: was simpa but TopSpace instances might be getting in the way
    simp only [CategoryTheory.Functor.comp_obj, CategoryTheory.Functor.prod'_obj, prodToProdTop_obj,
      CategoryTheory.Functor.comp_map, CategoryTheory.Functor.prod'_map, projLeft_map,
      projRight_map, CategoryTheory.Functor.id_obj, CategoryTheory.Functor.id_map, heq_eq_eq]
    apply this
    -- 🎉 no goals

end Prod
