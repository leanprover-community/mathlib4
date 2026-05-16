/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Joël Riou
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Small
public import Mathlib.CategoryTheory.Sites.DenseSubsite.OneHypercoverDense

/-!
# Small affine site induced by a morphism property

Let `P` be a morphism property of schemes and `S` be a scheme. In this file we study the small
affine `P`-site of `S`: its objects are rings `R` with a structure morphism `Spec R ⟶ S` that
satisfies `P`.

We don't make a separate definition for this site, but use
`CategoryTheory.MorphismProperty.CostructuredArrow P ⊤ Scheme.Spec S`.

Under suitable assumptions on `P`, the lemmas here can be used to show that the small affine
`P`-site has the same category of sheaves as the general small `P`-site. If `P` implies
finitely generated, the small affine `P`-site is essentially small, so in particular
this can be used to show that the `P`-site admits sheafification. For an example,
see the file `Mathlib.AlgebraicGeometry.Sites.AffineEtale`.
-/

@[expose] public section

universe u

open CategoryTheory Opposite Limits MorphismProperty

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}}

/-- Construct an object of affine `P`-schemes over `S` by giving a morphism `Spec R ⟶ S`. -/
@[simps! hom left]
noncomputable def affineOverMk {P : MorphismProperty Scheme.{u}} {R : CommRingCat.{u}}
    (f : Spec R ⟶ S) (hf : P f) :
    P.CostructuredArrow ⊤ Scheme.Spec S :=
  .mk ⊤ f hf

variable (P : MorphismProperty Scheme.{u}) [P.IsMultiplicative] [IsZariskiLocalAtSource P]
  [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P]

/-- The `Spec` functor from affine `P`-schemes over `S` to `P`-schemes over `S` is dense
if `P` is local at the source. -/
instance isCoverDense_toOver_Spec :
    (CostructuredArrow.toOver P Scheme.Spec S).IsCoverDense (smallGrothendieckTopology P) where
  is_cover U := by
    rw [Scheme.mem_smallGrothendieckTopology]
    let 𝒰 : Cover.{u} (precoverage P) U.left :=
      U.left.affineCover.changeProp
      (fun _ ↦ IsZariskiLocalAtSource.of_isOpenImmersion _)
    let _ (i : 𝒰.I₀) : (𝒰.X i).Over S := ⟨𝒰.f i ≫ U.hom⟩
    let _ : Cover.Over S 𝒰 := { isOver_map _ := ⟨rfl⟩ }
    refine ⟨𝒰, inferInstance,
      fun i ↦ P.comp_mem _ _ (𝒰.map_prop i) U.prop, fun X f ⟨i⟩ ↦ ?_⟩
    rw [Sieve.coverByImage]
    exact ⟨⟨affineOverMk (𝒰.f i ≫ U.hom) (P.comp_mem _ _ (𝒰.map_prop i) U.prop),
      CostructuredArrow.homMk (𝟙 _) ⟨⟩ rfl, Over.homMk (𝒰.f i) (by simp) trivial,
      by cat_disch⟩⟩

instance isOneHypercoverDense_toOver_Spec :
    Functor.IsOneHypercoverDense.{u} (CostructuredArrow.toOver P Scheme.Spec S)
      ((CostructuredArrow.toOver P Scheme.Spec S).inducedTopology (smallGrothendieckTopology P))
      (smallGrothendieckTopology P) :=
  Functor.IsOneHypercoverDense.of_hasPullbacks fun X ↦ by
    let 𝒰 := affineOpenCover X.left
    let 𝒱 : Cover (precoverage P) X.left :=
      𝒰.openCover.changeProp (fun _ ↦ IsZariskiLocalAtSource.of_isOpenImmersion _)
    let _ (i : 𝒱.I₀) : (𝒱.X i).Over S := ⟨𝒰.f i ≫ X.hom⟩
    let : Cover.Over S 𝒱 := { isOver_map _ := ⟨rfl⟩ }
    refine ⟨𝒰.I₀, fun i ↦ affineOverMk (𝒰.f i ≫ X.hom)
      (P.comp_mem _ _ (IsZariskiLocalAtSource.of_isOpenImmersion (𝒰.f i)) X.prop),
      fun i ↦ CostructuredArrow.homMk (𝒰.f i) (by simp), ?_⟩
    rw [Scheme.mem_smallGrothendieckTopology]
    exact ⟨𝒱, inferInstance, fun i ↦ P.comp_mem _ _ (𝒱.map_prop i) X.prop,
      fun _ _ ⟨i⟩ ↦ (Sieve.mem_ofArrows_iff ..).2 ⟨i, 𝟙 _, by cat_disch⟩⟩

end AlgebraicGeometry.Scheme
