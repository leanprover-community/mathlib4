/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Sites.LocallyBijective

/-!
# Functors which preserves locally bijective morphisms

In this file, we define two structures `Functor.PreservesLocallyInjective`,
`Functor.PreservesLocallySurjective` for a functor `F : A ⥤ B` between concrete
categories. These structures contains technical conditions which imply that the
post-composition with `F` on categories of presheaves preserve locally
injective/surjective morphisms for any Grothendieck topology. In particular, we
obtain that functors preserving locally injective and locally surjective
morphisms preserve sheafification.

## TODO
* show that the free module functor `Type u ⥤ ModuleCat.{u} R` preserves
locally injective and locally surjective maps, and thus preserves sheafification

-/

universe w₁ w₂ v₁ v₂ v u₁ u₂ u

namespace CategoryTheory

variable {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
  [ConcreteCategory.{w₁} A] [ConcreteCategory.{w₂} B]

attribute [local instance] ConcreteCategory.hasCoeToSort ConcreteCategory.instFunLike

namespace Functor

variable (F : A ⥤ B)

/-- Technical condition on a functor `F : A ⥤ B` between concrete categories which
implies that the postcomposition with `F` preserves locally surjective morphisms
for any Grothendieck topology. -/
structure PreservesLocallySurjective where
  /-- given `x : F.obj X`, this is a finset of `X` such that for any `f : X ⟶ Y`
  and `g : Z ⟶ Y` such that the image of this finset by `f` is contained in the
  image of `g`, then `F.map f x` belongs to the image of `F.map g`. -/
  G {X : A} (x : F.obj X) : Finset X
  mem {X Y Z : A} (x : F.obj X) (f : X ⟶ Y) (g : Z ⟶ Y)
      (hg : ∀ (a : G x), f a ∈ Set.range g) :
      F.map f x ∈ Set.range (F.map g)

namespace PreservesLocallySurjective

variable {F}
variable (hF : F.PreservesLocallySurjective)
  {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) {P Q : Cᵒᵖ ⥤ A}
  (f : P ⟶ Q) [Presheaf.IsLocallySurjective J f]

lemma isLocallySurjective : Presheaf.IsLocallySurjective J (whiskerRight f F) where
  imageSieve_mem {U} x := by
    classical
    let S := (hF.G x).image (fun a ↦ Presheaf.imageSieve f a)
    have hS := J.finite_intersection_covering _ (Finset.finite_toSet S) (fun T hT => by
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, S] at hT
      obtain ⟨a, _, rfl⟩ := hT
      apply Presheaf.imageSieve_mem)
    refine J.superset_covering ?_ hS
    rintro Y φ hφ
    apply hF.mem x (Q.map φ.op) (f.app _)
    rintro ⟨a, ha⟩
    exact hφ (Presheaf.imageSieve f a) (by
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, S]
      exact ⟨_, ha, rfl⟩)

end PreservesLocallySurjective

/-- Technical condition on a functor `F : A ⥤ B` between concrete categories which
implies that the postcomposition with `F` preserves locally injective morphisms
for any Grothendieck topology. -/
structure PreservesLocallyInjective where
  /-- Given elements `x₁` and `x₂` in `F.obj x` and `f : X ⟶ Y` such that
  `F.map f x₁ = F.map f x₂`, this a finset of tuples `(r₁, r₂)` of elements in `X` such
  that `f r₁ = f r₂` (see `eq`) and such that if `g : X ⟶ Z` is such that for
  these tuples we have `g r₁ = g r₂`, then `F.map g x₁ = F.map g x₂`. In other
  words, the identity `F.map f x₁ = F.map f x₂` can be "explained" by finitely
  many identities `f r₁ = f r₂`. -/
  R {X Y : A} (f : X ⟶ Y) {x₁ x₂ : F.obj X} (h : F.map f x₁ = F.map f x₂) : Finset (X × X)
  eq {X Y : A} {f : X ⟶ Y} {x₁ x₂ : F.obj X} {h : F.map f x₁ = F.map f x₂} (r : R f h) :
    f r.1.1 = f r.1.2
  imp {X Y Z : A} (f : X ⟶ Y) {x₁ x₂ : F.obj X} (h : F.map f x₁ = F.map f x₂) (g : X ⟶ Z)
      (hg : ∀ (r : R f h), g r.1.1 = g r.1.2) : F.map g x₁ = F.map g x₂

namespace PreservesLocallyInjective

variable {F}
variable (hF : F.PreservesLocallyInjective)
  {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) {P Q : Cᵒᵖ ⥤ A}
  (f : P ⟶ Q) [Presheaf.IsLocallyInjective J f]

lemma isLocallyInjective : Presheaf.IsLocallyInjective J (whiskerRight f F) where
  equalizerSieve_mem {U} x y h := by
    classical
    let S := (hF.R _ h).image (fun r => Presheaf.equalizerSieve r.1 r.2)
    have hS := J.finite_intersection_covering _ (Finset.finite_toSet S) (fun T hT => by
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Prod.exists, S] at hT
      obtain ⟨x₁, x₂, hx, rfl⟩ := hT
      exact Presheaf.equalizerSieve_mem J f x₁ x₂ (hF.eq ⟨_, hx⟩))
    refine J.superset_covering ?_ hS
    rintro Y φ hφ
    apply hF.imp _ h
    rintro ⟨⟨x₁, x₂⟩, hx⟩
    dsimp
    exact hφ (Presheaf.equalizerSieve x₁ x₂) (by
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Prod.exists, S]
      exact ⟨_, _, hx, rfl⟩)

end PreservesLocallyInjective

variable (hF₁ : F.PreservesLocallyInjective) (hF₂ : F.PreservesLocallySurjective)
  {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.WEqualsLocallyBijective A] [J.WEqualsLocallyBijective B]

lemma preservesSheafification_of_preservesLocallyInjectiveSurjective :
    J.PreservesSheafification F where
  le _ _ f := by
    simp only [MorphismProperty.inverseImage_iff, J.W_iff_isLocallyBijective]
    rintro ⟨_, _⟩
    exact ⟨hF₁.isLocallyInjective J f, hF₂.isLocallySurjective J f⟩

end Functor

end CategoryTheory
