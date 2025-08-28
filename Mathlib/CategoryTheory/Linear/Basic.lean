/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Group.Invertible.Defs
import Mathlib.Algebra.Module.Equiv.Defs
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.LinearAlgebra.Span.Basic

/-!
# Linear categories

An `R`-linear category is a category in which `X ⟶ Y` is an `R`-module in such a way that
composition of morphisms is `R`-linear in both variables.

Note that sometimes in the literature a "linear category" is further required to be abelian.

## Implementation

Corresponding to the fact that we need to have an `AddCommGroup X` structure in place
to talk about a `Module R X` structure,
we need `Preadditive C` as a prerequisite typeclass for `Linear R C`.
This makes for longer signatures than would be ideal.

## Future work

It would be nice to have a usable framework of enriched categories in which this just became
a category enriched in `Module R`.

-/

universe w v u

open CategoryTheory.Limits

open LinearMap

namespace CategoryTheory

/-- A category is called `R`-linear if `P ⟶ Q` is an `R`-module such that composition is
`R`-linear in both variables. -/
class Linear (R : Type w) [Semiring R] (C : Type u) [Category.{v} C] [Preadditive C] where
  homModule : ∀ X Y : C, Module R (X ⟶ Y) := by infer_instance
  /-- compatibility of the scalar multiplication with the post-composition -/
  smul_comp : ∀ (X Y Z : C) (r : R) (f : X ⟶ Y) (g : Y ⟶ Z), (r • f) ≫ g = r • f ≫ g := by
    cat_disch
  /-- compatibility of the scalar multiplication with the pre-composition -/
  comp_smul : ∀ (X Y Z : C) (f : X ⟶ Y) (r : R) (g : Y ⟶ Z), f ≫ (r • g) = r • f ≫ g := by
    cat_disch

attribute [instance] Linear.homModule

attribute [simp] Linear.smul_comp Linear.comp_smul

-- (the linter doesn't like `simp` on the `_assoc` lemma)
end CategoryTheory

open CategoryTheory

namespace CategoryTheory.Linear

variable {C : Type u} [Category.{v} C] [Preadditive C]

instance preadditiveNatLinear : Linear ℕ C where
  smul_comp X _Y _Z r f g := by exact (Preadditive.rightComp X g).map_nsmul f r
  comp_smul _X _Y Z f r g := by exact (Preadditive.leftComp Z f).map_nsmul g r

instance preadditiveIntLinear : Linear ℤ C where
  smul_comp X _Y _Z r f g := by exact (Preadditive.rightComp X g).map_zsmul f r
  comp_smul _X _Y Z f r g := by exact (Preadditive.leftComp Z f).map_zsmul g r

section End

variable {R : Type w}

instance [Semiring R] [Linear R C] (X : C) : Module R (End X) := by
  dsimp [End]
  infer_instance

instance [CommSemiring R] [Linear R C] (X : C) : Algebra R (End X) :=
  Algebra.ofModule (fun _ _ _ => comp_smul _ _ _ _ _ _) fun _ _ _ => smul_comp _ _ _ _ _ _

end End

section

variable {R : Type w} [Semiring R] [Linear R C]

section InducedCategory

universe u'

variable {D : Type u'} (F : D → C)

instance inducedCategory : Linear.{w, v} R (InducedCategory C F) where
  homModule X Y := @Linear.homModule R _ C _ _ _ (F X) (F Y)
  smul_comp _ _ _ _ _ _ := smul_comp _ _ _ _ _ _
  comp_smul _ _ _ _ _ _ := comp_smul _ _ _ _ _ _

end InducedCategory

instance fullSubcategory (Z : ObjectProperty C) : Linear.{w, v} R Z.FullSubcategory where
  homModule X Y := @Linear.homModule R _ C _ _ _ X.obj Y.obj
  smul_comp _ _ _ _ _ _ := smul_comp _ _ _ _ _ _
  comp_smul _ _ _ _ _ _ := comp_smul _ _ _ _ _ _

variable (R)

/-- Composition by a fixed left argument as an `R`-linear map. -/
@[simps]
def leftComp {X Y : C} (Z : C) (f : X ⟶ Y) : (Y ⟶ Z) →ₗ[R] X ⟶ Z where
  toFun g := f ≫ g
  map_add' := by simp
  map_smul' := by simp

/-- Composition by a fixed right argument as an `R`-linear map. -/
@[simps]
def rightComp (X : C) {Y Z : C} (g : Y ⟶ Z) : (X ⟶ Y) →ₗ[R] X ⟶ Z where
  toFun f := f ≫ g
  map_add' := by simp
  map_smul' := by simp

instance {X Y : C} (f : X ⟶ Y) [Epi f] (r : R) [Invertible r] : Epi (r • f) :=
  ⟨fun g g' H => by
    rw [smul_comp, smul_comp, ← comp_smul, ← comp_smul, cancel_epi] at H
    simpa [smul_smul] using congr_arg (fun f => ⅟r • f) H⟩

instance {X Y : C} (f : X ⟶ Y) [Mono f] (r : R) [Invertible r] : Mono (r • f) :=
  ⟨fun g g' H => by
    rw [comp_smul, comp_smul, ← smul_comp, ← smul_comp, cancel_mono] at H
    simpa [smul_smul] using congr_arg (fun f => ⅟r • f) H⟩

/-- Given isomorphic objects `X ≅ Y, W ≅ Z` in a `k`-linear category, we have a `k`-linear
isomorphism between `Hom(X, W)` and `Hom(Y, Z).` -/
def homCongr (k : Type*) {C : Type*} [Category C] [Semiring k] [Preadditive C] [Linear k C]
    {X Y W Z : C} (f₁ : X ≅ Y) (f₂ : W ≅ Z) : (X ⟶ W) ≃ₗ[k] Y ⟶ Z :=
  {
    (rightComp k Y f₂.hom).comp
      (leftComp k W
        f₁.symm.hom) with
    invFun := (leftComp k W f₁.hom).comp (rightComp k Y f₂.symm.hom)
    left_inv := fun x => by
      simp only [Iso.symm_hom, LinearMap.toFun_eq_coe, LinearMap.coe_comp, Function.comp_apply,
        leftComp_apply, rightComp_apply, Category.assoc, Iso.hom_inv_id, Category.comp_id,
        Iso.hom_inv_id_assoc]
    right_inv := fun x => by
      simp only [Iso.symm_hom, LinearMap.coe_comp, Function.comp_apply, rightComp_apply,
        leftComp_apply, LinearMap.toFun_eq_coe, Iso.inv_hom_id_assoc, Category.assoc,
        Iso.inv_hom_id, Category.comp_id] }

theorem homCongr_apply (k : Type*) {C : Type*} [Category C] [Semiring k] [Preadditive C]
    [Linear k C] {X Y W Z : C} (f₁ : X ≅ Y) (f₂ : W ≅ Z) (f : X ⟶ W) :
    homCongr k f₁ f₂ f = (f₁.inv ≫ f) ≫ f₂.hom :=
  rfl

theorem homCongr_symm_apply (k : Type*) {C : Type*} [Category C] [Semiring k] [Preadditive C]
    [Linear k C] {X Y W Z : C} (f₁ : X ≅ Y) (f₂ : W ≅ Z) (f : Y ⟶ Z) :
    (homCongr k f₁ f₂).symm f = f₁.hom ≫ f ≫ f₂.inv :=
  rfl

variable {R}

@[simp]
lemma units_smul_comp {X Y Z : C} (r : Rˣ) (f : X ⟶ Y) (g : Y ⟶ Z) :
    (r • f) ≫ g = r • f ≫ g := by
  apply Linear.smul_comp

@[simp]
lemma comp_units_smul {X Y Z : C} (f : X ⟶ Y) (r : Rˣ) (g : Y ⟶ Z) :
    f ≫ (r • g) = r • f ≫ g := by
  apply Linear.comp_smul

end

section

variable {S : Type w} [CommSemiring S] [Linear S C]

/-- Composition as a bilinear map. -/
@[simps]
def comp (X Y Z : C) : (X ⟶ Y) →ₗ[S] (Y ⟶ Z) →ₗ[S] X ⟶ Z where
  toFun f := leftComp S Z f
  map_add' := by
    intros
    ext
    simp
  map_smul' := by
    intros
    ext
    simp

/-- Characterization of the linear map `S →ₗ[S] X ⟶ Z` generated by the composition of morphisms
`f : X ⟶ Y` and `g : Y ⟶ Z`. -/
@[simp]
lemma toSpanSingleton_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    LinearMap.toSpanSingleton S (X ⟶ Z) (f ≫ g) =
    (Linear.rightComp S X g) ∘ₗ (LinearMap.toSpanSingleton S (X ⟶ Y) f) := by
  ext
  simp

end

end CategoryTheory.Linear
