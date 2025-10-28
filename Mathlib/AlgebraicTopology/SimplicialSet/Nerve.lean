/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.AlgebraicTopology.SimplicialSet.Basic
import Mathlib.CategoryTheory.ComposableArrows

/-!

# The nerve of a category

This file provides the definition of the nerve of a category `C`,
which is a simplicial set `nerve C` (see [goerss-jardine-2009], Example I.1.4).
By definition, the type of `n`-simplices of `nerve C` is `ComposableArrows C n`,
which is the category `Fin (n + 1) ⥤ C`.

## References
* [Paul G. Goerss, John F. Jardine, *Simplicial Homotopy Theory*][goerss-jardine-2009]

-/

open CategoryTheory.Category Simplicial

universe v u

namespace CategoryTheory

/-- The nerve of a category -/
@[simps]
def nerve (C : Type u) [Category.{v} C] : SSet.{max u v} where
  obj Δ := ComposableArrows C (Δ.unop.len)
  map f x := x.whiskerLeft (SimplexCategory.toCat.map f.unop)
  -- `aesop` can prove these but is slow, help it out:
  map_id _ := rfl
  map_comp _ _ := rfl

instance {C : Type*} [Category C] {Δ : SimplexCategoryᵒᵖ} : Category ((nerve C).obj Δ) :=
  (inferInstance : Category (ComposableArrows C (Δ.unop.len)))

/-- Given a functor `C ⥤ D`, we obtain a morphism `nerve C ⟶ nerve D` of simplicial sets. -/
@[simps]
def nerveMap {C D : Type u} [Category.{v} C] [Category.{v} D] (F : C ⥤ D) : nerve C ⟶ nerve D :=
  { app := fun _ => (F.mapComposableArrows _).obj }

/-- The nerve of a category, as a functor `Cat ⥤ SSet` -/
@[simps]
def nerveFunctor : Cat.{v, u} ⥤ SSet where
  obj C := nerve C
  map F := nerveMap F

/-- The 0-simplices of the nerve of a category are equivalent to the objects of the category. -/
def nerveEquiv (C : Type u) [Category.{v} C] : nerve C _⦋0⦌ ≃ C where
  toFun f := f.obj ⟨0, by omega⟩
  invFun f := (Functor.const _).obj f
  left_inv f := ComposableArrows.ext₀ rfl

namespace nerve

/-- Nerves of finite non-empty ordinals are representable functors. -/
def representableBy {n : ℕ} (α : Type u) [Preorder α] (e : α ≃o Fin (n + 1)) :
    (nerve α).RepresentableBy ⦋n⦌ where
  homEquiv := SimplexCategory.homEquivFunctor.trans
    { toFun F := F ⋙ e.symm.monotone.functor
      invFun F := F ⋙ e.monotone.functor
      left_inv F := Functor.ext (fun x ↦ by simp)
      right_inv F := Functor.ext (fun x ↦ by simp) }
  homEquiv_comp _ _ := rfl

variable {C : Type*} [Category C] {n : ℕ}

lemma δ_obj {n : ℕ} (i : Fin (n + 2)) (x : (nerve C) _⦋n + 1⦌) (j : Fin (n + 1)) :
    ((nerve C).δ i x).obj j = x.obj (i.succAbove j) :=
  rfl

lemma σ_obj {n : ℕ} (i : Fin (n + 1)) (x : (nerve C) _⦋n⦌) (j : Fin (n + 2)) :
    ((nerve C).σ i x).obj j = x.obj (i.predAbove j) :=
  rfl

lemma δ₀_eq {x : nerve C _⦋n + 1⦌} : (nerve C).δ (0 : Fin (n + 2)) x = x.δ₀ := rfl

lemma σ₀_mk₀_eq (x : C) : (nerve C).σ (0 : Fin 1) (.mk₀ x) = .mk₁ (𝟙 x) :=
  ComposableArrows.ext₁ rfl rfl (by simp; rfl)

section

variable {X₀ X₁ X₂ : C} (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂)

theorem δ₂_mk₂_eq : (nerve C).δ 2 (ComposableArrows.mk₂ f g) = ComposableArrows.mk₁ f :=
  ComposableArrows.ext₁ rfl rfl (by simp; rfl)

theorem δ₀_mk₂_eq : (nerve C).δ 0 (ComposableArrows.mk₂ f g) = ComposableArrows.mk₁ g :=
  ComposableArrows.ext₁ rfl rfl (by simp; rfl)

theorem δ₁_mk₂_eq : (nerve C).δ 1 (ComposableArrows.mk₂ f g) = ComposableArrows.mk₁ (f ≫ g) :=
  ComposableArrows.ext₁ rfl rfl (by simp; rfl)

end

@[ext]
lemma ext_of_isThin [Quiver.IsThin C] {n : SimplexCategoryᵒᵖ} {x y : (nerve C).obj n}
    (h : x.obj = y.obj) :
    x = y :=
  ComposableArrows.ext (by simp [h]) (by subsingleton)

end nerve

end CategoryTheory
