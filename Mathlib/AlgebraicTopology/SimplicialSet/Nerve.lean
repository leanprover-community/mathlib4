/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.CompStruct
public import Mathlib.CategoryTheory.ComposableArrows.Basic

/-!

# The nerve of a category

This file provides the definition of the nerve of a category `C`,
which is a simplicial set `nerve C` (see [goerss-jardine-2009], Example I.1.4).
By definition, the type of `n`-simplices of `nerve C` is `ComposableArrows C n`,
which is the category `Fin (n + 1) ⥤ C`.

## References
* [Paul G. Goerss, John F. Jardine, *Simplicial Homotopy Theory*][goerss-jardine-2009]

-/

@[expose] public section

open CategoryTheory.Category Simplicial Opposite

universe v u

namespace CategoryTheory

/-- The nerve of a category -/
@[simps -isSimp]
def nerve (C : Type u) [Category.{v} C] : SSet.{max u v} where
  obj Δ := ComposableArrows C (Δ.unop.len)
  map f x := x.whiskerLeft (SimplexCategory.toCat.map f.unop).toFunctor
  -- `aesop` can prove these but is slow, help it out:
  map_id _ := rfl
  map_comp _ _ := rfl

attribute [simp] nerve_obj

instance {C : Type*} [Category* C] {Δ : SimplexCategoryᵒᵖ} : Category ((nerve C).obj Δ) :=
  (inferInstance : Category (ComposableArrows C (Δ.unop.len)))

section

variable {C D : Type u} [Category.{v} C] [Category.{v} D] (F : C ⥤ D)

/-- Given a functor `C ⥤ D`, we obtain a morphism `nerve C ⟶ nerve D` of simplicial sets. -/
@[simps -isSimp]
def nerveMap {C D : Type u} [Category.{v} C] [Category.{v} D] (F : C ⥤ D) : nerve C ⟶ nerve D :=
  { app := fun _ => (F.mapComposableArrows _).obj }

lemma nerveMap_app_mk₀ (x : C) :
    (nerveMap F).app (op ⦋0⦌) (ComposableArrows.mk₀ x) =
      ComposableArrows.mk₀ (F.obj x) :=
  ComposableArrows.ext₀ rfl

lemma nerveMap_app_mk₁ {x y : C} (f : x ⟶ y) :
    (nerveMap F).app (op ⦋1⦌) (ComposableArrows.mk₁ f) =
      ComposableArrows.mk₁ (F.map f) :=
  ComposableArrows.ext₁ rfl rfl (by simp [nerveMap_app])

end

/-- The nerve of a category, as a functor `Cat ⥤ SSet` -/
@[simps]
def nerveFunctor : Cat.{v, u} ⥤ SSet where
  obj C := nerve C
  map F := nerveMap F.toFunctor

/-- The 0-simplices of the nerve of a category are equivalent to the objects of the category. -/
def nerveEquiv {C : Type u} [Category.{v} C] : ComposableArrows C 0 ≃ C where
  toFun f := f.obj ⟨0, by lia⟩
  invFun f := ComposableArrows.mk₀ f
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

variable {C : Type u} [Category.{v} C] {n : ℕ}

lemma δ_obj {n : ℕ} (i : Fin (n + 2)) (x : ComposableArrows C (n + 1)) (j : Fin (n + 1)) :
    ((nerve C).δ i x).obj j = x.obj (i.succAbove j) :=
  rfl

lemma σ_obj {n : ℕ} (i : Fin (n + 1)) (x : ComposableArrows C n) (j : Fin (n + 2)) :
    ((nerve C).σ i x).obj j = x.obj (i.predAbove j) :=
  rfl

lemma δ₀_eq {x : ComposableArrows C (n + 1)} : (nerve C).δ (0 : Fin (n + 2)) x = x.δ₀ := rfl

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

open SSet

@[simp]
lemma left_edge {x y : ComposableArrows C 0} (e : (nerve C).Edge x y) :
    ComposableArrows.left (n := 1) e.edge = nerveEquiv x := by
  simp only [← e.src_eq]
  rfl

@[simp]
lemma right_edge {x y : ComposableArrows C 0} (e : (nerve C).Edge x y) :
    ComposableArrows.right (n := 1) e.edge = nerveEquiv y := by
  simp only [← e.tgt_eq]
  rfl

lemma δ₂_two (x : ComposableArrows C 2) :
    (nerve C).δ 2 x = .mk₁ (x.map' 0 1) :=
  ComposableArrows.ext₁ rfl rfl (by cat_disch)

lemma δ₂_zero (x : ComposableArrows C 2) :
    (nerve C).δ 0 x = .mk₁ (x.map' 1 2) :=
  ComposableArrows.ext₁ rfl rfl (by cat_disch)

section

attribute [local ext (iff := false)] ComposableArrows.ext₀ ComposableArrows.ext₁

/-- Bijection between edges in the nerve of category and morphisms in the category. -/
@[simps -isSimp]
def homEquiv {x y : ComposableArrows C 0} :
    (nerve C).Edge x y ≃ (nerveEquiv x ⟶ nerveEquiv y) where
  toFun e := eqToHom (by simp) ≫ e.edge.hom ≫ eqToHom (by simp)
  invFun f := .mk (ComposableArrows.mk₁ f) (ComposableArrows.ext₀ rfl) (ComposableArrows.ext₀ rfl)
  left_inv e := by cat_disch
  right_inv f := by simp

lemma mk₁_homEquiv_apply {x y : ComposableArrows C 0} (e : (nerve C).Edge x y) :
    ComposableArrows.mk₁ (homEquiv e) = ComposableArrows.mk₁ e.edge.hom := by
  simp [homEquiv, ComposableArrows.mk₁_eqToHom_comp, ComposableArrows.mk₁_comp_eqToHom]

/-- Constructor for edges in the nerve of a category. (See also `homEquiv`.) -/
def edgeMk {x y : C} (f : x ⟶ y) : (nerve C).Edge (nerveEquiv.symm x) (nerveEquiv.symm y) :=
  Edge.mk (ComposableArrows.mk₁ f)

@[simp]
lemma edgeMk_edge {x y : C} (f : x ⟶ y) : (edgeMk f).edge = ComposableArrows.mk₁ f := rfl

@[simp]
lemma edgeMk_id (x : C) : edgeMk (𝟙 x) = .id _ := by cat_disch

lemma edgeMk_surjective {x y : C} :
    Function.Surjective (edgeMk : (x ⟶ y) → _) :=
  fun e ↦ ⟨eqToHom (by simp) ≫ homEquiv e ≫ eqToHom (by simp), by cat_disch⟩

@[simp]
lemma homEquiv_edgeMk {x y : C} (f : x ⟶ y) :
    homEquiv (edgeMk f) = f :=
  homEquiv.symm.injective (by cat_disch)

lemma homEquiv_id (x : ComposableArrows C 0) :
    homEquiv (Edge.id x) = 𝟙 _ := by
  obtain ⟨x, rfl⟩ := nerveEquiv.symm.surjective x
  dsimp [homEquiv]
  cat_disch

lemma nonempty_compStruct_iff {x₀ x₁ x₂ : C}
    (f₀₁ : x₀ ⟶ x₁) (f₁₂ : x₁ ⟶ x₂) (f₀₂ : x₀ ⟶ x₂) :
    Nonempty (Edge.CompStruct (edgeMk f₀₁) (edgeMk f₁₂) (edgeMk f₀₂)) ↔
      f₀₁ ≫ f₁₂ = f₀₂ := by
  let h' : Edge.CompStruct (edgeMk f₀₁) (edgeMk f₁₂) (edgeMk (f₀₁ ≫ f₁₂)) :=
      Edge.CompStruct.mk (ComposableArrows.mk₂ f₀₁ f₁₂)
        (by cat_disch) (by cat_disch) (by cat_disch)
  refine ⟨fun ⟨h⟩ ↦ ?_, fun h ↦ ⟨by rwa [← h]⟩⟩
  rw [← Arrow.mk_inj]
  apply ComposableArrows.arrowEquiv.symm.injective
  convert_to (nerve C).δ 1 h'.simplex = (nerve C).δ 1 h.simplex
  · exact (h'.d₁).symm
  · exact (h.d₁).symm
  · have h₀ := h.d₀
    have h₂ := h.d₂
    have h'₀ := h'.d₀
    have h'₂ := h'.d₂
    simp only [δ₂_zero, δ₂_two, edgeMk_edge] at h₀ h₂ h'₀ h'₂
    exact congr_arg _ (ComposableArrows.ext₂_of_arrow
      (ComposableArrows.arrowEquiv.symm.injective
        (by simp [-Edge.CompStruct.d₂, h'₂, ← h₂]))
      (ComposableArrows.arrowEquiv.symm.injective
        (by simp [-Edge.CompStruct.d₀, h'₀, ← h₀])))

lemma homEquiv_comp {x₀ x₁ x₂ : ComposableArrows C 0}
    {e₀₁ : (nerve C).Edge x₀ x₁}
    {e₁₂ : (nerve C).Edge x₁ x₂} {e₀₂ : (nerve C).Edge x₀ x₂}
    (h : Edge.CompStruct e₀₁ e₁₂ e₀₂) :
    homEquiv e₀₁ ≫ homEquiv e₁₂ = homEquiv e₀₂ := by
  obtain ⟨x₀, rfl⟩ := nerveEquiv.symm.surjective x₀
  obtain ⟨x₁, rfl⟩ := nerveEquiv.symm.surjective x₁
  obtain ⟨x₂, rfl⟩ := nerveEquiv.symm.surjective x₂
  obtain ⟨f₀₁, rfl⟩ := edgeMk_surjective e₀₁
  obtain ⟨f₁₂, rfl⟩ := edgeMk_surjective e₁₂
  obtain ⟨f₀₂, rfl⟩ := edgeMk_surjective e₀₂
  convert (nerve.nonempty_compStruct_iff _ _ _).1 ⟨h⟩ <;> apply homEquiv_edgeMk

lemma σ_zero_nerveEquiv_symm (x : C) :
    (nerve C).σ 0 (nerveEquiv.symm x) = ComposableArrows.mk₁ (𝟙 x) := by
  cat_disch

@[simp]
lemma homEquiv_edgeMk_map_nerveMap {D : Type u} [Category.{v} D] {x y : C}
    (f : x ⟶ y) (F : C ⥤ D) :
    homEquiv ((edgeMk f).map (nerveMap F)) = F.map f := by
  simp [homEquiv, nerveMap_app]

end

end nerve

end CategoryTheory
