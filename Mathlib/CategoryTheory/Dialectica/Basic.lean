/-
Copyright (c) 2024 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts

/-!
# Dialectica category

We define the category `Dial` of the Dialectica interpretation, after:

* Valeria de Paiva, The Dialectica Categories.
  University of Cambridge, Computer Laboratory, PhD Thesis, Technical Report 213, 1991
  ([pdf](https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-213.pdf)).
-/

noncomputable section

namespace CategoryTheory

open Limits

universe v u
variable {C : Type u} [Category.{v} C] [HasFiniteProducts C] [HasPullbacks C]

variable (C) in
/-- The Dialectica category. An object of the category is a triple `⟨U, X, α ⊆ U × X⟩`,
and a morphism from `⟨U, X, α⟩` to `⟨V, Y, β⟩` is a pair `(f : U ⟶ V, F : U ⨯ Y ⟶ X)` such that
`{(u,y) | α(u, F(u, y))} ⊆ {(u,y) | β(f(u), y)}`. The subset `α` is actually encoded as an element
of `Subobject (U × X)`, and the above inequality is expressed using pullbacks. -/
structure Dial where
  /-- The source object -/
  src : C
  /-- The target object -/
  tgt : C
  /-- A subobject of `src ⨯ tgt`, interpreted as a relation -/
  rel : Subobject (src ⨯ tgt)

namespace Dial

local notation "π₁" => prod.fst
local notation "π₂" => prod.snd
local notation "π(" a ", " b ")" => prod.lift a b

/-- A morphism in the `Dial C` category from `⟨U, X, α⟩` to `⟨V, Y, β⟩` is a pair
`(f : U ⟶ V, F : U ⨯ Y ⟶ X)` such that `{(u,y) | α(u, F(u, y))} ≤ {(u,y) | β(f(u), y)}`. -/
@[ext] structure Hom (X Y : Dial C) where
  /-- Maps the sources -/
  f : X.src ⟶ Y.src
  /-- Maps the targets (contravariantly) -/
  F : X.src ⨯ Y.tgt ⟶ X.tgt
  /-- This says `{(u, y) | α(u, F(u, y))} ⊆ {(u, y) | β(f(u), y)}` using subobject pullbacks -/
  le :
    (Subobject.pullback π(π₁, F)).obj X.rel ≤
    (Subobject.pullback (prod.map f (𝟙 _))).obj Y.rel

theorem comp_le_lemma {X Y Z : Dial C} (F : Dial.Hom X Y) (G : Dial.Hom Y Z) :
    let F1 := π(π₁, prod.map F.f (𝟙 _) ≫ G.F)
    (Subobject.pullback π(π₁, F1 ≫ F.F)).obj X.rel ≤
    (Subobject.pullback (prod.map (F.f ≫ G.f) (𝟙 Z.tgt))).obj Z.rel := by
  intro F1
  let F2 := prod.map F.f (𝟙 Z.tgt)
  have h1 := (Subobject.pullback F1).monotone F.le
  have h2 := (Subobject.pullback F2).monotone G.le
  rw [← Subobject.pullback_comp, ← Subobject.pullback_comp] at h1 h2
  rw [(_ : F1 ≫ _ = _)] at h1
  rw [(_ : F2 ≫ _ = _), (_ : F2 ≫ _ = _)] at h2
  · exact le_trans h1 h2
  · simp [F2]
  · simp [F1, F2]
  · simp [F1]

@[simps]
instance : Category (Dial C) where
  Hom := Dial.Hom
  id X := {
    f := 𝟙 _
    F := π₂
    le := by simp
  }
  comp {X Y Z} (F G : Dial.Hom ..) := {
    f := F.f ≫ G.f
    F := π(π₁, prod.map F.f (𝟙 _) ≫ G.F) ≫ F.F
    le := comp_le_lemma F G
  }
  id_comp f := by simp; rfl
  comp_id f := by simp; rfl
  assoc f g h := by
    simp only [Category.assoc, Hom.mk.injEq, true_and]
    rw [← Category.assoc, ← Category.assoc]; congr 1
    ext <;> simp

@[ext] theorem hom_ext {X Y : Dial C} {x y : X ⟶ Y} (hf : x.f = y.f) (hF : x.F = y.F) : x = y :=
   Hom.ext x y hf hF

@[simps]
def isoMk {X Y : Dial C} (e₁ : X.src ≅ Y.src) (e₂ : X.tgt ≅ Y.tgt)
    (eq : X.rel = (Subobject.pullback (prod.map e₁.hom e₂.hom)).obj Y.rel) : X ≅ Y where
  hom := {
    f := e₁.hom
    F := π₂ ≫ e₂.inv
    le := by rw [eq, ← Subobject.pullback_comp]; apply le_of_eq; congr; ext <;> simp
  }
  inv := {
    f := e₁.inv
    F := π₂ ≫ e₂.hom
    le := by rw [eq, ← Subobject.pullback_comp]; apply le_of_eq; congr; ext <;> simp
  }

end Dial

end CategoryTheory
