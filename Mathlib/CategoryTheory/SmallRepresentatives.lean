/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.EssentiallySmall
import Mathlib.SetTheory.Cardinal.Basic

/-!
# Representatives of essentially small categories

-/

universe w v u

namespace CategoryTheory

variable (Ω : Type w)

/-- Structure which allows to construct a category whose types
of objects and morphisms are subtype of a fixed type `Ω`. -/
structure SmallCategoryOfSet where
  obj : Set Ω
  hom (X Y : obj) : Set Ω
  id (X : obj) : hom X X
  comp {X Y Z : obj} (f : hom X Y) (g : hom Y Z) : hom X Z
  id_comp {X Y : obj} (f : hom X Y) : comp (id _) f = f := by cat_disch
  comp_id {X Y : obj} (f : hom X Y) : comp f (id _) = f := by cat_disch
  assoc {X Y Z T : obj} (f : hom X Y) (g : hom Y Z) (h : hom Z T) :
      comp (comp f g) h = comp f (comp g h) := by cat_disch

namespace SmallCategoryOfSet

attribute [simp] id_comp comp_id assoc

@[simps]
instance (S : SmallCategoryOfSet Ω) : SmallCategory S.obj where
  Hom X Y := S.hom X Y
  id := S.id
  comp := S.comp

abbrev categoryFamily : SmallCategoryOfSet Ω → Type w := fun S ↦ S.obj

end SmallCategoryOfSet

variable (C : Type u) [Category.{v} C]

structure CoreSmallCategoryOfSet where
  obj : Set Ω
  hom (X Y : obj) : Set Ω
  objEquiv : obj ≃ C
  homEquiv {X Y : obj} : hom X Y ≃ (objEquiv X ⟶ objEquiv Y)

namespace CoreSmallCategoryOfSet

variable {Ω C} (h : CoreSmallCategoryOfSet Ω C)

/-- The `SmallCategoryOfSet` structure induced by a
`CoreSmallCategoryOfSet` structure. -/
@[simps]
def smallCategoryOfSet : SmallCategoryOfSet Ω where
  obj := h.obj
  hom := h.hom
  id X := h.homEquiv.symm (𝟙 _)
  comp f g := h.homEquiv.symm (h.homEquiv f ≫ h.homEquiv g)

@[simps!]
def functor : h.smallCategoryOfSet.obj ⥤ C where
  obj := h.objEquiv
  map := h.homEquiv
  map_id _ := by
    rw [SmallCategoryOfSet.id_def]
    simp
  map_comp _ _ := by
    rw [SmallCategoryOfSet.comp_def]
    simp

def fullyFaithfulFunctor : h.functor.FullyFaithful where
  preimage := h.homEquiv.symm

instance : h.functor.Faithful := h.fullyFaithfulFunctor.faithful

instance : h.functor.Full := h.fullyFaithfulFunctor.full

instance : h.functor.EssSurj where
  mem_essImage Y := by
    obtain ⟨X, rfl⟩ := h.objEquiv.surjective Y
    exact ⟨_, ⟨Iso.refl _⟩⟩

instance : h.functor.IsEquivalence where

noncomputable def equivalence : h.smallCategoryOfSet.obj ≌ C :=
  h.functor.asEquivalence

end CoreSmallCategoryOfSet

namespace SmallCategoryOfSet

lemma exists_equivalence (C : Type w) [Category.{w} C]
    (h₁ : Cardinal.mk C ≤ Cardinal.mk Ω)
    (h₂ : ∀ (X Y : C), Cardinal.mk (X ⟶ Y) ≤ Cardinal.mk Ω) :
    ∃ (h : SmallCategoryOfSet Ω), Nonempty (categoryFamily Ω h ≌ C) := by
  obtain ⟨f₁, hf₁⟩ := h₁
  let f₂ (X Y) := (h₂ X Y).some
  let e := Equiv.ofInjective f₁ hf₁
  let h : CoreSmallCategoryOfSet Ω C :=
    { obj := Set.range f₁
      hom X Y := Set.range (f₂ (e.symm X) (e.symm Y))
      objEquiv := e.symm
      homEquiv {_ _} := by simpa using (Equiv.ofInjective _ ((f₂ _ _).injective)).symm }
  exact ⟨h.smallCategoryOfSet, ⟨h.equivalence⟩⟩

end SmallCategoryOfSet

end CategoryTheory
