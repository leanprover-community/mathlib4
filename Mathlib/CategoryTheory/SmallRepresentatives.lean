/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Equivalence
import Mathlib.SetTheory.Cardinal.Order

/-!
# Representatives of small categories

Given a type `Ω : Type w`, we construct a structure `SmallCategoryOfSet Ω : Type w`
which consists of the data and axioms that allows to define a category
structure such that the type of objects and morphisms identify to subtypes of `Ω`.

This allows to define a small family of small categories
`SmallCategoryOfSet.categoryFamily : SmallCategoryOfSet Ω → Type w`
which, up to equivalence, represents all categories such that
types of objects and morphisms have cardinalities less than or equal to
that of `Ω` (see `SmallCategoryOfSet.exists_equivalence`).

-/

universe w v u

namespace CategoryTheory

variable (Ω : Type w)

/-- Structure which allows to construct a category whose types
of objects and morphisms are subtypes of a fixed type `Ω`. -/
structure SmallCategoryOfSet where
  /-- objects -/
  obj : Set Ω
  /-- morphisms -/
  hom (X Y : obj) : Set Ω
  /-- identity morphisms -/
  id (X : obj) : hom X X
  /-- the composition of morphisms -/
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

/-- The family of all categories such that the types of objects and
morphisms are subtypes of a given type `Ω`. -/
abbrev categoryFamily : SmallCategoryOfSet Ω → Type w := fun S ↦ S.obj

end SmallCategoryOfSet

variable (C : Type u) [Category.{v} C]

/-- Helper structure for the construction of a term in `SmallCategoryOfSet`.
This involves the choice of bijections between types of objects and morphisms
in a category `C` and subtypes of a type `Ω`. -/
structure CoreSmallCategoryOfSet where
  /-- objects -/
  obj : Set Ω
  /-- morphisms -/
  hom (X Y : obj) : Set Ω
  /-- a bijection between the types of objects -/
  objEquiv : obj ≃ C
  /-- a bijection between the types of morphisms -/
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

/-- Given `h : CoreSmallCategoryOfSet Ω C`, this is the
obvious functor `h.smallCategoryOfSet.obj ⥤ C`. -/
@[simps!]
def functor : h.smallCategoryOfSet.obj ⥤ C where
  obj := h.objEquiv
  map := h.homEquiv
  map_id _ := by rw [SmallCategoryOfSet.id_def]; simp
  map_comp _ _ := by rw [SmallCategoryOfSet.comp_def]; simp

/-- Given `h : CoreSmallCategoryOfSet Ω C`,
the obvious functor `h.smallCategoryOfSet.obj ⥤ C` is fully faithful. -/
def fullyFaithfulFunctor : h.functor.FullyFaithful where
  preimage := h.homEquiv.symm

instance : h.functor.IsEquivalence where
  faithful := h.fullyFaithfulFunctor.faithful
  full := h.fullyFaithfulFunctor.full
  essSurj.mem_essImage Y := by
    obtain ⟨X, rfl⟩ := h.objEquiv.surjective Y
    exact ⟨_, ⟨Iso.refl _⟩⟩

/-- Given `h : CoreSmallCategoryOfSet Ω C`,
the obvious functor `h.smallCategoryOfSet.obj ⥤ C` is an equivalence. -/
noncomputable def equivalence : h.smallCategoryOfSet.obj ≌ C :=
  h.functor.asEquivalence

end CoreSmallCategoryOfSet

namespace SmallCategoryOfSet

lemma exists_equivalence (C : Type u) [Category.{v} C]
    (h₁ : Cardinal.lift.{w} (Cardinal.mk C) ≤ Cardinal.lift.{u} (Cardinal.mk Ω))
    (h₂ : ∀ (X Y : C), Cardinal.lift.{w} (Cardinal.mk (X ⟶ Y)) ≤
      Cardinal.lift.{v} (Cardinal.mk Ω)) :
    ∃ (h : SmallCategoryOfSet Ω), Nonempty (categoryFamily Ω h ≌ C) := by
  let f₁ := (Cardinal.lift_mk_le'.1 h₁).some
  let f₂ (X Y) := (Cardinal.lift_mk_le'.1 (h₂ X Y)).some
  let e := Equiv.ofInjective _ f₁.injective
  let h : CoreSmallCategoryOfSet Ω C :=
    { obj := Set.range f₁
      hom X Y := Set.range (f₂ (e.symm X) (e.symm Y))
      objEquiv := e.symm
      homEquiv {_ _} := by simpa using (Equiv.ofInjective _ ((f₂ _ _).injective)).symm }
  exact ⟨h.smallCategoryOfSet, ⟨h.equivalence⟩⟩

end SmallCategoryOfSet

end CategoryTheory
