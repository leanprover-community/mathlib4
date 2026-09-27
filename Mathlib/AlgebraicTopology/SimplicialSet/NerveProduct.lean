/-
Copyright (c) 2026 Dennis Sweeney. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dennis Sweeney
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Cat
public import Mathlib.CategoryTheory.Functor.Currying

/-!
# The nerve of a product category

The nerve of a product category can be identified with the product of the nerves. This leads
to a proof that a natural transformation between functors induces a homotopy between their
`nerveMap`s.
-/

@[expose] public section

open CategoryTheory MonoidalCategory SSet Functor

universe v u

namespace CategoryTheory.nerve

/-- `nerve` preserves products. -/
def nerveProdIso (C₁ C₂ : Type u) [Category.{v} C₁] [Category.{v} C₂] :
    nerve (C₁ × C₂) ≅ nerve C₁ ⊗ nerve C₂ :=
  NatIso.ofComponents (fun n ↦ (ComposableArrows.prodEquiv C₁ C₂ n.unop.len).toIso)

instance : Monoidal nerveFunctor where
  δ C₁ C₂ := (nerveProdIso C₁ C₂).hom
  μ C₁ C₂ := (nerveProdIso C₁ C₂).inv
  η := SemiCartesianMonoidalCategory.toUnit _
  ε.app _ := TypeCat.ofHom fun _ ↦
    { obj _ := ⟨⟨⟨⟩⟩⟩
      map _ := ⟨⟨⟨rfl⟩⟩⟩ }

section
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
variable {F₀ F₁ : C ⥤ D}

/-- Convert a natural transformation between functors into a homotopy between their `nerveMap`s. -/
def homotopyOfNatTrans (η : F₀ ⟶ F₁) : Homotopy (nerveMap F₀) (nerveMap F₁) where
  h := nerve C ◁ (stdSimplex.isoNerve 1).hom ≫
    (nerveProdIso C (ULift (Fin 2))).inv ≫
    nerveMap ((𝟭 C).prod ( { obj i := i.down,
                             map ij := ⟨⟨ij.down.down⟩⟩} : ULift (Fin 2) ⥤ Fin 2) ⋙
              Prod.swap C (Fin 2) ⋙
              uncurry.obj (ComposableArrows.mk₁ η))
  h₀ := by
    let G₀ : C ⥤ Fin 2 × C := { obj c := ⟨0, c⟩, map f := ⟨𝟙 0, f⟩ }
    change nerveMap (G₀ ⋙ uncurry.obj (ComposableArrows.mk₁ η)) = nerveMap F₀
    apply congrArg nerveMap
    apply CategoryTheory.Functor.mk.congr_simp
    ext x y f
    apply Category.id_comp
  h₁ := by
    let G₁ : C ⥤ Fin 2 × C := { obj c := ⟨1, c⟩, map f := ⟨𝟙 1, f⟩ }
    change nerveMap (G₁ ⋙ uncurry.obj (ComposableArrows.mk₁ η)) = nerveMap F₁
    apply congrArg nerveMap
    apply CategoryTheory.Functor.mk.congr_simp
    ext x y f
    apply Category.id_comp
  rel := by
    ext n e_σ
    refine IsEmpty.elim' ?_ e_σ
    constructor
    intro ⟨⟨e, he⟩, _⟩
    simp at he

end

end CategoryTheory.nerve
