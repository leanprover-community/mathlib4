import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.CategoryTheory.ChosenFiniteProducts
import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes
import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.CategoryTheory.Limits.Presheaf

namespace CategoryTheory

universe v u

open MonoidalCategory

class ChosenMonoidalClosed (C : Type u) [Category.{v} C] [ChosenFiniteProducts C] where
  closed (X : C) : Closed X

/-
def cartesianClosedOfChosenCartesianClosed
    {C : Type u} [Category.{v} C] [ChosenFiniteProducts C] [ChosenMonoidalClosed C]
    (rightAdj : C ⥤ C) (adj : (X : C) → tensorLeft X ⊣ rightAdj) :
  CartesianClosed C where
    closed := _
-/

-- namespace ChosenMonoidalClosed

/-
instance (priority := 100)
    (C : Type u) [Category.{v} C] [ChosenFiniteProducts C] [ChosenMonoidalClosed C] :
    CartesianClosed C where
-/

variable (C : Type u) [Category.{v} C] [ChosenFiniteProducts C] [ChosenMonoidalClosed C]

open Simplicial SimplexCategory

noncomputable
def SSetIHom (X Y : SSet) : SSet where
  obj := fun ⟨n⟩ ↦ (Δ[len n] ⊗ X) ⟶ Y
  map := fun f g ↦ SSet.standardSimplex.map f.unop ▷ X ≫ g

/-
noncomputable
def SSetIHomMap (X Y Z : SSet) (f : Y ⟶ Z) : SSetIHom X Y ⟶ SSetIHom X Z where
  app _ g := g ≫ f

noncomputable
def SSetRightAdj (X : SSet) : SSet ⥤ SSet where
  obj Y := SSetIHom X Y
  map f := SSetIHomMap _ _ _ f

def SSetAdj (X : SSet) : tensorLeft X ⊣ SSetRightAdj X := sorry
-/

variable (X Y : SSet)

def IHom_eval (X A : SSet) : X ⊗ SSetIHom X A ⟶ A where
  app n := fun ⟨x, f⟩ ↦ by
    refine f.app n ⟨?_, x⟩
    exact SSet.standardSimplex.objMk (OrderHom.id)
  naturality n m g := by
    ext ⟨x, f⟩
    have := f.naturality g
    apply_fun (fun f => f (SSet.standardSimplex.objMk OrderHom.id, x)) at this
    dsimp at this ⊢
    rw [← this]
    rfl

@[simp]
noncomputable
def IHomCostruct (X A : SSet) : CostructuredArrow (tensorLeft X) A :=
  CostructuredArrow.mk (IHom_eval X A)

noncomputable
def uniqhom (X A : SSet) : (H : CostructuredArrow (tensorLeft X) A) → H ⟶ (IHomCostruct X A) := by
  rintro ⟨H, h1, h2, h3⟩
  refine {
    left := {
      app := by
        dsimp only [IHomCostruct, CostructuredArrow.mk_left]
        intro n h
        refine ⟨?_, ?_⟩
        intro m
        sorry
        sorry
    }
    right := sorry
  }

noncomputable
def costruct_isterminal (X A : SSet) : Limits.IsTerminal (IHomCostruct X A) := by
  apply Limits.IsTerminal.ofUniqueHom (uniqhom X A)
  intro H f
  sorry


lemma costruct_terminal : ∀ A, Limits.HasTerminal (CostructuredArrow (tensorLeft X) A) := fun A ↦ by
  sorry

#check @rightAdjointOfCostructuredArrowTerminalsAux _ _ _ _ (tensorLeft X) (costruct_terminal X) Y
