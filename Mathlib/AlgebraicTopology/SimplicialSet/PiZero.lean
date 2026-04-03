/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Nonempty
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers

/-!
# Connected components of simplicial sets

-/

universe u

open CategoryTheory Simplicial Limits Opposite

namespace SSet

variable {X Y Z : SSet.{u}}

def π₀Rel (x₀ x₁ : X _⦋0⦌) : Prop :=
  ∃ (e : X _⦋1⦌), X.δ 1 e = x₀ ∧ X.δ 0 e = x₁

variable (X) in
def π₀ : Type u := Quot (π₀Rel (X := X))

def π₀.mk : X _⦋0⦌ → X.π₀ := Quot.mk _

lemma π₀.mk_surjective : Function.Surjective (π₀.mk (X := X)) := Quot.mk_surjective

lemma π₀.sound {x₀ x₁ : X _⦋0⦌} (e : X _⦋1⦌) (h₀ : X.δ 1 e = x₀) (h₁ : X.δ 0 e = x₁) :
    π₀.mk x₀ = π₀.mk x₁ :=
  Quot.sound ⟨e, h₀, h₁⟩

lemma π₀.mk_eq_mk_iff (x₀ x₁ : X _⦋0⦌) :
    π₀.mk x₀ = π₀.mk x₁ ↔ Relation.EqvGen π₀Rel x₀ x₁ :=
  Quot.eq

def mapπ₀ (f : X ⟶ Y) : π₀ X → π₀ Y :=
  Quot.lift (fun x ↦ π₀.mk (f.app _ x)) (by
    rintro _ _ ⟨e, rfl, rfl⟩
    apply π₀.sound (f.app _ e)
    all_goals simp only [δ_naturality_apply])

@[simp]
lemma mapπ₀_mk (f : X ⟶ Y) (x₀ : X _⦋0⦌) : mapπ₀ f (π₀.mk x₀) = π₀.mk (f.app _ x₀) := rfl

@[simp]
lemma mapπ₀_id_apply (x : π₀ X) : mapπ₀ (𝟙 X) x = x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  rw [mapπ₀_mk, NatTrans.id_app, types_id_apply]

@[simp]
lemma mapπ₀_comp_apply (f : X ⟶ Y) (g : Y ⟶ Z) (x : π₀ X) :
    mapπ₀ (f ≫ g) x = mapπ₀ g (mapπ₀ f x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  simp

@[simps]
def π₀Functor : SSet.{u} ⥤ Type u where
  obj X := π₀ X
  map f := mapπ₀ f

def toπ₀NatTrans : SSet.evaluation.obj (op ⦋0⦌) ⟶ π₀Functor.{u} where
  app X := π₀.mk

abbrev coforkπ₀Functor :
    Cofork (SSet.evaluation.{u}.map (SimplexCategory.δ (1 : Fin 2)).op)
      (SSet.evaluation.map (SimplexCategory.δ (0 : Fin 2)).op) :=
  Cofork.ofπ toπ₀NatTrans (by
    ext X s
    exact π₀.sound s rfl rfl)

def isColimitCoforkπ₀Functor : IsColimit coforkπ₀Functor.{u} :=
  evaluationJointlyReflectsColimits _ (fun X ↦
    (isColimitMapCoconeCoforkEquiv _ _).2
      (Cofork.IsColimit.mk _ (fun s ↦ Quot.lift s.π (by
          dsimp at s
          rintro _ _ ⟨h, rfl, rfl⟩
          exact congr_fun s.condition h))
        (fun s ↦ rfl) (fun s m hm ↦ by
          ext x
          obtain ⟨x, rfl⟩ := x.mk_surjective
          dsimp at s m hm x ⊢
          exact congr_fun hm x)))

instance {J : Type*} [Category J] [Small.{u} J] :
    PreservesColimitsOfShape J π₀Functor.{u} := by
  have : (ObjectProperty.preservesColimitsOfShape J :
      ObjectProperty (SSet.{u} ⥤ Type u)).IsClosedUnderColimitsOfShape
        WalkingParallelPair :=
    ObjectProperty.closedUnderColimitsOfShape_preservesColimitsOfShape ..
  exact (ObjectProperty.preservesColimitsOfShape J).prop_of_isColimit
    isColimitCoforkπ₀Functor (by
      rintro (_ | _) <;> apply evaluation_preservesColimitsOfShape)

variable (X)
abbrev IsPreconnected : Prop := Subsingleton (π₀ X)

class IsConnected : Prop extends IsPreconnected X where
  nonempty : X.Nonempty := by infer_instance

attribute [instance] IsConnected.nonempty

end SSet
