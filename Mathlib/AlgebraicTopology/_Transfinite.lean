import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.SetTheory.Ordinal.Basic

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]

def B {α β : Ordinal.{v}} (hβ : β < α) : {β | β ≤ α} := ⟨β, le_of_lt hβ⟩

def BSucc {α β : Ordinal.{v}} (hβ : β < α) : {β | β ≤ α} := ⟨β + 1, Order.succ_le_of_lt hβ⟩

def bot {α : Ordinal.{v}} : {β | β ≤ α} := ⟨0, Ordinal.zero_le α⟩

def top (α : Ordinal.{v}) : {β | β ≤ α} := ⟨α, le_refl α⟩

def bot_to_top {α : Ordinal.{v}} : bot ⟶ top α := LE.le.hom (Ordinal.zero_le α)

def to_succ {α β : Ordinal.{v}} (hβ : β < α) : (B hβ) ⟶ (BSucc hβ) :=
  LE.le.hom (Ordinal.le_add_right β 1)

inductive IsTransfiniteCompositionAux
    (S : MorphismProperty C) : ⦃X Y : C⦄ → (X ⟶ Y) → Prop where
  | mk
    (α : Ordinal.{v})
    (F : {β | β ≤ α} ⥤ C)
    (hF : Limits.PreservesColimits F)
    (hS : ∀ (β) (hβ : β < α), S (F.map (to_succ hβ))) :
      IsTransfiniteCompositionAux S (F.map bot_to_top)

def IsTransfiniteComposition (S : MorphismProperty C) : MorphismProperty C := fun _ _ f =>
  IsTransfiniteCompositionAux S f

example {C : Type u} [Category.{v} C] (S : MorphismProperty C)
    {X Y : C} (f : X ⟶ Y) (h : IsTransfiniteComposition S f) : f = f → True := by
  induction h
  sorry
