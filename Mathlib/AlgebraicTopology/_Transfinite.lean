import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.SetTheory.Ordinal.Arithmetic

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]

-- constructions in the category {β | β ≤ α}

def ord_le_of_lt {α β : Ordinal.{v}} (hβ : β < α) : {β | β ≤ α} := ⟨β, le_of_lt hβ⟩

def ord_succ_le_of_lt {α β : Ordinal.{v}} (hβ : β < α) : {β | β ≤ α} :=
  ⟨β + 1, Order.succ_le_of_lt hβ⟩

def ord_zero_le {α : Ordinal.{v}} : {β | β ≤ α} := ⟨0, Ordinal.zero_le α⟩

def ord_le_refl (α : Ordinal.{v}) : {β | β ≤ α} := ⟨α, le_refl α⟩

def bot_to_top {α : Ordinal.{v}} : ord_zero_le ⟶ ord_le_refl α := LE.le.hom (Ordinal.zero_le α)

def ord_le_to_top {α β : Ordinal.{v}} (hβ : β ≤ α) : ⟨β, hβ⟩ ⟶ (ord_le_refl α) :=
  LE.le.hom hβ

def zero_to {α : Ordinal.{v}} (γ : Ordinal.{v}) (hγ : γ ≤ α) : ord_zero_le ⟶ ⟨γ, hγ⟩ :=
  LE.le.hom (Ordinal.zero_le γ)

def to_succ {α β : Ordinal.{v}} (hβ : β < α) : (ord_le_of_lt hβ) ⟶ (ord_succ_le_of_lt hβ) :=
  LE.le.hom (Ordinal.le_add_right β 1)

/-
  f is a transfinite composition if we have an ordinal α,
  and a colimit preserving F : {β | β ≤ α} ⥤ C
  such that F(β ⟶ β + 1) is of type S for all β < α.
  AND we have for this α that F(0 ⟶ α) is the same transfinite composition
  so that f = F(0 ⟶ α) (?)
-/
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
