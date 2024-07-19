/-
Copyright (c) 2024 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete
import Mathlib.CategoryTheory.Bicategory.FunctorBicategory
import Mathlib.Tactic.Widget.StringDiagram
import ProofWidgets.Component.Panel.GoalTypePanel

/-!
# Monads in a bicategory

We define a monad and a comonad in a bicategory `B`.
-/

namespace CategoryTheory

namespace Bicategory

universe w v u u₁

variable {B : Type u} [Bicategory.{w, v} B]

/-- A monad in a bicategory `B` is a 1-morphism `t : a ⟶ a` together with 2-morphisms
`μ : t ≫ t ⟶ t` and `η : 𝟙 a ⟶ t` satisfying the monad laws. -/
class Monad {a : B} (t : a ⟶ a) where
  /-- The multiplication 2-morphism of the monad. -/
  mul : t ≫ t ⟶ t
  /-- The unit 2-morphism of the monad. -/
  unit : 𝟙 a ⟶ t
  assoc : mul ▷ t ≫ mul = (α_ _ _ _).hom ≫ t ◁ mul ≫ mul := by aesop_cat
  left_unit : unit ▷ t ≫ mul = (λ_ t).hom := by aesop_cat
  right_unit : t ◁ unit ≫ mul = (ρ_ t).hom := by aesop_cat

@[inherit_doc] scoped notation " μ " => Monad.mul
@[inherit_doc] scoped notation " η " => Monad.unit

/-- A comonad in a bicategory `B` is a 1-morphism `g : a ⟶ a` together with 2-morphisms
`δ : g ⟶ g ≫ g` and `ε : g ⟶ 𝟙 a` satisfying the comonad laws. -/
class Comonad {a : B} (g : a ⟶ a) where
  /-- The comultiplication 2-morphism of the comonad. -/
  comul : g ⟶ g ≫ g
  /-- The counit 2-morphism of the comonad. -/
  counit : g ⟶ 𝟙 a
  coassoc : comul ≫ comul ▷ g = comul ≫ g ◁ comul ≫ (α_ _ _ _).inv := by aesop_cat
  left_counit : comul ≫ counit ▷ g = (λ_ g).inv := by aesop_cat
  right_counit : comul ≫ g ◁ counit = (ρ_ g).inv := by aesop_cat

@[inherit_doc] scoped notation " δ " => Comonad.comul
@[inherit_doc] scoped notation " ε " => Comonad.counit

attribute [reassoc (attr := simp)] Comonad.left_counit Comonad.right_counit

open ProofWidgets

show_panel_widgets [local GoalTypePanel]

example {a : B} (t : a ⟶ a) [Monad t] : μ ▷ t ≫ μ = (α_ _ _ _).hom ≫ t ◁ μ ≫ μ := by
  -- Place cursor here to see the string diagrams
  apply Monad.assoc

example {a : B} (t : a ⟶ a) [Monad t] : η ▷ t ≫ μ = (λ_ t).hom := by
  --
  apply Monad.left_unit

example {a : B} (t : a ⟶ a) [Monad t] : t ◁ η ≫ μ = (ρ_ t).hom := by
  --
  apply Monad.right_unit

example {a : B} (g : a ⟶ a) [Comonad g] : δ ≫ δ ▷ g = δ ≫ g ◁ δ ≫ (α_ _ _ _).inv := by
  --
  apply Comonad.coassoc

example {a : B} (g : a ⟶ a) [Comonad g] : δ ≫ ε ▷ g = (λ_ g).inv := by
  --
  apply Comonad.left_counit

example {a : B} (g : a ⟶ a) [Comonad g] : δ ≫ g ◁ ε = (ρ_ g).inv := by
  --
  apply Comonad.right_counit


namespace Monad

instance {a : B} : Monad (𝟙 a) where
  mul := (ρ_ _).hom
  unit := 𝟙 _

/-- Construct a monad in `B` from a lax functor from the trivial bicategory to `B`. -/
def ofLaxFromPUnit (F : LaxFunctor (LocallyDiscrete (Discrete PUnit)) B) :
    Monad (F.map (𝟙 ⟨⟨PUnit.unit⟩⟩)) where
  mul := F.mapComp _ _ ≫ F.map₂ (ρ_ _).hom
  unit := F.mapId _
  assoc := by
    set x : LocallyDiscrete (Discrete PUnit) := ⟨⟨PUnit.unit⟩⟩
    simp only [comp_whiskerRight, Category.assoc, whiskerLeft_comp]
    rw [← F.mapComp_naturality_left_assoc, ← F.mapComp_naturality_right_assoc]
    simp [F.mapComp_assoc_left_assoc]
  left_unit := (F.map₂_leftUnitor_hom _).symm
  right_unit := (F.map₂_rightUnitor_hom _).symm

end Monad

namespace Comonad

theorem coassoc_symm {a : B} (g : a ⟶ a) [Comonad g] :
    comul ≫ g ◁ comul = comul ≫ comul ▷ g ≫ (α_ _ _ _).hom := by
  rw [← cancel_mono (α_ _ _ _).inv]
  simp [Comonad.coassoc]

instance {a : B} : Comonad (𝟙 a) where
  comul := (ρ_ _).inv
  counit := 𝟙 _

/-- Construct a comonad in `B` from an oplax functor from the trivial bicategory to `B`. -/
def ofOplaxFromPUnit (F : OplaxFunctor (LocallyDiscrete (Discrete PUnit)) B) :
    Comonad (F.map (𝟙 ⟨⟨PUnit.unit⟩⟩)) where
  comul := F.map₂ (ρ_ _).inv ≫ F.mapComp _ _
  counit := F.mapId _
  coassoc := by
    set x : LocallyDiscrete (Discrete PUnit) := ⟨⟨PUnit.unit⟩⟩
    simp only [comp_whiskerRight, Category.assoc, whiskerLeft_comp]
    rw [← F.mapComp_naturality_left_assoc, ← F.mapComp_naturality_right_assoc]
    simp only [whiskerRight_id, Iso.hom_inv_id_assoc, whiskerLeft_rightUnitor_inv,
      PrelaxFunctor.map₂_comp, Category.assoc, OplaxFunctor.map₂_associator_assoc, Iso.hom_inv_id,
      Category.comp_id]
  left_counit := by
    set x : LocallyDiscrete (Discrete PUnit) := ⟨⟨PUnit.unit⟩⟩
    rw [Category.assoc, F.mapComp_id_left, unitors_equal, F.map₂_inv_hom_assoc]
  right_counit := by
    set x : LocallyDiscrete (Discrete PUnit) := ⟨⟨PUnit.unit⟩⟩
    rw [Category.assoc, F.mapComp_id_right, F.map₂_inv_hom_assoc]

/-- The oplax functor from the trivial bicategory to `B` associated with the comonad. -/
def toOplax {a : B} (t : a ⟶ a) [Comonad t] :
    OplaxFunctor (LocallyDiscrete (Discrete PUnit)) B where
  obj := fun _ => a
  map := fun _ => t
  map₂ := fun _ => 𝟙 _
  mapId _ := ε
  mapComp _ _ := δ
  map₂_associator _ _ _ := by
    dsimp only
    rw [Category.id_comp]
    apply coassoc_symm

end Comonad

/-- The bicateogry of comonads in `B`. -/
def ComonadBicat (B : Type u) [Bicategory.{w, v} B] :=
  OplaxFunctor (LocallyDiscrete (Discrete PUnit)) B

namespace ComonadBicat

instance : Bicategory (ComonadBicat B) :=
  inferInstanceAs <| Bicategory (OplaxFunctor (LocallyDiscrete (Discrete PUnit)) B)

/-- The oplax functor from the trivial bicategory to `B` associated with the comonad. -/
def toOplax (m : ComonadBicat B) : OplaxFunctor (LocallyDiscrete (Discrete PUnit)) B :=
  m

/-- The object in `B` associated with the comonad. -/
def obj (m : ComonadBicat B) :=
  m.toOplax.obj ⟨⟨PUnit.unit⟩⟩

/-- The morphism in `B` associated with the comonad. -/
def hom (m : ComonadBicat B) : m.obj ⟶ m.obj :=
  m.toOplax.map (𝟙 ⟨⟨PUnit.unit⟩⟩)

instance (m : ComonadBicat B) : Comonad m.hom :=
  Comonad.ofOplaxFromPUnit m.toOplax

/-- Construct a comonad as an object in `ComonadBicat B`. -/
def mkOfComonad {a : B} (g : a ⟶ a) [Comonad g] : ComonadBicat B :=
  Comonad.toOplax g

end ComonadBicat

end Bicategory

end CategoryTheory
