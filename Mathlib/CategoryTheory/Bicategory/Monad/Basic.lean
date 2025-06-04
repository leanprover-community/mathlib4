/-
Copyright (c) 2025 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete
import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Oplax
import Mathlib.CategoryTheory.Bicategory.End
import Mathlib.CategoryTheory.Monoidal.Comon_

/-!
# Comonads in a bicategory

We define comonads in a bicategory `B` as comonoid objects in an endomorphism monoidal category.
We show that this is equivalent to oplax functors from the trivial bicategory to `B`. From this,
we show that comonads in `B` form a bicategory.

## TODO

We can also define monads in a bicategory. This is not yet done as we don't have the bicategory
structure on the set of lax functors at this point, which is needed to show that monads form a
bicategory.
-/

namespace CategoryTheory

namespace Bicategory

universe u₀ w v u

variable {B : Type u} [Bicategory.{w, v} B]

/-- A comonad in a bicategory `B` is a 1-morphism `t : a ⟶ a` together with 2-morphisms
`Δ : t ⟶ t ≫ t` and `ε : t ⟶ 𝟙 a` satisfying the comonad laws. -/
abbrev Comonad {a : B} (t : a ⟶ a) := Comon_Class t

/-- The counit 2-morphism of the comonad. -/
abbrev Comonad.counit {a : B} {t : a ⟶ a} [Comonad t] : t ⟶ 𝟙 a := Comon_Class.counit

/-- The comultiplication 2-morphism of the comonad. -/
abbrev Comonad.comul {a : B} {t : a ⟶ a} [Comonad t] : t ⟶ t ≫ t := Comon_Class.comul

@[inherit_doc] scoped notation "ε" => Comonad.counit
@[inherit_doc] scoped notation "ε["x"]" => Comonad.counit (t := x)
@[inherit_doc] scoped notation "Δ" => Comonad.comul
@[inherit_doc] scoped notation "Δ["x"]" => Comonad.comul (t := x)

namespace Comonad

variable {a: B}

/- Comonad laws -/
section

variable (t : a ⟶ a) [Comonad t]

@[reassoc (attr := simp)]
theorem counit_comul : Δ ≫ ε ▷ t = (λ_ t).inv := Comon_Class.counit_comul t

@[reassoc (attr := simp)]
theorem comul_counit : Δ ≫ t ◁ ε = (ρ_ t).inv := Comon_Class.comul_counit t

@[reassoc (attr := simp)]
theorem comul_assoc : Δ ≫ t ◁ Δ = Δ ≫ Δ ▷ t ≫ (α_ t t t).hom := Comon_Class.comul_assoc t

@[reassoc]
theorem comul_assoc_flip : Δ ≫ Δ ▷ t = Δ ≫ t ◁ Δ ≫ (α_ t t t).inv := Comon_Class.comul_assoc_flip t

end

@[simps!]
instance {a : B} : Comonad (𝟙 a) :=
  inferInstanceAs <| Comon_Class (MonoidalCategory.tensorUnit (a ⟶ a))

/-- An oplax functor from the trivial bicategory to `B` defines a comonad in `B`. -/
def ofOplaxFromPUnit (F : OplaxFunctor (LocallyDiscrete (Discrete PUnit.{u₀ + 1})) B) :
    Comonad (F.map (𝟙 ⟨⟨PUnit.unit⟩⟩)) where
  comul := F.map₂ (ρ_ _).inv ≫ F.mapComp _ _
  counit := F.mapId _
  comul_assoc' := by
    simp only [tensorObj_def, MonoidalCategory.whiskerLeft_comp, whiskerLeft_def, Category.assoc,
      MonoidalCategory.comp_whiskerRight, whiskerRight_def, associator_def]
    rw [← F.mapComp_naturality_left_assoc, ← F.mapComp_naturality_right_assoc]
    simp only [whiskerLeft_rightUnitor_inv, PrelaxFunctor.map₂_comp, Category.assoc,
      OplaxFunctor.map₂_associator, whiskerRight_id, Iso.hom_inv_id_assoc]
  counit_comul' := by
    simp only [tensorUnit_def, tensorObj_def, whiskerRight_def, Category.assoc, leftUnitor_def]
    rw [F.mapComp_id_left, unitors_equal, F.map₂_inv_hom_assoc]
  comul_counit' := by
    simp only [tensorUnit_def, tensorObj_def, whiskerLeft_def, rightUnitor_def]
    rw [Category.assoc, F.mapComp_id_right, F.map₂_inv_hom_assoc]

/-- A comonad in `B` defines a oplax functor from the trivial bicategory to `B`. -/
def toOplax {a : B} (t : a ⟶ a) [Comonad t] :
    OplaxFunctor (LocallyDiscrete (Discrete PUnit.{u₀ + 1})) B where
  obj _ := a
  map _ := t
  map₂ _ := 𝟙 _
  mapId _ := ε
  mapComp _ _ := Δ
  map₂_associator _ _ _ := by
    rw [Category.id_comp]
    apply Comonad.comul_assoc

end Comonad

/-- The bicategory of comonads in `B`. -/
def ComonadBicat (B : Type u) [Bicategory.{w, v} B] :=
  OplaxFunctor (LocallyDiscrete (Discrete PUnit.{u₀ + 1})) B

namespace ComonadBicat

open scoped Oplax.OplaxTrans.OplaxFunctor in
instance : Bicategory (ComonadBicat B) :=
  inferInstanceAs <| Bicategory (OplaxFunctor (LocallyDiscrete (Discrete PUnit.{u₀ + 1})) B)

/-- The oplax functor from the trivial bicategory to `B` associated with the comonad. -/
def toOplax (m : ComonadBicat B) : OplaxFunctor (LocallyDiscrete (Discrete PUnit.{u₀ + 1})) B :=
  m

/-- The object in `B` associated with the comonad. -/
def obj (m : ComonadBicat B) :=
  m.toOplax.obj ⟨⟨PUnit.unit.{u₀ + 1}⟩⟩

/-- The morphism in `B` associated with the comonad. -/
def hom (m : ComonadBicat B) : ComonadBicat.obj.{u₀} m ⟶ ComonadBicat.obj.{u₀} m :=
  m.toOplax.map (𝟙 (⟨⟨PUnit.unit.{u₀ + 1}⟩⟩ : LocallyDiscrete (Discrete PUnit.{u₀ + 1})))

instance (m : ComonadBicat B) : Comonad m.hom :=
  Comonad.ofOplaxFromPUnit <| ComonadBicat.toOplax.{u₀} m

/-- Construct a comonad as an object in `ComonadBicat B`. -/
def mkOfComonad {a : B} (g : a ⟶ a) [Comonad g] : ComonadBicat B :=
  Comonad.toOplax.{u₀} g

open Comonad

section

variable {a : B} (g : a ⟶ a) [Comonad g]

theorem mkOfComonad_hom : (mkOfComonad.{u₀} g).hom = g := rfl

theorem mkOfComonad_counit : ε[(mkOfComonad.{u₀} g).hom] = ε[g] := rfl

theorem mkOfComonad_comul : Δ[(mkOfComonad.{u₀} g).hom] = Δ[g] := by
  change 𝟙 g ≫ Δ = Δ
  apply Category.id_comp

end

end ComonadBicat

end Bicategory

end CategoryTheory
