/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tim Baumann, Stephen Morgan, Scott Morrison, Floris van Doorn
-/
import Mathlib.CategoryTheory.NatTrans
import Mathlib.CategoryTheory.Iso

/-!
# The category of functors and natural transformations between two fixed categories.

We provide the category instance on `C ⥤ D`, with morphisms the natural transformations.

## Universes

If `C` and `D` are both small categories at the same universe level,
this is another small category at that level.
However if `C` and `D` are both large categories at the same universe level,
this is a small category at the next higher level.
-/

set_option warningAsError false

section
open Lean Elab Tactic

-- https://github.com/leanprover/std4/pull/33
def extCore' : TacticM Unit := do do
    let gs ← Std.Tactic.Ext.extCore (← getMainGoal) [] 1000000 true
    replaceMainGoal <| gs.map (·.1) |>.toList

end

namespace CategoryTheory

-- declare the `v`'s first; see note [category_theory universes].
universe v₁ v₂ v₃ u₁ u₂ u₃

open NatTrans Category CategoryTheory.Functor

variable (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D]

attribute [local simp] vcomp_app

/-- `Functor.category C D` gives the category structure on functors and natural transformations
between categories `C` and `D`.

Notice that if `C` and `D` are both small categories at the same universe level,
this is another small category at that level.
However if `C` and `D` are both large categories at the same universe level,
this is a small category at the next higher level.
-/
instance Functor.category : Category.{max u₁ v₂} (C ⥤ D) where
  Hom F G := NatTrans F G
  id F := NatTrans.id F
  comp α β := vcomp α β
  comp_id' := by
    intros
    -- Sad that `ext` won't do this, indexing??
    apply NatTrans.ext
    ext X
    intros
    erw [vcomp_app] -- Lame, c.f. https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/unfolding.20earlier.20fields
    erw [id_app'] -- Again, lame
    simp
  id_comp' := sorry
  assoc' := sorry
#align category_theory.functor.category CategoryTheory.Functor.category

variable {C D} {E : Type u₃} [Category.{v₃} E]

variable {F G H I : C ⥤ D}

namespace NatTrans

-- Porting note: the behaviour of `ext` has changed here.
-- We need to provide a copy of the `NatTrans.ext` lemma,
-- written in terms of `F ⟶ G` rather than `NatTrans F G`,
-- or the `ext` will not retrieve it from the cache.
@[ext]
theorem ext' {α β : F ⟶ G} (w : α.app = β.app) : α = β := NatTrans.ext _ _ w

-- TODO Perhaps we should just turn on `ext` in aesop?
attribute [aesop safe tactic (rule_sets [CategoryTheory])] extCore'

@[simp]
theorem vcomp_eq_comp (α : F ⟶ G) (β : G ⟶ H) : vcomp α β = α ≫ β := rfl
#align category_theory.nat_trans.vcomp_eq_comp CategoryTheory.NatTrans.vcomp_eq_comp

theorem vcomp_app' (α : F ⟶ G) (β : G ⟶ H) (X : C) : (α ≫ β).app X = α.app X ≫ β.app X := rfl
#align category_theory.nat_trans.vcomp_app' CategoryTheory.NatTrans.vcomp_app'

theorem congr_app {α β : F ⟶ G} (h : α = β) (X : C) : α.app X = β.app X := by rw [h]
#align category_theory.nat_trans.congr_app CategoryTheory.NatTrans.congr_app

@[simp]
theorem id_app (F : C ⥤ D) (X : C) : (𝟙 F : F ⟶ F).app X = 𝟙 (F.obj X) := rfl
#align category_theory.nat_trans.id_app CategoryTheory.NatTrans.id_app

@[simp]
theorem comp_app {F G H : C ⥤ D} (α : F ⟶ G) (β : G ⟶ H) (X : C) :
    (α ≫ β).app X = α.app X ≫ β.app X := rfl
#align category_theory.nat_trans.comp_app CategoryTheory.NatTrans.comp_app

theorem app_naturality {F G : C ⥤ D ⥤ E} (T : F ⟶ G) (X : C) {Y Z : D} (f : Y ⟶ Z) :
    (F.obj X).map f ≫ (T.app X).app Z = (T.app X).app Y ≫ (G.obj X).map f :=
  (T.app X).naturality f
#align category_theory.nat_trans.app_naturality CategoryTheory.NatTrans.app_naturality

theorem naturality_app {F G : C ⥤ D ⥤ E} (T : F ⟶ G) (Z : D) {X Y : C} (f : X ⟶ Y) :
    (F.map f).app Z ≫ (T.app Y).app Z = (T.app X).app Z ≫ (G.map f).app Z :=
  congr_fun (congr_arg app (T.naturality f)) Z
#align category_theory.nat_trans.naturality_app CategoryTheory.NatTrans.naturality_app

/-- A natural transformation is a monomorphism if each component is. -/
theorem mono_of_mono_app (α : F ⟶ G) [∀ X : C, Mono (α.app X)] : Mono α :=
  ⟨fun g h eq => by
    ext X
    rw [← cancel_mono (α.app X), ← comp_app, eq, comp_app]⟩
#align category_theory.nat_trans.mono_of_mono_app CategoryTheory.NatTrans.mono_of_mono_app

/-- A natural transformation is an epimorphism if each component is. -/
theorem epi_of_epi_app (α : F ⟶ G) [∀ X : C, Epi (α.app X)] : Epi α :=
  ⟨fun g h eq => by
    ext X
    rw [← cancel_epi (α.app X), ← comp_app, eq, comp_app]⟩
#align category_theory.nat_trans.epi_of_epi_app CategoryTheory.NatTrans.epi_of_epi_app

/-- `hcomp α β` is the horizontal composition of natural transformations. -/
@[simps]
def hcomp {H I : D ⥤ E} (α : F ⟶ G) (β : H ⟶ I) : F ⋙ H ⟶ G ⋙ I where
  app := fun X : C => β.app (F.obj X) ≫ I.map (α.app X)
  naturality' X Y f := by
    rw [Functor.comp_map, Functor.comp_map, ← assoc, naturality, assoc, ← map_comp I, naturality,
      map_comp, assoc]
#align category_theory.nat_trans.hcomp CategoryTheory.NatTrans.hcomp

infixl:80 " ◫ " => hcomp

theorem hcomp_id_app {H : D ⥤ E} (α : F ⟶ G) (X : C) : (α ◫ 𝟙 H).app X = H.map (α.app X) := by
  simp
#align category_theory.nat_trans.hcomp_id_app CategoryTheory.NatTrans.hcomp_id_app

theorem id_hcomp_app {H : E ⥤ C} (α : F ⟶ G) (X : E) : (𝟙 H ◫ α).app X = α.app _ := by simp
#align category_theory.nat_trans.id_hcomp_app CategoryTheory.NatTrans.id_hcomp_app

-- Note that we don't yet prove a `hcomp_assoc` lemma here: even stating it is painful, because we
-- need to use associativity of functor composition. (It's true without the explicit associator,
-- because functor composition is definitionally associative,
-- but relying on the definitional equality causes bad problems with elaboration later.)
theorem exchange {I J K : D ⥤ E} (α : F ⟶ G) (β : G ⟶ H) (γ : I ⟶ J) (δ : J ⟶ K) :
    (α ≫ β) ◫ (γ ≫ δ) = (α ◫ γ) ≫ β ◫ δ := by
  aesop (rule_sets [CategoryTheory])
#align category_theory.nat_trans.exchange CategoryTheory.NatTrans.exchange

end NatTrans

open NatTrans

namespace Functor

/-- Flip the arguments of a bifunctor. See also `currying.lean`. -/
@[simps]
protected def flip (F : C ⥤ D ⥤ E) : D ⥤ C ⥤ E where
  obj k :=
    { obj := fun j => (F.obj j).obj k,
      map := fun f => (F.map f).app k, }
  map f := { app := fun j => (F.obj j).map f }
#align category_theory.functor.flip CategoryTheory.Functor.flip

end Functor

@[simp, reassoc]
theorem map_hom_inv_app (F : C ⥤ D ⥤ E) {X Y : C} (e : X ≅ Y) (Z : D) :
    (F.map e.hom).app Z ≫ (F.map e.inv).app Z = 𝟙 _ := by
  simp [← NatTrans.comp_app, ← Functor.map_comp]
#align category_theory.map_hom_inv_app CategoryTheory.map_hom_inv_app

@[simp, reassoc]
theorem map_inv_hom_app (F : C ⥤ D ⥤ E) {X Y : C} (e : X ≅ Y) (Z : D) :
    (F.map e.inv).app Z ≫ (F.map e.hom).app Z = 𝟙 _ := by
  simp [← NatTrans.comp_app, ← Functor.map_comp]
#align category_theory.map_inv_hom_app CategoryTheory.map_inv_hom_app

end CategoryTheory
