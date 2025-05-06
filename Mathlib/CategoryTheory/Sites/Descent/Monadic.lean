/-
Copyright (c) 2025 Christian Merten, Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Joël Riou
-/

import Mathlib.CategoryTheory.Sites.Descent.DescentData
import Mathlib.CategoryTheory.Monad.Adjunction

/-!
# Descent and Coalgebras
-/

-- a v4.19.0 regression
set_option linter.unusedTactic false

noncomputable section

universe t v' v u' u

namespace CategoryTheory

open Limits Opposite

section Adjunction

variable {C : Type*} [Bicategory C] (F : Pseudofunctor C Cat.{v', u'})

/- This is a stub, should be replaced by a psedofunctor with (judgementally) fixed `obj`
in the opposite direction. -/
structure Pseudofunctor.Adjunction where
  /-- A pseudo-functor in the opposite direction -/
  map {X Y : C} (f : X ⟶ Y) : F.obj Y ⟶ F.obj X
  /-- Componentwise adjunctions -/
  adj {X Y : C} (f : X ⟶ Y) : F.map f ⊣ map f

variable {F} (G : F.Adjunction)

instance {X Y : C} (f : X ⟶ Y) : (G.map f).IsRightAdjoint :=
  (G.adj f).isRightAdjoint

end Adjunction

variable {C : Type u} [Category.{v} C] {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
  {G : F.Adjunction}

variable {X S : C} {f : X ⟶ S} {sq : ChosenPullback f f}
  (e : G.map f.op.toLoc ⋙ F.map f.op.toLoc ≅ F.map sq.p₂.op.toLoc ⋙ G.map sq.p₁.op.toLoc)
  (diag : sq.Diagonal) (sq₃ : ChosenPullback₃ sq sq sq)

namespace Comonad

def Coalgebra.descentDataHom (A : (G.adj f.op.toLoc).toComonad.Coalgebra) :
    (F.map sq.p₁.op.toLoc).obj A.A ⟶ (F.map sq.p₂.op.toLoc).obj A.A :=
  ((G.adj sq.p₁.op.toLoc).homEquiv A.A _).symm (A.a ≫ e.hom.app A.A)

variable (A : (G.adj f.op.toLoc).toComonad.Coalgebra)

lemma Coalgebra.descentDataHom_eq_comp :
    A.descentDataHom e =
      (F.map (sq.p₁.op.toLoc)).map (A.a ≫ e.hom.app A.A) ≫
        (G.adj sq.p₁.op.toLoc).counit.app ((F.map sq.p₂.op.toLoc).obj A.A) :=
  rfl

macro "simptoloc" : tactic => `(tactic|simp [← Quiver.Hom.comp_toLoc, ← op_comp])

/-
Compatiblity of the base change isomorphism `e` and the adjunctions at `f` and `p₁`. This
is needed, because the counits are not uniquely determined (only up to unique isomorphism).

TODO: Is there a better way to state this? Since there is no map `F(p₁) ⟶ F(p₂)`, the "obvious"
square is missing a map. Hence we whisker the "obvious" square on the right with `F(diag)`.
-/
-- note: we are def-eq abusing here, there could (should?) be `Functor.associator`s
def IsCompatible : Prop :=
  (G.adj f.op.toLoc).counit ≫
    (F.mapId' _).inv ≫ (F.mapComp' sq.p₂.op.toLoc diag.f.op.toLoc (𝟙 _)
      (by simptoloc)).hom =
    e.hom ≫
      whiskerLeft _ ((Functor.rightUnitor (G.map sq.p₁.op.toLoc)).inv ≫
        whiskerLeft _ (F.mapId' _).inv ≫
        whiskerLeft (G.map sq.p₁.op.toLoc)
          (F.mapComp' sq.p₁.op.toLoc diag.f.op.toLoc (𝟙 _) (by simptoloc)).hom) ≫
      (Functor.associator _ _ _).inv ≫ (Functor.associator _ _ _).inv ≫
      whiskerRight
        (whiskerLeft (F.map sq.p₂.op.toLoc) (G.adj sq.p₁.op.toLoc).counit) (F.map diag.f.op.toLoc)

lemma counit_adj_comp_mapComp' (H : IsCompatible e diag) (M : F.obj ⟨op X⟩) :
    (G.adj f.op.toLoc).counit.app M ≫
      (F.mapId' _).inv.app M ≫
      (F.mapComp' sq.p₂.op.toLoc diag.f.op.toLoc (𝟙 _)
          (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.app M =
        e.hom.app M ≫
          (F.mapId' _).inv.app _ ≫
          (F.mapComp' sq.p₁.op.toLoc diag.f.op.toLoc (𝟙 _)
            (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.app _ ≫
          (F.map diag.f.op.toLoc).map
            ((G.adj sq.p₁.op.toLoc).counit.app _) := by
  simpa using congr($(H).app M)

lemma counit_adj_comp_mapComp'_2 (H : IsCompatible e diag) (M : F.obj ⟨op X⟩) :
    (F.map diag.f.op.toLoc).map
        ((G.adj sq.p₁.op.toLoc).counit.app ((F.map sq.p₂.op.toLoc).obj M)) =
    (F.mapComp' sq.p₁.op.toLoc diag.f.op.toLoc (𝟙 _)
      (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).inv.app _ ≫
      (F.mapId' _).hom.app _ ≫
      e.inv.app M ≫ (G.adj f.op.toLoc).counit.app M ≫ (F.mapId' _).inv.app M ≫
      (F.mapComp' sq.p₂.op.toLoc diag.f.op.toLoc (𝟙 _)
          (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.app M := by
  rw [counit_adj_comp_mapComp' e diag H]
  simp

lemma Coalgebra.mk''Hom_eq₁₂ :
    Pseudofunctor.DescentData.mk''Hom (i₁ := ()) (i₂ := ())
      (fun _ : Unit ↦ A.A) (fun _ _ : Unit ↦ sq) (fun _ _ ↦ A.descentDataHom e)
      sq₃.p sq₃.p₁ sq₃.p₂ (by simp) (by simp) =
      (F.mapComp' sq.p₁.op.toLoc sq₃.p₁₂.op.toLoc sq₃.p₁.op.toLoc (by simptoloc)).hom.app A.A ≫
    (F.map sq₃.p₁₂.op.toLoc).map (Coalgebra.descentDataHom e A) ≫
      (F.mapComp' sq.p₂.op.toLoc sq₃.p₁₂.op.toLoc sq₃.p₂.op.toLoc (by simptoloc)).inv.app A.A := by
  rw [Pseudofunctor.DescentData.mk''Hom_eq (Y := sq₃.chosenPullback.pullback) _ _ _ sq₃.p
    (p := sq₃.p₁₂)]
  · simp
  · simp

lemma Coalgebra.mk''Hom_eq₁₃ :
    Pseudofunctor.DescentData.mk''Hom (i₁ := ()) (i₂ := ())
      (fun _ : Unit ↦ A.A) (fun _ _ : Unit ↦ sq) (fun _ _ ↦ A.descentDataHom e)
      sq₃.p sq₃.p₁ sq₃.p₃ (by simp) (by simp) =
    (F.mapComp' sq.p₁.op.toLoc sq₃.p₁₃.op.toLoc sq₃.p₁.op.toLoc (by simptoloc)).hom.app A.A ≫
      (F.map sq₃.p₁₃.op.toLoc).map (descentDataHom e A) ≫
        (F.mapComp' sq.p₂.op.toLoc sq₃.p₁₃.op.toLoc sq₃.p₃.op.toLoc
          (by simptoloc)).inv.app A.A := by
  rw [Pseudofunctor.DescentData.mk''Hom_eq (Y := sq₃.chosenPullback.pullback) _ _ _ sq₃.p
    (p := sq₃.p₁₃)]
  · simp
  · simp

lemma Coalgebra.mk''Hom_eq₂₃ :
    Pseudofunctor.DescentData.mk''Hom (i₁ := ()) (i₂ := ())
      (fun _ : Unit ↦ A.A) (fun _ _ : Unit ↦ sq) (fun _ _ ↦ A.descentDataHom e)
      sq₃.p sq₃.p₂ sq₃.p₃ (by simp) (by simp) =
    (F.mapComp' sq.p₁.op.toLoc sq₃.p₂₃.op.toLoc sq₃.p₂.op.toLoc (by simptoloc)).hom.app A.A ≫
    (F.map sq₃.p₂₃.op.toLoc).map (descentDataHom e A) ≫
      (F.mapComp' sq.p₂.op.toLoc sq₃.p₂₃.op.toLoc sq₃.p₃.op.toLoc (by simptoloc)).inv.app A.A := by
  rw [Pseudofunctor.DescentData.mk''Hom_eq (Y := sq₃.chosenPullback.pullback) _ _ _ sq₃.p
    (p := sq₃.p₂₃)]
  · simp
  · simp

-- the coassociativity axiom expressed in terms of `descentDataHom`
lemma Coalgebra.descentDataHom_map_p₂_a (A : (G.adj f.op.toLoc).toComonad.Coalgebra) :
    A.descentDataHom e ≫ (F.map sq.p₂.op.toLoc).map A.a =
      (F.map sq.p₁.op.toLoc).map A.a ≫
        (F.map sq.p₁.op.toLoc).map ((G.adj f.op.toLoc).toComonad.δ.app A.A) ≫
        (F.map sq.p₁.op.toLoc).map (e.hom.app _) ≫
        (G.adj sq.p₁.op.toLoc).counit.app _ := by
  rw [descentDataHom_eq_comp]
  simp only [Adjunction.toComonad_coe, Functor.comp_obj, Functor.id_obj, Functor.map_comp,
    Category.assoc, Adjunction.toComonad_δ, whiskerRight_app, whiskerLeft_app]
  have := (G.adj sq.p₁.op.toLoc).counit.naturality ((F.map sq.p₂.op.toLoc).map A.a)
  dsimp at this
  rw [← this]
  simp_rw [← Functor.map_comp_assoc]
  have := e.hom.naturality A.a
  dsimp at this
  rw [← this]
  have := A.coassoc
  dsimp at this
  rw [← reassoc_of% this]

-- sq₃.p sq₃.p₂ sq₃.p₃
/-- A coalgebra defines a descent datum. -/
def Coalgebra.descentData (H : IsCompatible e diag) (A : (G.adj f.op.toLoc).toComonad.Coalgebra) :
    F.DescentData (fun _ : Unit ↦ f) := by
  refine .mk'' (fun _ ↦ A.A) (fun _ _ ↦ sq) (fun _ _ ↦ A.descentDataHom e) (fun _ ↦ diag)
      (fun _ ↦ ?_) (fun _ _ _ ↦ sq₃) (fun _ _ _ ↦ ?_)
  · dsimp
    rw [Coalgebra.descentDataHom_eq_comp]
    simp only [Functor.comp_obj, Functor.id_obj, Adjunction.toComonad_coe, Functor.map_comp,
      Category.assoc]
    rw [counit_adj_comp_mapComp'_2 e diag H]
    simp only [Cat.comp_obj, Cat.id_obj, Functor.comp_obj, Functor.id_obj,
      Pseudofunctor.mapComp'_inv_naturality_assoc, NatTrans.naturality_assoc, Cat.id_map,
      Iso.hom_inv_id_app_assoc, NatIso.cancel_natIso_inv_left]
    -- TODO: add specialized lemmas for comonad coming from an adjunction?
    erw [A.counit_assoc]
    simp
  · dsimp
    rw [Coalgebra.mk''Hom_eq₁₂, Coalgebra.mk''Hom_eq₁₃, Coalgebra.mk''Hom_eq₂₃]
    nth_rw 2 [Coalgebra.descentDataHom_eq_comp]
    simp
    have heq :
        (F.mapComp' sq.p₂.op.toLoc sq₃.p₁₂.op.toLoc sq₃.p₂.op.toLoc (by simptoloc)).inv.app A.A ≫
        (F.mapComp' sq.p₁.op.toLoc sq₃.p₂₃.op.toLoc sq₃.p₂.op.toLoc (by simptoloc)).hom.app A.A ≫
        (F.map sq₃.p₂₃.op.toLoc).map ((F.map sq.p₁.op.toLoc).map A.a) =
        (F.map sq₃.p₁₂.op.toLoc).map ((F.map sq.p₂.op.toLoc).map A.a) ≫
        (F.mapComp' sq.p₂.op.toLoc sq₃.p₁₂.op.toLoc sq₃.p₂.op.toLoc (by simptoloc)).inv.app _ ≫
        (F.mapComp' sq.p₁.op.toLoc sq₃.p₂₃.op.toLoc sq₃.p₂.op.toLoc (by simptoloc)).hom.app _ := by
      simp
    rw [reassoc_of% heq]
    simp_rw [← Functor.map_comp_assoc, Coalgebra.descentDataHom_map_p₂_a]
    simp
    sorry

end Comonad

end CategoryTheory
