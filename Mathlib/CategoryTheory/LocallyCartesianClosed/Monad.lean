/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
module

public import Mathlib.CategoryTheory.LocallyCartesianClosed.ExponentiableMorphism
public import Mathlib.CategoryTheory.Monad.Adjunction
public import Mathlib.CategoryTheory.Monad.Algebra


/-! # The monads and comonads associated to the pullback and pushforward adjunctions


-/


@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category Adjunction MonoidalCategory ChosenPullbacksAlong ExponentiableMorphism

#check Over.pullback

variable {C : Type u₁} [Category.{v₁} C]
variable {I J : C} (g : I ⟶ J)

#check Over.pullback

/-- The monad associated to the adjunction `Over.map g ⊣ pullback g`. -/
def mapPullbackMonad [ChosenPullbacksAlong g] : Monad (Over I) :=
  mapPullbackAdj g |>.toMonad

/-- The comonad associated to the adjunction `Over.map g ⊣ pullback g`. -/
def mapPullbackComonad [ChosenPullbacksAlong g] : Comonad (Over J) :=
  mapPullbackAdj g |>.toComonad

theorem mapPullbackComonad_obj [ChosenPullbacksAlong g] (X : Over J) :
    (mapPullbackComonad g).obj X =
      Over.mk (snd (X.hom) g ≫ g) := by
  rfl

theorem mapPullbackComonad_obj_left [ChosenPullbacksAlong g] (X : Over J) :
    ((mapPullbackComonad g).obj X).left = pullbackObj X.hom g := by
  rfl

@[simp]
theorem mapPullbackComonad_obj_hom [ChosenPullbacksAlong g] (X : Over J) :
    ((mapPullbackComonad g).obj X).hom = snd X.hom g ≫ g := by
  rfl

@[simp]
theorem mapPullbackComonad_map [ChosenPullbacksAlong g] {X Y : Over J} (f : X ⟶ Y) :
    (mapPullbackComonad g).map f = (Over.map g).map ((pullback g).map f) := by
    rfl

@[reassoc]
theorem mapPullbackComonad_map_left [ChosenPullbacksAlong g] {X Y : Over J} (f : X ⟶ Y) :
    ((mapPullbackComonad g).map f).left = ((pullback g).map f).left := by
  simp

@[simp]
theorem mapPullbackComonad_ε_app [ChosenPullbacksAlong g] (X : Over J) :
    ((mapPullbackComonad g).ε).app X = fst' X.hom g := by
  rfl

theorem pullbackComonad_ε_app_left [ChosenPullbacksAlong g] (X : Over J) :
    (((mapPullbackComonad g).ε).app X).left = fst X.hom g := by
  simp

-- without appealing to the comonadicity theorem we show that the functor
-- `Over.map g : Over I ⥤ Over J` is comonadic.

namespace mapPullbackComonad

open Comonad

variable [ChosenPullbacksAlong g]

/-- The inverse to the comonad comparison functor for the adjunction `Over.map g ⊣ pullback g`.
This establishes that `Over.map g : Over I ⥤ Over J` is comonadic. -/
@[simps]
def comparisonInv : (mapPullbackComonad g).Coalgebra ⥤ Over I where
  obj c := Over.mk (Y := c.A.left) (c.a.left ≫ (snd c.A.hom g))
  map {c c'} f := Over.homMk f.f.left
    (by rw [Over.mk_hom, ← Category.assoc, ← Over.comp_left, ← f.h, Over.comp_left]; cat_disch)

theorem comparison_mapPullbackAdj_obj_comparisonInv_obj_a_left
    (c : mapPullbackComonad g |>.Coalgebra) :
    (comparison (mapPullbackAdj g) |>.obj (comparisonInv g |>.obj c)).a.left =
      lift (𝟙 _) (((comparisonInv g).obj c).hom) (by cat_disch) :=
  by
    simp

@[simp]
theorem coalgebra_a_left_snd_map (c : mapPullbackComonad g |>.Coalgebra) :
    c.a.left ≫ snd c.A.hom g ≫ g = c.A.hom := by
  have h := c.a.w
  simp only [Functor.id_map, mapPullbackComonad_obj_hom] at h
  simp [h]

@[reassoc (attr := simp)]
theorem coalgebra_a_left_fst (c : mapPullbackComonad g |>.Coalgebra) :
    c.a.left ≫ fst c.A.hom g = 𝟙 _ :=
  congrArg (CommaMorphism.left) c.counit

theorem coalgebra_a_left (c : mapPullbackComonad g |>.Coalgebra) :
    c.a.left = lift (𝟙 _) (c.a.left ≫ snd c.A.hom g) (by cat_disch) := by
  have := lift_comp_fst_snd (f := c.A.hom) (g := g) c.a.left
  conv_lhs => rw [← this]
  simp only [coalgebra_a_left_fst]

/-- The `A.hom` component of the counit for the equivalence
`comparisonInverse ⋙ Comonad.comparison (mapPullbackAdj g) ≅ 𝟭`.

This shows that, on objects `c` in the coalgebra category,
the underlying over morphism is definitionally the original `c.A.hom`. -/
-- @[reassoc (attr := simp)]
lemma comparisonInv_comparison_A_hom
    (c : mapPullbackComonad g |>.Coalgebra) :
      ((comparisonInv g ⋙
        Comonad.comparison (mapPullbackAdj g)).obj c).A.hom =
        ((𝟭 (mapPullbackComonad g).Coalgebra).obj c).A.hom := by
  simp

@[simps]
def comparisonComparisonInvIsoId :
     𝟭 (Over I) ≅ comparison (mapPullbackAdj g) ⋙ comparisonInv g where
  hom.app X := Over.homMk (𝟙 X.left) (by simp)
  inv.app X := Over.homMk (𝟙 X.left) (by simp)

#check Coalgebra.isoMk

#check NatIso.ofComponents

@[simps]
def comparisonInvComparisonIsoId  :
    comparisonInv g ⋙ Comonad.comparison (mapPullbackAdj g) ≅
      𝟭 (mapPullbackComonad g).Coalgebra := by
  refine NatIso.ofComponents (fun c => ?_) ?_
  · refine Coalgebra.isoMk ?_ ?_
    · exact ⟨Over.homMk (𝟙 c.A.left), Over.homMk (𝟙 c.A.left), by aesop, by aesop⟩
    · ext
      simp
      conv_rhs =>
        rw [coalgebra_a_left]
      generalize_proofs h1 h2 h3
      have : ((pullback g).map (Over.homMk (U := Over.mk (Y := c.A.left) (c.a.left ≫ snd c.A.hom g ≫ g)) (V := c.A) (𝟙 c.A.left))).left = Over.homMk (𝟙 _) (by sorry) := by sorry
      --have : ((pullback g).map (CostructuredArrow.homMk (𝟙 c.A.left) h2)).left = 𝟙 _ := by sorry
      simp
      convert this using 1
      conv_lhs =>
        rw [this]
      sorry
  · aesop




    -- hom := {
    --   app c := {
    --     f := Over.homMk (𝟙 c.A.left)
    --     h := by
    --       ext
    --       simp
    --       have := lift_comp_fst_snd (f := c.A.hom) (g := g) c.a.left
    --       conv_rhs => rw [← this]
    --       simp_rw [coalgebra_left_fst]


    --       -- convert Category.comp_id (lift (𝟙 c.A.left) (c.a.left ≫ snd c.A.hom g) ⋯)
    --       -- simp
    --       -- aesop


    --       --convert this


    --   }
    --   naturality := _
    -- }
    -- inv := _
    -- hom_inv_id := _
    -- inv_hom_id := _

example (X : Over I) (f : X.left ⟶ I) (h : f = X.hom) :
    Over.mk (Y := X.left) f = X := by
  rw [h]
  rfl

@[simps!]
def comparisonEquivalence  :
    Over I ≌  mapPullbackComonad g |>.Coalgebra where
  functor := Comonad.comparison (mapPullbackAdj g)
  inverse := comparisonInv g
  unitIso := {
    hom.app X := Over.homMk (𝟙 X.left) (by simp)
    inv.app X := Over.homMk (𝟙 X.left) (by simp)
  }
  counitIso := {
    hom.app c := {
      f := Over.homMk (𝟙 c.A.left)
      h := by
        ext
        simp only [Functor.comp_obj, comparisonInv_obj]
        simp only [Comonad.comparison_obj_a, mapPullbackAdj_unit_app]
        simp only [Over.comp_left]
        simp only [Over.map_map_left, Over.homMk_left, Over.mk_hom]
        simp only [mapPullbackComonad_map, Over.map_map_left]
        simp?
        generalize_proofs h1 h2
        simp only [Over.map_obj_hom, Over.mk_hom] at h2
        have h3 : c.a.left ≫ fst c.A.hom g = 𝟙 _ := by
          exact congrArg (CommaMorphism.left) c.counit
        --simp_rw [← h3]
        have := lift_comp_fst_snd (f := c.A.hom) (g := g) c.a.left
        conv_rhs => rw [← this]
        simp [Over.homMk_id]
        sorry
        --simp_rw [h3]
        --conv_lhs => rw [Over.homMK_id]

        --cat_disch
        -- rw [this]
        -- ext
        -- simp

    }
    inv.app c := {
      f := Over.homMk (𝟙 c.A.left)
      h := by
        ext
        simp


        sorry
    }
  }
  functor_unitIso_comp := sorry

instance [ChosenPullbacksAlong g] : ComonadicLeftAdjoint (Over.map g) where
  R := pullback g
  adj := mapPullbackAdj g
  eqv := Equivalence.isEquivalence_functor (mapPullbackMonadComparisonEquivalence g)


end mapPullbackComonad


/-- The comonad associated to the adjunction `Over.map g ⊣ pullback g`. -/
def pullbackPushforwardMonad [ChosenPullbacksAlong g] [ExponentiableMorphism g] :
    Monad (Over J) := pullbackPushforwardAdj g |>.toMonad


end CategoryTheory
