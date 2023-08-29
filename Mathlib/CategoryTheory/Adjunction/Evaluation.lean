/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Functor.EpiMono

#align_import category_theory.adjunction.evaluation from "leanprover-community/mathlib"@"937c692d73f5130c7fecd3fd32e81419f4e04eb7"

/-!

# Adjunctions involving evaluation

We show that evaluation of functors have adjoints, given the existence of (co)products.

-/


namespace CategoryTheory

open CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D]

noncomputable section

section

variable [∀ a b : C, HasCoproductsOfShape (a ⟶ b) D]

/-- The left adjoint of evaluation. -/
@[simps]
def evaluationLeftAdjoint (c : C) : D ⥤ C ⥤ D where
  obj d :=
    { obj := fun t => ∐ fun _ : c ⟶ t => d
      map := fun f => Sigma.desc fun g => (Sigma.ι fun _ => d) <| g ≫ f}
  map {_ d₂} f :=
    { app := fun e => Sigma.desc fun h => f ≫ Sigma.ι (fun _ => d₂) h
      naturality := by
        intros
        -- ⊢ ((fun d => Functor.mk { obj := fun t => ∐ fun x => d, map := fun {X Y} f =>  …
        dsimp
        -- ⊢ ((Sigma.desc fun g => Sigma.ι (fun x => x✝) (g ≫ f✝)) ≫ Sigma.desc fun h =>  …
        ext
        -- ⊢ (Sigma.ι (fun x => x✝) b✝ ≫ (Sigma.desc fun g => Sigma.ι (fun x => x✝) (g ≫  …
        simp }
        -- 🎉 no goals
#align category_theory.evaluation_left_adjoint CategoryTheory.evaluationLeftAdjoint

/-- The adjunction showing that evaluation is a right adjoint. -/
@[simps! unit_app counit_app_app]
def evaluationAdjunctionRight (c : C) : evaluationLeftAdjoint D c ⊣ (evaluation _ _).obj c :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun d F =>
        { toFun := fun f => Sigma.ι (fun _ => d) (𝟙 _) ≫ f.app c
          invFun := fun f =>
            { app := fun e => Sigma.desc fun h => f ≫ F.map h
              naturality := by
                intros
                -- ⊢ ((evaluationLeftAdjoint D c).obj d).map f✝ ≫ (fun e => Sigma.desc fun h => f …
                dsimp
                -- ⊢ ((Sigma.desc fun g => Sigma.ι (fun x => d) (g ≫ f✝)) ≫ Sigma.desc fun h => f …
                ext
                -- ⊢ (Sigma.ι (fun x => d) b✝ ≫ (Sigma.desc fun g => Sigma.ι (fun x => d) (g ≫ f✝ …
                simp }
                -- 🎉 no goals
          left_inv := by
            intro f
            -- ⊢ (fun f => NatTrans.mk fun e => Sigma.desc fun h => f ≫ F.map h) ((fun f => S …
            ext x
            -- ⊢ NatTrans.app ((fun f => NatTrans.mk fun e => Sigma.desc fun h => f ≫ F.map h …
            dsimp
            -- ⊢ (Sigma.desc fun h => (Sigma.ι (fun x => d) (𝟙 c) ≫ NatTrans.app f c) ≫ F.map …
            ext g
            -- ⊢ (Sigma.ι (fun x => d) g ≫ Sigma.desc fun h => (Sigma.ι (fun x => d) (𝟙 c) ≫  …
            simp only [colimit.ι_desc, Cofan.mk_ι_app, Category.assoc, ←f.naturality,
              evaluationLeftAdjoint_obj_map, colimit.ι_desc_assoc,
              Discrete.functor_obj, Cofan.mk_pt, Discrete.natTrans_app, Category.id_comp]
          right_inv := fun f => by
            dsimp
            -- ⊢ (Sigma.ι (fun x => d) (𝟙 c) ≫ Sigma.desc fun h => f ≫ F.map h) = f
            simp } }
            -- 🎉 no goals
#align category_theory.evaluation_adjunction_right CategoryTheory.evaluationAdjunctionRight

instance evaluationIsRightAdjoint (c : C) : IsRightAdjoint ((evaluation _ D).obj c) :=
  ⟨_, evaluationAdjunctionRight _ _⟩
#align category_theory.evaluation_is_right_adjoint CategoryTheory.evaluationIsRightAdjoint

theorem NatTrans.mono_iff_mono_app {F G : C ⥤ D} (η : F ⟶ G) : Mono η ↔ ∀ c, Mono (η.app c) := by
  constructor
  -- ⊢ Mono η → ∀ (c : C), Mono (app η c)
  · intro h c
    -- ⊢ Mono (app η c)
    exact (inferInstance : Mono (((evaluation _ _).obj c).map η))
    -- 🎉 no goals
  · intro _
    -- ⊢ Mono η
    apply NatTrans.mono_of_mono_app
    -- 🎉 no goals
#align category_theory.nat_trans.mono_iff_mono_app CategoryTheory.NatTrans.mono_iff_mono_app

end

section

variable [∀ a b : C, HasProductsOfShape (a ⟶ b) D]

/-- The right adjoint of evaluation. -/
@[simps]
def evaluationRightAdjoint (c : C) : D ⥤ C ⥤ D where
  obj d :=
    { obj := fun t => ∏ fun _ : t ⟶ c => d
      map := fun f => Pi.lift fun g => Pi.π _ <| f ≫ g }
  map f :=
    { app := fun t => Pi.lift fun g => Pi.π _ g ≫ f
      naturality := by
        intros
        -- ⊢ ((fun d => Functor.mk { obj := fun t => ∏ fun x => d, map := fun {X Y} f =>  …
        dsimp
        -- ⊢ ((Pi.lift fun g => Pi.π (fun x => X✝¹) (f✝ ≫ g)) ≫ Pi.lift fun g => Pi.π (fu …
        ext
        -- ⊢ ((Pi.lift fun g => Pi.π (fun x => X✝¹) (f✝ ≫ g)) ≫ Pi.lift fun g => Pi.π (fu …
        simp }
        -- 🎉 no goals
#align category_theory.evaluation_right_adjoint CategoryTheory.evaluationRightAdjoint

/-- The adjunction showing that evaluation is a left adjoint. -/
@[simps! unit_app_app counit_app]
def evaluationAdjunctionLeft (c : C) : (evaluation _ _).obj c ⊣ evaluationRightAdjoint D c :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun F d =>
        { toFun := fun f =>
            { app := fun t => Pi.lift fun g => F.map g ≫ f
              naturality := by
                intros
                -- ⊢ F.map f✝ ≫ (fun t => Pi.lift fun g => F.map g ≫ f) Y✝ = (fun t => Pi.lift fu …
                dsimp
                -- ⊢ (F.map f✝ ≫ Pi.lift fun g => F.map g ≫ f) = (Pi.lift fun g => F.map g ≫ f) ≫ …
                ext
                -- ⊢ (F.map f✝ ≫ Pi.lift fun g => F.map g ≫ f) ≫ Pi.π (fun x => d) b✝ = ((Pi.lift …
                simp }
                -- 🎉 no goals
          invFun := fun f => f.app _ ≫ Pi.π _ (𝟙 _)
          left_inv := fun f => by
            dsimp
            -- ⊢ (Pi.lift fun g => F.map g ≫ f) ≫ Pi.π (fun x => d) (𝟙 c) = f
            simp
            -- 🎉 no goals
          right_inv := by
            intro f
            -- ⊢ (fun f => NatTrans.mk fun t => Pi.lift fun g => F.map g ≫ f) ((fun f => NatT …
            ext x
            -- ⊢ NatTrans.app ((fun f => NatTrans.mk fun t => Pi.lift fun g => F.map g ≫ f) ( …
            dsimp
            -- ⊢ (Pi.lift fun g => F.map g ≫ NatTrans.app f c ≫ Pi.π (fun x => d) (𝟙 c)) = Na …
            ext g
            -- ⊢ (Pi.lift fun g => F.map g ≫ NatTrans.app f c ≫ Pi.π (fun x => d) (𝟙 c)) ≫ Pi …
            simp only [Discrete.functor_obj, NatTrans.naturality_assoc,
              evaluationRightAdjoint_obj_obj, evaluationRightAdjoint_obj_map, limit.lift_π,
              Fan.mk_pt, Fan.mk_π_app, Discrete.natTrans_app, Category.comp_id] } }
#align category_theory.evaluation_adjunction_left CategoryTheory.evaluationAdjunctionLeft

instance evaluationIsLeftAdjoint (c : C) : IsLeftAdjoint ((evaluation _ D).obj c) :=
  ⟨_, evaluationAdjunctionLeft _ _⟩
#align category_theory.evaluation_is_left_adjoint CategoryTheory.evaluationIsLeftAdjoint

theorem NatTrans.epi_iff_epi_app {F G : C ⥤ D} (η : F ⟶ G) : Epi η ↔ ∀ c, Epi (η.app c) := by
  constructor
  -- ⊢ Epi η → ∀ (c : C), Epi (app η c)
  · intro h c
    -- ⊢ Epi (app η c)
    exact (inferInstance : Epi (((evaluation _ _).obj c).map η))
    -- 🎉 no goals
  · intros
    -- ⊢ Epi η
    apply NatTrans.epi_of_epi_app
    -- 🎉 no goals
#align category_theory.nat_trans.epi_iff_epi_app CategoryTheory.NatTrans.epi_iff_epi_app

end

end

end CategoryTheory
