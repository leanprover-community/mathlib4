/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Functor.EpiMono

/-!

# Adjunctions involving evaluation

We show that evaluation of functors has adjoints, given the existence of (co)products.

-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section


namespace CategoryTheory

open CategoryTheory.Limits

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D]

noncomputable section

section

variable [∀ a b : C, HasCoproductsOfShape (a ⟶ b) D]

set_option backward.isDefEq.respectTransparency false in
/-- The left adjoint of evaluation. -/
@[simps]
def evaluationLeftAdjoint (c : C) : D ⥤ C ⥤ D where
  obj d :=
    { obj := fun t => ∐ fun _ : c ⟶ t => d
      map := fun f => Sigma.desc fun g => (Sigma.ι fun _ => d) <| g ≫ f }
  map {_ d₂} f :=
    { app := fun _ => Sigma.desc fun h => f ≫ Sigma.ι (fun _ => d₂) h
      naturality := by
        intros
        dsimp
        ext
        simp }

set_option backward.isDefEq.respectTransparency false in
/-- The adjunction showing that evaluation is a right adjoint. -/
@[simps! unit_app counit_app_app]
def evaluationAdjunctionRight (c : C) : evaluationLeftAdjoint D c ⊣ (evaluation _ _).obj c :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun d F =>
        { toFun := fun f => Sigma.ι (fun _ => d) (𝟙 _) ≫ f.app c
          invFun := fun f => { app := fun _ => Sigma.desc fun h => f ≫ F.map h }
          left_inv := by
            intro f
            ext x
            dsimp
            ext g
            simp only [colimit.ι_desc, Cofan.mk_ι_app, Category.assoc, ← f.naturality,
              evaluationLeftAdjoint_obj_map, colimit.ι_desc_assoc,
              Discrete.functor_obj, Cofan.mk_pt, Category.id_comp]
          right_inv := fun f => by simp } }

instance evaluationIsRightAdjoint (c : C) : ((evaluation _ D).obj c).IsRightAdjoint :=
  ⟨_, ⟨evaluationAdjunctionRight _ _⟩⟩

/-- See also the file `Mathlib/CategoryTheory/Limits/FunctorCategory/EpiMono.lean`
for a similar result under a `HasPullbacks` assumption. -/
theorem NatTrans.mono_iff_mono_app' {F G : C ⥤ D} (η : F ⟶ G) : Mono η ↔ ∀ c, Mono (η.app c) := by
  constructor
  · intro h c
    exact (inferInstance : Mono (((evaluation _ _).obj c).map η))
  · intro _
    apply NatTrans.mono_of_mono_app

end

section

variable [∀ a b : C, HasProductsOfShape (a ⟶ b) D]

set_option backward.isDefEq.respectTransparency false in
/-- The right adjoint of evaluation. -/
@[simps]
def evaluationRightAdjoint (c : C) : D ⥤ C ⥤ D where
  obj d :=
    { obj := fun t => ∏ᶜ fun _ : t ⟶ c => d
      map := fun f => Pi.lift fun g => Pi.π _ <| f ≫ g }
  map f := { app := fun _ => Pi.lift fun g => Pi.π _ g ≫ f }

set_option backward.isDefEq.respectTransparency false in
/-- The adjunction showing that evaluation is a left adjoint. -/
@[simps! unit_app_app counit_app]
def evaluationAdjunctionLeft (c : C) : (evaluation _ _).obj c ⊣ evaluationRightAdjoint D c :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun F d =>
        { toFun := fun f => { app := fun _ => Pi.lift fun g => F.map g ≫ f }
          invFun := fun f => f.app _ ≫ Pi.π _ (𝟙 _)
          left_inv := fun f => by simp
          right_inv := by
            intro f
            ext x
            dsimp
            ext g
            simp only [NatTrans.naturality_assoc,
              evaluationRightAdjoint_obj_obj, evaluationRightAdjoint_obj_map, limit.lift_π,
              Fan.mk_pt, Fan.mk_π_app, Category.comp_id] } }

instance evaluationIsLeftAdjoint (c : C) : ((evaluation _ D).obj c).IsLeftAdjoint :=
  ⟨_, ⟨evaluationAdjunctionLeft _ _⟩⟩

/-- See also the file `Mathlib/CategoryTheory/Limits/FunctorCategory/EpiMono.lean`
for a similar result under a `HasPushouts` assumption. -/
theorem NatTrans.epi_iff_epi_app' {F G : C ⥤ D} (η : F ⟶ G) : Epi η ↔ ∀ c, Epi (η.app c) := by
  constructor
  · intro h c
    exact (inferInstance : Epi (((evaluation _ _).obj c).map η))
  · intros
    apply NatTrans.epi_of_epi_app

end

end

end CategoryTheory
