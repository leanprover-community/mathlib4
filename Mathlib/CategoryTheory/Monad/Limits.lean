/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta

! This file was ported from Lean 3 source module category_theory.monad.limits
! leanprover-community/mathlib commit 70fd9563a21e7b963887c9360bd29b2393e6225a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Monad.Adjunction
import Mathbin.CategoryTheory.Adjunction.Limits
import Mathbin.CategoryTheory.Limits.Shapes.Terminal

/-!
# Limits and colimits in the category of algebras

This file shows that the forgetful functor `forget T : algebra T ⥤ C` for a monad `T : C ⥤ C`
creates limits and creates any colimits which `T` preserves.
This is used to show that `algebra T` has any limits which `C` has, and any colimits which `C` has
and `T` preserves.
This is generalised to the case of a monadic functor `D ⥤ C`.

## TODO

Dualise for the category of coalgebras and comonadic left adjoints.
-/


namespace CategoryTheory

open Category

open CategoryTheory.Limits

universe v u v₁ v₂ u₁ u₂

-- morphism levels before object levels. See note [category_theory universes].
namespace Monad

variable {C : Type u₁} [Category.{v₁} C]

variable {T : Monad C}

variable {J : Type u} [Category.{v} J]

namespace ForgetCreatesLimits

variable (D : J ⥤ Algebra T) (c : Cone (D ⋙ T.forget)) (t : IsLimit c)

/-- (Impl) The natural transformation used to define the new cone -/
@[simps]
def γ : D ⋙ T.forget ⋙ ↑T ⟶ D ⋙ T.forget where app j := (D.obj j).a
#align category_theory.monad.forget_creates_limits.γ CategoryTheory.Monad.ForgetCreatesLimits.γ

/-- (Impl) This new cone is used to construct the algebra structure -/
@[simps π_app]
def newCone : Cone (D ⋙ forget T) where
  pt := T.obj c.pt
  π := (Functor.constComp _ _ ↑T).inv ≫ whiskerRight c.π T ≫ γ D
#align category_theory.monad.forget_creates_limits.new_cone CategoryTheory.Monad.ForgetCreatesLimits.newCone

/-- The algebra structure which will be the apex of the new limit cone for `D`. -/
@[simps]
def conePoint : Algebra T where
  A := c.pt
  a := t.lift (newCone D c)
  unit' :=
    t.hom_ext fun j =>
      by
      rw [category.assoc, t.fac, new_cone_π_app, ← T.η.naturality_assoc, functor.id_map,
        (D.obj j).Unit]
      dsimp; simp
  -- See library note [dsimp, simp]
  assoc' :=
    t.hom_ext fun j =>
      by
      rw [category.assoc, category.assoc, t.fac (new_cone D c), new_cone_π_app, ←
        functor.map_comp_assoc, t.fac (new_cone D c), new_cone_π_app, ← T.μ.naturality_assoc,
        (D.obj j).and_assoc, functor.map_comp, category.assoc]
      rfl
#align category_theory.monad.forget_creates_limits.cone_point CategoryTheory.Monad.ForgetCreatesLimits.conePoint

/-- (Impl) Construct the lifted cone in `algebra T` which will be limiting. -/
@[simps]
def liftedCone : Cone D where
  pt := conePoint D c t
  π :=
    { app := fun j => { f := c.π.app j }
      naturality' := fun X Y f => by
        ext1
        dsimp
        erw [c.w f]
        simp }
#align category_theory.monad.forget_creates_limits.lifted_cone CategoryTheory.Monad.ForgetCreatesLimits.liftedCone

/-- (Impl) Prove that the lifted cone is limiting. -/
@[simps]
def liftedConeIsLimit : IsLimit (liftedCone D c t)
    where
  lift s :=
    { f := t.lift ((forget T).mapCone s)
      h' :=
        t.hom_ext fun j => by
          dsimp
          rw [category.assoc, category.assoc, t.fac, new_cone_π_app, ← functor.map_comp_assoc,
            t.fac, functor.map_cone_π_app]
          apply (s.π.app j).h }
  uniq s m J := by
    ext1
    apply t.hom_ext
    intro j
    simpa [t.fac ((forget T).mapCone s) j] using congr_arg algebra.hom.f (J j)
#align category_theory.monad.forget_creates_limits.lifted_cone_is_limit CategoryTheory.Monad.ForgetCreatesLimits.liftedConeIsLimit

end ForgetCreatesLimits

-- Theorem 5.6.5 from [Riehl][riehl2017]
/-- The forgetful functor from the Eilenberg-Moore category creates limits. -/
noncomputable instance forgetCreatesLimits : CreatesLimitsOfSize (forget T)
    where CreatesLimitsOfShape J 𝒥 :=
    {
      CreatesLimit := fun D =>
        creates_limit_of_reflects_iso fun c t =>
          { liftedCone := forget_creates_limits.lifted_cone D c t
            validLift := cones.ext (iso.refl _) fun j => (id_comp _).symm
            makesLimit := forget_creates_limits.lifted_cone_is_limit _ _ _ } }
#align category_theory.monad.forget_creates_limits CategoryTheory.Monad.forgetCreatesLimits

/-- `D ⋙ forget T` has a limit, then `D` has a limit. -/
theorem hasLimit_of_comp_forget_hasLimit (D : J ⥤ Algebra T) [HasLimit (D ⋙ forget T)] :
    HasLimit D :=
  hasLimit_of_created D (forget T)
#align category_theory.monad.has_limit_of_comp_forget_has_limit CategoryTheory.Monad.hasLimit_of_comp_forget_hasLimit

namespace ForgetCreatesColimits

-- Let's hide the implementation details in a namespace
variable {D : J ⥤ Algebra T} (c : Cocone (D ⋙ forget T)) (t : IsColimit c)

-- We have a diagram D of shape J in the category of algebras, and we assume that we are given a
-- colimit for its image D ⋙ forget T under the forgetful functor, say its apex is L.
-- We'll construct a colimiting coalgebra for D, whose carrier will also be L.
-- To do this, we must find a map TL ⟶ L. Since T preserves colimits, TL is also a colimit.
-- In particular, it is a colimit for the diagram `(D ⋙ forget T) ⋙ T`
-- so to construct a map TL ⟶ L it suffices to show that L is the apex of a cocone for this diagram.
-- In other words, we need a natural transformation from const L to `(D ⋙ forget T) ⋙ T`.
-- But we already know that L is the apex of a cocone for the diagram `D ⋙ forget T`, so it
-- suffices to give a natural transformation `((D ⋙ forget T) ⋙ T) ⟶ (D ⋙ forget T)`:
/-- (Impl)
The natural transformation given by the algebra structure maps, used to construct a cocone `c` with
apex `colimit (D ⋙ forget T)`.
 -/
@[simps]
def γ : (D ⋙ forget T) ⋙ ↑T ⟶ D ⋙ forget T where app j := (D.obj j).a
#align category_theory.monad.forget_creates_colimits.γ CategoryTheory.Monad.ForgetCreatesColimits.γ

/-- (Impl)
A cocone for the diagram `(D ⋙ forget T) ⋙ T` found by composing the natural transformation `γ`
with the colimiting cocone for `D ⋙ forget T`.
-/
@[simps]
def newCocone : Cocone ((D ⋙ forget T) ⋙ ↑T)
    where
  pt := c.pt
  ι := γ ≫ c.ι
#align category_theory.monad.forget_creates_colimits.new_cocone CategoryTheory.Monad.ForgetCreatesColimits.newCocone

variable [PreservesColimit (D ⋙ forget T) (T : C ⥤ C)]

/-- (Impl)
Define the map `λ : TL ⟶ L`, which will serve as the structure of the coalgebra on `L`, and
we will show is the colimiting object. We use the cocone constructed by `c` and the fact that
`T` preserves colimits to produce this morphism.
-/
@[reducible]
def lambda : ((T : C ⥤ C).mapCocone c).pt ⟶ c.pt :=
  (isColimitOfPreserves _ t).desc (newCocone c)
#align category_theory.monad.forget_creates_colimits.lambda CategoryTheory.Monad.ForgetCreatesColimits.lambda

/-- (Impl) The key property defining the map `λ : TL ⟶ L`. -/
theorem commuting (j : J) : (T : C ⥤ C).map (c.ι.app j) ≫ lambda c t = (D.obj j).a ≫ c.ι.app j :=
  (isColimitOfPreserves _ t).fac (newCocone c) j
#align category_theory.monad.forget_creates_colimits.commuting CategoryTheory.Monad.ForgetCreatesColimits.commuting

variable [PreservesColimit ((D ⋙ forget T) ⋙ ↑T) (T : C ⥤ C)]

/-- (Impl)
Construct the colimiting algebra from the map `λ : TL ⟶ L` given by `lambda`. We are required to
show it satisfies the two algebra laws, which follow from the algebra laws for the image of `D` and
our `commuting` lemma.
-/
@[simps]
def coconePoint : Algebra T where
  A := c.pt
  a := lambda c t
  unit' := by
    apply t.hom_ext
    intro j
    rw [show c.ι.app j ≫ T.η.app c.X ≫ _ = T.η.app (D.obj j).A ≫ _ ≫ _ from
        T.η.naturality_assoc _ _,
      commuting, algebra.unit_assoc (D.obj j)]
    dsimp; simp
  -- See library note [dsimp, simp]
  assoc' :=
    by
    refine' (is_colimit_of_preserves _ (is_colimit_of_preserves _ t)).hom_ext fun j => _
    rw [functor.map_cocone_ι_app, functor.map_cocone_ι_app,
      show (T : C ⥤ C).map ((T : C ⥤ C).map _) ≫ _ ≫ _ = _ from T.μ.naturality_assoc _ _, ←
      functor.map_comp_assoc, commuting, functor.map_comp, category.assoc, commuting]
    apply (D.obj j).assoc_assoc _
#align category_theory.monad.forget_creates_colimits.cocone_point CategoryTheory.Monad.ForgetCreatesColimits.coconePoint

/-- (Impl) Construct the lifted cocone in `algebra T` which will be colimiting. -/
@[simps]
def liftedCocone : Cocone D where
  pt := coconePoint c t
  ι :=
    { app := fun j =>
        { f := c.ι.app j
          h' := commuting _ _ _ }
      naturality' := fun A B f => by
        ext1
        dsimp
        rw [comp_id]
        apply c.w }
#align category_theory.monad.forget_creates_colimits.lifted_cocone CategoryTheory.Monad.ForgetCreatesColimits.liftedCocone

/-- (Impl) Prove that the lifted cocone is colimiting. -/
@[simps]
def liftedCoconeIsColimit : IsColimit (liftedCocone c t)
    where
  desc s :=
    { f := t.desc ((forget T).mapCocone s)
      h' :=
        (isColimitOfPreserves (T : C ⥤ C) t).hom_ext fun j =>
          by
          dsimp
          rw [← functor.map_comp_assoc, ← category.assoc, t.fac, commuting, category.assoc, t.fac]
          apply algebra.hom.h }
  uniq s m J := by
    ext1
    apply t.hom_ext
    intro j
    simpa using congr_arg algebra.hom.f (J j)
#align category_theory.monad.forget_creates_colimits.lifted_cocone_is_colimit CategoryTheory.Monad.ForgetCreatesColimits.liftedCoconeIsColimit

end ForgetCreatesColimits

open ForgetCreatesColimits

-- TODO: the converse of this is true as well
/-- The forgetful functor from the Eilenberg-Moore category for a monad creates any colimit
which the monad itself preserves.
-/
noncomputable instance forgetCreatesColimit (D : J ⥤ Algebra T)
    [PreservesColimit (D ⋙ forget T) (T : C ⥤ C)]
    [PreservesColimit ((D ⋙ forget T) ⋙ ↑T) (T : C ⥤ C)] : CreatesColimit D (forget T) :=
  createsColimitOfReflectsIso fun c t =>
    { liftedCocone :=
        { pt := coconePoint c t
          ι :=
            { app := fun j =>
                { f := c.ι.app j
                  h' := commuting _ _ _ }
              naturality' := fun A B f => by
                ext1
                dsimp
                erw [comp_id, c.w] } }
      validLift := Cocones.ext (Iso.refl _) (by tidy)
      makesColimit := liftedCoconeIsColimit _ _ }
#align category_theory.monad.forget_creates_colimit CategoryTheory.Monad.forgetCreatesColimit

noncomputable instance forgetCreatesColimitsOfShape [PreservesColimitsOfShape J (T : C ⥤ C)] :
    CreatesColimitsOfShape J (forget T) where CreatesColimit K := by infer_instance
#align category_theory.monad.forget_creates_colimits_of_shape CategoryTheory.Monad.forgetCreatesColimitsOfShape

noncomputable instance forgetCreatesColimits [PreservesColimitsOfSize.{v, u} (T : C ⥤ C)] :
    CreatesColimitsOfSize.{v, u} (forget T) where CreatesColimitsOfShape J 𝒥₁ := by infer_instance
#align category_theory.monad.forget_creates_colimits CategoryTheory.Monad.forgetCreatesColimits

/-- For `D : J ⥤ algebra T`, `D ⋙ forget T` has a colimit, then `D` has a colimit provided colimits
of shape `J` are preserved by `T`.
-/
theorem forget_creates_colimits_of_monad_preserves [PreservesColimitsOfShape J (T : C ⥤ C)]
    (D : J ⥤ Algebra T) [HasColimit (D ⋙ forget T)] : HasColimit D :=
  hasColimit_of_created D (forget T)
#align category_theory.monad.forget_creates_colimits_of_monad_preserves CategoryTheory.Monad.forget_creates_colimits_of_monad_preserves

end Monad

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

variable {J : Type u} [Category.{v} J]

instance comp_comparison_forget_hasLimit (F : J ⥤ D) (R : D ⥤ C) [MonadicRightAdjoint R]
    [HasLimit (F ⋙ R)] :
    HasLimit ((F ⋙ Monad.comparison (Adjunction.ofRightAdjoint R)) ⋙ Monad.forget _) :=
  @hasLimitOfIso _ _ _ _ (F ⋙ R) _ _
    (isoWhiskerLeft F (Monad.comparisonForget (Adjunction.ofRightAdjoint R)).symm)
#align category_theory.comp_comparison_forget_has_limit CategoryTheory.comp_comparison_forget_hasLimit

instance comp_comparison_hasLimit (F : J ⥤ D) (R : D ⥤ C) [MonadicRightAdjoint R]
    [HasLimit (F ⋙ R)] : HasLimit (F ⋙ Monad.comparison (Adjunction.ofRightAdjoint R)) :=
  Monad.hasLimit_of_comp_forget_hasLimit (F ⋙ Monad.comparison (Adjunction.ofRightAdjoint R))
#align category_theory.comp_comparison_has_limit CategoryTheory.comp_comparison_hasLimit

/-- Any monadic functor creates limits. -/
noncomputable def monadicCreatesLimits (R : D ⥤ C) [MonadicRightAdjoint R] :
    CreatesLimitsOfSize.{v, u} R :=
  createsLimitsOfNatIso (Monad.comparisonForget (Adjunction.ofRightAdjoint R))
#align category_theory.monadic_creates_limits CategoryTheory.monadicCreatesLimits

/-- The forgetful functor from the Eilenberg-Moore category for a monad creates any colimit
which the monad itself preserves.
-/
noncomputable def monadicCreatesColimitOfPreservesColimit (R : D ⥤ C) (K : J ⥤ D)
    [MonadicRightAdjoint R] [PreservesColimit (K ⋙ R) (leftAdjoint R ⋙ R)]
    [PreservesColimit ((K ⋙ R) ⋙ leftAdjoint R ⋙ R) (leftAdjoint R ⋙ R)] : CreatesColimit K R :=
  by
  apply creates_colimit_of_nat_iso (monad.comparison_forget (adjunction.of_right_adjoint R))
  apply CategoryTheory.compCreatesColimit _ _
  infer_instance
  let i : (K ⋙ monad.comparison (adjunction.of_right_adjoint R)) ⋙ monad.forget _ ≅ K ⋙ R :=
    functor.associator _ _ _ ≪≫
      iso_whisker_left K (monad.comparison_forget (adjunction.of_right_adjoint R))
  apply CategoryTheory.Monad.forgetCreatesColimit _
  · dsimp
    refine' preserves_colimit_of_iso_diagram _ i.symm
  · dsimp
    refine' preserves_colimit_of_iso_diagram _ (iso_whisker_right i (left_adjoint R ⋙ R)).symm
#align category_theory.monadic_creates_colimit_of_preserves_colimit CategoryTheory.monadicCreatesColimitOfPreservesColimit

/-- A monadic functor creates any colimits of shapes it preserves. -/
noncomputable def monadicCreatesColimitsOfShapeOfPreservesColimitsOfShape (R : D ⥤ C)
    [MonadicRightAdjoint R] [PreservesColimitsOfShape J R] : CreatesColimitsOfShape J R :=
  haveI : preserves_colimits_of_shape J (left_adjoint R ⋙ R) :=
    by
    apply CategoryTheory.Limits.compPreservesColimitsOfShape _ _
    apply (adjunction.left_adjoint_preserves_colimits (adjunction.of_right_adjoint R)).1
    infer_instance
  ⟨fun K => monadic_creates_colimit_of_preserves_colimit _ _⟩
#align category_theory.monadic_creates_colimits_of_shape_of_preserves_colimits_of_shape CategoryTheory.monadicCreatesColimitsOfShapeOfPreservesColimitsOfShape

/-- A monadic functor creates colimits if it preserves colimits. -/
noncomputable def monadicCreatesColimitsOfPreservesColimits (R : D ⥤ C) [MonadicRightAdjoint R]
    [PreservesColimitsOfSize.{v, u} R] : CreatesColimitsOfSize.{v, u} R
    where CreatesColimitsOfShape J 𝒥₁ :=
    monadic_creates_colimits_of_shape_of_preserves_colimits_of_shape _
#align category_theory.monadic_creates_colimits_of_preserves_colimits CategoryTheory.monadicCreatesColimitsOfPreservesColimits

section

theorem hasLimit_of_reflective (F : J ⥤ D) (R : D ⥤ C) [HasLimit (F ⋙ R)] [Reflective R] :
    HasLimit F :=
  haveI := monadicCreatesLimits.{v, u} R
  has_limit_of_created F R
#align category_theory.has_limit_of_reflective CategoryTheory.hasLimit_of_reflective

/-- If `C` has limits of shape `J` then any reflective subcategory has limits of shape `J`. -/
theorem hasLimitsOfShape_of_reflective [HasLimitsOfShape J C] (R : D ⥤ C) [Reflective R] :
    HasLimitsOfShape J D :=
  { HasLimit := fun F => hasLimit_of_reflective F R }
#align category_theory.has_limits_of_shape_of_reflective CategoryTheory.hasLimitsOfShape_of_reflective

/-- If `C` has limits then any reflective subcategory has limits. -/
theorem has_limits_of_reflective (R : D ⥤ C) [HasLimitsOfSize.{v, u} C] [Reflective R] :
    HasLimitsOfSize.{v, u} D :=
  { HasLimitsOfShape := fun J 𝒥₁ => has_limits_of_shape_of_reflective R }
#align category_theory.has_limits_of_reflective CategoryTheory.has_limits_of_reflective

/-- If `C` has colimits of shape `J` then any reflective subcategory has colimits of shape `J`. -/
theorem hasColimitsOfShape_of_reflective (R : D ⥤ C) [Reflective R] [HasColimitsOfShape J C] :
    HasColimitsOfShape J D :=
  {
    HasColimit := fun F =>
      by
      let c := (left_adjoint R).mapCocone (colimit.cocone (F ⋙ R))
      letI : preserves_colimits_of_shape J _ :=
        (adjunction.of_right_adjoint R).leftAdjointPreservesColimits.1
      let t : is_colimit c := is_colimit_of_preserves (left_adjoint R) (colimit.is_colimit _)
      apply has_colimit.mk ⟨_, (is_colimit.precompose_inv_equiv _ _).symm t⟩
      apply
        (iso_whisker_left F (as_iso (adjunction.of_right_adjoint R).counit) : _) ≪≫ F.right_unitor }
#align category_theory.has_colimits_of_shape_of_reflective CategoryTheory.hasColimitsOfShape_of_reflective

/-- If `C` has colimits then any reflective subcategory has colimits. -/
theorem has_colimits_of_reflective (R : D ⥤ C) [Reflective R] [HasColimitsOfSize.{v, u} C] :
    HasColimitsOfSize.{v, u} D :=
  { HasColimitsOfShape := fun J 𝒥 => has_colimits_of_shape_of_reflective R }
#align category_theory.has_colimits_of_reflective CategoryTheory.has_colimits_of_reflective

/-- The reflector always preserves terminal objects. Note this in general doesn't apply to any other
limit.
-/
noncomputable def leftAdjointPreservesTerminalOfReflective (R : D ⥤ C) [Reflective R] :
    PreservesLimitsOfShape (Discrete.{v} PEmpty) (leftAdjoint R)
    where PreservesLimit K := by
    let F := Functor.empty.{v} D
    apply preserves_limit_of_iso_diagram _ (functor.empty_ext (F ⋙ R) _)
    fconstructor; intro c h; haveI : has_limit (F ⋙ R) := ⟨⟨⟨c, h⟩⟩⟩
    haveI : has_limit F := has_limit_of_reflective F R
    apply is_limit_change_empty_cone D (limit.is_limit F)
    apply (as_iso ((adjunction.of_right_adjoint R).counit.app _)).symm.trans
    · apply (left_adjoint R).mapIso
      letI := monadicCreatesLimits.{v, v} R
      let this := (CategoryTheory.preservesLimitOfCreatesLimitAndHasLimit F R).preserves
      apply (this (limit.is_limit F)).conePointUniqueUpToIso h
    infer_instance
#align category_theory.left_adjoint_preserves_terminal_of_reflective CategoryTheory.leftAdjointPreservesTerminalOfReflective

end

end CategoryTheory

