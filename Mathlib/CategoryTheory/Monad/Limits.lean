/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta, Jack McKoen
-/
import Mathlib.CategoryTheory.Monad.Adjunction
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

#align_import category_theory.monad.limits from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!
# Limits and colimits in the category of (co)algebras

This file shows that the forgetful functor `forget T : Algebra T ⥤ C` for a monad `T : C ⥤ C`
creates limits and creates any colimits which `T` preserves.
This is used to show that `Algebra T` has any limits which `C` has, and any colimits which `C` has
and `T` preserves.
This is generalised to the case of a monadic functor `D ⥤ C`.

Dually, this file shows that the forgetful functor `forget T : Coalgebra T ⥤ C` for a
comonad `T : C ⥤ C` creates colimits and creates any limits which `T` preserves.
This is used to show that `Coalgebra T` has any colimits which `C` has, and any limits which `C` has
and `T` preserves.
This is generalised to the case of a comonadic functor `D ⥤ C`.
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
@[simps! π_app]
def newCone : Cone (D ⋙ forget T) where
  pt := T.obj c.pt
  π := (Functor.constComp _ _ (T : C ⥤ C)).inv ≫ whiskerRight c.π (T : C ⥤ C) ≫ γ D
#align category_theory.monad.forget_creates_limits.new_cone CategoryTheory.Monad.ForgetCreatesLimits.newCone

/-- The algebra structure which will be the apex of the new limit cone for `D`. -/
@[simps]
def conePoint : Algebra T where
  A := c.pt
  a := t.lift (newCone D c)
  unit :=
    t.hom_ext fun j => by
      rw [Category.assoc, t.fac, newCone_π_app, ← T.η.naturality_assoc, Functor.id_map,
        (D.obj j).unit]
      dsimp; simp
  -- See library note [dsimp, simp]
  assoc :=
    t.hom_ext fun j => by
      rw [Category.assoc, Category.assoc, t.fac (newCone D c), newCone_π_app, ←
        Functor.map_comp_assoc, t.fac (newCone D c), newCone_π_app, ← T.μ.naturality_assoc,
        (D.obj j).assoc, Functor.map_comp, Category.assoc]
      rfl
#align category_theory.monad.forget_creates_limits.cone_point CategoryTheory.Monad.ForgetCreatesLimits.conePoint

/-- (Impl) Construct the lifted cone in `Algebra T` which will be limiting. -/
@[simps]
def liftedCone : Cone D where
  pt := conePoint D c t
  π :=
    { app := fun j => { f := c.π.app j }
      naturality := fun X Y f => by
        ext1
        dsimp
        erw [c.w f]
        simp }
#align category_theory.monad.forget_creates_limits.lifted_cone CategoryTheory.Monad.ForgetCreatesLimits.liftedCone

/-- (Impl) Prove that the lifted cone is limiting. -/
@[simps]
def liftedConeIsLimit : IsLimit (liftedCone D c t) where
  lift s :=
    { f := t.lift ((forget T).mapCone s)
      h :=
        t.hom_ext fun j => by
          dsimp
          rw [Category.assoc, Category.assoc, t.fac, newCone_π_app, ← Functor.map_comp_assoc,
            t.fac, Functor.mapCone_π_app]
          apply (s.π.app j).h }
  uniq s m J := by
    ext1
    apply t.hom_ext
    intro j
    simpa [t.fac ((forget T).mapCone s) j] using congr_arg Algebra.Hom.f (J j)
#align category_theory.monad.forget_creates_limits.lifted_cone_is_limit CategoryTheory.Monad.ForgetCreatesLimits.liftedConeIsLimit

end ForgetCreatesLimits

-- Theorem 5.6.5 from [Riehl][riehl2017]
/-- The forgetful functor from the Eilenberg-Moore category creates limits. -/
noncomputable instance forgetCreatesLimits : CreatesLimitsOfSize (forget T) where
  CreatesLimitsOfShape := {
    CreatesLimit := fun {D} =>
      createsLimitOfReflectsIso fun c t =>
        { liftedCone := ForgetCreatesLimits.liftedCone D c t
          validLift := Cones.ext (Iso.refl _) fun _ => (id_comp _).symm
          makesLimit := ForgetCreatesLimits.liftedConeIsLimit _ _ _ } }
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
-- colimit for its image D ⋙ forget T under the forgetful functor, say its point is L.
-- We'll construct a colimiting coalgebra for D, whose carrier will also be L.
-- To do this, we must find a map TL ⟶ L. Since T preserves colimits, TL is also a colimit.
-- In particular, it is a colimit for the diagram `(D ⋙ forget T) ⋙ T`
-- so to construct a map TL ⟶ L it suffices to show that L is the point of a cocone for this
-- diagram. In other words, we need a natural transformation from const L to `(D ⋙ forget T) ⋙ T`.
-- But we already know that L is the point of a cocone for the diagram `D ⋙ forget T`, so it
-- suffices to give a natural transformation `((D ⋙ forget T) ⋙ T) ⟶ (D ⋙ forget T)`:
/-- (Impl)
The natural transformation given by the algebra structure maps, used to construct a cocone `c` with
point `colimit (D ⋙ forget T)`.
 -/
@[simps]
def γ : (D ⋙ forget T) ⋙ ↑T ⟶ D ⋙ forget T where app j := (D.obj j).a
#align category_theory.monad.forget_creates_colimits.γ CategoryTheory.Monad.ForgetCreatesColimits.γ

/-- (Impl)
A cocone for the diagram `(D ⋙ forget T) ⋙ T` found by composing the natural transformation `γ`
with the colimiting cocone for `D ⋙ forget T`.
-/
@[simps]
def newCocone : Cocone ((D ⋙ forget T) ⋙ (T : C ⥤ C)) where
  pt := c.pt
  ι := γ ≫ c.ι
#align category_theory.monad.forget_creates_colimits.new_cocone CategoryTheory.Monad.ForgetCreatesColimits.newCocone

variable [PreservesColimit (D ⋙ forget T) (T : C ⥤ C)]

/-- (Impl)
Define the map `λ : TL ⟶ L`, which will serve as the structure of the coalgebra on `L`, and
we will show is the colimiting object. We use the cocone constructed by `c` and the fact that
`T` preserves colimits to produce this morphism.
-/
abbrev lambda : ((T : C ⥤ C).mapCocone c).pt ⟶ c.pt :=
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
  unit := by
    apply t.hom_ext
    intro j
    rw [show c.ι.app j ≫ T.η.app c.pt ≫ _ = T.η.app (D.obj j).A ≫ _ ≫ _ from
        T.η.naturality_assoc _ _,
      commuting, Algebra.unit_assoc (D.obj j)]
    dsimp; simp
  -- See library note [dsimp, simp]
  assoc := by
    refine (isColimitOfPreserves _ (isColimitOfPreserves _ t)).hom_ext fun j => ?_
    rw [Functor.mapCocone_ι_app, Functor.mapCocone_ι_app,
      show (T : C ⥤ C).map ((T : C ⥤ C).map _) ≫ _ ≫ _ = _ from T.μ.naturality_assoc _ _, ←
      Functor.map_comp_assoc, commuting, Functor.map_comp, Category.assoc, commuting]
    apply (D.obj j).assoc_assoc _
#align category_theory.monad.forget_creates_colimits.cocone_point CategoryTheory.Monad.ForgetCreatesColimits.coconePoint

/-- (Impl) Construct the lifted cocone in `Algebra T` which will be colimiting. -/
@[simps]
def liftedCocone : Cocone D where
  pt := coconePoint c t
  ι :=
    { app := fun j =>
        { f := c.ι.app j
          h := commuting _ _ _ }
      naturality := fun A B f => by
        ext1
        dsimp
        rw [comp_id]
        apply c.w }
#align category_theory.monad.forget_creates_colimits.lifted_cocone CategoryTheory.Monad.ForgetCreatesColimits.liftedCocone

/-- (Impl) Prove that the lifted cocone is colimiting. -/
@[simps]
def liftedCoconeIsColimit : IsColimit (liftedCocone c t) where
  desc s :=
    { f := t.desc ((forget T).mapCocone s)
      h :=
        (isColimitOfPreserves (T : C ⥤ C) t).hom_ext fun j => by
          dsimp
          rw [← Functor.map_comp_assoc, ← Category.assoc, t.fac, commuting, Category.assoc, t.fac]
          apply Algebra.Hom.h }
  uniq s m J := by
    ext1
    apply t.hom_ext
    intro j
    simpa using congr_arg Algebra.Hom.f (J j)
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
                  h := commuting _ _ _ }
              naturality := fun A B f => by
                ext1
                dsimp
                erw [comp_id, c.w] } }
      validLift := Cocones.ext (Iso.refl _)
      makesColimit := liftedCoconeIsColimit _ _ }
#align category_theory.monad.forget_creates_colimit CategoryTheory.Monad.forgetCreatesColimit

noncomputable instance forgetCreatesColimitsOfShape [PreservesColimitsOfShape J (T : C ⥤ C)] :
    CreatesColimitsOfShape J (forget T) where CreatesColimit := by infer_instance
#align category_theory.monad.forget_creates_colimits_of_shape CategoryTheory.Monad.forgetCreatesColimitsOfShape

noncomputable instance forgetCreatesColimits [PreservesColimitsOfSize.{v, u} (T : C ⥤ C)] :
    CreatesColimitsOfSize.{v, u} (forget T) where CreatesColimitsOfShape := by infer_instance
#align category_theory.monad.forget_creates_colimits CategoryTheory.Monad.forgetCreatesColimits

/-- For `D : J ⥤ Algebra T`, `D ⋙ forget T` has a colimit, then `D` has a colimit provided colimits
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
    HasLimit ((F ⋙ Monad.comparison (monadicAdjunction R)) ⋙ Monad.forget _) :=
  @hasLimitOfIso _ _ _ _ (F ⋙ R) _ _
    (isoWhiskerLeft F (Monad.comparisonForget (monadicAdjunction R)).symm)
#align category_theory.comp_comparison_forget_has_limit CategoryTheory.comp_comparison_forget_hasLimit

instance comp_comparison_hasLimit (F : J ⥤ D) (R : D ⥤ C) [MonadicRightAdjoint R]
    [HasLimit (F ⋙ R)] : HasLimit (F ⋙ Monad.comparison (monadicAdjunction R)) :=
  Monad.hasLimit_of_comp_forget_hasLimit (F ⋙ Monad.comparison (monadicAdjunction R))
#align category_theory.comp_comparison_has_limit CategoryTheory.comp_comparison_hasLimit

/-- Any monadic functor creates limits. -/
noncomputable def monadicCreatesLimits (R : D ⥤ C) [MonadicRightAdjoint R] :
    CreatesLimitsOfSize.{v, u} R :=
  createsLimitsOfNatIso (Monad.comparisonForget (monadicAdjunction R))
#align category_theory.monadic_creates_limits CategoryTheory.monadicCreatesLimits

/-- The forgetful functor from the Eilenberg-Moore category for a monad creates any colimit
which the monad itself preserves.
-/
noncomputable def monadicCreatesColimitOfPreservesColimit (R : D ⥤ C) (K : J ⥤ D)
    [MonadicRightAdjoint R] [PreservesColimit (K ⋙ R) (monadicLeftAdjoint R ⋙ R)]
    [PreservesColimit ((K ⋙ R) ⋙ monadicLeftAdjoint R ⋙ R) (monadicLeftAdjoint R ⋙ R)] :
      CreatesColimit K R := by
  -- Porting note: It would be nice to have a variant of apply which introduces goals for missing
  -- instances.
  letI A := Monad.comparison (monadicAdjunction R)
  letI B := Monad.forget (Adjunction.toMonad (monadicAdjunction R))
  let i : (K ⋙ Monad.comparison (monadicAdjunction R)) ⋙ Monad.forget _ ≅ K ⋙ R :=
    Functor.associator _ _ _ ≪≫
      isoWhiskerLeft K (Monad.comparisonForget (monadicAdjunction R))
  letI : PreservesColimit ((K ⋙ A) ⋙ Monad.forget
    (Adjunction.toMonad (monadicAdjunction R)))
      (Adjunction.toMonad (monadicAdjunction R)).toFunctor := by
    dsimp
    exact preservesColimitOfIsoDiagram _ i.symm
  letI : PreservesColimit
    (((K ⋙ A) ⋙ Monad.forget (Adjunction.toMonad (monadicAdjunction R))) ⋙
      (Adjunction.toMonad (monadicAdjunction R)).toFunctor)
      (Adjunction.toMonad (monadicAdjunction R)).toFunctor := by
    dsimp
    exact preservesColimitOfIsoDiagram _ (isoWhiskerRight i (monadicLeftAdjoint R ⋙ R)).symm
  letI : CreatesColimit (K ⋙ A) B := CategoryTheory.Monad.forgetCreatesColimit _
  letI : CreatesColimit K (A ⋙ B) := CategoryTheory.compCreatesColimit _ _
  let e := Monad.comparisonForget (monadicAdjunction R)
  apply createsColimitOfNatIso e
#align category_theory.monadic_creates_colimit_of_preserves_colimit CategoryTheory.monadicCreatesColimitOfPreservesColimit

/-- A monadic functor creates any colimits of shapes it preserves. -/
noncomputable def monadicCreatesColimitsOfShapeOfPreservesColimitsOfShape (R : D ⥤ C)
    [MonadicRightAdjoint R] [PreservesColimitsOfShape J R] : CreatesColimitsOfShape J R :=
  letI : PreservesColimitsOfShape J (monadicLeftAdjoint R) := by
    apply (Adjunction.leftAdjointPreservesColimits (monadicAdjunction R)).1
  letI : PreservesColimitsOfShape J (monadicLeftAdjoint R ⋙ R) := by
    apply CategoryTheory.Limits.compPreservesColimitsOfShape _ _
  ⟨monadicCreatesColimitOfPreservesColimit _ _⟩
#align category_theory.monadic_creates_colimits_of_shape_of_preserves_colimits_of_shape CategoryTheory.monadicCreatesColimitsOfShapeOfPreservesColimitsOfShape

/-- A monadic functor creates colimits if it preserves colimits. -/
noncomputable def monadicCreatesColimitsOfPreservesColimits (R : D ⥤ C) [MonadicRightAdjoint R]
    [PreservesColimitsOfSize.{v, u} R] : CreatesColimitsOfSize.{v, u} R where
  CreatesColimitsOfShape :=
    monadicCreatesColimitsOfShapeOfPreservesColimitsOfShape _
#align category_theory.monadic_creates_colimits_of_preserves_colimits CategoryTheory.monadicCreatesColimitsOfPreservesColimits

section

theorem hasLimit_of_reflective (F : J ⥤ D) (R : D ⥤ C) [HasLimit (F ⋙ R)] [Reflective R] :
    HasLimit F :=
  haveI := monadicCreatesLimits.{v, u} R
  hasLimit_of_created F R
#align category_theory.has_limit_of_reflective CategoryTheory.hasLimit_of_reflective

/-- If `C` has limits of shape `J` then any reflective subcategory has limits of shape `J`. -/
theorem hasLimitsOfShape_of_reflective [HasLimitsOfShape J C] (R : D ⥤ C) [Reflective R] :
    HasLimitsOfShape J D :=
  ⟨fun F => hasLimit_of_reflective F R⟩
#align category_theory.has_limits_of_shape_of_reflective CategoryTheory.hasLimitsOfShape_of_reflective

/-- If `C` has limits then any reflective subcategory has limits. -/
theorem hasLimits_of_reflective (R : D ⥤ C) [HasLimitsOfSize.{v, u} C] [Reflective R] :
    HasLimitsOfSize.{v, u} D :=
  ⟨fun _ => hasLimitsOfShape_of_reflective R⟩
#align category_theory.has_limits_of_reflective CategoryTheory.hasLimits_of_reflective

/-- If `C` has colimits of shape `J` then any reflective subcategory has colimits of shape `J`. -/
theorem hasColimitsOfShape_of_reflective (R : D ⥤ C) [Reflective R] [HasColimitsOfShape J C] :
    HasColimitsOfShape J D where
  has_colimit := fun F => by
      let c := (monadicLeftAdjoint R).mapCocone (colimit.cocone (F ⋙ R))
      letI : PreservesColimitsOfShape J _ :=
        (monadicAdjunction R).leftAdjointPreservesColimits.1
      let t : IsColimit c := isColimitOfPreserves (monadicLeftAdjoint R) (colimit.isColimit _)
      apply HasColimit.mk ⟨_, (IsColimit.precomposeInvEquiv _ _).symm t⟩
      apply
        (isoWhiskerLeft F (asIso (monadicAdjunction R).counit) : _) ≪≫ F.rightUnitor
#align category_theory.has_colimits_of_shape_of_reflective CategoryTheory.hasColimitsOfShape_of_reflective

/-- If `C` has colimits then any reflective subcategory has colimits. -/
theorem hasColimits_of_reflective (R : D ⥤ C) [Reflective R] [HasColimitsOfSize.{v, u} C] :
    HasColimitsOfSize.{v, u} D :=
  ⟨fun _ => hasColimitsOfShape_of_reflective R⟩
#align category_theory.has_colimits_of_reflective CategoryTheory.hasColimits_of_reflective

/-- The reflector always preserves terminal objects. Note this in general doesn't apply to any other
limit.
-/
noncomputable def leftAdjointPreservesTerminalOfReflective (R : D ⥤ C) [Reflective R] :
    PreservesLimitsOfShape (Discrete.{v} PEmpty) (monadicLeftAdjoint R) where
  preservesLimit {K} := by
    let F := Functor.empty.{v} D
    letI : PreservesLimit (F ⋙ R) (monadicLeftAdjoint R) := by
      constructor
      intro c h
      haveI : HasLimit (F ⋙ R) := ⟨⟨⟨c, h⟩⟩⟩
      haveI : HasLimit F := hasLimit_of_reflective F R
      apply isLimitChangeEmptyCone D (limit.isLimit F)
      apply (asIso ((monadicAdjunction R).counit.app _)).symm.trans
      apply (monadicLeftAdjoint R).mapIso
      letI := monadicCreatesLimits.{v, v} R
      let A := CategoryTheory.preservesLimitOfCreatesLimitAndHasLimit F R
      apply (A.preserves (limit.isLimit F)).conePointUniqueUpToIso h
    apply preservesLimitOfIsoDiagram _ (Functor.emptyExt (F ⋙ R) _)
#align category_theory.left_adjoint_preserves_terminal_of_reflective CategoryTheory.leftAdjointPreservesTerminalOfReflective

end

-- We dualise all of the above for comonads.
namespace Comonad

variable {T : Comonad C}

namespace ForgetCreatesColimits'

variable (D : J ⥤ Coalgebra T) (c : Cocone (D ⋙ T.forget)) (t : IsColimit c)

/-- (Impl) The natural transformation used to define the new cocone -/
@[simps]
def γ : D ⋙ T.forget ⟶ D ⋙ T.forget ⋙ ↑T  where app j := (D.obj j).a

/-- (Impl) This new cocone is used to construct the coalgebra structure -/
@[simps! ι_app]
def newCocone : Cocone (D ⋙ forget T) where
  pt := T.obj c.pt
  ι := γ D ≫ whiskerRight c.ι (T : C ⥤ C) ≫ (Functor.constComp J _ (T : C ⥤ C)).hom

/-- The coalgebra structure which will be the point of the new colimit cone for `D`. -/
@[simps]
def coconePoint : Coalgebra T where
  A := c.pt
  a := t.desc (newCocone D c)
  counit := t.hom_ext fun j ↦ by
    simp only [Functor.comp_obj, forget_obj, Functor.id_obj, Functor.const_obj_obj,
      IsColimit.fac_assoc, newCocone_ι_app, assoc, NatTrans.naturality, Functor.id_map, comp_id]
    rw [← Category.assoc, (D.obj j).counit, Category.id_comp]
  coassoc := t.hom_ext fun j ↦ by
    simp only [Functor.comp_obj, forget_obj, Functor.const_obj_obj, IsColimit.fac_assoc,
      newCocone_ι_app, assoc, NatTrans.naturality, Functor.comp_map]
    rw [← Category.assoc, (D.obj j).coassoc, ← Functor.map_comp, t.fac (newCocone D c) j,
      newCocone_ι_app, Functor.map_comp, assoc]

/-- (Impl) Construct the lifted cocone in `Coalgebra T` which will be colimiting. -/
@[simps]
def liftedCocone : Cocone D where
  pt := coconePoint D c t
  ι :=
    { app := fun j => { f := c.ι.app j }
      naturality := fun X Y f => by
        ext1
        dsimp
        erw [c.w f]
        simp }

/-- (Impl) Prove that the lifted cocone is colimiting. -/
@[simps]
def liftedCoconeIsColimit : IsColimit (liftedCocone D c t) where
  desc s :=
    { f := t.desc ((forget T).mapCocone s)
      h :=
        t.hom_ext fun j => by
          dsimp
          rw [← Category.assoc, ← Category.assoc, t.fac, newCocone_ι_app, t.fac,
            Functor.mapCocone_ι_app, Category.assoc, ← Functor.map_comp, t.fac]
          apply (s.ι.app j).h }
  uniq s m J := by
    ext1
    apply t.hom_ext
    intro j
    simpa [t.fac ((forget T).mapCocone s) j] using congr_arg Coalgebra.Hom.f (J j)

end ForgetCreatesColimits'

-- Dual to theorem 5.6.5 from [Riehl][riehl2017]
/-- The forgetful functor from the Eilenberg-Moore category creates colimits. -/
noncomputable instance forgetCreatesColimit : CreatesColimitsOfSize (forget T) where
  CreatesColimitsOfShape := {
    CreatesColimit := fun {D} =>
      createsColimitOfReflectsIso fun c t =>
        { liftedCocone := ForgetCreatesColimits'.liftedCocone D c t
          validLift := Cocones.ext (Iso.refl _) fun _ => (comp_id _)
          makesColimit := ForgetCreatesColimits'.liftedCoconeIsColimit _ _ _ } }

/-- If `D ⋙ forget T` has a colimit, then `D` has a colimit. -/
theorem hasColimit_of_comp_forget_hasColimit (D : J ⥤ Coalgebra T) [HasColimit (D ⋙ forget T)] :
    HasColimit D :=
  hasColimit_of_created D (forget T)

namespace ForgetCreatesLimits'

-- Let's hide the implementation details in a namespace
variable {D : J ⥤ Coalgebra T} (c : Cone (D ⋙ forget T)) (t : IsLimit c)

/-- (Impl)
The natural transformation given by the coalgebra structure maps, used to construct a cone `c` with
point `limit (D ⋙ forget T)`.
 -/
@[simps]
def γ : D ⋙ forget T ⟶ (D ⋙ forget T) ⋙ ↑T where app j := (D.obj j).a

/-- (Impl)
A cone for the diagram `(D ⋙ forget T) ⋙ T` found by composing the natural transformation `γ`
with the limiting cone for `D ⋙ forget T`.
-/
@[simps]
def newCone : Cone ((D ⋙ forget T) ⋙ (T : C ⥤ C)) where
  pt := c.pt
  π := c.π ≫ γ

variable [PreservesLimit (D ⋙ forget T) (T : C ⥤ C)]
  [PreservesLimit ((D ⋙ forget T) ⋙ T.toFunctor) T.toFunctor]

/-- (Impl)
Define the map `λ : L ⟶ TL`, which will serve as the structure of the algebra on `L`, and
we will show is the limiting object. We use the cone constructed by `c` and the fact that
`T` preserves limits to produce this morphism.
-/
abbrev lambda : c.pt ⟶ ((T : C ⥤ C).mapCone c).pt :=
  (isLimitOfPreserves _ t).lift (newCone c)

/-- (Impl) The key property defining the map `λ : L ⟶ TL`. -/
theorem commuting (j : J) : lambda c t ≫ (T : C ⥤ C).map (c.π.app j) = c.π.app j ≫ (D.obj j).a :=
  (isLimitOfPreserves _ t).fac (newCone c) j

variable [PreservesColimit ((D ⋙ forget T) ⋙ ↑T) (T : C ⥤ C)]

/-- (Impl)
Construct the limiting coalgebra from the map `λ : L ⟶ TL` given by `lambda`. We are required to
show it satisfies the two coalgebra laws, which follow from the coalgebra laws for the image of `D`
and our `commuting` lemma.
-/
@[simps]
def conePoint : Coalgebra T where
  A := c.pt
  a := lambda c t
  counit := t.hom_ext fun j ↦ by
    rw [assoc, ← show _ = _ ≫ c.π.app j from T.ε.naturality _, ← assoc, commuting, assoc]
    simp [Coalgebra.counit (D.obj j)]
  coassoc := by
    refine (isLimitOfPreserves _ (isLimitOfPreserves _ t)).hom_ext fun j => ?_
    rw [Functor.mapCone_π_app, Functor.mapCone_π_app, assoc,
      ← show _ = _ ≫ T.map (T.map _) from T.δ.naturality _, assoc, ← Functor.map_comp, commuting,
      Functor.map_comp, ← assoc, commuting]
    simp only [Functor.comp_obj, forget_obj, Functor.const_obj_obj, assoc]
    rw [(D.obj j).coassoc,  ← assoc, ← assoc, commuting]

/-- (Impl) Construct the lifted cone in `Coalgebra T` which will be limiting. -/
@[simps]
def liftedCone : Cone D where
  pt := conePoint c t
  π :=
    { app := fun j =>
        { f := c.π.app j
          h := commuting _ _ _ }
      naturality := fun A B f => by
        ext1
        dsimp
        rw [id_comp, ← c.w]
        rfl }

/-- (Impl) Prove that the lifted cone is limiting. -/
@[simps]
def liftedConeIsLimit : IsLimit (liftedCone c t) where
  lift s :=
    { f := t.lift ((forget T).mapCone s)
      h :=
        (isLimitOfPreserves (T : C ⥤ C) t).hom_ext fun j => by
          dsimp
          rw [Category.assoc, ← t.fac, Category.assoc, t.fac, commuting, ← assoc, ← assoc, t.fac,
            assoc, ← Functor.map_comp, t.fac]
          exact (s.π.app j).h }
  uniq s m J := by
    ext1
    apply t.hom_ext
    intro j
    simpa using congr_arg Coalgebra.Hom.f (J j)

end ForgetCreatesLimits'

open ForgetCreatesLimits'

-- TODO: the converse of this is true as well
/-- The forgetful functor from the Eilenberg-Moore category for a comonad creates any limit
which the comonad itself preserves.
-/
noncomputable instance forgetCreatesLimit (D : J ⥤ Coalgebra T)
    [PreservesLimit (D ⋙ forget T) (T : C ⥤ C)]
    [PreservesLimit ((D ⋙ forget T) ⋙ ↑T) (T : C ⥤ C)] : CreatesLimit D (forget T) :=
  createsLimitOfReflectsIso fun c t =>
    { liftedCone :=
        { pt := conePoint c t
          π :=
            { app := fun j =>
                { f := c.π.app j
                  h := commuting _ _ _ }
              naturality := fun A B f => by
                ext1
                dsimp
                erw [id_comp, c.w] } }
      validLift := Cones.ext (Iso.refl _)
      makesLimit := liftedConeIsLimit _ _ }

noncomputable instance forgetCreatesLimitsOfShape [PreservesLimitsOfShape J (T : C ⥤ C)] :
    CreatesLimitsOfShape J (forget T) where CreatesLimit := by infer_instance

noncomputable instance forgetCreatesLimits [PreservesLimitsOfSize.{v, u} (T : C ⥤ C)] :
    CreatesLimitsOfSize.{v, u} (forget T) where CreatesLimitsOfShape := by infer_instance

/-- For `D : J ⥤ Coalgebra T`, `D ⋙ forget T` has a limit, then `D` has a limit provided limits
of shape `J` are preserved by `T`.
-/
theorem forget_creates_limits_of_comonad_preserves [PreservesLimitsOfShape J (T : C ⥤ C)]
    (D : J ⥤ Coalgebra T) [HasLimit (D ⋙ forget T)] : HasLimit D :=
  hasLimit_of_created D (forget T)

end Comonad

instance comp_comparison_forget_hasColimit (F : J ⥤ D) (R : D ⥤ C) [ComonadicLeftAdjoint R]
    [HasColimit (F ⋙ R)] :
    HasColimit ((F ⋙ Comonad.comparison (comonadicAdjunction R)) ⋙ Comonad.forget _) :=
  @hasColimitOfIso _ _ _ _ (F ⋙ R) _ _
    (isoWhiskerLeft F (Comonad.comparisonForget (comonadicAdjunction R)).symm)

instance comp_comparison_hasColimit (F : J ⥤ D) (R : D ⥤ C) [ComonadicLeftAdjoint R]
    [HasColimit (F ⋙ R)] : HasColimit (F ⋙ Comonad.comparison (comonadicAdjunction R)) :=
  Comonad.hasColimit_of_comp_forget_hasColimit (F ⋙ Comonad.comparison (comonadicAdjunction R))

/-- Any comonadic functor creates colimits. -/
noncomputable def comonadicCreatesColimits (R : D ⥤ C) [ComonadicLeftAdjoint R] :
    CreatesColimitsOfSize.{v, u} R :=
  createsColimitsOfNatIso (Comonad.comparisonForget (comonadicAdjunction R))

/-- The forgetful functor from the Eilenberg-Moore category for a comonad creates any limit
which the comonad itself preserves.
-/
noncomputable def comonadicCreatesLimitOfPreservesLimit (R : D ⥤ C) (K : J ⥤ D)
    [ComonadicLeftAdjoint R] [PreservesLimit (K ⋙ R) (comonadicRightAdjoint R ⋙ R)]
    [PreservesLimit ((K ⋙ R) ⋙ comonadicRightAdjoint R ⋙ R) (comonadicRightAdjoint R ⋙ R)] :
      CreatesLimit K R := by
  letI A := Comonad.comparison (comonadicAdjunction R)
  letI B := Comonad.forget (Adjunction.toComonad (comonadicAdjunction R))
  let i : (K ⋙ Comonad.comparison (comonadicAdjunction R)) ⋙ Comonad.forget _ ≅ K ⋙ R :=
    Functor.associator _ _ _ ≪≫
      isoWhiskerLeft K (Comonad.comparisonForget (comonadicAdjunction R))
  letI : PreservesLimit ((K ⋙ A) ⋙ Comonad.forget
    (Adjunction.toComonad (comonadicAdjunction R)))
      (Adjunction.toComonad (comonadicAdjunction R)).toFunctor := by
    dsimp
    exact preservesLimitOfIsoDiagram _ i.symm
  letI : PreservesLimit
    (((K ⋙ A) ⋙ Comonad.forget (Adjunction.toComonad (comonadicAdjunction R))) ⋙
      (Adjunction.toComonad (comonadicAdjunction R)).toFunctor)
      (Adjunction.toComonad (comonadicAdjunction R)).toFunctor := by
    dsimp
    exact preservesLimitOfIsoDiagram _ (isoWhiskerRight i (comonadicRightAdjoint R ⋙ R)).symm
  letI : CreatesLimit (K ⋙ A) B := CategoryTheory.Comonad.forgetCreatesLimit _
  letI : CreatesLimit K (A ⋙ B) := CategoryTheory.compCreatesLimit _ _
  let e := Comonad.comparisonForget (comonadicAdjunction R)
  apply createsLimitOfNatIso e

/-- A comonadic functor creates any limits of shapes it preserves. -/
noncomputable def comonadicCreatesLimitsOfShapeOfPreservesLimitsOfShape (R : D ⥤ C)
    [ComonadicLeftAdjoint R] [PreservesLimitsOfShape J R] : CreatesLimitsOfShape J R :=
  letI : PreservesLimitsOfShape J (comonadicRightAdjoint R) := by
    apply (Adjunction.rightAdjointPreservesLimits (comonadicAdjunction R)).1
  letI : PreservesLimitsOfShape J (comonadicRightAdjoint R ⋙ R) := by
    apply CategoryTheory.Limits.compPreservesLimitsOfShape _ _
  ⟨comonadicCreatesLimitOfPreservesLimit _ _⟩

/-- A comonadic functor creates limits if it preserves limits. -/
noncomputable def comonadicCreatesLimitsOfPreservesLimits (R : D ⥤ C) [ComonadicLeftAdjoint R]
    [PreservesLimitsOfSize.{v, u} R] : CreatesLimitsOfSize.{v, u} R where
  CreatesLimitsOfShape :=
    comonadicCreatesLimitsOfShapeOfPreservesLimitsOfShape _

section

theorem hasColimit_of_coreflective (F : J ⥤ D) (R : D ⥤ C) [HasColimit (F ⋙ R)] [Coreflective R] :
    HasColimit F :=
  haveI := comonadicCreatesColimits.{v, u} R
  hasColimit_of_created F R

/-- If `C` has colimits of shape `J` then any coreflective subcategory has colimits of shape `J`. -/
theorem hasColimitsOfShape_of_coreflective [HasColimitsOfShape J C] (R : D ⥤ C) [Coreflective R] :
    HasColimitsOfShape J D :=
  ⟨fun F => hasColimit_of_coreflective F R⟩

/-- If `C` has colimits then any coreflective subcategory has colimits. -/
theorem hasColimits_of_coreflective (R : D ⥤ C) [HasColimitsOfSize.{v, u} C] [Coreflective R] :
    HasColimitsOfSize.{v, u} D :=
  ⟨fun _ => hasColimitsOfShape_of_coreflective R⟩

/-- If `C` has limits of shape `J` then any coreflective subcategory has limits of shape `J`. -/
theorem hasLimitsOfShape_of_coreflective (R : D ⥤ C) [Coreflective R] [HasLimitsOfShape J C] :
    HasLimitsOfShape J D where
  has_limit := fun F => by
      let c := (comonadicRightAdjoint R).mapCone (limit.cone (F ⋙ R))
      letI : PreservesLimitsOfShape J _ :=
        (comonadicAdjunction R).rightAdjointPreservesLimits.1
      let t : IsLimit c := isLimitOfPreserves (comonadicRightAdjoint R) (limit.isLimit _)
      apply HasLimit.mk ⟨_, (IsLimit.postcomposeHomEquiv _ _).symm t⟩
      apply
        (F.rightUnitor ≪≫ (isoWhiskerLeft F ((asIso (comonadicAdjunction R).unit) : _) )).symm

/-- If `C` has limits then any coreflective subcategory has limits. -/
theorem hasLimits_of_coreflective (R : D ⥤ C) [Coreflective R] [HasLimitsOfSize.{v, u} C] :
    HasLimitsOfSize.{v, u} D :=
  ⟨fun _ => hasLimitsOfShape_of_coreflective R⟩

/-- The coreflector always preserves initial objects. Note this in general doesn't apply to any
other colimit.
-/
noncomputable def rightAdjointPreservesInitialOfCoreflective (R : D ⥤ C) [Coreflective R] :
    PreservesColimitsOfShape (Discrete.{v} PEmpty) (comonadicRightAdjoint R) where
  preservesColimit {K} := by
    let F := Functor.empty.{v} D
    letI : PreservesColimit (F ⋙ R) (comonadicRightAdjoint R) := by
      constructor
      intro c h
      haveI : HasColimit (F ⋙ R) := ⟨⟨⟨c, h⟩⟩⟩
      haveI : HasColimit F := hasColimit_of_coreflective F R
      apply isColimitChangeEmptyCocone D (colimit.isColimit F)
      apply (asIso ((comonadicAdjunction R).unit.app _)).trans
      apply (comonadicRightAdjoint R).mapIso
      letI := comonadicCreatesColimits.{v, v} R
      let A := CategoryTheory.preservesColimitOfCreatesColimitAndHasColimit F R
      apply (A.preserves (colimit.isColimit F)).coconePointUniqueUpToIso h
    apply preservesColimitOfIsoDiagram _ (Functor.emptyExt (F ⋙ R) _)

end

end CategoryTheory
