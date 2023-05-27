/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta

! This file was ported from Lean 3 source module category_theory.adjunction.lifting
! leanprover-community/mathlib commit 9bc7dfa6e50f902fb0684c9670a680459ebaed68
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Limits.Shapes.Equalizers
import Mathbin.CategoryTheory.Limits.Shapes.Reflexive
import Mathbin.CategoryTheory.Monad.Adjunction
import Mathbin.CategoryTheory.Monad.Coequalizer

/-!
# Adjoint lifting

This file gives two constructions for building left adjoints: the adjoint triangle theorem and the
adjoint lifting theorem.
The adjoint triangle theorem says that given a functor `U : B ⥤ C` with a left adjoint `F` such
that `ε_X : FUX ⟶ X` is a regular epi. Then for any category `A` with coequalizers of reflexive
pairs, a functor `R : A ⥤ B` has a left adjoint if (and only if) the composite `R ⋙ U` does.
Note that the condition on `U` regarding `ε_X` is automatically satisfied in the case when `U` is
a monadic functor, giving the corollary: `monadic_adjoint_triangle_lift`, i.e. if `U` is monadic,
`A` has reflexive coequalizers then `R : A ⥤ B` has a left adjoint provided `R ⋙ U` does.

The adjoint lifting theorem says that given a commutative square of functors (up to isomorphism):

      Q
    A → B
  U ↓   ↓ V
    C → D
      R

where `U` and `V` are monadic and `A` has reflexive coequalizers, then if `R` has a left adjoint
then `Q` has a left adjoint.

## Implementation

It is more convenient to prove this theorem by assuming we are given the explicit adjunction rather
than just a functor known to be a right adjoint. In docstrings, we write `(η, ε)` for the unit
and counit of the adjunction `adj₁ : F ⊣ U` and `(ι, δ)` for the unit and counit of the adjunction
`adj₂ : F' ⊣ R ⋙ U`.

## TODO

Dualise to lift right adjoints through comonads (by reversing 1-cells) and dualise to lift right
adjoints through monads (by reversing 2-cells), and the combination.

## References
* https://ncatlab.org/nlab/show/adjoint+triangle+theorem
* https://ncatlab.org/nlab/show/adjoint+lifting+theorem
* Adjoint Lifting Theorems for Categories of Algebras (PT Johnstone, 1975)
* A unified approach to the lifting of adjoints (AJ Power, 1988)
-/


namespace CategoryTheory

open Category Limits

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {A : Type u₁} {B : Type u₂} {C : Type u₃}

variable [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]

-- Hide implementation details in this namespace
namespace LiftAdjoint

variable {U : B ⥤ C} {F : C ⥤ B} (R : A ⥤ B) (F' : C ⥤ A)

variable (adj₁ : F ⊣ U) (adj₂ : F' ⊣ R ⋙ U)

/-- To show that `ε_X` is a coequalizer for `(FUε_X, ε_FUX)`, it suffices to assume it's always a
coequalizer of something (i.e. a regular epi).
-/
def counitCoequalises [∀ X : B, RegularEpi (adj₁.counit.app X)] (X : B) :
    IsColimit (Cofork.ofπ (adj₁.counit.app X) (adj₁.counit_naturality _)) :=
  Cofork.IsColimit.mk' _ fun s =>
    by
    refine' ⟨(regular_epi.desc' (adj₁.counit.app X) s.π _).1, _, _⟩
    · rw [← cancel_epi (adj₁.counit.app (regular_epi.W (adj₁.counit.app X)))]
      rw [← adj₁.counit_naturality_assoc]
      dsimp only [functor.comp_obj]
      rw [← s.condition, ← F.map_comp_assoc, ← U.map_comp, regular_epi.w, U.map_comp,
        F.map_comp_assoc, s.condition, ← adj₁.counit_naturality_assoc]
    · apply (regular_epi.desc' (adj₁.counit.app X) s.π _).2
    · intro m hm
      rw [← cancel_epi (adj₁.counit.app X)]
      apply hm.trans (regular_epi.desc' (adj₁.counit.app X) s.π _).2.symm
#align category_theory.lift_adjoint.counit_coequalises CategoryTheory.LiftAdjoint.counitCoequalises

include adj₁ adj₂

/-- (Implementation)
To construct the left adjoint, we use the coequalizer of `F' U ε_Y` with the composite

`F' U F U X ⟶ F' U F U R F U' X ⟶ F' U R F' U X ⟶ F' U X`

where the first morphism is `F' U F ι_UX`, the second is `F' U ε_RF'UX`, and the third is `δ_F'UX`.
We will show that this coequalizer exists and that it forms the object map for a left adjoint to
`R`.
-/
def otherMap (X) : F'.obj (U.obj (F.obj (U.obj X))) ⟶ F'.obj (U.obj X) :=
  F'.map (U.map (F.map (adj₂.Unit.app _) ≫ adj₁.counit.app _)) ≫ adj₂.counit.app _
#align category_theory.lift_adjoint.other_map CategoryTheory.LiftAdjoint.otherMap

/--
`(F'Uε_X, other_map X)` is a reflexive pair: in particular if `A` has reflexive coequalizers then
it has a coequalizer.
-/
instance (X : B) :
    IsReflexivePair (F'.map (U.map (adj₁.counit.app X))) (otherMap _ _ adj₁ adj₂ X) :=
  IsReflexivePair.mk' (F'.map (adj₁.Unit.app (U.obj X)))
    (by
      rw [← F'.map_comp, adj₁.right_triangle_components]
      apply F'.map_id)
    (by
      dsimp [other_map]
      rw [← F'.map_comp_assoc, U.map_comp, adj₁.unit_naturality_assoc,
        adj₁.right_triangle_components, comp_id, adj₂.left_triangle_components])

variable [HasReflexiveCoequalizers A]

/-- Construct the object part of the desired left adjoint as the coequalizer of `F'Uε_Y` with
`other_map`.
-/
noncomputable def constructLeftAdjointObj (Y : B) : A :=
  coequalizer (F'.map (U.map (adj₁.counit.app Y))) (otherMap _ _ adj₁ adj₂ Y)
#align category_theory.lift_adjoint.construct_left_adjoint_obj CategoryTheory.LiftAdjoint.constructLeftAdjointObj

/-- The homset equivalence which helps show that `R` is a right adjoint. -/
@[simps (config := { rhsMd := semireducible })]
noncomputable def constructLeftAdjointEquiv [∀ X : B, RegularEpi (adj₁.counit.app X)] (Y : A)
    (X : B) : (constructLeftAdjointObj _ _ adj₁ adj₂ X ⟶ Y) ≃ (X ⟶ R.obj Y) :=
  calc
    (constructLeftAdjointObj _ _ adj₁ adj₂ X ⟶ Y) ≃
        { f : F'.obj (U.obj X) ⟶ Y //
          F'.map (U.map (adj₁.counit.app X)) ≫ f = otherMap _ _ adj₁ adj₂ _ ≫ f } :=
      Cofork.IsColimit.homIso (colimit.isColimit _) _
    _ ≃
        { g : U.obj X ⟶ U.obj (R.obj Y) //
          U.map (F.map g ≫ adj₁.counit.app _) = U.map (adj₁.counit.app _) ≫ g } :=
      by
      apply (adj₂.hom_equiv _ _).subtypeEquiv _
      intro f
      rw [← (adj₂.hom_equiv _ _).Injective.eq_iff, eq_comm, adj₂.hom_equiv_naturality_left,
        other_map, assoc, adj₂.hom_equiv_naturality_left, ← adj₂.counit_naturality,
        adj₂.hom_equiv_naturality_left, adj₂.hom_equiv_unit, adj₂.right_triangle_components,
        comp_id, functor.comp_map, ← U.map_comp, assoc, ← adj₁.counit_naturality,
        adj₂.hom_equiv_unit, adj₂.hom_equiv_unit, F.map_comp, assoc]
      rfl
    _ ≃ { z : F.obj (U.obj X) ⟶ R.obj Y // _ } :=
      by
      apply (adj₁.hom_equiv _ _).symm.subtypeEquiv
      intro g
      rw [← (adj₁.hom_equiv _ _).symm.Injective.eq_iff, adj₁.hom_equiv_counit,
        adj₁.hom_equiv_counit, adj₁.hom_equiv_counit, F.map_comp, assoc, U.map_comp, F.map_comp,
        assoc, adj₁.counit_naturality, adj₁.counit_naturality_assoc]
      apply eq_comm
    _ ≃ (X ⟶ R.obj Y) := (Cofork.IsColimit.homIso (counitCoequalises adj₁ X) _).symm
    
#align category_theory.lift_adjoint.construct_left_adjoint_equiv CategoryTheory.LiftAdjoint.constructLeftAdjointEquiv

/-- Construct the left adjoint to `R`, with object map `construct_left_adjoint_obj`. -/
noncomputable def constructLeftAdjoint [∀ X : B, RegularEpi (adj₁.counit.app X)] : B ⥤ A :=
  by
  refine'
    adjunction.left_adjoint_of_equiv (fun X Y => construct_left_adjoint_equiv R _ adj₁ adj₂ Y X) _
  intro X Y Y' g h
  rw [construct_left_adjoint_equiv_apply, construct_left_adjoint_equiv_apply, Function.comp_apply,
    Function.comp_apply, Equiv.trans_apply, Equiv.trans_apply, Equiv.trans_apply, Equiv.trans_apply,
    Equiv.symm_apply_eq, Subtype.ext_iff, cofork.is_colimit.hom_iso_natural, Equiv.apply_symm_apply,
    Equiv.subtypeEquiv_apply, Equiv.subtypeEquiv_apply, Equiv.subtypeEquiv_apply,
    Equiv.subtypeEquiv_apply, Subtype.coe_mk, Subtype.coe_mk, Subtype.coe_mk, Subtype.coe_mk, ←
    adj₁.hom_equiv_naturality_right_symm, cofork.is_colimit.hom_iso_natural,
    adj₂.hom_equiv_naturality_right, functor.comp_map]
#align category_theory.lift_adjoint.construct_left_adjoint CategoryTheory.LiftAdjoint.constructLeftAdjoint

end LiftAdjoint

/-- The adjoint triangle theorem: Suppose `U : B ⥤ C` has a left adjoint `F` such that each counit
`ε_X : FUX ⟶ X` is a regular epimorphism. Then if a category `A` has coequalizers of reflexive
pairs, then a functor `R : A ⥤ B` has a left adjoint if the composite `R ⋙ U` does.

Note the converse is true (with weaker assumptions), by `adjunction.comp`.
See https://ncatlab.org/nlab/show/adjoint+triangle+theorem
-/
noncomputable def adjointTriangleLift {U : B ⥤ C} {F : C ⥤ B} (R : A ⥤ B) (adj₁ : F ⊣ U)
    [∀ X : B, RegularEpi (adj₁.counit.app X)] [HasReflexiveCoequalizers A]
    [IsRightAdjoint (R ⋙ U)] : IsRightAdjoint R
    where
  left := LiftAdjoint.constructLeftAdjoint R _ adj₁ (Adjunction.ofRightAdjoint _)
  adj := Adjunction.adjunctionOfEquivLeft _ _
#align category_theory.adjoint_triangle_lift CategoryTheory.adjointTriangleLift

/-- If `R ⋙ U` has a left adjoint, the domain of `R` has reflexive coequalizers and `U` is a monadic
functor, then `R` has a left adjoint.
This is a special case of `adjoint_triangle_lift` which is often more useful in practice.
-/
noncomputable def monadicAdjointTriangleLift (U : B ⥤ C) [MonadicRightAdjoint U] {R : A ⥤ B}
    [HasReflexiveCoequalizers A] [IsRightAdjoint (R ⋙ U)] : IsRightAdjoint R :=
  by
  let R' : A ⥤ _ := R ⋙ monad.comparison (adjunction.of_right_adjoint U)
  rsuffices : is_right_adjoint R'
  · let this : is_right_adjoint (R' ⋙ (monad.comparison (adjunction.of_right_adjoint U)).inv) := by
      infer_instance
    · let this : R' ⋙ (monad.comparison (adjunction.of_right_adjoint U)).inv ≅ R :=
        (iso_whisker_left R (monad.comparison _).asEquivalence.unitIso.symm : _) ≪≫ R.right_unitor
      exact adjunction.right_adjoint_of_nat_iso this
  let this : is_right_adjoint (R' ⋙ monad.forget (adjunction.of_right_adjoint U).toMonad) :=
    adjunction.right_adjoint_of_nat_iso
      (iso_whisker_left R (monad.comparison_forget (adjunction.of_right_adjoint U)).symm : _)
  let this : ∀ X, regular_epi ((monad.adj (adjunction.of_right_adjoint U).toMonad).counit.app X) :=
    by
    intro X
    simp only [monad.adj_counit]
    exact ⟨_, _, _, _, monad.beck_algebra_coequalizer X⟩
  exact adjoint_triangle_lift R' (monad.adj _)
#align category_theory.monadic_adjoint_triangle_lift CategoryTheory.monadicAdjointTriangleLift

variable {D : Type u₄}

variable [Category.{v₄} D]

/-- Suppose we have a commutative square of functors

      Q
    A → B
  U ↓   ↓ V
    C → D
      R

where `U` has a left adjoint, `A` has reflexive coequalizers and `V` has a left adjoint such that
each component of the counit is a regular epi.
Then `Q` has a left adjoint if `R` has a left adjoint.

See https://ncatlab.org/nlab/show/adjoint+lifting+theorem
-/
noncomputable def adjointSquareLift (Q : A ⥤ B) (V : B ⥤ D) (U : A ⥤ C) (R : C ⥤ D)
    (comm : U ⋙ R ≅ Q ⋙ V) [IsRightAdjoint U] [IsRightAdjoint V] [IsRightAdjoint R]
    [∀ X, RegularEpi ((Adjunction.ofRightAdjoint V).counit.app X)] [HasReflexiveCoequalizers A] :
    IsRightAdjoint Q :=
  by
  let this := adjunction.right_adjoint_of_nat_iso comm
  exact adjoint_triangle_lift Q (adjunction.of_right_adjoint V)
#align category_theory.adjoint_square_lift CategoryTheory.adjointSquareLift

/-- Suppose we have a commutative square of functors

      Q
    A → B
  U ↓   ↓ V
    C → D
      R

where `U` has a left adjoint, `A` has reflexive coequalizers and `V` is monadic.
Then `Q` has a left adjoint if `R` has a left adjoint.

See https://ncatlab.org/nlab/show/adjoint+lifting+theorem
-/
noncomputable def monadicAdjointSquareLift (Q : A ⥤ B) (V : B ⥤ D) (U : A ⥤ C) (R : C ⥤ D)
    (comm : U ⋙ R ≅ Q ⋙ V) [IsRightAdjoint U] [MonadicRightAdjoint V] [IsRightAdjoint R]
    [HasReflexiveCoequalizers A] : IsRightAdjoint Q :=
  by
  let this := adjunction.right_adjoint_of_nat_iso comm
  exact monadic_adjoint_triangle_lift V
#align category_theory.monadic_adjoint_square_lift CategoryTheory.monadicAdjointSquareLift

end CategoryTheory

