/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Shapes.Reflexive
import Mathlib.CategoryTheory.Monad.Adjunction
import Mathlib.CategoryTheory.Monad.Coequalizer

#align_import category_theory.adjunction.lifting from "leanprover-community/mathlib"@"9bc7dfa6e50f902fb0684c9670a680459ebaed68"

/-!
# Adjoint lifting

This file gives two constructions for building left adjoints: the adjoint triangle theorem and the
adjoint lifting theorem.
The adjoint triangle theorem concerns a functor `U : B ⥤ C` with a left adjoint `F` such
that `ε_X : FUX ⟶ X` is a regular epi. Then for any category `A` with coequalizers of reflexive
pairs, a functor `R : A ⥤ B` has a left adjoint if (and only if) the composite `R ⋙ U` does.
Note that the condition on `U` regarding `ε_X` is automatically satisfied in the case when `U` is
a monadic functor, giving the corollary: `monadicAdjointTriangleLift`, i.e. if `U` is monadic,
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
  Cofork.IsColimit.mk' _ fun s => by
    refine' ⟨(RegularEpi.desc' (adj₁.counit.app X) s.π _).1, _, _⟩
    · rw [← cancel_epi (adj₁.counit.app (RegularEpi.W (adj₁.counit.app X)))]
      -- ⊢ NatTrans.app adj₁.counit (RegularEpi.W (NatTrans.app adj₁.counit X)) ≫ Regul …
      rw [← adj₁.counit_naturality_assoc RegularEpi.left]
      -- ⊢ F.map (U.map RegularEpi.left) ≫ NatTrans.app adj₁.counit ((U ⋙ F).obj X) ≫ C …
      dsimp only [Functor.comp_obj]
      -- ⊢ F.map (U.map RegularEpi.left) ≫ NatTrans.app adj₁.counit (F.obj (U.obj X)) ≫ …
      rw [← s.condition, ← F.map_comp_assoc, ← U.map_comp, RegularEpi.w, U.map_comp,
        F.map_comp_assoc, s.condition, ← adj₁.counit_naturality_assoc RegularEpi.right]
    · apply (RegularEpi.desc' (adj₁.counit.app X) s.π _).2
      -- 🎉 no goals
    · intro m hm
      -- ⊢ m = ↑(RegularEpi.desc' (NatTrans.app adj₁.counit X) (Cofork.π s) (_ : Regula …
      rw [← cancel_epi (adj₁.counit.app X)]
      -- ⊢ NatTrans.app adj₁.counit X ≫ m = NatTrans.app adj₁.counit X ≫ ↑(RegularEpi.d …
      apply hm.trans (RegularEpi.desc' (adj₁.counit.app X) s.π _).2.symm
      -- 🎉 no goals
#align category_theory.lift_adjoint.counit_coequalises CategoryTheory.LiftAdjoint.counitCoequalises

/-- (Implementation)
To construct the left adjoint, we use the coequalizer of `F' U ε_Y` with the composite

`F' U F U X ⟶ F' U F U R F U' X ⟶ F' U R F' U X ⟶ F' U X`

where the first morphism is `F' U F ι_UX`, the second is `F' U ε_RF'UX`, and the third is `δ_F'UX`.
We will show that this coequalizer exists and that it forms the object map for a left adjoint to
`R`.
-/
def otherMap (X) : F'.obj (U.obj (F.obj (U.obj X))) ⟶ F'.obj (U.obj X) :=
  F'.map (U.map (F.map (adj₂.unit.app _) ≫ adj₁.counit.app _)) ≫ adj₂.counit.app _
#align category_theory.lift_adjoint.other_map CategoryTheory.LiftAdjoint.otherMap

/-- `(F'Uε_X, otherMap X)` is a reflexive pair: in particular if `A` has reflexive coequalizers then
it has a coequalizer.
-/
instance (X : B) :
    IsReflexivePair (F'.map (U.map (adj₁.counit.app X))) (otherMap _ _ adj₁ adj₂ X) :=
  IsReflexivePair.mk' (F'.map (adj₁.unit.app (U.obj X)))
    (by
      rw [← F'.map_comp, adj₁.right_triangle_components]
      -- ⊢ F'.map (𝟙 (U.obj X)) = 𝟙 (F'.obj (U.obj ((𝟭 B).obj X)))
      apply F'.map_id)
      -- 🎉 no goals
    (by
      dsimp [otherMap]
      -- ⊢ F'.map (NatTrans.app adj₁.unit (U.obj X)) ≫ F'.map (U.map (F.map (NatTrans.a …
      rw [← F'.map_comp_assoc, U.map_comp, adj₁.unit_naturality_assoc,
        adj₁.right_triangle_components, comp_id, adj₂.left_triangle_components])

variable [HasReflexiveCoequalizers A]

/-- Construct the object part of the desired left adjoint as the coequalizer of `F'Uε_Y` with
`otherMap`.
-/
noncomputable def constructLeftAdjointObj (Y : B) : A :=
  coequalizer (F'.map (U.map (adj₁.counit.app Y))) (otherMap _ _ adj₁ adj₂ Y)
#align category_theory.lift_adjoint.construct_left_adjoint_obj CategoryTheory.LiftAdjoint.constructLeftAdjointObj

/-- The homset equivalence which helps show that `R` is a right adjoint. -/
@[simps!] -- Porting note: Originally `@[simps (config := { rhsMd := semireducible })]`
noncomputable def constructLeftAdjointEquiv [∀ X : B, RegularEpi (adj₁.counit.app X)] (Y : A)
    (X : B) : (constructLeftAdjointObj _ _ adj₁ adj₂ X ⟶ Y) ≃ (X ⟶ R.obj Y) :=
  calc
    (constructLeftAdjointObj _ _ adj₁ adj₂ X ⟶ Y) ≃
        { f : F'.obj (U.obj X) ⟶ Y //
          F'.map (U.map (adj₁.counit.app X)) ≫ f = otherMap _ _ adj₁ adj₂ _ ≫ f } :=
      Cofork.IsColimit.homIso (colimit.isColimit _) _
    _ ≃ { g : U.obj X ⟶ U.obj (R.obj Y) //
          U.map (F.map g ≫ adj₁.counit.app _) = U.map (adj₁.counit.app _) ≫ g } := by
      apply (adj₂.homEquiv _ _).subtypeEquiv _
      -- ⊢ ∀ (a : F'.obj (U.obj X) ⟶ Y), F'.map (U.map (NatTrans.app adj₁.counit X)) ≫  …
      intro f
      -- ⊢ F'.map (U.map (NatTrans.app adj₁.counit X)) ≫ f = otherMap R F' adj₁ adj₂ X  …
      rw [← (adj₂.homEquiv _ _).injective.eq_iff, eq_comm, adj₂.homEquiv_naturality_left,
        otherMap, assoc, adj₂.homEquiv_naturality_left, ← adj₂.counit_naturality,
        adj₂.homEquiv_naturality_left, adj₂.homEquiv_unit, adj₂.right_triangle_components,
        comp_id, Functor.comp_map, ← U.map_comp, assoc, ← adj₁.counit_naturality,
        adj₂.homEquiv_unit, adj₂.homEquiv_unit, F.map_comp, assoc]
      rfl
      -- 🎉 no goals
    _ ≃ { z : F.obj (U.obj X) ⟶ R.obj Y // _ } := by
      apply (adj₁.homEquiv _ _).symm.subtypeEquiv
      -- ⊢ ∀ (a : U.obj X ⟶ U.obj (R.obj Y)), U.map (F.map a ≫ NatTrans.app adj₁.counit …
      intro g
      -- ⊢ U.map (F.map g ≫ NatTrans.app adj₁.counit (R.obj Y)) = U.map (NatTrans.app a …
      rw [← (adj₁.homEquiv _ _).symm.injective.eq_iff, adj₁.homEquiv_counit,
        adj₁.homEquiv_counit, adj₁.homEquiv_counit, F.map_comp, assoc, U.map_comp, F.map_comp,
        assoc, adj₁.counit_naturality, adj₁.counit_naturality_assoc]
      apply eq_comm
      -- 🎉 no goals
    _ ≃ (X ⟶ R.obj Y) := (Cofork.IsColimit.homIso (counitCoequalises adj₁ X) _).symm
#align category_theory.lift_adjoint.construct_left_adjoint_equiv CategoryTheory.LiftAdjoint.constructLeftAdjointEquiv

/-- Construct the left adjoint to `R`, with object map `constructLeftAdjointObj`. -/
noncomputable def constructLeftAdjoint [∀ X : B, RegularEpi (adj₁.counit.app X)] : B ⥤ A := by
  refine' Adjunction.leftAdjointOfEquiv (fun X Y => constructLeftAdjointEquiv R _ adj₁ adj₂ Y X) _
  -- ⊢ ∀ (X : B) (Y Y' : A) (g : Y ⟶ Y') (h : constructLeftAdjointObj R F' adj₁ adj …
  intro X Y Y' g h
  -- ⊢ ↑((fun X Y => constructLeftAdjointEquiv R F' adj₁ adj₂ Y X) X Y') (h ≫ g) =  …
  rw [constructLeftAdjointEquiv_apply, constructLeftAdjointEquiv_apply,
    Equiv.symm_apply_eq, Subtype.ext_iff]
  dsimp
  -- ⊢ F.map (↑(Adjunction.homEquiv adj₂ (U.obj X) Y') ↑(↑(Cofork.IsColimit.homIso  …
  rw [Cofork.IsColimit.homIso_natural, Cofork.IsColimit.homIso_natural]
  -- ⊢ F.map (↑(Adjunction.homEquiv adj₂ (U.obj X) Y') (↑(↑(Cofork.IsColimit.homIso …
  erw [adj₂.homEquiv_naturality_right]
  -- ⊢ F.map (↑(Adjunction.homEquiv adj₂ (U.obj X) Y) ↑(↑(Cofork.IsColimit.homIso ( …
  simp_rw [Functor.comp_map]
  -- ⊢ F.map (↑(Adjunction.homEquiv adj₂ (U.obj X) Y) ↑(↑(Cofork.IsColimit.homIso ( …
  simp
  -- 🎉 no goals
#align category_theory.lift_adjoint.construct_left_adjoint CategoryTheory.LiftAdjoint.constructLeftAdjoint

end LiftAdjoint

/-- The adjoint triangle theorem: Suppose `U : B ⥤ C` has a left adjoint `F` such that each counit
`ε_X : FUX ⟶ X` is a regular epimorphism. Then if a category `A` has coequalizers of reflexive
pairs, then a functor `R : A ⥤ B` has a left adjoint if the composite `R ⋙ U` does.

Note the converse is true (with weaker assumptions), by `Adjunction.comp`.
See https://ncatlab.org/nlab/show/adjoint+triangle+theorem
-/
noncomputable def adjointTriangleLift {U : B ⥤ C} {F : C ⥤ B} (R : A ⥤ B) (adj₁ : F ⊣ U)
    [∀ X : B, RegularEpi (adj₁.counit.app X)] [HasReflexiveCoequalizers A]
    [IsRightAdjoint (R ⋙ U)] : IsRightAdjoint R where
  left := LiftAdjoint.constructLeftAdjoint R _ adj₁ (Adjunction.ofRightAdjoint _)
  adj := Adjunction.adjunctionOfEquivLeft _ _
#align category_theory.adjoint_triangle_lift CategoryTheory.adjointTriangleLift

/-- If `R ⋙ U` has a left adjoint, the domain of `R` has reflexive coequalizers and `U` is a monadic
functor, then `R` has a left adjoint.
This is a special case of `adjointTriangleLift` which is often more useful in practice.
-/
noncomputable def monadicAdjointTriangleLift (U : B ⥤ C) [MonadicRightAdjoint U] {R : A ⥤ B}
    [HasReflexiveCoequalizers A] [IsRightAdjoint (R ⋙ U)] : IsRightAdjoint R := by
  let R' : A ⥤ _ := R ⋙ Monad.comparison (Adjunction.ofRightAdjoint U)
  -- ⊢ IsRightAdjoint R
  rsuffices : IsRightAdjoint R'
  -- ⊢ IsRightAdjoint R
  · let this : IsRightAdjoint (R' ⋙ (Monad.comparison (Adjunction.ofRightAdjoint U)).inv) := by
      infer_instance
    · let this : R' ⋙ (Monad.comparison (Adjunction.ofRightAdjoint U)).inv ≅ R :=
        (isoWhiskerLeft R (Monad.comparison _).asEquivalence.unitIso.symm : _) ≪≫ R.rightUnitor
      exact Adjunction.rightAdjointOfNatIso this
      -- 🎉 no goals
  let this : IsRightAdjoint (R' ⋙ Monad.forget (Adjunction.ofRightAdjoint U).toMonad) :=
    Adjunction.rightAdjointOfNatIso
      (isoWhiskerLeft R (Monad.comparisonForget (Adjunction.ofRightAdjoint U)).symm : _)
  let this : ∀ X, RegularEpi ((Monad.adj (Adjunction.ofRightAdjoint U).toMonad).counit.app X) := by
    intro X
    simp only [Monad.adj_counit]
    exact ⟨_, _, _, _, Monad.beckAlgebraCoequalizer X⟩
  exact adjointTriangleLift R' (Monad.adj _)
  -- 🎉 no goals
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
  letI := Adjunction.rightAdjointOfNatIso comm
  adjointTriangleLift Q (Adjunction.ofRightAdjoint V)
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
  letI := Adjunction.rightAdjointOfNatIso comm
  monadicAdjointTriangleLift V
#align category_theory.monadic_adjoint_square_lift CategoryTheory.monadicAdjointSquareLift

end CategoryTheory
