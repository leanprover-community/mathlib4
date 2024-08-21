/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Shapes.Reflexive
import Mathlib.CategoryTheory.Monad.Adjunction
import Mathlib.CategoryTheory.Monad.Equalizer

/-!
# Adjoint lifting

This file gives two constructions for building right adjoints: the adjoint triangle theorem and the
adjoint lifting theorem.

TODO: dualize the rest of the docstring

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

variable {U : B ⥤ C} {F : C ⥤ B} (L : B ⥤ A) (U' : A ⥤ C)
variable (adj₁ : F ⊣ U) (adj₂ : F ⋙ L ⊣ U')

/-- To show that `ε_X` is a coequalizer for `(FUε_X, ε_FUX)`, it suffices to assume it's always a
coequalizer of something (i.e. a regular epi).
-/
def unitEqualises [∀ X : C, RegularMono (adj₁.unit.app X)] (X : C) :
    IsLimit (Fork.ofι (adj₁.unit.app X) (adj₁.unit_naturality _)) :=
  Fork.IsLimit.mk' _ fun s => by
    refine ⟨(RegularMono.lift' (adj₁.unit.app X) s.ι ?_).1, ?_, ?_⟩
    · rw [← cancel_mono (adj₁.unit.app (RegularMono.Z (adj₁.unit.app X)))]
      rw [assoc, ← adj₁.unit_naturality RegularMono.left]
      dsimp only [Functor.comp_obj]
      erw [← assoc, ← s.condition, assoc, ← U.map_comp, ← F.map_comp, RegularMono.w, F.map_comp,
        U.map_comp, s.condition_assoc, assoc, ← adj₁.unit_naturality RegularMono.right]
      rfl
    · apply (RegularMono.lift' (adj₁.unit.app X) s.ι _).2
    · intro m hm
      rw [← cancel_mono (adj₁.unit.app X)]
      apply hm.trans (RegularMono.lift' (adj₁.unit.app X) s.ι _).2.symm

/-- (Implementation)
To construct the left adjoint, we use the coequalizer of `F' U ε_Y` with the composite

`F' U F U X ⟶ F' U F U R F U' X ⟶ F' U R F' U X ⟶ F' U X`

where the first morphism is `F' U F ι_UX`, the second is `F' U ε_RF'UX`, and the third is `δ_F'UX`.
We will show that this coequalizer exists and that it forms the object map for a left adjoint to
`R`.
-/
def otherMap (X) : U'.obj X ⟶  U.obj (F.obj (U'.obj X)) :=
  adj₁.unit.app _ ≫ U.map (F.map (adj₂.unit.app _)) ≫ U.map (F.map (U'.map (adj₂.counit.app _)))

/-- `(F'Uε_X, otherMap X)` is a reflexive pair: in particular if `A` has reflexive coequalizers then
it has a coequalizer.
-/
instance (X : A) :
    IsCoreflexivePair (F.map (adj₁.unit.app (U'.obj X))) (F.map (otherMap _ _ adj₁ adj₂ X)) :=
  IsCoreflexivePair.mk' (adj₁.counit.app _) (by simp) (by simp [otherMap])

variable [HasCoreflexiveEqualizers B]

/-- Construct the object part of the desired left adjoint as the coequalizer of `F'Uε_Y` with
`otherMap`.
-/
noncomputable def constructRightAdjointObj (Y : A) : B :=
  equalizer (F.map (adj₁.unit.app (U'.obj Y))) (F.map (otherMap _ _ adj₁ adj₂ Y))

/-- The homset equivalence which helps show that `R` is a right adjoint. -/
@[simps!] -- Porting note: Originally `@[simps (config := { rhsMd := semireducible })]`
noncomputable def constructRightAdjointEquiv [∀ X : C, RegularMono (adj₁.unit.app X)] (Y : A)
    (X : B) : (X ⟶ constructRightAdjointObj _ _ adj₁ adj₂ Y) ≃ (L.obj X ⟶ Y) :=
  calc
    (X ⟶ constructRightAdjointObj _ _ adj₁ adj₂ Y) ≃
        { f : X ⟶ F.obj (U'.obj Y) //
          f ≫ (F.map (adj₁.unit.app (U'.obj Y))) = f ≫ (F.map (otherMap _ _ adj₁ adj₂ Y)) } :=
      Fork.IsLimit.homIso (limit.isLimit _) _
    _ ≃ { g : U.obj X ⟶ U'.obj Y // sorry } := sorry
    _ ≃ _ := sorry
    --     apply (adj₁.homEquiv _ _).symm.subtypeEquiv _

    -- -- { g : U.obj X ⟶ U.obj (R.obj Y) //
    -- --       U.map (F.map g ≫ adj₁.counit.app _) = U.map (adj₁.counit.app _) ≫ g } := by
    -- --   apply (adj₂.homEquiv _ _).subtypeEquiv _
    -- --   intro f
    -- --   rw [← (adj₂.homEquiv _ _).injective.eq_iff, eq_comm, adj₂.homEquiv_naturality_left,
    -- --     otherMap, assoc, adj₂.homEquiv_naturality_left, ← adj₂.counit_naturality,
    -- --     adj₂.homEquiv_naturality_left, adj₂.homEquiv_unit, adj₂.right_triangle_components,
    -- --     comp_id, Functor.comp_map, ← U.map_comp, assoc, ← adj₁.counit_naturality,
    -- --     adj₂.homEquiv_unit, adj₂.homEquiv_unit, F.map_comp, assoc]
    -- --   rfl
    -- _ ≃ { z : F.obj (U.obj X) ⟶ R.obj Y // _ } := by
    --   apply (adj₁.homEquiv _ _).symm.subtypeEquiv
    --   intro g
    --   rw [← (adj₁.homEquiv _ _).symm.injective.eq_iff, adj₁.homEquiv_counit,
    --     adj₁.homEquiv_counit, adj₁.homEquiv_counit, F.map_comp, assoc, U.map_comp, F.map_comp,
    --     assoc, adj₁.counit_naturality, adj₁.counit_naturality_assoc]
    --   apply eq_comm
    -- _ ≃ (X ⟶ R.obj Y) := (Cofork.IsColimit.homIso (counitCoequalises adj₁ X) _).symm

/-- Construct the left adjoint to `R`, with object map `constructLeftAdjointObj`. -/
noncomputable def constructRightAdjoint [∀ X : C, RegularMono (adj₁.unit.app X)] : A ⥤ B := by
  refine Adjunction.rightAdjointOfEquiv
    (fun X Y => (constructRightAdjointEquiv L _ adj₁ adj₂ Y X).symm) ?_
  intro X Y Y' g h
  sorry
  -- rw [constructLeftAdjointEquiv_apply, constructLeftAdjointEquiv_apply,
  --   Equiv.symm_apply_eq, Subtype.ext_iff]
  -- dsimp
  -- -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
  -- erw [Cofork.IsColimit.homIso_natural, Cofork.IsColimit.homIso_natural]
  -- erw [adj₂.homEquiv_naturality_right]
  -- simp_rw [Functor.comp_map]
  -- -- This used to be `simp`, but we need `aesop_cat` after leanprover/lean4#2644
  -- aesop_cat

end LiftAdjoint

/-- The adjoint triangle theorem: Suppose `U : B ⥤ C` has a left adjoint `F` such that each counit
`ε_X : FUX ⟶ X` is a regular epimorphism. Then if a category `A` has coequalizers of reflexive
pairs, then a functor `R : A ⥤ B` has a left adjoint if the composite `R ⋙ U` does.

Note the converse is true (with weaker assumptions), by `Adjunction.comp`.
See https://ncatlab.org/nlab/show/adjoint+triangle+theorem
-/
lemma adjointTriangleLift  {U : B ⥤ C} {F : C ⥤ B} (L : B ⥤ A) (adj₁ : F ⊣ U)
    [∀ X : C, RegularMono (adj₁.unit.app X)] [HasCoreflexiveEqualizers B]
    [(F ⋙ L).IsLeftAdjoint ] : L.IsLeftAdjoint where
  exists_rightAdjoint :=
    ⟨LiftAdjoint.constructRightAdjoint L _ adj₁ (Adjunction.ofIsLeftAdjoint _),
      ⟨Adjunction.adjunctionOfEquivRight _ _⟩⟩

/-- If `R ⋙ U` has a left adjoint, the domain of `R` has reflexive coequalizers and `U` is a monadic
functor, then `R` has a left adjoint.
This is a special case of `adjointTriangleLift` which is often more useful in practice.
-/
lemma monadicAdjointTriangleLift (F : C ⥤ B) [ComonadicLeftAdjoint F] {L : B ⥤ A}
    [HasCoreflexiveEqualizers B] [(F ⋙ L).IsLeftAdjoint] : L.IsLeftAdjoint := by
  let L' : _ ⥤ B := (Comonad.comparison (comonadicAdjunction F)).asEquivalence.inverse ⋙ F
  sorry
  -- rsuffices : L'.IsLeftAdjoint
  -- · let this : (L' ⋙ (Monad.comparison (monadicAdjunction U)).inv).IsRightAdjoint := by
  --     infer_instance
  --   refine ((Adjunction.ofIsRightAdjoint
  --     (R' ⋙ (Monad.comparison (monadicAdjunction U)).inv)).ofNatIsoRight ?_).isRightAdjoint
  --   exact isoWhiskerLeft R (Monad.comparison _).asEquivalence.unitIso.symm ≪≫ R.rightUnitor
  -- let this : (R' ⋙ Monad.forget (monadicAdjunction U).toMonad).IsRightAdjoint := by
  --   refine ((Adjunction.ofIsRightAdjoint (R ⋙ U)).ofNatIsoRight ?_).isRightAdjoint
  --   exact isoWhiskerLeft R (Monad.comparisonForget (monadicAdjunction U)).symm
  -- let this : ∀ X, RegularEpi ((Monad.adj (monadicAdjunction U).toMonad).counit.app X) := by
  --   intro X
  --   simp only [Monad.adj_counit]
  --   exact ⟨_, _, _, _, Monad.beckAlgebraCoequalizer X⟩
  -- exact adjointTriangleLift R' (Monad.adj _)

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
lemma adjointSquareLift (Q : A ⥤ B) (V : B ⥤ D) (U : A ⥤ C) (R : C ⥤ D)
    (comm : U ⋙ R ≅ Q ⋙ V) [U.IsRightAdjoint] [V.IsRightAdjoint] [R.IsRightAdjoint]
    [∀ X, RegularEpi ((Adjunction.ofIsRightAdjoint V).counit.app X)] [HasReflexiveCoequalizers A] :
    Q.IsRightAdjoint :=
  have := ((Adjunction.ofIsRightAdjoint (U ⋙ R)).ofNatIsoRight comm).isRightAdjoint
  sorry
  -- adjointTriangleLift Q (Adjunction.ofIsRightAdjoint V)

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
lemma monadicAdjointSquareLift (Q : A ⥤ B) (V : B ⥤ D) (U : A ⥤ C) (R : C ⥤ D)
    (comm : U ⋙ R ≅ Q ⋙ V) [U.IsRightAdjoint] [MonadicRightAdjoint V] [R.IsRightAdjoint]
    [HasReflexiveCoequalizers A] : Q.IsRightAdjoint :=
  have := ((Adjunction.ofIsRightAdjoint (U ⋙ R)).ofNatIsoRight comm).isRightAdjoint
  sorry
  -- monadicAdjointTriangleLift V

end CategoryTheory
