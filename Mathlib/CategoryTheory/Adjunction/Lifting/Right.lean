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

variable {U : A ⥤ B} {F : B ⥤ A} (L : C ⥤ B) (U' : A ⥤ C)
variable (adj₁ : F ⊣ U) (adj₂ : L ⋙ F ⊣ U')

/-- To show that `ε_X` is a coequalizer for `(FUε_X, ε_FUX)`, it suffices to assume it's always a
coequalizer of something (i.e. a regular epi).
-/
def unitEqualises [∀ X : B, RegularMono (adj₁.unit.app X)] (X : B) :
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
def otherMap (X : B) : U'.obj (F.obj X) ⟶  U'.obj (F.obj (U.obj (F.obj X))) :=
  adj₂.unit.app _ ≫ U'.map (F.map (adj₁.unit.app _ ≫ (U.map (adj₂.counit.app _))))

/-- `(F'Uε_X, otherMap X)` is a reflexive pair: in particular if `A` has reflexive coequalizers then
it has a coequalizer.
-/
instance (X : B) :
    IsCoreflexivePair (U'.map (F.map (adj₁.unit.app X))) (otherMap _ _ adj₁ adj₂ X) :=
  IsCoreflexivePair.mk' (U'.map (adj₁.counit.app (F.obj X)))
    (by simp [← Functor.map_comp])
    (by simp only [otherMap, assoc, ← Functor.map_comp]; simp)

variable [HasCoreflexiveEqualizers C]

/-- Construct the object part of the desired left adjoint as the coequalizer of `F'Uε_Y` with
`otherMap`.
-/
noncomputable def constructRightAdjointObj (Y : B) : C :=
  equalizer (U'.map (F.map (adj₁.unit.app Y))) (otherMap _ _ adj₁ adj₂ Y)

/-- The homset equivalence which helps show that `R` is a right adjoint. -/
@[simps!] -- Porting note: Originally `@[simps (config := { rhsMd := semireducible })]`
noncomputable def constructRightAdjointEquiv [∀ X : B, RegularMono (adj₁.unit.app X)] (Y : C)
    (X : B) : (Y ⟶ constructRightAdjointObj _ _ adj₁ adj₂ X) ≃ (L.obj Y ⟶ X) :=
  calc
    (Y ⟶ constructRightAdjointObj _ _ adj₁ adj₂ X) ≃
        { f : Y ⟶ U'.obj (F.obj X) //
          f ≫ U'.map (F.map (adj₁.unit.app X)) = f ≫ (otherMap _ _ adj₁ adj₂ X) } :=
      Fork.IsLimit.homIso (limit.isLimit _) _
    _ ≃ { g : F.obj (L.obj Y) ⟶ F.obj X // F.map (adj₁.unit.app _≫ U.map g) =
        g ≫ F.map (adj₁.unit.app _) } := by
      apply (adj₂.homEquiv _ _).symm.subtypeEquiv _
      intro f
      rw [← (adj₂.homEquiv _ _).injective.eq_iff, eq_comm, otherMap,
        ← adj₂.homEquiv_naturality_right_symm, adj₂.homEquiv_unit, ← adj₂.unit_naturality_assoc,
        adj₂.homEquiv_counit]
      simp
    _ ≃ { z : L.obj Y ⟶ U.obj (F.obj X) //
        z ≫ U.map (F.map (adj₁.unit.app X)) = z ≫ adj₁.unit.app (U.obj (F.obj X)) } := by
      apply (adj₁.homEquiv _ _).subtypeEquiv
      intro g
      rw [← (adj₁.homEquiv _ _).injective.eq_iff, adj₁.homEquiv_unit,
        adj₁.homEquiv_unit, adj₁.homEquiv_unit, eq_comm]
      simp
    _ ≃ (L.obj Y ⟶ X) := (Fork.IsLimit.homIso (unitEqualises adj₁ X) _).symm

/-- Construct the left adjoint to `R`, with object map `constructLeftAdjointObj`. -/
noncomputable def constructRightAdjoint [∀ X : B, RegularMono (adj₁.unit.app X)] : B ⥤ C := by
  refine Adjunction.rightAdjointOfEquiv
    (fun X Y => (constructRightAdjointEquiv L _ adj₁ adj₂ X Y).symm) ?_
  intro X Y Y' g h
  rw [constructRightAdjointEquiv_symm_apply, constructRightAdjointEquiv_symm_apply,
    Equiv.symm_apply_eq, Subtype.ext_iff]
  dsimp [otherMap]
  erw [Fork.IsLimit.homIso_natural, Fork.IsLimit.homIso_natural]
  simp only [Fork.ofι_pt, Functor.map_comp, assoc, limit.cone_x]
  erw [adj₂.homEquiv_naturality_left, Equiv.rightInverse_symm]
  aesop_cat

end LiftAdjoint

/-- The adjoint triangle theorem: Suppose `U : B ⥤ C` has a left adjoint `F` such that each counit
`ε_X : FUX ⟶ X` is a regular epimorphism. Then if a category `A` has coequalizers of reflexive
pairs, then a functor `R : A ⥤ B` has a left adjoint if the composite `R ⋙ U` does.

Note the converse is true (with weaker assumptions), by `Adjunction.comp`.
See https://ncatlab.org/nlab/show/adjoint+triangle+theorem
-/
lemma adjointTriangleLift  {U : A ⥤ B} {F : B ⥤ A} (L : C ⥤ B) (adj₁ : F ⊣ U)
    [∀ X, RegularMono (adj₁.unit.app X)] [HasCoreflexiveEqualizers C]
    [(L ⋙ F).IsLeftAdjoint ] : L.IsLeftAdjoint where
  exists_rightAdjoint :=
    ⟨LiftAdjoint.constructRightAdjoint L _ adj₁ (Adjunction.ofIsLeftAdjoint _),
      ⟨Adjunction.adjunctionOfEquivRight _ _⟩⟩

/-- If `R ⋙ U` has a left adjoint, the domain of `R` has reflexive coequalizers and `U` is a monadic
functor, then `R` has a left adjoint.
This is a special case of `adjointTriangleLift` which is often more useful in practice.
-/
lemma comonadicAdjointTriangleLift (F : B ⥤ A) [ComonadicLeftAdjoint F] {L : C ⥤ B}
    [HasCoreflexiveEqualizers C] [(L ⋙ F).IsLeftAdjoint] : L.IsLeftAdjoint := by
  let L' : _ ⥤ _ := L ⋙ Comonad.comparison (comonadicAdjunction F)
  rsuffices : L'.IsLeftAdjoint
  · let this : (L' ⋙ (Comonad.comparison (comonadicAdjunction F)).inv).IsLeftAdjoint := by
      infer_instance
    refine ((Adjunction.ofIsLeftAdjoint
      (L' ⋙ (Comonad.comparison (comonadicAdjunction F)).inv)).ofNatIsoLeft ?_).isLeftAdjoint
    exact isoWhiskerLeft L (Comonad.comparison _).asEquivalence.unitIso.symm ≪≫ L.leftUnitor
  let this : (L' ⋙ Comonad.forget (comonadicAdjunction F).toComonad).IsLeftAdjoint := by
    refine ((Adjunction.ofIsLeftAdjoint (L ⋙ F)).ofNatIsoLeft ?_).isLeftAdjoint
    exact isoWhiskerLeft L (Comonad.comparisonForget (comonadicAdjunction F)).symm
  let this : ∀ X, RegularMono ((Comonad.adj (comonadicAdjunction F).toComonad).unit.app X) := by
    intro X
    simp only [Comonad.adj_unit]
    exact ⟨_, _, _, _, Comonad.beckCoalgebraEqualizer X⟩
  exact adjointTriangleLift L' (Comonad.adj _)

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
lemma adjointSquareLift (Q : A ⥤ B) (V : B ⥤ D) (U : A ⥤ C) (L : C ⥤ D)
    (comm : U ⋙ L ≅ Q ⋙ V) [U.IsLeftAdjoint] [V.IsLeftAdjoint] [L.IsLeftAdjoint]
    [∀ X, RegularMono ((Adjunction.ofIsLeftAdjoint V).unit.app X)] [HasCoreflexiveEqualizers A] :
    Q.IsLeftAdjoint :=
  have := ((Adjunction.ofIsLeftAdjoint (U ⋙ L)).ofNatIsoLeft comm).isLeftAdjoint
  adjointTriangleLift Q (Adjunction.ofIsLeftAdjoint V)

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
lemma comonadicAdjointSquareLift (Q : A ⥤ B) (V : B ⥤ D) (U : A ⥤ C) (L : C ⥤ D)
    (comm : U ⋙ L ≅ Q ⋙ V) [U.IsLeftAdjoint] [ComonadicLeftAdjoint V] [L.IsLeftAdjoint]
    [HasCoreflexiveEqualizers A] : Q.IsLeftAdjoint :=
  have := ((Adjunction.ofIsLeftAdjoint (U ⋙ L)).ofNatIsoLeft comm).isLeftAdjoint
  comonadicAdjointTriangleLift V

end CategoryTheory
