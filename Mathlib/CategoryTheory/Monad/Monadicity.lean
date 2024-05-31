/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Shapes.Reflexive
import Mathlib.CategoryTheory.Monad.Coequalizer
import Mathlib.CategoryTheory.Monad.Limits

#align_import category_theory.monad.monadicity from "leanprover-community/mathlib"@"4bd8c855d6ba8f0d5eefbf80c20fa00ee034dec9"

/-!
# Monadicity theorems

We prove monadicity theorems which can establish a given functor is monadic. In particular, we
show three versions of Beck's monadicity theorem, and the reflexive (crude) monadicity theorem:

`G` is a monadic right adjoint if it has a right adjoint, and:

* `D` has, `G` preserves and reflects `G`-split coequalizers, see
  `CategoryTheory.Monad.monadicOfHasPreservesReflectsGSplitCoequalizers`
* `G` creates `G`-split coequalizers, see
  `CategoryTheory.Monad.monadicOfCreatesGSplitCoequalizers`
  (The converse of this is also shown, see
   `CategoryTheory.Monad.createsGSplitCoequalizersOfMonadic`)
* `D` has and `G` preserves `G`-split coequalizers, and `G` reflects isomorphisms, see
  `CategoryTheory.Monad.monadicOfHasPreservesGSplitCoequalizersOfReflectsIsomorphisms`
* `D` has and `G` preserves reflexive coequalizers, and `G` reflects isomorphisms, see
  `CategoryTheory.Monad.monadicOfHasPreservesReflexiveCoequalizersOfReflectsIsomorphisms`

## Tags

Beck, monadicity, descent

## TODO

Dualise to show comonadicity theorems.
-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

namespace Monad

open Limits

noncomputable section

-- Hide the implementation details in this namespace.
namespace MonadicityInternal

variable {C : Type u₁} {D : Type u₂}
variable [Category.{v₁} C] [Category.{v₁} D]
variable {G : D ⥤ C} {F : C ⥤ D} (adj : F ⊣ G)

/-- The "main pair" for an algebra `(A, α)` is the pair of morphisms `(F α, ε_FA)`. It is always a
reflexive pair, and will be used to construct the left adjoint to the comparison functor and show it
is an equivalence.
-/
instance main_pair_reflexive (A : adj.toMonad.Algebra) :
    IsReflexivePair (F.map A.a) (adj.counit.app (F.obj A.A)) := by
  apply IsReflexivePair.mk' (F.map (adj.unit.app _)) _ _
  · rw [← F.map_comp, ← F.map_id]
    exact congr_arg F.map A.unit
  · rw [adj.left_triangle_components]
    rfl
#align category_theory.monad.monadicity_internal.main_pair_reflexive CategoryTheory.Monad.MonadicityInternal.main_pair_reflexive

/-- The "main pair" for an algebra `(A, α)` is the pair of morphisms `(F α, ε_FA)`. It is always a
`G`-split pair, and will be used to construct the left adjoint to the comparison functor and show it
is an equivalence.
-/
instance main_pair_G_split (A : adj.toMonad.Algebra) :
    G.IsSplitPair (F.map A.a)
      (adj.counit.app (F.obj A.A)) where
  splittable := ⟨_, _, ⟨beckSplitCoequalizer A⟩⟩
set_option linter.uppercaseLean3 false in
#align category_theory.monad.monadicity_internal.main_pair_G_split CategoryTheory.Monad.MonadicityInternal.main_pair_G_split

/-- The object function for the left adjoint to the comparison functor. -/
def comparisonLeftAdjointObj (A : adj.toMonad.Algebra)
    [HasCoequalizer (F.map A.a) (adj.counit.app _)] : D :=
  coequalizer (F.map A.a) (adj.counit.app _)
#align category_theory.monad.monadicity_internal.comparison_left_adjoint_obj CategoryTheory.Monad.MonadicityInternal.comparisonLeftAdjointObj

/--
We have a bijection of homsets which will be used to construct the left adjoint to the comparison
functor.
-/
@[simps!]
def comparisonLeftAdjointHomEquiv (A : adj.toMonad.Algebra) (B : D)
    [HasCoequalizer (F.map A.a) (adj.counit.app (F.obj A.A))] :
    (comparisonLeftAdjointObj adj A ⟶ B) ≃ (A ⟶ (comparison adj).obj B) :=
  calc
    (comparisonLeftAdjointObj adj A ⟶ B) ≃ { f : F.obj A.A ⟶ B // _ } :=
      Cofork.IsColimit.homIso (colimit.isColimit _) B
    _ ≃ { g : A.A ⟶ G.obj B // G.map (F.map g) ≫ G.map (adj.counit.app B) = A.a ≫ g } := by
      refine (adj.homEquiv _ _).subtypeEquiv ?_
      intro f
      rw [← (adj.homEquiv _ _).injective.eq_iff, Adjunction.homEquiv_naturality_left,
        adj.homEquiv_unit, adj.homEquiv_unit, G.map_comp]
      dsimp
      rw [adj.right_triangle_components_assoc, ← G.map_comp, F.map_comp, Category.assoc,
        adj.counit_naturality, adj.left_triangle_components_assoc]
      apply eq_comm
    _ ≃ (A ⟶ (comparison adj).obj B) :=
      { toFun := fun g =>
          { f := _
            h := g.prop }
        invFun := fun f => ⟨f.f, f.h⟩
        left_inv := fun g => by ext; rfl
        right_inv := fun f => by ext; rfl }
#align category_theory.monad.monadicity_internal.comparison_left_adjoint_hom_equiv CategoryTheory.Monad.MonadicityInternal.comparisonLeftAdjointHomEquiv

/-- Construct the adjunction to the comparison functor.
-/
def leftAdjointComparison
    [∀ A : adj.toMonad.Algebra, HasCoequalizer (F.map A.a)
      (adj.counit.app (F.obj A.A))] :
    adj.toMonad.Algebra ⥤ D := by
  refine
    Adjunction.leftAdjointOfEquiv (G := comparison adj)
      (F_obj := fun A => comparisonLeftAdjointObj adj A) (fun A B => ?_) ?_
  · apply comparisonLeftAdjointHomEquiv
  · intro A B B' g h
    ext1
    -- Porting note: the goal was previously closed by the following, which succeeds until
    -- `Category.assoc`.
    -- dsimp [comparisonLeftAdjointHomEquiv]
    -- rw [← adj.homEquiv_naturality_right, Category.assoc]
    simp [Cofork.IsColimit.homIso]
#align category_theory.monad.monadicity_internal.left_adjoint_comparison CategoryTheory.Monad.MonadicityInternal.leftAdjointComparison

/-- Provided we have the appropriate coequalizers, we have an adjunction to the comparison functor.
-/
@[simps! counit]
def comparisonAdjunction
    [∀ A : adj.toMonad.Algebra, HasCoequalizer (F.map A.a)
      (adj.counit.app (F.obj A.A))] :
    leftAdjointComparison adj ⊣ comparison adj :=
  Adjunction.adjunctionOfEquivLeft _ _
#align category_theory.monad.monadicity_internal.comparison_adjunction CategoryTheory.Monad.MonadicityInternal.comparisonAdjunction

variable {adj}

theorem comparisonAdjunction_unit_f_aux
    [∀ A : adj.toMonad.Algebra, HasCoequalizer (F.map A.a)
      (adj.counit.app (F.obj A.A))]
    (A : adj.toMonad.Algebra) :
    ((comparisonAdjunction adj).unit.app A).f =
      adj.homEquiv A.A _
        (coequalizer.π (F.map A.a) (adj.counit.app (F.obj A.A))) :=
  congr_arg (adj.homEquiv _ _) (Category.comp_id _)
#align category_theory.monad.monadicity_internal.comparison_adjunction_unit_f_aux CategoryTheory.Monad.MonadicityInternal.comparisonAdjunction_unit_f_aux

/-- This is a cofork which is helpful for establishing monadicity: the morphism from the Beck
coequalizer to this cofork is the unit for the adjunction on the comparison functor.
-/
@[simps! pt]
def unitCofork (A : adj.toMonad.Algebra)
    [HasCoequalizer (F.map A.a) (adj.counit.app (F.obj A.A))] :
    Cofork (G.map (F.map A.a)) (G.map (adj.counit.app (F.obj A.A))) :=
  Cofork.ofπ (G.map (coequalizer.π (F.map A.a) (adj.counit.app (F.obj A.A))))
    (by
      change _ = G.map _ ≫ _
      rw [← G.map_comp, coequalizer.condition, G.map_comp])
#align category_theory.monad.monadicity_internal.unit_cofork CategoryTheory.Monad.MonadicityInternal.unitCofork

@[simp]
theorem unitCofork_π (A : adj.toMonad.Algebra)
    [HasCoequalizer (F.map A.a) (adj.counit.app (F.obj A.A))] :
    (unitCofork A).π = G.map (coequalizer.π (F.map A.a) (adj.counit.app (F.obj A.A))) :=
  rfl
#align category_theory.monad.monadicity_internal.unit_cofork_π CategoryTheory.Monad.MonadicityInternal.unitCofork_π

theorem comparisonAdjunction_unit_f
    [∀ A : adj.toMonad.Algebra, HasCoequalizer (F.map A.a)
      (adj.counit.app (F.obj A.A))]
    (A : adj.toMonad.Algebra) :
    ((comparisonAdjunction adj).unit.app A).f = (beckCoequalizer A).desc (unitCofork A) := by
  apply Limits.Cofork.IsColimit.hom_ext (beckCoequalizer A)
  rw [Cofork.IsColimit.π_desc]
  dsimp only [beckCofork_π, unitCofork_π]
  rw [comparisonAdjunction_unit_f_aux, ← adj.homEquiv_naturality_left A.a, coequalizer.condition,
    adj.homEquiv_naturality_right, adj.homEquiv_unit, Category.assoc]
  apply adj.right_triangle_components_assoc
#align category_theory.monad.monadicity_internal.comparison_adjunction_unit_f CategoryTheory.Monad.MonadicityInternal.comparisonAdjunction_unit_f

variable (adj)

/-- The cofork which describes the counit of the adjunction: the morphism from the coequalizer of
this pair to this morphism is the counit.
-/
@[simps!]
def counitCofork (B : D) :
    Cofork (F.map (G.map (adj.counit.app B)))
      (adj.counit.app (F.obj (G.obj B))) :=
  Cofork.ofπ (adj.counit.app B) (adj.counit_naturality _)
#align category_theory.monad.monadicity_internal.counit_cofork CategoryTheory.Monad.MonadicityInternal.counitCofork

variable {adj} in
/-- The unit cofork is a colimit provided `G` preserves it.  -/
def unitColimitOfPreservesCoequalizer (A : adj.toMonad.Algebra)
    [HasCoequalizer (F.map A.a) (adj.counit.app (F.obj A.A))]
    [PreservesColimit (parallelPair (F.map A.a) (adj.counit.app (F.obj A.A))) G] :
    IsColimit (unitCofork (G := G) A) :=
  isColimitOfHasCoequalizerOfPreservesColimit G _ _
#align category_theory.monad.monadicity_internal.unit_colimit_of_preserves_coequalizer CategoryTheory.Monad.MonadicityInternal.unitColimitOfPreservesCoequalizer

/-- The counit cofork is a colimit provided `G` reflects it. -/
def counitCoequalizerOfReflectsCoequalizer (B : D)
    [ReflectsColimit (parallelPair (F.map (G.map (adj.counit.app B)))
      (adj.counit.app (F.obj (G.obj B)))) G] :
    IsColimit (counitCofork (adj := adj) B) :=
  isColimitOfIsColimitCoforkMap G _ (beckCoequalizer ((comparison adj).obj B))
#align category_theory.monad.monadicity_internal.counit_coequalizer_of_reflects_coequalizer CategoryTheory.Monad.MonadicityInternal.counitCoequalizerOfReflectsCoequalizer

-- Porting note: Lean 3 didn't seem to need this
instance
    [∀ A : adj.toMonad.Algebra, HasCoequalizer (F.map A.a) (adj.counit.app (F.obj A.A))]
    (B : D) : HasColimit (parallelPair
      (F.map (G.map (NatTrans.app adj.counit B)))
      (NatTrans.app adj.counit (F.obj (G.obj B)))) :=
  inferInstanceAs <| HasCoequalizer
    (F.map ((comparison adj).obj B).a)
    (adj.counit.app (F.obj ((comparison adj).obj B).A))

theorem comparisonAdjunction_counit_app
    [∀ A : adj.toMonad.Algebra, HasCoequalizer (F.map A.a) (adj.counit.app (F.obj A.A))] (B : D) :
    (comparisonAdjunction adj).counit.app B = colimit.desc _ (counitCofork adj B) := by
  apply coequalizer.hom_ext
  change
    coequalizer.π _ _ ≫ coequalizer.desc ((adj.homEquiv _ B).symm (𝟙 _)) _ =
      coequalizer.π _ _ ≫ coequalizer.desc _ _
  simp
#align category_theory.monad.monadicity_internal.comparison_adjunction_counit_app CategoryTheory.Monad.MonadicityInternal.comparisonAdjunction_counit_app

end MonadicityInternal

open CategoryTheory Adjunction Monad MonadicityInternal

variable {C : Type u₁} {D : Type u₂}
variable [Category.{v₁} C] [Category.{v₁} D]
variable {G : D ⥤ C} {F : C ⥤ D} (adj : F ⊣ G)

variable (G) in
/--
If `G` is monadic, it creates colimits of `G`-split pairs. This is the "boring" direction of Beck's
monadicity theorem, the converse is given in `monadicOfCreatesGSplitCoequalizers`.
-/
def createsGSplitCoequalizersOfMonadic [MonadicRightAdjoint G] ⦃A B⦄ (f g : A ⟶ B)
    [G.IsSplitPair f g] : CreatesColimit (parallelPair f g) G := by
  apply (config := {allowSynthFailures := true}) monadicCreatesColimitOfPreservesColimit
    -- Porting note: oddly (config := {allowSynthFailures := true}) had no effect here and below
  · apply @preservesColimitOfIsoDiagram _ _ _ _ _ _ _ _ _ (diagramIsoParallelPair.{v₁} _).symm ?_
    dsimp
    infer_instance
  · apply @preservesColimitOfIsoDiagram _ _ _ _ _ _ _ _ _ (diagramIsoParallelPair.{v₁} _).symm ?_
    dsimp
    infer_instance
set_option linter.uppercaseLean3 false in
#align category_theory.monad.creates_G_split_coequalizers_of_monadic CategoryTheory.Monad.createsGSplitCoequalizersOfMonadic

section BeckMonadicity

-- Porting note: added these to replace parametric instances lean4#2311
-- When this is fixed the proofs below that struggle with instances should be reviewed.
-- [∀ ⦃A B⦄ (f g : A ⟶ B) [G.IsSplitPair f g], HasCoequalizer f g]
class HasCoequalizerOfIsSplitPair (G : D ⥤ C) : Prop where
  out : ∀ {A B} (f g : A ⟶ B) [G.IsSplitPair f g], HasCoequalizer f g

-- Porting note: cannot find synth order
-- instance {A B} (f g : A ⟶ B) [G.IsSplitPair f g] [HasCoequalizerOfIsSplitPair G] :
--     HasCoequalizer f g := HasCoequalizerOfIsSplitPair.out f g

instance [HasCoequalizerOfIsSplitPair G] : ∀ (A : Algebra adj.toMonad),
    HasCoequalizer (F.map A.a)
      (adj.counit.app (F.obj A.A)) :=
  fun _ => HasCoequalizerOfIsSplitPair.out G _ _

-- Porting note: added these to replace parametric instances lean4#2311
-- [∀ ⦃A B⦄ (f g : A ⟶ B) [G.IsSplitPair f g], PreservesColimit (parallelPair f g) G]
class PreservesColimitOfIsSplitPair (G : D ⥤ C) where
  out : ∀ {A B} (f g : A ⟶ B) [G.IsSplitPair f g], PreservesColimit (parallelPair f g) G

instance {A B} (f g : A ⟶ B) [G.IsSplitPair f g] [PreservesColimitOfIsSplitPair G] :
    PreservesColimit (parallelPair f g) G := PreservesColimitOfIsSplitPair.out f g

instance [PreservesColimitOfIsSplitPair G] : ∀ (A : Algebra adj.toMonad),
   PreservesColimit (parallelPair (F.map A.a)
      (NatTrans.app adj.counit (F.obj A.A))) G :=
  fun _ => PreservesColimitOfIsSplitPair.out _ _

-- Porting note: added these to replace parametric instances lean4#2311
-- [∀ ⦃A B⦄ (f g : A ⟶ B) [G.IsSplitPair f g], ReflectsColimit (parallelPair f g) G] :
class ReflectsColimitOfIsSplitPair (G : D ⥤ C) where
  out : ∀ {A B} (f g : A ⟶ B) [G.IsSplitPair f g], ReflectsColimit (parallelPair f g) G

instance {A B} (f g : A ⟶ B) [G.IsSplitPair f g] [ReflectsColimitOfIsSplitPair G] :
    ReflectsColimit (parallelPair f g) G := ReflectsColimitOfIsSplitPair.out f g

instance [ReflectsColimitOfIsSplitPair G] : ∀ (A : Algebra adj.toMonad),
    ReflectsColimit (parallelPair (F.map A.a)
      (NatTrans.app adj.counit (F.obj A.A))) G :=
  fun _ => ReflectsColimitOfIsSplitPair.out _ _

/-- To show `G` is a monadic right adjoint, we can show it preserves and reflects `G`-split
coequalizers, and `C` has them.
-/
def monadicOfHasPreservesReflectsGSplitCoequalizers [HasCoequalizerOfIsSplitPair G]
    [PreservesColimitOfIsSplitPair G] [ReflectsColimitOfIsSplitPair G] :
    MonadicRightAdjoint G where
  adj := adj
  eqv := by
    have : ∀ (X : Algebra adj.toMonad), IsIso ((comparisonAdjunction adj).unit.app X) := by
      intro X
      apply @isIso_of_reflects_iso _ _ _ _ _ _ _ (Monad.forget adj.toMonad) ?_ _
      · change IsIso ((comparisonAdjunction adj).unit.app X).f
        rw [comparisonAdjunction_unit_f]
        change
          IsIso
            (IsColimit.coconePointUniqueUpToIso (beckCoequalizer X)
                (unitColimitOfPreservesCoequalizer X)).hom
        exact (IsColimit.coconePointUniqueUpToIso _ _).isIso_hom
    have : ∀ (Y : D), IsIso ((comparisonAdjunction adj).counit.app Y) := by
      intro Y
      rw [comparisonAdjunction_counit_app]
      -- Porting note: passing instances through
      change IsIso (IsColimit.coconePointUniqueUpToIso _ ?_).hom
      infer_instance
      -- Porting note: passing instances through
      apply @counitCoequalizerOfReflectsCoequalizer _ _ _ _ _ _ _ _ ?_
      letI _ :
        G.IsSplitPair (F.map (G.map (adj.counit.app Y)))
          (adj.counit.app (F.obj (G.obj Y))) :=
        MonadicityInternal.main_pair_G_split _ ((comparison adj).obj Y)
      infer_instance
    exact (comparisonAdjunction adj).toEquivalence.isEquivalence_inverse
set_option linter.uppercaseLean3 false in
#align category_theory.monad.monadic_of_has_preserves_reflects_G_split_coequalizers CategoryTheory.Monad.monadicOfHasPreservesReflectsGSplitCoequalizers

-- Porting note: added these to replace parametric instances lean4#2311
-- [∀ ⦃A B⦄ (f g : A ⟶ B) [G.IsSplitPair f g], CreatesColimit (parallelPair f g) G] :
class CreatesColimitOfIsSplitPair (G : D ⥤ C) where
  out : ∀ {A B} (f g : A ⟶ B) [G.IsSplitPair f g], CreatesColimit (parallelPair f g) G

instance {A B} (f g : A ⟶ B) [G.IsSplitPair f g] [CreatesColimitOfIsSplitPair G] :
    CreatesColimit (parallelPair f g) G := CreatesColimitOfIsSplitPair.out f g

instance [CreatesColimitOfIsSplitPair G] : ∀ (A : Algebra adj.toMonad),
    CreatesColimit (parallelPair (F.map A.a)
      (NatTrans.app adj.counit (F.obj A.A))) G :=
  fun _ => CreatesColimitOfIsSplitPair.out _ _

/--
Beck's monadicity theorem. If `G` has a right adjoint and creates coequalizers of `G`-split pairs,
then it is monadic.
This is the converse of `createsGSplitOfMonadic`.
-/
def monadicOfCreatesGSplitCoequalizers [CreatesColimitOfIsSplitPair G] :
    MonadicRightAdjoint G := by
  let I {A B} (f g : A ⟶ B) [G.IsSplitPair f g] : HasColimit (parallelPair f g ⋙ G) := by
    apply @hasColimitOfIso _ _ _ _ _ _ ?_ (diagramIsoParallelPair.{v₁} _)
    exact inferInstanceAs <| HasCoequalizer (G.map f) (G.map g)
  have : HasCoequalizerOfIsSplitPair G := ⟨fun _ _ => hasColimit_of_created (parallelPair _ _) G⟩
  have : PreservesColimitOfIsSplitPair G := ⟨by intros; infer_instance⟩
  have : ReflectsColimitOfIsSplitPair G := ⟨by intros; infer_instance⟩
  exact monadicOfHasPreservesReflectsGSplitCoequalizers adj
set_option linter.uppercaseLean3 false in
#align category_theory.monad.monadic_of_creates_G_split_coequalizers CategoryTheory.Monad.monadicOfCreatesGSplitCoequalizers

/-- An alternate version of Beck's monadicity theorem. If `G` reflects isomorphisms, preserves
coequalizers of `G`-split pairs and `C` has coequalizers of `G`-split pairs, then it is monadic.
-/
def monadicOfHasPreservesGSplitCoequalizersOfReflectsIsomorphisms [G.ReflectsIsomorphisms]
    [HasCoequalizerOfIsSplitPair G] [PreservesColimitOfIsSplitPair G] :
    MonadicRightAdjoint G := by
  have : ReflectsColimitOfIsSplitPair G := ⟨fun f g _ => by
    have := HasCoequalizerOfIsSplitPair.out G f g
    apply reflectsColimitOfReflectsIsomorphisms⟩
  apply monadicOfHasPreservesReflectsGSplitCoequalizers adj
set_option linter.uppercaseLean3 false in
#align category_theory.monad.monadic_of_has_preserves_G_split_coequalizers_of_reflects_isomorphisms CategoryTheory.Monad.monadicOfHasPreservesGSplitCoequalizersOfReflectsIsomorphisms

end BeckMonadicity

section ReflexiveMonadicity

variable [HasReflexiveCoequalizers D] [G.ReflectsIsomorphisms]

-- Porting note: added these to replace parametric instances lean4#2311
-- [∀ ⦃A B⦄ (f g : A ⟶ B) [G.IsReflexivePair f g], PreservesColimit (parallelPair f g) G] :
class PreservesColimitOfIsReflexivePair (G : C ⥤ D) where
  out : ∀ ⦃A B⦄ (f g : A ⟶ B) [IsReflexivePair f g], PreservesColimit (parallelPair f g) G

instance {A B} (f g : A ⟶ B) [IsReflexivePair f g] [PreservesColimitOfIsReflexivePair G] :
  PreservesColimit (parallelPair f g) G := PreservesColimitOfIsReflexivePair.out f g

instance [PreservesColimitOfIsReflexivePair G] : ∀ X : Algebra adj.toMonad,
    PreservesColimit (parallelPair (F.map X.a)
      (NatTrans.app adj.counit (F.obj X.A))) G :=
 fun _ => PreservesColimitOfIsReflexivePair.out _ _

variable [PreservesColimitOfIsReflexivePair G]

/-- Reflexive (crude) monadicity theorem. If `G` has a right adjoint, `D` has and `G` preserves
reflexive coequalizers and `G` reflects isomorphisms, then `G` is monadic.
-/
def monadicOfHasPreservesReflexiveCoequalizersOfReflectsIsomorphisms : MonadicRightAdjoint G where
  adj := adj
  eqv := by
    have : ∀ (X : Algebra adj.toMonad), IsIso ((comparisonAdjunction adj).unit.app X) := by
      intro X
      apply
        @isIso_of_reflects_iso _ _ _ _ _ _ _ (Monad.forget adj.toMonad) ?_ _
      · change IsIso ((comparisonAdjunction adj).unit.app X).f
        rw [comparisonAdjunction_unit_f]
        exact (IsColimit.coconePointUniqueUpToIso (beckCoequalizer X)
          (unitColimitOfPreservesCoequalizer X)).isIso_hom
    have : ∀ (Y : D), IsIso ((comparisonAdjunction adj).counit.app Y) := by
      intro Y
      rw [comparisonAdjunction_counit_app]
      -- Porting note: passing instances through
      change IsIso (IsColimit.coconePointUniqueUpToIso _ ?_).hom
      infer_instance
      -- Porting note: passing instances through
      apply @counitCoequalizerOfReflectsCoequalizer _ _ _ _ _ _ _ _ ?_
      apply reflectsColimitOfReflectsIsomorphisms
    exact (comparisonAdjunction adj).toEquivalence.isEquivalence_inverse
#align category_theory.monad.monadic_of_has_preserves_reflexive_coequalizers_of_reflects_isomorphisms CategoryTheory.Monad.monadicOfHasPreservesReflexiveCoequalizersOfReflectsIsomorphisms

end ReflexiveMonadicity

end

end Monad

end CategoryTheory
