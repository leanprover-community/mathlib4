/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta

! This file was ported from Lean 3 source module category_theory.monad.monadicity
! leanprover-community/mathlib commit 4bd8c855d6ba8f0d5eefbf80c20fa00ee034dec9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Shapes.Reflexive
import Mathlib.CategoryTheory.Monad.Coequalizer
import Mathlib.CategoryTheory.Monad.Limits

/-!
# Monadicity theorems

We prove monadicity theorems which can establish a given functor is monadic. In particular, we
show three versions of Beck's monadicity theorem, and the reflexive (crude) monadicity theorem:

`G` is a monadic right adjoint if it has a right adjoint, and:

* `D` has, `G` preserves and reflects `G`-split coequalizers, see
  `category_theory.monad.monadic_of_has_preserves_reflects_G_split_coequalizers`
* `G` creates `G`-split coequalizers, see
  `category_theory.monad.monadic_of_creates_G_split_coequalizers`
  (The converse of this is also shown, see
   `category_theory.monad.creates_G_split_coequalizers_of_monadic`)
* `D` has and `G` preserves `G`-split coequalizers, and `G` reflects isomorphisms, see
  `category_theory.monad.monadic_of_has_preserves_G_split_coequalizers_of_reflects_isomorphisms`
* `D` has and `G` preserves reflexive coequalizers, and `G` reflects isomorphisms, see
  `category_theory.monad.monadic_of_has_preserves_reflexive_coequalizers_of_reflects_isomorphisms`

## Tags

Beck, monadicity, descent

## TODO

Dualise to show comonadicity theorems.
-/

-- Porting note: TODO remove
set_option autoImplicit false

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

namespace Monad

open Limits

noncomputable section

-- Hide the implementation details in this namespace.
namespace MonadicityInternal

section

variable {C : Type u₁} {D : Type u₂}

variable [Category.{v₁} C] [Category.{v₁} D]

variable {G : D ⥤ C} [IsRightAdjoint G]

-- Porting note: these were `local notation` in mathlib3. However, `abbrev` is not always
-- sufficient for synthesizing the right instances, so some occurrences have been inlined as a
-- temporary measure. All occurrences of `leftAdjoint G` and `Adjunction.ofRightAdjoint G` are the
-- result of inlining.
abbrev F := leftAdjoint G
abbrev adj := Adjunction.ofRightAdjoint G

/-- The "main pair" for an algebra `(A, α)` is the pair of morphisms `(F α, ε_FA)`. It is always a
reflexive pair, and will be used to construct the left adjoint to the comparison functor and show it
is an equivalence.
-/
instance main_pair_reflexive (A : (Adjunction.ofRightAdjoint G).toMonad.Algebra) :
    IsReflexivePair ((leftAdjoint G).map A.a) (adj.counit.app (F.obj A.A)) := by
  apply IsReflexivePair.mk' (F.map (adj.unit.app _)) _ _
  · rw [← F.map_comp, ← F.map_id]
    -- Porting note: used to be
    -- exact congr_arg (fun _ => F.map _) A.unit
    exact congr_arg F.map A.unit
  · rw [adj.left_triangle_components]
    rfl
#align category_theory.monad.monadicity_internal.main_pair_reflexive CategoryTheory.Monad.MonadicityInternal.main_pair_reflexive

/-- The "main pair" for an algebra `(A, α)` is the pair of morphisms `(F α, ε_FA)`. It is always a
`G`-split pair, and will be used to construct the left adjoint to the comparison functor and show it
is an equivalence.
-/
instance main_pair_G_split (A : (Adjunction.ofRightAdjoint G).toMonad.Algebra) :
    G.IsSplitPair ((leftAdjoint G).map A.a) ((Adjunction.ofRightAdjoint G).counit.app ((leftAdjoint G).obj A.A))
    where splittable := ⟨_, _, ⟨beckSplitCoequalizer A⟩⟩
set_option linter.uppercaseLean3 false in
#align category_theory.monad.monadicity_internal.main_pair_G_split CategoryTheory.Monad.MonadicityInternal.main_pair_G_split

/-- The object function for the left adjoint to the comparison functor. -/
def comparisonLeftAdjointObj (A : (Adjunction.ofRightAdjoint G).toMonad.Algebra)
    [HasCoequalizer ((leftAdjoint G).map A.a) ((Adjunction.ofRightAdjoint G).counit.app _)] : D :=
  coequalizer (F.map A.a) (adj.counit.app _)
#align category_theory.monad.monadicity_internal.comparison_left_adjoint_obj CategoryTheory.Monad.MonadicityInternal.comparisonLeftAdjointObj

/--
We have a bijection of homsets which will be used to construct the left adjoint to the comparison
functor.
-/
-- Porting note: changed `simps` to `simps!`
@[simps!]
def comparisonLeftAdjointHomEquiv (A : (Adjunction.ofRightAdjoint G).toMonad.Algebra) (B : D)
    [HasCoequalizer ((leftAdjoint G).map A.a) (adj.counit.app (F.obj A.A))] :
    (comparisonLeftAdjointObj A ⟶ B) ≃ (A ⟶ (comparison adj).obj B) :=
  calc
    (comparisonLeftAdjointObj A ⟶ B) ≃ { f : F.obj A.A ⟶ B // _ } :=
      Cofork.IsColimit.homIso (colimit.isColimit _) B
    _ ≃ { g : A.A ⟶ G.obj B // G.map (F.map g) ≫ G.map (adj.counit.app B) = A.a ≫ g } := by
      refine' ((Adjunction.ofRightAdjoint G).homEquiv _ _).subtypeEquiv _
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
    [∀ A : adj.toMonad.Algebra, HasCoequalizer ((leftAdjoint G).map A.a)
      (adj.counit.app (F.obj A.A))] :
    (Adjunction.ofRightAdjoint G).toMonad.Algebra ⥤ D := by
  refine'
    Adjunction.leftAdjointOfEquiv (G := comparison adj)
      (F_obj := fun A => comparisonLeftAdjointObj A) (fun A B => _) _
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
-- Porting note: changed `simps` to `simps!`
@[simps! counit]
def comparisonAdjunction
    [∀ A : (Adjunction.ofRightAdjoint G).toMonad.Algebra, HasCoequalizer ((leftAdjoint G).map A.a)
      ((Adjunction.ofRightAdjoint G).counit.app ((leftAdjoint G).obj A.A))] :
    leftAdjointComparison ⊣ comparison (Adjunction.ofRightAdjoint G) :=
  Adjunction.adjunctionOfEquivLeft _ _
#align category_theory.monad.monadicity_internal.comparison_adjunction CategoryTheory.Monad.MonadicityInternal.comparisonAdjunction

theorem comparisonAdjunction_unit_f_aux
    [∀ A : (Adjunction.ofRightAdjoint G).toMonad.Algebra, HasCoequalizer ((leftAdjoint G).map A.a)
      ((Adjunction.ofRightAdjoint G).counit.app ((leftAdjoint G).obj A.A))]
    (A : (Adjunction.ofRightAdjoint G).toMonad.Algebra) :
    (comparisonAdjunction.unit.app A).f =
      (Adjunction.ofRightAdjoint G).homEquiv A.A _
        (coequalizer.π (F.map A.a) (adj.counit.app (F.obj A.A))) :=
  congr_arg (adj.homEquiv _ _) (Category.comp_id _)
#align category_theory.monad.monadicity_internal.comparison_adjunction_unit_f_aux CategoryTheory.Monad.MonadicityInternal.comparisonAdjunction_unit_f_aux

/-- This is a cofork which is helpful for establishing monadicity: the morphism from the Beck
coequalizer to this cofork is the unit for the adjunction on the comparison functor.
-/
-- Porting note: changed `simps` to `simps!`
@[simps! pt]
def unitCofork (A : adj.toMonad.Algebra) [HasCoequalizer (F.map A.a) (adj.counit.app (F.obj A.A))] :
    Cofork (G.map (F.map A.a)) (G.map (adj.counit.app ((leftAdjoint G).obj A.A))) :=
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
    [∀ A : (Adjunction.ofRightAdjoint G).toMonad.Algebra, HasCoequalizer (F.map A.a)
      (adj.counit.app (F.obj A.A))]
    (A : (Adjunction.ofRightAdjoint G).toMonad.Algebra) :
    (comparisonAdjunction.unit.app A).f = (beckCoequalizer A).desc (unitCofork A) := by
  apply Limits.Cofork.IsColimit.hom_ext (beckCoequalizer A)
  rw [Cofork.IsColimit.π_desc]
  dsimp only [beckCofork_π, unitCofork_π]
  rw [comparisonAdjunction_unit_f_aux, ← adj.homEquiv_naturality_left A.a, coequalizer.condition,
    adj.homEquiv_naturality_right, adj.homEquiv_unit, Category.assoc]
  apply adj.right_triangle_components_assoc
#align category_theory.monad.monadicity_internal.comparison_adjunction_unit_f CategoryTheory.Monad.MonadicityInternal.comparisonAdjunction_unit_f

/-- The cofork which describes the counit of the adjunction: the morphism from the coequalizer of
this pair to this morphism is the counit.
-/
-- Porting note: changed `simps` to `simps!`
@[simps!]
def counitCofork (B : D) :
    Cofork ((leftAdjoint G).map (G.map ((Adjunction.ofRightAdjoint G).counit.app B))) ((Adjunction.ofRightAdjoint G).counit.app ((leftAdjoint G).obj (G.obj B))) :=
  Cofork.ofπ (adj.counit.app B) (adj.counit_naturality _)
#align category_theory.monad.monadicity_internal.counit_cofork CategoryTheory.Monad.MonadicityInternal.counitCofork

/-- The unit cofork is a colimit provided `G` preserves it.  -/
def unitColimitOfPreservesCoequalizer (A : adj.toMonad.Algebra)
    [HasCoequalizer ((leftAdjoint G).map A.a) (adj.counit.app ((leftAdjoint G).obj A.A))]
    [PreservesColimit (parallelPair (F.map A.a) (adj.counit.app ((leftAdjoint G).obj A.A))) G] :
    IsColimit (unitCofork (G := G) A) :=
  isColimitOfHasCoequalizerOfPreservesColimit G _ _
#align category_theory.monad.monadicity_internal.unit_colimit_of_preserves_coequalizer CategoryTheory.Monad.MonadicityInternal.unitColimitOfPreservesCoequalizer

/-- The counit cofork is a colimit provided `G` reflects it. -/
def counitCoequalizerOfReflectsCoequalizer (B : D)
    [ReflectsColimit
        (parallelPair ((leftAdjoint G).map (G.map (adj.counit.app B))) (adj.counit.app ((leftAdjoint G).obj (G.obj B)))) G] :
    IsColimit (counitCofork (G := G) B) :=
  isColimitOfIsColimitCoforkMap G _ (beckCoequalizer ((comparison adj).obj B))
#align category_theory.monad.monadicity_internal.counit_coequalizer_of_reflects_coequalizer CategoryTheory.Monad.MonadicityInternal.counitCoequalizerOfReflectsCoequalizer

variable  [∀ A : (Adjunction.ofRightAdjoint G).toMonad.Algebra, HasCoequalizer ((leftAdjoint G).map A.a) ((Adjunction.ofRightAdjoint G).counit.app ((leftAdjoint G).obj A.A))] (B : D)

-- Porting note: Lean 3 didn't seem to need this
instance : HasColimit
    (parallelPair ((leftAdjoint G).map (G.map (NatTrans.app (Adjunction.ofRightAdjoint G).counit B)))
      (NatTrans.app (Adjunction.ofRightAdjoint G).counit ((leftAdjoint G).obj (G.obj B)))) :=
  inferInstanceAs <| HasCoequalizer
    ((leftAdjoint G).map ((comparison (Adjunction.ofRightAdjoint G)).obj B).a)
    ((Adjunction.ofRightAdjoint G).counit.app ((leftAdjoint G).obj
      ((comparison (Adjunction.ofRightAdjoint G)).obj B).A))
  --
theorem comparisonAdjunction_counit_app
    [∀ A : (Adjunction.ofRightAdjoint G).toMonad.Algebra, HasCoequalizer ((leftAdjoint G).map A.a) ((Adjunction.ofRightAdjoint G).counit.app ((leftAdjoint G).obj A.A))] (B : D) :
    (comparisonAdjunction (G := G)).counit.app B = colimit.desc _ (counitCofork B) := by
  apply coequalizer.hom_ext
  change
    coequalizer.π _ _ ≫ coequalizer.desc ((adj.homEquiv _ B).symm (𝟙 _)) _ =
      coequalizer.π _ _ ≫ coequalizer.desc _ _
  simp
#align category_theory.monad.monadicity_internal.comparison_adjunction_counit_app CategoryTheory.Monad.MonadicityInternal.comparisonAdjunction_counit_app

end

end MonadicityInternal

open CategoryTheory.Adjunction

open MonadicityInternal

variable {C : Type u₁} {D : Type u₂}

variable [Category.{v₁} C] [Category.{v₁} D]

variable (G : D ⥤ C)

/--
If `G` is monadic, it creates colimits of `G`-split pairs. This is the "boring" direction of Beck's
monadicity theorem, the converse is given in `monadic_of_creates_G_split_coequalizers`.
-/
def createsGSplitCoequalizersOfMonadic [MonadicRightAdjoint G] ⦃A B⦄ (f g : A ⟶ B)
    [G.IsSplitPair f g] : CreatesColimit (parallelPair f g) G := by
  apply (config := {allowSynthFailures := true}) monadicCreatesColimitOfPreservesColimit
    -- Porting note: apparently cannot do synth failures here?
  · apply @preservesColimitOfIsoDiagram _ _ _ _ _ _ _ _ _ (diagramIsoParallelPair.{v₁} _).symm ?_
    dsimp
    infer_instance
  · apply @preservesColimitOfIsoDiagram _ _ _ _ _ _ _ _ _ (diagramIsoParallelPair.{v₁} _).symm ?_
    dsimp
    infer_instance
set_option linter.uppercaseLean3 false in
#align category_theory.monad.creates_G_split_coequalizers_of_monadic CategoryTheory.Monad.createsGSplitCoequalizersOfMonadic

variable [IsRightAdjoint G]

section BeckMonadicity

-- Porting note: added these to replace parametetric instances lean4#2311
-- [∀ ⦃A B⦄ (f g : A ⟶ B) [G.IsSplitPair f g], HasCoequalizer f g]
class HasCoequalizerOfIsSplitPair (G : D ⥤ C) where
  out : ∀ {A B} (f g : A ⟶ B) [G.IsSplitPair f g], HasCoequalizer f g

-- Porting note: cannot find synth order
-- instance {A B} (f g : A ⟶  B) [G.IsSplitPair f g] [HasCoequalizerOfIsSplitPair G] :
--     HasCoequalizer f g := HasCoequalizerOfIsSplitPair.out f g

instance [HasCoequalizerOfIsSplitPair G] : ∀ (A : Algebra (toMonad (ofRightAdjoint G))),
    HasCoequalizer ((leftAdjoint G).map A.a)
      ((ofRightAdjoint G).counit.app ((leftAdjoint G).obj A.A)) :=
  fun _ => HasCoequalizerOfIsSplitPair.out G _ _

-- Porting note: added these to replace parametetric instances lean4#2311
-- [∀ ⦃A B⦄ (f g : A ⟶ B) [G.IsSplitPair f g], PreservesColimit (parallelPair f g) G]
class PreservesColimitOfIsSplitPair (G : D ⥤ C) where
  out : ∀ {A B} (f g : A ⟶ B) [G.IsSplitPair f g], PreservesColimit (parallelPair f g) G

instance {A B} (f g : A ⟶  B) [G.IsSplitPair f g] [PreservesColimitOfIsSplitPair G] :
    PreservesColimit (parallelPair f g) G := PreservesColimitOfIsSplitPair.out f g

instance [PreservesColimitOfIsSplitPair G] : ∀ (A: Algebra (toMonad (ofRightAdjoint G))),
    PreservesColimit (parallelPair (F.map A.a)
      (NatTrans.app MonadicityInternal.adj.counit ((leftAdjoint G).obj A.A))) G :=
  fun _ => PreservesColimitOfIsSplitPair.out _ _

-- Porting note: added these to replace parametetric instances lean4#2311
-- [∀ ⦃A B⦄ (f g : A ⟶ B) [G.IsSplitPair f g], ReflectsColimit (parallelPair f g) G] :
class ReflectsColimitOfIsSplitPair (G : D ⥤ C) where
  out : ∀ {A B} (f g : A ⟶ B) [G.IsSplitPair f g], ReflectsColimit (parallelPair f g) G

instance {A B} (f g : A ⟶  B) [G.IsSplitPair f g] [ReflectsColimitOfIsSplitPair G] :
    ReflectsColimit (parallelPair f g) G := ReflectsColimitOfIsSplitPair.out f g

instance [ReflectsColimitOfIsSplitPair G] : ∀ (A: Algebra (toMonad (ofRightAdjoint G))),
    ReflectsColimit (parallelPair (F.map A.a)
      (NatTrans.app MonadicityInternal.adj.counit ((leftAdjoint G).obj A.A))) G :=
  fun _ => ReflectsColimitOfIsSplitPair.out _ _

/-- To show `G` is a monadic right adjoint, we can show it preserves and reflects `G`-split
coequalizers, and `C` has them.
-/
def monadicOfHasPreservesReflectsGSplitCoequalizers [HasCoequalizerOfIsSplitPair G]
    [PreservesColimitOfIsSplitPair G] [ReflectsColimitOfIsSplitPair G] : MonadicRightAdjoint G := by
  let L : (Adjunction.ofRightAdjoint G).toMonad.Algebra ⥤ D := leftAdjointComparison
  let i : IsRightAdjoint (comparison (ofRightAdjoint G)) := ⟨_, comparisonAdjunction⟩
  constructor
  let _ : ∀ X : (ofRightAdjoint G).toMonad.Algebra,
      IsIso ((ofRightAdjoint (comparison (ofRightAdjoint G))).unit.app X) := by
    intro X
    apply @isIso_of_reflects_iso _ _ _ _ _ _ _ (Monad.forget (ofRightAdjoint G).toMonad) ?_ _
    · change IsIso (comparisonAdjunction.unit.app X).f
      rw [comparisonAdjunction_unit_f]
      change
        IsIso
          (IsColimit.coconePointUniqueUpToIso (beckCoequalizer X)
              (unitColimitOfPreservesCoequalizer X)).hom
      refine' IsIso.of_iso (IsColimit.coconePointUniqueUpToIso _ _)
  let _ : ∀ Y : D, IsIso ((ofRightAdjoint (comparison (ofRightAdjoint G))).counit.app Y) := by
    intro Y
    change IsIso (comparisonAdjunction.counit.app Y)
    rw [comparisonAdjunction_counit_app]
    change IsIso (IsColimit.coconePointUniqueUpToIso _ _).hom
    infer_instance
    apply counitCoequalizerOfReflectsCoequalizer _
    letI _ :
      G.IsSplitPair ((leftAdjoint G).map (G.map ((Adjunction.ofRightAdjoint G).counit.app Y)))
        ((Adjunction.ofRightAdjoint G).counit.app ((leftAdjoint G).obj (G.obj Y))) :=
      MonadicityInternal.main_pair_G_split ((comparison (Adjunction.ofRightAdjoint G)).obj Y)
    infer_instance
  exact Adjunction.isRightAdjointToIsEquivalence
set_option linter.uppercaseLean3 false in
#align category_theory.monad.monadic_of_has_preserves_reflects_G_split_coequalizers CategoryTheory.Monad.monadicOfHasPreservesReflectsGSplitCoequalizers

-- Porting note: added these to replace parametetric instances lean4#2311
-- [∀ ⦃A B⦄ (f g : A ⟶ B) [G.IsSplitPair f g], CreatesColimit (parallelPair f g) G] :
class CreatesColimitOfIsSplitPair (G : D ⥤ C) where
  out : ∀ {A B} (f g : A ⟶ B) [G.IsSplitPair f g], CreatesColimit (parallelPair f g) G

instance {A B} (f g : A ⟶  B) [G.IsSplitPair f g] [CreatesColimitOfIsSplitPair G] :
    CreatesColimit (parallelPair f g) G := CreatesColimitOfIsSplitPair.out f g

instance [CreatesColimitOfIsSplitPair G] : ∀ (A: Algebra (toMonad (ofRightAdjoint G))),
    CreatesColimit (parallelPair (F.map A.a)
      (NatTrans.app MonadicityInternal.adj.counit ((leftAdjoint G).obj A.A))) G :=
  fun _ => CreatesColimitOfIsSplitPair.out _ _

/--
Beck's monadicity theorem. If `G` has a right adjoint and creates coequalizers of `G`-split pairs,
then it is monadic.
This is the converse of `creates_G_split_of_monadic`.
-/
def monadicOfCreatesGSplitCoequalizers [CreatesColimitOfIsSplitPair G] :
    MonadicRightAdjoint G := by
  let I {A B} (f g : A ⟶ B) [G.IsSplitPair f g] : HasColimit (parallelPair f g ⋙ G) := by
    apply @hasColimitOfIso _ _ _ _ _ _ ?_ (diagramIsoParallelPair.{v₁} _)
    change HasCoequalizer (G.map f) (G.map g)
    infer_instance
  apply @monadicOfHasPreservesReflectsGSplitCoequalizers _ _ _ _ _ ?_ ?_ ?_ ?_
  · infer_instance
  · constructor
    intros
    apply hasColimit_of_created (parallelPair _ _) G
  · constructor
    intros
    infer_instance
  · constructor
    intros
    infer_instance
set_option linter.uppercaseLean3 false in
#align category_theory.monad.monadic_of_creates_G_split_coequalizers CategoryTheory.Monad.monadicOfCreatesGSplitCoequalizers

/-- An alternate version of Beck's monadicity theorem. If `G` reflects isomorphisms, preserves
coequalizers of `G`-split pairs and `C` has coequalizers of `G`-split pairs, then it is monadic.
-/
def monadicOfHasPreservesGSplitCoequalizersOfReflectsIsomorphisms [ReflectsIsomorphisms G]
    [HasCoequalizerOfIsSplitPair G] [PreservesColimitOfIsSplitPair G] :
    MonadicRightAdjoint G := by
  apply @monadicOfHasPreservesReflectsGSplitCoequalizers _ _ _ _ _ ?_ ?_ ?_ ?_
  · infer_instance
  · assumption
  · assumption
  · constructor
    intro _ _ f g _
    have := HasCoequalizerOfIsSplitPair.out G f g
    apply reflectsColimitOfReflectsIsomorphisms
set_option linter.uppercaseLean3 false in
#align category_theory.monad.monadic_of_has_preserves_G_split_coequalizers_of_reflects_isomorphisms CategoryTheory.Monad.monadicOfHasPreservesGSplitCoequalizersOfReflectsIsomorphisms

end BeckMonadicity

section ReflexiveMonadicity

variable [HasReflexiveCoequalizers D] [ReflectsIsomorphisms G]

-- Porting note: added these to replace parametetric instances lean4#2311
-- [∀ ⦃A B⦄ (f g : A ⟶ B) [G.IsReflexivePair f g], PreservesColimit (parallelPair f g) G] :
class PreservesColimitOfIsReflexivePair (G : C ⥤ D) where
  out :∀ ⦃A B⦄ (f g : A ⟶ B) [IsReflexivePair f g], PreservesColimit (parallelPair f g) G

instance [PreservesColimitOfIsReflexivePair G] : ∀ X : Algebra (toMonad (ofRightAdjoint G)),
    PreservesColimit (parallelPair (F.map X.a)
      (NatTrans.app MonadicityInternal.adj.counit ((leftAdjoint G).obj X.A))) G :=
 fun _ => PreservesColimitOfIsReflexivePair.out _ _

variable [PreservesColimitOfIsReflexivePair G]

/-- Reflexive (crude) monadicity theorem. If `G` has a right adjoint, `D` has and `G` preserves
reflexive coequalizers and `G` reflects isomorphisms, then `G` is monadic.
-/
def monadicOfHasPreservesReflexiveCoequalizersOfReflectsIsomorphisms : MonadicRightAdjoint G := by
  let L : (Adjunction.ofRightAdjoint G).toMonad.Algebra ⥤ D := leftAdjointComparison
  letI i : IsRightAdjoint (comparison (Adjunction.ofRightAdjoint G)) :=
    ⟨_, comparisonAdjunction⟩
  constructor
  let _ :
    ∀ X : (Adjunction.ofRightAdjoint G).toMonad.Algebra,
      IsIso
        ((Adjunction.ofRightAdjoint (comparison (Adjunction.ofRightAdjoint G))).unit.app X) :=
    by
    intro X
    apply
      @isIso_of_reflects_iso _ _ _ _ _ _ _ (Monad.forget (Adjunction.ofRightAdjoint G).toMonad) ?_ _
    · change IsIso (comparisonAdjunction.unit.app X).f
      rw [comparisonAdjunction_unit_f]
      change
        IsIso
          (IsColimit.coconePointUniqueUpToIso (beckCoequalizer X)
              (unitColimitOfPreservesCoequalizer X)).hom
      apply IsIso.of_iso (IsColimit.coconePointUniqueUpToIso _ _)
  let _ :
    ∀ Y : D,
      IsIso ((ofRightAdjoint (comparison (Adjunction.ofRightAdjoint G))).counit.app Y) := by
    intro Y
    change IsIso (comparisonAdjunction.counit.app Y)
    rw [comparisonAdjunction_counit_app]
    change IsIso (IsColimit.coconePointUniqueUpToIso _ _).hom
    infer_instance
    apply counitCoequalizerOfReflectsCoequalizer _
    apply reflectsColimitOfReflectsIsomorphisms
  exact Adjunction.isRightAdjointToIsEquivalence
#align category_theory.monad.monadic_of_has_preserves_reflexive_coequalizers_of_reflects_isomorphisms CategoryTheory.Monad.monadicOfHasPreservesReflexiveCoequalizersOfReflectsIsomorphisms

end ReflexiveMonadicity

end

end Monad

end CategoryTheory
