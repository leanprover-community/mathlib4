/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Shapes.Reflexive
import Mathlib.CategoryTheory.Monad.Equalizer
import Mathlib.CategoryTheory.Monad.Limits

/-!
# Comonadicity theorems

We prove comonadicity theorems which can establish a given functor is comonadic. In particular, we
show three versions of Beck's comonadicity theorem, and the coreflexive (crude) comonadicity theorem:

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

Beck, comonadicity, descent

-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

namespace Comonad

open Limits

noncomputable section

-- Hide the implementation details in this namespace.
namespace ComonadicityInternal

variable {C : Type u₁} {D : Type u₂}
variable [Category.{v₁} C] [Category.{v₁} D]
variable {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)

/-- The "main pair" for a coalgebra `(A, α)` is the pair of morphisms `(F α, ε_FA)`. It is always a
reflexive pair, and will be used to construct the left adjoint to the comparison functor and show it
is an equivalence.
-/
instance main_pair_coreflexive (A : adj.toComonad.Coalgebra) :
    IsCoreflexivePair (G.map A.a) (adj.unit.app (G.obj A.A)) := by
  apply IsCoreflexivePair.mk' (G.map (adj.counit.app _)) _ _
  · rw [← G.map_comp, ← G.map_id]
    exact congr_arg G.map A.counit
  · rw [adj.right_triangle_components]
    rfl

/-- The "main pair" for a coalgebra `(A, α)` is the pair of morphisms `(F α, ε_FA)`. It is always a
`G`-split pair, and will be used to construct the left adjoint to the comparison functor and show it
is an equivalence.
-/
instance main_pair_F_cosplit (A : adj.toComonad.Coalgebra) :
    F.IsCosplitPair (G.map A.a)
      (adj.unit.app (G.obj A.A)) where
  splittable := ⟨_, _, ⟨beckSplitEqualizer A⟩⟩

/-- The object function for the right adjoint to the comparison functor. -/
def comparisonRightAdjointObj (A : adj.toComonad.Coalgebra)
    [HasEqualizer (G.map A.a) (adj.unit.app _)] : C :=
  equalizer (G.map A.a) (adj.unit.app _)

--TODO: CLEAN THIS UP!
/--
We have a bijection of homsets which will be used to construct the right adjoint to the comparison
functor.
-/
@[simps!]
def comparisonRightAdjointHomEquiv (A : adj.toComonad.Coalgebra) (B : C)
    [HasEqualizer (G.map A.a) (adj.unit.app (G.obj A.A))] :
    ((comparison adj).obj B ⟶ A) ≃ (B ⟶ comparisonRightAdjointObj adj A) where
      toFun f := by
        refine equalizer.lift (adj.homEquiv _ _ f.f) ?_
        simp only [Adjunction.toComonad_coe, Functor.comp_obj, Adjunction.homEquiv_unit,
          Functor.id_obj, Category.assoc, ← G.map_comp, ← f.h]
        simp
      invFun f := by
        refine ⟨(adj.homEquiv _ _).symm (f ≫ (equalizer.ι _ _)), ?_⟩
        apply (adj.homEquiv _ _).injective
        simp only [Adjunction.toComonad_coe, Functor.comp_obj, comparison_obj_A, comparison_obj_a,
          Adjunction.homEquiv_counit, Functor.id_obj, Functor.map_comp, Category.assoc,
          Functor.comp_map, Adjunction.homEquiv_unit, Adjunction.unit_naturality_assoc,
          Adjunction.unit_naturality, Adjunction.right_triangle_components_assoc]
        congr 1
        symm
        apply equalizer.condition
      left_inv f := by aesop
      right_inv f := by apply equalizer.hom_ext; simp

/-- Construct the adjunction to the comparison functor.
-/
def rightAdjointComparison
    [∀ A : adj.toComonad.Coalgebra, HasEqualizer (G.map A.a)
      (adj.unit.app (G.obj A.A))] :
    adj.toComonad.Coalgebra ⥤ C := by
  refine
    Adjunction.rightAdjointOfEquiv (F := comparison adj)
      (G_obj := fun A => comparisonRightAdjointObj adj A) (fun A B => ?_) ?_
  · apply comparisonRightAdjointHomEquiv
  · intro A B B' g h
    apply equalizer.hom_ext
    simp

/-- Provided we have the appropriate equalizers, we have an adjunction to the comparison functor.
-/
@[simps! counit]
def comparisonAdjunction
    [∀ A : adj.toComonad.Coalgebra, HasEqualizer (G.map A.a)
      (adj.unit.app (G.obj A.A))] :
    comparison adj ⊣ rightAdjointComparison adj :=
  Adjunction.adjunctionOfEquivRight _ _

variable {adj}

theorem comparisonAdjunction_counit_f_aux
    [∀ A : adj.toComonad.Coalgebra, HasEqualizer (G.map A.a)
      (adj.unit.app (G.obj A.A))]
    (A : adj.toComonad.Coalgebra) :
    ((comparisonAdjunction adj).counit.app A).f =
      (adj.homEquiv _ A.A).symm (equalizer.ι (G.map A.a) (adj.unit.app (G.obj A.A))) :=
  congr_arg (adj.homEquiv _ _).symm (Category.id_comp _)

/-- This is a fork which is helpful for establishing comonadicity: the morphism from the Beck
equalizer to this fork is the counit for the adjunction on the comparison functor.
-/
@[simps! pt]
def counitFork (A : adj.toComonad.Coalgebra)
    [HasEqualizer (G.map A.a) (adj.unit.app (G.obj A.A))] :
    Fork (F.map (G.map A.a)) (F.map (adj.unit.app (G.obj A.A))) :=
  Fork.ofι (F.map (equalizer.ι (G.map A.a) (adj.unit.app (G.obj A.A))))
    (by
      change _ = F.map _ ≫ _
      rw [← F.map_comp, equalizer.condition, F.map_comp])

@[simp]
theorem unitFork_ι (A : adj.toComonad.Coalgebra)
    [HasEqualizer (G.map A.a) (adj.unit.app (G.obj A.A))] :
    (counitFork A).ι = F.map (equalizer.ι (G.map A.a) (adj.unit.app (G.obj A.A))) :=
  rfl

theorem comparisonAdjunction_counit_f
    [∀ A : adj.toComonad.Coalgebra, HasEqualizer (G.map A.a)
      (adj.unit.app (G.obj A.A))]
    (A : adj.toComonad.Coalgebra) :
    ((comparisonAdjunction adj).counit.app A).f = (beckEqualizer A).lift (counitFork A) := by
  simp

variable (adj)

/-- The fork which describes the unit of the adjunction: the morphism from the equalizer of
this pair to this morphism is the unit.
-/
@[simps!]
def unitFork (B : C) :
    Fork (G.map (F.map (adj.unit.app B)))
      (adj.unit.app (G.obj (F.obj B))) :=
  Fork.ofι (adj.unit.app B) (adj.unit_naturality _)

variable {adj} in
/-- The counit fork is a limit provided `F` preserves it.  -/
def counitLimitOfPreservesEqualizer (A : adj.toComonad.Coalgebra)
    [HasEqualizer (G.map A.a) (adj.unit.app (G.obj A.A))]
    [PreservesLimit (parallelPair (G.map A.a) (adj.unit.app (G.obj A.A))) F] :
    IsLimit (counitFork (G := G) A) :=
  isLimitOfHasEqualizerOfPreservesLimit F _ _

/-- The unit fork is a colimit provided `G` reflects it. -/
def unitEqualizerOfCoreflectsEqualizer (B : C)
    [ReflectsLimit (parallelPair (G.map (F.map (adj.unit.app B)))
      (adj.unit.app (G.obj (F.obj B)))) F] :
    IsLimit (unitFork (adj := adj) B) :=
  isLimitOfIsLimitForkMap F _ (beckEqualizer ((comparison adj).obj B))

-- Porting note: Lean 3 didn't seem to need this
instance
    [∀ A : adj.toComonad.Coalgebra, HasEqualizer (G.map A.a) (adj.unit.app (G.obj A.A))]
    (B : C) : HasLimit (parallelPair
      (G.map (F.map (NatTrans.app adj.unit B)))
      (NatTrans.app adj.unit (G.obj (F.obj B)))) :=
  inferInstanceAs <| HasEqualizer
    (G.map ((comparison adj).obj B).a)
    (adj.unit.app (G.obj ((comparison adj).obj B).A))

theorem comparisonAdjunction_unit_app
    [∀ A : adj.toComonad.Coalgebra, HasEqualizer (G.map A.a) (adj.unit.app (G.obj A.A))] (B : C) :
    (comparisonAdjunction adj).unit.app B = limit.lift _ (unitFork adj B) := by
  apply equalizer.hom_ext
  change
    equalizer.lift ((adj.homEquiv B _) (𝟙 _)) _ ≫ equalizer.ι _ _ =
      equalizer.lift _ _ ≫ equalizer.ι _ _
  simp

end ComonadicityInternal

open CategoryTheory Adjunction Comonad ComonadicityInternal

variable {C : Type u₁} {D : Type u₂}
variable [Category.{v₁} C] [Category.{v₁} D]
variable {G : D ⥤ C} {F : C ⥤ D} (adj : F ⊣ G)

-- TODO: dualise `CategoryTheory.Monad.Limits`
variable (G) in
/--
If `F` is comonadic, it creates limits of `F`-cosplit pairs. This is the "boring" direction of Beck's
comonadicity theorem, the converse is given in `comonadicOfCreatesGSplitEqualizers`.
-/
def createsGSplitEqualizersOfComonadic [ComonadicLeftAdjoint F] ⦃A B⦄ (f g : A ⟶ B)
    [F.IsCosplitPair f g] : CreatesLimit (parallelPair f g) F := by
  apply (config := {allowSynthFailures := true}) comonadicCreatesLimitOfPreservesLimit
    -- Porting note: oddly (config := {allowSynthFailures := true}) had no effect here and below
  · apply @preservesLimitOfIsoDiagram _ _ _ _ _ _ _ _ _ (diagramIsoParallelPair.{v₁} _).symm ?_
    dsimp
    infer_instance
  · apply @preservesLimitOfIsoDiagram _ _ _ _ _ _ _ _ _ (diagramIsoParallelPair.{v₁} _).symm ?_
    dsimp
    infer_instance

section BeckComonadicity

-- [∀ ⦃A B⦄ (f g : A ⟶ B) [G.IsCosplitPair f g], HasEqualizer f g]
class HasEqualizerOfIsCosplitPair (G : D ⥤ C) : Prop where
  out : ∀ {A B} (f g : A ⟶ B) [G.IsCosplitPair f g], HasEqualizer f g

-- Porting note: cannot find synth order
-- instance {A B} (f g : A ⟶ B) [G.IsSplitPair f g] [HasCoequalizerOfIsSplitPair G] :
--     HasCoequalizer f g := HasCoequalizerOfIsSplitPair.out f g

instance [HasEqualizerOfIsCosplitPair F] : ∀ (A : Coalgebra adj.toComonad),
    HasEqualizer (G.map A.a)
      (adj.unit.app (G.obj A.A)) :=
  fun _ => HasEqualizerOfIsCosplitPair.out F _ _

-- Porting note: added these to replace parametric instances lean4#2311
-- [∀ ⦃A B⦄ (f g : A ⟶ B) [G.IsCosplitPair f g], PreservesLimit (parallelPair f g) G]
class PreservesLimitOfIsCosplitPair (G : D ⥤ C) where
  out : ∀ {A B} (f g : A ⟶ B) [G.IsCosplitPair f g], PreservesLimit (parallelPair f g) G

instance {A B} (f g : A ⟶ B) [G.IsCosplitPair f g] [PreservesLimitOfIsCosplitPair G] :
    PreservesLimit (parallelPair f g) G := PreservesLimitOfIsCosplitPair.out f g

instance [PreservesLimitOfIsCosplitPair F] : ∀ (A : Coalgebra adj.toComonad),
   PreservesLimit (parallelPair (G.map A.a)
      (NatTrans.app adj.unit (G.obj A.A))) F :=
  fun _ => PreservesLimitOfIsCosplitPair.out _ _

-- Porting note: added these to replace parametric instances lean4#2311
-- [∀ ⦃A B⦄ (f g : A ⟶ B) [G.IsCosplitPair f g], ReflectsLimit (parallelPair f g) G] :
class ReflectsLimitOfIsCosplitPair (G : D ⥤ C) where
  out : ∀ {A B} (f g : A ⟶ B) [G.IsCosplitPair f g], ReflectsLimit (parallelPair f g) G

instance {A B} (f g : A ⟶ B) [G.IsCosplitPair f g] [ReflectsLimitOfIsCosplitPair G] :
    ReflectsLimit (parallelPair f g) G := ReflectsLimitOfIsCosplitPair.out f g

instance [ReflectsLimitOfIsCosplitPair F] : ∀ (A : Coalgebra adj.toComonad),
    ReflectsLimit (parallelPair (G.map A.a)
      (NatTrans.app adj.unit (G.obj A.A))) F :=
  fun _ => ReflectsLimitOfIsCosplitPair.out _ _

/-- To show `F` is a comonadic left adjoint, we can show it preserves and reflects `F`-split
equalizers, and `C` has them.
-/
def comonadicOfHasPreservesReflectsGSplitEqualizers [HasEqualizerOfIsCosplitPair F]
    [PreservesLimitOfIsCosplitPair F] [ReflectsLimitOfIsCosplitPair F] :
    ComonadicLeftAdjoint F where
  adj := adj
  eqv := by
    have : ∀ (X : Coalgebra adj.toComonad), IsIso ((comparisonAdjunction adj).counit.app X) := by
      intro X
      apply @isIso_of_reflects_iso _ _ _ _ _ _ _ (Comonad.forget adj.toComonad) ?_ _
      · change IsIso ((comparisonAdjunction adj).counit.app X).f
        rw [comparisonAdjunction_counit_f]
        change
          IsIso
            (IsLimit.conePointUniqueUpToIso (beckEqualizer X)
                (counitLimitOfPreservesEqualizer X)).inv
        exact (IsLimit.conePointUniqueUpToIso _ _).isIso_inv
    have : ∀ (Y : C), IsIso ((comparisonAdjunction adj).unit.app Y) := by
      intro Y
      rw [comparisonAdjunction_unit_app]
      -- Porting note: passing instances through
      change IsIso (IsLimit.conePointUniqueUpToIso _ ?_).inv
      infer_instance
      -- Porting note: passing instances through
      apply @unitEqualizerOfCoreflectsEqualizer _ _ _ _ _ _ _ _ ?_
      letI _ :
        F.IsCosplitPair (G.map (F.map (adj.unit.app Y)))
          (adj.unit.app (G.obj (F.obj Y))) :=
        ComonadicityInternal.main_pair_F_cosplit _ ((comparison adj).obj Y)
      infer_instance
    exact (comparisonAdjunction adj).toEquivalence.symm.isEquivalence_inverse

-- Porting note: added these to replace parametric instances lean4#2311
-- [∀ ⦃A B⦄ (f g : A ⟶ B) [G.IsCosplitPair f g], CreatesLimit (parallelPair f g) G] :
class CreatesLimitOfIsCosplitPair (G : D ⥤ C) where
  out : ∀ {A B} (f g : A ⟶ B) [G.IsCosplitPair f g], CreatesLimit (parallelPair f g) G

instance {A B} (f g : A ⟶ B) [G.IsCosplitPair f g] [CreatesLimitOfIsCosplitPair G] :
    CreatesLimit (parallelPair f g) G := CreatesLimitOfIsCosplitPair.out f g

instance [CreatesLimitOfIsCosplitPair F] : ∀ (A : Coalgebra adj.toComonad),
    CreatesLimit (parallelPair (G.map A.a)
      (NatTrans.app adj.unit (G.obj A.A))) F :=
  fun _ => CreatesLimitOfIsCosplitPair.out _ _

/--
Beck's comonadicity theorem. If `F` has a right adjoint and creates equalizers of `F`-cosplit pairs,
then it is comonadic.
This is the converse of `createsGSplitOfComonadic`.
-/
def comonadicOfCreatesGSplitEqualizers [CreatesLimitOfIsCosplitPair F] :
    ComonadicLeftAdjoint F := by
  let I {A B} (f g : A ⟶ B) [F.IsCosplitPair f g] : HasLimit (parallelPair f g ⋙ F) := by
    apply @hasLimitOfIso _ _ _ _ _ _ ?_ (diagramIsoParallelPair.{v₁} _).symm
    exact inferInstanceAs <| HasEqualizer (F.map f) (F.map g)
  have : HasEqualizerOfIsCosplitPair F := ⟨fun _ _ => hasLimit_of_created (parallelPair _ _) F⟩
  have : PreservesLimitOfIsCosplitPair F := ⟨by intros; infer_instance⟩
  have : ReflectsLimitOfIsCosplitPair F := ⟨by intros; infer_instance⟩
  exact comonadicOfHasPreservesReflectsGSplitEqualizers adj

/-- An alternate version of Beck's comonadicity theorem. If `F` reflects isomorphisms, preserves
equalizers of `F`-cosplit pairs and `C` has equalizers of `F`-cosplit pairs, then it is comonadic.
-/
def comonadicOfHasPreservesGSplitCoequalizersOfReflectsIsomorphisms [F.ReflectsIsomorphisms]
    [HasEqualizerOfIsCosplitPair F] [PreservesLimitOfIsCosplitPair F] :
    ComonadicLeftAdjoint F := by
  have : ReflectsLimitOfIsCosplitPair F := ⟨fun f g _ => by
    have := HasEqualizerOfIsCosplitPair.out F f g
    apply reflectsLimitOfReflectsIsomorphisms⟩
  apply comonadicOfHasPreservesReflectsGSplitEqualizers adj

end BeckComonadicity

section CoreflexiveComonadicity

variable [HasCoreflexiveEqualizers C] [F.ReflectsIsomorphisms]

-- Porting note: added these to replace parametric instances lean4#2311
-- [∀ ⦃A B⦄ (f g : A ⟶ B) [F.IsCoreflexivePair f g], PreservesLimit (parallelPair f g) F] :
class PreservesLimitOfIsCoreflexivePair (F : C ⥤ D) where
  out : ∀ ⦃A B⦄ (f g : A ⟶ B) [IsCoreflexivePair f g], PreservesLimit (parallelPair f g) F

instance temp {A B} (f g : A ⟶ B) [IsCoreflexivePair f g] [PreservesLimitOfIsCoreflexivePair F] :
  PreservesLimit (parallelPair f g) F := PreservesLimitOfIsCoreflexivePair.out f g

instance [PreservesLimitOfIsCoreflexivePair F] : ∀ X : Coalgebra adj.toComonad,
    PreservesLimit (parallelPair (G.map X.a)
      (NatTrans.app adj.unit (G.obj X.A))) F :=
 fun _ => PreservesLimitOfIsCoreflexivePair.out _ _

variable [PreservesLimitOfIsCoreflexivePair F]

/-- Reflexive (crude) monadicity theorem. If `F` has a right adjoint, `C` has and `F` preserves
coreflexive equalizers and `F` reflects isomorphisms, then `F` is comonadic.
-/
def comonadicOfHasPreservesCoreflexiveEqualizersOfReflectsIsomorphisms :
    ComonadicLeftAdjoint F where
  adj := adj
  eqv := by
    have : ∀ (X : adj.toComonad.Coalgebra), IsIso ((comparisonAdjunction adj).counit.app X) := by
      intro X
      apply
        @isIso_of_reflects_iso _ _ _ _ _ _ _ (Comonad.forget adj.toComonad) ?_ _
      · change IsIso ((comparisonAdjunction adj).counit.app X).f
        rw [comparisonAdjunction_counit_f]
        exact (IsLimit.conePointUniqueUpToIso (beckEqualizer X)
          (counitLimitOfPreservesEqualizer X)).isIso_inv
    have : ∀ (Y : C), IsIso ((comparisonAdjunction adj).unit.app Y) := by
      intro Y
      rw [comparisonAdjunction_unit_app]
      -- Porting note: passing instances through
      change IsIso (IsLimit.conePointUniqueUpToIso _ ?_).inv
      infer_instance
      -- Porting note: passing instances through
      have : IsCoreflexivePair (G.map (F.map (adj.unit.app Y)))
          (adj.unit.app (G.obj (F.obj Y))) := by
        apply IsCoreflexivePair.mk' (G.map (adj.counit.app _)) _ _
        · rw [← G.map_comp, ← G.map_id]
          exact congr_arg G.map (adj.left_triangle_components Y)
        · rw [← G.map_id]
          simp
      apply @unitEqualizerOfCoreflectsEqualizer _ _ _ _ _ _ _ _ ?_
      apply reflectsLimitOfReflectsIsomorphisms
    exact (comparisonAdjunction adj).toEquivalence.symm.isEquivalence_inverse

end CoreflexiveComonadicity

end

end Comonad

end CategoryTheory
