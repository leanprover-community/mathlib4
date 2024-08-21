/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Closed.Monoidal
import Mathlib.CategoryTheory.Closed.GroupoidFunctorCategory
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Monoidal.FunctorCategory
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Monad.Adjunction
/-!
# Functors into a complete monoidal closed category form a monoidal closed category.

-/

universe v₁ v₂ u₁ u₂

open CategoryTheory MonoidalCategory MonoidalClosed Limits

section

variable {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)

#check adj.toComonad.forget
#check adj.toComonad.cofree
#check adj.toComonad.adj

example : Comonad.comparison adj ⋙ adj.toComonad.forget = L := rfl
example : R ⋙ Comonad.comparison adj = adj.toComonad.cofree := rfl

end

noncomputable section

namespace CategoryTheory.Functor

section Lifting

def adjointLiftingAuxRightAdjoint' {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (T : Comonad C) (S : Comonad D)
    (Q : T.Coalgebra ⥤ S.Coalgebra)
    (i : Q ⋙ S.forget ≅ T.forget ⋙ L) : S.Coalgebra ⥤ T.Coalgebra := by
  let τ := T.adj.unit
  let σ := S.adj.unit
  have : T.toFunctor = T.cofree ⋙ T.forget := rfl
  have h₁ : T.δ = whiskerRight (whiskerLeft T.cofree T.adj.unit) T.forget := by ext; simp
  have h₂ : S.δ = whiskerRight (whiskerLeft S.cofree S.adj.unit) S.forget := by ext; simp
  let α := adj.unit
  let β := adj.counit
  sorry

def adjointLiftingAuxAdjunction' {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (T : Comonad C) (S : Comonad D)
    (Q : T.Coalgebra ⥤ S.Coalgebra)
    (i : Q ⋙ S.forget ≅ T.forget ⋙ L) : Q ⊣ adjointLiftingAuxRightAdjoint' adj T S Q i := sorry

def adjointLiftingAuxRightAdjoint {C D : Type*} [Category C] [Category D]
    (L : C ⥤ D) [IsLeftAdjoint L] (T : Comonad C) (S : Comonad D) (Q : T.Coalgebra ⥤ S.Coalgebra)
    (i : Q ⋙ S.forget ≅ T.forget ⋙ L) : S.Coalgebra ⥤ T.Coalgebra :=
  adjointLiftingAuxRightAdjoint' (Adjunction.ofIsLeftAdjoint L) T S Q i

def adjointLiftingAuxAdjunction {C D : Type*} [Category C] [Category D]
    (L : C ⥤ D) [IsLeftAdjoint L] (T : Comonad C) (S : Comonad D) (Q : T.Coalgebra ⥤ S.Coalgebra)
    (i : Q ⋙ S.forget ≅ T.forget ⋙ L) : Q ⊣ adjointLiftingAuxRightAdjoint L T S Q i :=
  adjointLiftingAuxAdjunction' (Adjunction.ofIsLeftAdjoint L) T S Q i

def adjointLiftingRightAdjoint {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (U : A ⥤ C) [ComonadicLeftAdjoint U] (V : B ⥤ D) [ComonadicLeftAdjoint V]
    (Q : A ⥤ B) (L : C ⥤ D) [IsLeftAdjoint L] (i : Q ⋙ V ≅ U ⋙ L) : B ⥤ A :=
  (Comonad.comparison (comonadicAdjunction V)) ⋙ adjointLiftingAuxRightAdjoint L
    (comonadicAdjunction U).toComonad
      (comonadicAdjunction V).toComonad
        ((asEquivalence (Comonad.comparison (comonadicAdjunction U))).inverse ⋙ Q ⋙
           (Comonad.comparison (comonadicAdjunction V)))
            (associator _ _ _ ≪≫ isoWhiskerLeft _ i ≪≫
              isoWhiskerRight (Comonad.comparison (comonadicAdjunction U)).asEquivalence.counitIso
                ((comonadicAdjunction U).toComonad.forget ⋙ L)) ⋙
                  (asEquivalence (Comonad.comparison (comonadicAdjunction U))).inverse

def adjointLiftingAdjunction {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (U : A ⥤ C) [ComonadicLeftAdjoint U] (V : B ⥤ D) [ComonadicLeftAdjoint V]
    (Q : A ⥤ B) (L : C ⥤ D) [IsLeftAdjoint L] (i : Q ⋙ V ≅ U ⋙ L) :
      Q ⊣ adjointLiftingRightAdjoint U V Q L i := by
  let h :=
    (adjointLiftingAuxAdjunction L
      (comonadicAdjunction U).toComonad
        (comonadicAdjunction V).toComonad
          ((asEquivalence (Comonad.comparison (comonadicAdjunction U))).inverse ⋙ Q ⋙
            (Comonad.comparison (comonadicAdjunction V)))
              (associator _ _ _ ≪≫ isoWhiskerLeft _ i ≪≫
                isoWhiskerRight (Comonad.comparison (comonadicAdjunction U)).asEquivalence.counitIso
                  ((comonadicAdjunction U).toComonad.forget ⋙ L)))
  let h₁ := (asEquivalence (Comonad.comparison (comonadicAdjunction U))).toAdjunction
  let h₂ := (asEquivalence (Comonad.comparison (comonadicAdjunction V))).symm.toAdjunction
  let adj := (h₁.comp h).comp h₂
  refine Adjunction.ofNatIsoLeft adj ?_
  refine (isoWhiskerRight (asEquivalence (Comonad.comparison (comonadicAdjunction U))).unitIso.symm
    ((Q ⋙ Comonad.comparison (comonadicAdjunction V)) ⋙
      (Comonad.comparison (comonadicAdjunction V)).asEquivalence.inverse)) ≪≫
    isoWhiskerLeft Q (asEquivalence (Comonad.comparison (comonadicAdjunction V))).unitIso.symm


lemma adjoint_lifting_aux {C D : Type*} [Category C] [Category D]
    (L : C ⥤ D) [IsLeftAdjoint L]  (T : Comonad C) (S : Comonad D) (Q : T.Coalgebra ⥤ S.Coalgebra)
    (i : Q ⋙ S.forget ≅ T.forget ⋙ L) : IsLeftAdjoint Q := sorry

theorem adjoint_lifting {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (U : A ⥤ C) [ComonadicLeftAdjoint U] (V : B ⥤ D) [ComonadicLeftAdjoint V]
    (Q : A ⥤ B) (L : C ⥤ D) [IsLeftAdjoint L] (i : Q ⋙ V ≅ U ⋙ L) : IsLeftAdjoint Q := by
  sorry

end Lifting

section
variable (I : Type u₂) [Category.{v₂} I]

abbrev incl : Discrete I ⥤ I := Discrete.functor id

instance : Groupoid (Discrete I) := { inv := fun h ↦ ⟨⟨h.1.1.symm⟩⟩ }

variable (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C] [MonoidalClosed C]

-- Since `Discrete I` is a groupoid, functors to `C` form a monoidal closed category.
example : MonoidalClosed (Discrete I ⥤ C) := inferInstance

variable [∀ (F : Discrete I ⥤ C), (Discrete.functor id).HasRightKanExtension F]
-- ...is also implied by: `[HasLimitsOfSize.{u₂, max u₂ v₂} C]`

abbrev ranDiscrete : (Discrete I ⥤ C) ⥤ (I ⥤ C) := (incl I).ran

instance : Faithful <| (whiskeringLeft _ _ C).obj (incl I) where
  map_injective {_ _ a b} h := by ext X; exact NatTrans.congr_app h ⟨X⟩

-- works if `I : Type v₁`, but we should be able to genereralize universes (and/or give a
-- `PreservesLimitsOfShape` instance)
instance [HasLimits C] : PreservesLimits <| (whiskeringLeft _ _ C).obj (incl I) := sorry

instance : ReflectsIsomorphisms <| (whiskeringLeft _ _ C).obj (incl I) where
  reflects f h := by
    simp only [NatTrans.isIso_iff_isIso_app] at *
    intro X
    exact h ⟨X⟩

-- Beck's comonadicity theorem should imply this
instance :  ComonadicLeftAdjoint ((whiskeringLeft _ _ C).obj (incl I)) where
  adj := (incl I).ranAdjunction C
  eqv := sorry

instance (F : I ⥤ C) : IsLeftAdjoint (tensorLeft (incl I ⋙ F)) :=
  (ihom.adjunction (incl I ⋙ F)).isLeftAdjoint

instance (F : I ⥤ C) : Closed F where
  rightAdj := adjointLiftingRightAdjoint ((whiskeringLeft _ _ C).obj (incl I))
    ((whiskeringLeft _ _ C).obj (incl I)) (tensorLeft F) (tensorLeft (incl I ⋙ F)) (Iso.refl _)
  adj := adjointLiftingAdjunction ((whiskeringLeft _ _ C).obj (incl I))
    ((whiskeringLeft _ _ C).obj (incl I)) (tensorLeft F) (tensorLeft (incl I ⋙ F)) (Iso.refl _)
  -- have := (ihom.adjunction (incl I ⋙ F)).isLeftAdjoint
  -- have := adjoint_lifting ((whiskeringLeft _ _ C).obj (incl I))
  --   ((whiskeringLeft _ _ C).obj (incl I)) (tensorLeft F) (tensorLeft (incl I ⋙ F)) (Iso.refl _)
  -- { rightAdj := (tensorLeft F).rightAdjoint
  --   adj := Adjunction.ofIsLeftAdjoint (tensorLeft F) }

instance : MonoidalClosed (I ⥤ C) where

end

end CategoryTheory.Functor
