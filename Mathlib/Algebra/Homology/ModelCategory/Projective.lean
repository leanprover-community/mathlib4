/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.ModelCategory.Injective
public import Mathlib.Algebra.Homology.CochainComplexMinus
public import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant
public import Mathlib.AlgebraicTopology.ModelCategory.Opposite
public import Mathlib.AlgebraicTopology.ModelCategory.Transport

/-!
# Factorization lemma

-/

@[expose] public section

open CategoryTheory HomotopicalAlgebra Limits Opposite

namespace CochainComplex

variable {C : Type*} [Category C] [Abelian C]

namespace Minus

namespace modelCategoryQuillen

scoped instance : CategoryWithWeakEquivalences (CochainComplex.Minus C) where
  weakEquivalences := quasiIso C

scoped instance : CategoryWithCofibrations (CochainComplex.Minus C) where
  cofibrations := degreewiseMonoWithProjectiveCokernel.inverseImage (ι C)

scoped instance : CategoryWithFibrations (CochainComplex.Minus C) where
  fibrations := .epimorphisms _

lemma cofibration_iff {X Y : Minus C} (f : X ⟶ Y) :
    Cofibration f ↔ degreewiseMonoWithProjectiveCokernel f.hom :=
  HomotopicalAlgebra.cofibration_iff _

lemma weakEquivalence_iff {X Y : Minus C} (f : X ⟶ Y) :
    WeakEquivalence f ↔ QuasiIso f.hom :=
  HomotopicalAlgebra.weakEquivalence_iff _

lemma fibration_iff {X Y : Minus C} (f : X ⟶ Y) :
    Fibration f ↔ Epi f :=
  HomotopicalAlgebra.fibration_iff _

instance {X Y : CochainComplex.Minus C} (p : X ⟶ Y) [Fibration p] :
    Epi p := by
  rwa [← fibration_iff]

variable [EnoughProjectives C]

variable (C) in
def opEquivalence : (Minus C)ᵒᵖ ≌ Plus Cᵒᵖ where
  functor :=
    ObjectProperty.lift _
      (ι C ⋙ (CochainComplex.opEquivalence C).functor.rightOp).leftOp (by
        rintro ⟨X, n, hX⟩
        refine ⟨-n, ?_⟩
        rw [isStrictlyGE_iff]
        exact fun i _ ↦ (X.isZero_of_isStrictlyLE n (-i)).op)
  inverse :=
    Functor.rightOp (ObjectProperty.lift _
      ((Plus.ι Cᵒᵖ).op ⋙ (CochainComplex.opEquivalence C).inverse.leftOp) (by
        rintro ⟨X, n, hX⟩
        refine ⟨-n, ?_⟩
        rw [isStrictlyLE_iff]
        exact fun i _ ↦ (X.isZero_of_isStrictlyGE n _ (by dsimp; lia)).unop))
  unitIso :=
    NatIso.ofComponents (fun K ↦ (ObjectProperty.isoMk _
      ((CochainComplex.opEquivalence C).unitIso.app (op K.unop.obj)).unop).op)
        (fun f ↦ Quiver.Hom.unop_inj (by
          ext : 1
          exact Quiver.Hom.op_inj
            ((CochainComplex.opEquivalence C).unitIso.hom.naturality f.unop.hom.op)))
  counitIso :=
    NatIso.ofComponents (fun K ↦ ObjectProperty.isoMk _
      ((CochainComplex.opEquivalence C).counitIso.app K.obj))
        (fun f ↦ by
          ext : 1
          exact (CochainComplex.opEquivalence C).counitIso.hom.naturality f.hom)
  functor_unitIso_comp X := by
    ext : 1
    exact (CochainComplex.opEquivalence C).functor_unit_comp (op X.unop.obj)

set_option backward.isDefEq.respectTransparency false in
open Plus.modelCategoryQuillen in
scoped instance : ModelCategory (CochainComplex.Minus C) := by
  apply ModelCategory.transport (opEquivalence C).rightOp
  · ext K L f
    simp [← HomotopicalAlgebra.cofibration_iff, cofibration_iff, cofibration_op_iff,
      Plus.modelCategoryQuillen.fibration_iff,
      degreewiseMonoWithProjectiveCokernel_eq_unop, opEquivalence]
  · ext K L f
    simp [← HomotopicalAlgebra.fibration_iff, fibration_iff, fibration_op_iff,
      Plus.modelCategoryQuillen.cofibration_iff,
      Functor.mono_map_iff_mono (opEquivalence C).functor f.op]
  · ext K L f
    simp [← HomotopicalAlgebra.weakEquivalence_iff, weakEquivalence_iff,
      weakEquivalence_op_iff, Plus.modelCategoryQuillen.weakEquivalence_iff,
      opEquivalence, quasiIso_opEquivalence_map_iff]

lemma isCofibrant_iff (X : Minus C) :
    IsCofibrant X ↔ ∀ (n : ℤ), Projective (X.obj.X n) := by
  rw [HomotopicalAlgebra.isCofibrant_iff, cofibration_iff,
    degreewiseMonoWithProjectiveCokernel_iff_of_isZero]
  exact Functor.map_isZero (Minus.ι C) initialIsInitial.isZero

end modelCategoryQuillen

end Minus

end CochainComplex
