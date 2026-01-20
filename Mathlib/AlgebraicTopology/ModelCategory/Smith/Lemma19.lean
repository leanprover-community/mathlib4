/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.ModelCategory.Smith.Lemma18
public import Mathlib.AlgebraicTopology.ModelCategory.Smith.SolutionSetCondition
public import Mathlib.CategoryTheory.MorphismProperty.RetractArgument
public import Mathlib.CategoryTheory.Presentable.LocallyPresentable
public import Mathlib.CategoryTheory.SmallObject.Basic

/-!
# Lemma 1.8 (T. Beke)

-/

@[expose] public section

universe w v u

open HomotopicalAlgebra CategoryTheory Limits MorphismProperty

variable {C : Type u} [Category.{v} C]

namespace CategoryTheory

namespace SmallObject

namespace lemma_1_9

variable [HasPushouts C]
  {I W : MorphismProperty C}
  [HasFactorization I.rlp.llp I.rlp]
  (hIW₁ : I.rlp ≤ W)
  (hIW₃ : I ≤ solutionSetCondition.{w} W)

def Index : Type _ :=
  Σ (f : I.toSet) (w : (hIW₃ _ f.2).morphismProperty.toSet), f.1 ⟶ w.1

instance [LocallySmall.{w} C] [MorphismProperty.IsSmall.{w} I] :
    Small.{w} (Index hIW₃) := by
  dsimp [Index]
  infer_instance

namespace Index

variable {hIW₃} (i : Index hIW₃)

protected noncomputable nonrec abbrev pushout : C :=
  pushout i.2.2.left i.1.1.hom

noncomputable abbrev c : i.pushout ⟶ i.2.1.1.right :=
  pushout.desc i.2.1.1.hom i.2.2.right

end Index

def J : MorphismProperty C :=
  .ofHoms (fun (i : Index hIW₃) ↦
    pushout.inl _ _ ≫ (factorizationData I.rlp.llp I.rlp i.c).i)

instance [LocallySmall.{w} C] [MorphismProperty.IsSmall.{w} I] :
    MorphismProperty.IsSmall.{w} (J hIW₃) := by
  dsimp [J]
  infer_instance

lemma J_le_llp_rlp : J hIW₃ ≤ I.rlp.llp := by
  rintro _ _ _ ⟨i⟩
  exact comp_mem _ _ _
    (pushout_inl _ _ (MorphismProperty.le_llp_rlp _ _ i.1.2))
    (factorizationData I.rlp.llp I.rlp i.c).hi

include hIW₁ in
lemma J_le [W.HasTwoOutOfThreeProperty] :
    J hIW₃ ≤ W := by
  rintro _ _ _ ⟨i⟩
  refine W.of_postcomp _ _ (hIW₁ _ (factorizationData I.rlp.llp I.rlp i.c).hp) ?_
  simpa using solutionSetCondition.morphismProperty_le _ _ i.2.1.2

include hIW₁ in
lemma J_le_inter [W.HasTwoOutOfThreeProperty] :
    J hIW₃ ≤ I.rlp.llp ⊓ W := by
  simp only [le_inf_iff]
  exact ⟨J_le_llp_rlp hIW₃, J_le hIW₁ hIW₃⟩

lemma condition {i w : Arrow C} (sq : i ⟶ w) (hi : I i.hom) (hw : W w.hom) :
    ∃ (j : Arrow C) (_ : J hIW₃ j.hom) (a : i ⟶ j) (b : j ⟶ w), a ≫ b = sq := by
  obtain ⟨X, Y, w', hw', α, β, rfl⟩ := (hIW₃ _ hi).exists_fac _ hw sq
  let u : Index hIW₃ := ⟨⟨Arrow.mk _, hi⟩, ⟨w', hw'⟩, α⟩
  refine ⟨Arrow.mk _, ⟨u⟩,
    Arrow.homMk α.left (pushout.inr _ _ ≫ (factorizationData I.rlp.llp I.rlp u.c).i) ?_,
    Arrow.homMk β.left ((factorizationData I.rlp.llp I.rlp u.c).p ≫ β.right) ?_, ?_⟩
  · simp [u, pushout.condition_assoc]
  · dsimp
    rw [Arrow.w_mk_right, Category.assoc, MapFactorizationData.fac_assoc,
      pushout.inl_desc_assoc]
  · ext
    · simp
    · simp [u, Index.c]

include hIW₁ in
lemma llp_rlp_J [W.HasTwoOutOfThreeProperty] [W.IsStableUnderRetracts]
    [(I.rlp.llp ⊓ W).IsStableUnderCobaseChange]
    [HasColimitsOfSize.{w, w} C] [MorphismProperty.IsSmall.{w} I] [LocallySmall.{w} C]
    [IsStableUnderTransfiniteComposition.{w} (I.rlp.llp ⊓ W)]
    [IsStableUnderCoproducts.{w} (I.rlp.llp ⊓ W)]
    [HasSmallObjectArgument.{w} (J hIW₃)]
    (κ : Cardinal.{w}) [Fact κ.IsRegular]
    (hκ : ∀ {A B : C} (i : A ⟶ B), I i → IsCardinalPresentable A κ) :
    (J hIW₃).rlp.llp = I.rlp.llp ⊓ W := by
  refine le_antisymm ?_ ?_
  · rw [(J hIW₃).llp_rlp_of_hasSmallObjectArgument, retracts_le_iff,
      transfiniteCompositions_le_iff, pushouts_le_iff, coproducts_le_iff]
    exact J_le_inter hIW₁ hIW₃
  · intro X Y f hf
    obtain ⟨Z, a, b, ha, hb, fac⟩ :=
      lemma_1_8'.{w} (condition hIW₃) (J_le_inter hIW₁ hIW₃) κ hκ f hf.2
    have := hf.1 _ hb
    exact MorphismProperty.of_retract (.ofLeftLiftingProperty fac) ha

end lemma_1_9

end SmallObject

end CategoryTheory
