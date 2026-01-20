module

public import Mathlib.AlgebraicTopology.ModelCategory.Smith.Lemma18
public import Mathlib.AlgebraicTopology.ModelCategory.Smith.SolutionSetCondition
public import Mathlib.CategoryTheory.Presentable.LocallyPresentable
public import Mathlib.CategoryTheory.SmallObject.Basic

/-!
# Lemma 1.8 (T. Beke)

-/

@[expose] public section

universe w v u

open HomotopicalAlgebra CategoryTheory Limits

variable {C : Type u} [Category.{v} C]

namespace CategoryTheory

namespace SmallObject

section

variable [LocallySmall.{w} C] [HasPushouts C]
  {I W : MorphismProperty C} [MorphismProperty.IsSmall.{w} I]
  [MorphismProperty.HasFactorization I.rlp.llp I.rlp]
  (hIW : I ≤ MorphismProperty.solutionSetCondition.{w} W)

namespace lemma_1_9

def Index : Type _ :=
  Σ (f : I.toSet) (w : (hIW _ f.2).morphismProperty.toSet), f.1 ⟶ w.1

instance : Small.{w} (Index hIW) := by
  dsimp [Index]
  infer_instance

namespace Index

variable {hIW} (i : Index hIW)

protected noncomputable nonrec abbrev pushout : C :=
  pushout i.2.2.left i.1.1.hom

noncomputable abbrev c : i.pushout ⟶ i.2.1.1.right :=
  pushout.desc i.2.1.1.hom i.2.2.right

end Index

def J : MorphismProperty C :=
  MorphismProperty.ofHoms (fun (i : Index hIW) ↦
    pushout.inl _ _ ≫ (MorphismProperty.factorizationData I.rlp.llp I.rlp i.c).i)

end lemma_1_9

end

end SmallObject

end CategoryTheory
