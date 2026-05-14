/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexOp
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Pairing

/-!
# The opposite of a pairing

Let `A` be a subcomplex of a simplicial set `X`. If `P` is a pairing of `A`,
we construct a pairing `P.op` for the subcomplex `A.op` of `X.op`.

-/

@[expose] public section

universe u

namespace SSet.Subcomplex.Pairing

variable {X : SSet.{u}} {A : X.Subcomplex} (P : A.Pairing)

/-- If `P` is a pairing for a subcomplex `A` of a simplicial set `X`,
this is the corresponding pairing of `A.op`. -/
@[simps I II]
def op : A.op.Pairing where
  I := Subcomplex.N.opEquiv ⁻¹' P.I
  II := Subcomplex.N.opEquiv ⁻¹' P.II
  inter := by simp [← Set.preimage_inter, P.inter]
  union := by simp [← Set.preimage_union, P.union]
  p := (N.opEquiv.subtypeEquiv (by simp)).trans
    (P.p.trans (N.opEquiv.symm.subtypeEquiv (by simp)))

@[simp]
lemma op_p (x : P.II) :
    dsimp% P.op.p ⟨Subcomplex.N.opEquiv.symm x.1, x.2⟩ =
      ⟨Subcomplex.N.opEquiv.symm (P.p x), by simp⟩ := rfl

lemma op_ancestralRel_iff (x y : P.II) :
    P.op.AncestralRel ⟨Subcomplex.N.opEquiv.symm x.1, x.2⟩
      ⟨Subcomplex.N.opEquiv.symm y.1, y.2⟩ ↔ P.AncestralRel x y :=
  and_congr (not_congr (by aesop)) (by simp)

instance [P.IsProper] : P.op.IsProper where
  isUniquelyCodimOneFace x := (P.isUniquelyCodimOneFace ⟨_, x.2⟩).op

instance [P.IsRegular] : P.op.IsRegular where
  wf := by
    have hP := P.wf
    rw [wellFounded_iff_isEmpty_descending_chain] at hP ⊢
    by_contra!
    obtain ⟨f, hf⟩ := this
    refine hP.false ⟨fun n ↦ ⟨_, (f n).2⟩, fun n ↦ ?_⟩
    simpa [← P.op_ancestralRel_iff] using hf n

end SSet.Subcomplex.Pairing
