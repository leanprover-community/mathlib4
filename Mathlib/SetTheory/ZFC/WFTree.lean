import Mathlib.SetTheory.ZFC.Basic
import Mathlib.SetTheory.WFTree

namespace ZFSet

universe u

noncomputable def to_wfTree (x : ZFSet.{u}) : WFTree.{u} Unit :=
  WFTree.ofChildren {((), to_wfTree c) | (c : ZFSet.{u}) (_ : c ∈ x)}
termination_by x

noncomputable def of_wfTree (t : WFTree.{u} Unit) : ZFSet.{u} :=
  ZFSet.range.{u, u} fun x : Shrink.{u} t.children ↦
    let ⟨((), x), h⟩ := (equivShrink _).symm x
    have := WFTree.depth_lt_of_mem h
    of_wfTree x
termination_by t.depth

private lemma toSet_equiv_aux {s : Set ZFSet.{u}} (hs : Small.{u} s) :
  (mk <| PSet.mk (Shrink s) fun x ↦ ((equivShrink s).symm x).1.out).toSet = s := by
    ext x
    rw [mem_toSet, ← mk_out x, mk_mem_iff, mk_out]
    refine' ⟨_, λ xs ↦ ⟨equivShrink s (Subtype.mk x xs), _⟩⟩
    · rintro ⟨b, h2⟩
      rw [← ZFSet.eq, ZFSet.mk_out] at h2
      simp [h2]
    · simp [PSet.Equiv.refl]

/-- `ZFSet.toSet` as an equivalence. -/
@[simps apply_coe]
noncomputable def toSet_equiv : ZFSet.{u} ≃ {s : Set ZFSet.{u} // Small.{u, u+1} s} where
  toFun x := ⟨x.toSet, x.small_toSet⟩
  invFun := λ ⟨s, h⟩ ↦ mk <| PSet.mk (Shrink s) fun x ↦ ((equivShrink.{u, u+1} s).symm x).1.out
  left_inv := Function.rightInverse_of_injective_of_leftInverse (by intros x y; simp)
    λ s ↦ Subtype.coe_injective <| toSet_equiv_aux s.2
  right_inv s := Subtype.coe_injective <| toSet_equiv_aux s.2


end ZFSet
