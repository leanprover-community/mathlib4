/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

module

public import Mathlib.LinearAlgebra.Transvection
public import Mathlib.LinearAlgebra.Center

/-!
# Center of the group of linear endomorphisms

-/

@[expose] public section

open Module LinearMap LinearEquiv Set

namespace LinearMap.GeneralLinearGroup

variable {R V : Type*}

/-- The center of linear endomorphisms of a free module
consists of homotheties with central ratio. -/
theorem mem_center_iff
    [Ring R] [AddCommGroup V] [Module R V] [Free R V] {f : GeneralLinearGroup R V} :
    f ∈ center (GeneralLinearGroup R V) ↔
      ∃ a ∈ center Rˣ, ∀ x : V, f.val x = a • x  := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · constructor
    · intro hf
      use 1
      suffices ∀ x, f.val x = x by simpa using this
      intro; apply hV.allEq
    · rintro ⟨a, _, hfa⟩
      rw [Semigroup.mem_center_iff]
      intro g
      ext x
      simp [hfa]
  constructor
  · intro hf
    obtain ⟨a, ha, hfa⟩ := (center_End_of_free (f := f.toLinearEquiv.toLinearMap)).mp ?_
    let ι := Free.ChooseBasisIndex R V
    let b : Basis ι R V := Free.chooseBasis R V
    have : Nonempty ι := inferInstance
    let i : ι := Classical.ofNonempty
    have : f⁻¹.toLinearEquiv = f.toLinearEquiv.symm := by
      rw [toLinearEquiv_inv]
      -- missing rw
      rfl
    suffices IsUnit a by
      use this.unit
      constructor
      · rw [Semigroup.mem_center_iff] at ha ⊢
        simp [← Units.val_inj, ha]
      · intro x
        simpa [this] using hfa x
    rw [isUnit_iff_exists]
    use b.coord i (f⁻¹.toLinearEquiv (b i))
    have hfa (r : R) : f.val (r • b i) = (a * r) • b i := by
      simpa [mul_smul] using hfa (r • b i)
    have isLeftRegular : IsLeftRegular a := by
      intro r s hrs
      replace hrs : (a * r) • b i = (a * s) • b i := by simp [hrs]
      -- missing lemma
      have : Function.Injective f.val := sorry
      simp only [← hfa, this.eq_iff] at hrs
      simpa using congr(b.coord i $hrs)
    suffices _ by
      refine ⟨this, ?_⟩
      apply isLeftRegular
      simp only [← mul_assoc, this, one_mul, mul_one]
    have :  a • f⁻¹.toLinearEquiv (b i) = b i := by
      rw [this, ← LinearEquiv.map_smul, LinearEquiv.symm_apply_eq]
      simpa using (hfa 1).symm
    simpa using congr(b.coord i $((this)))
  · -- the easy direction
    sorry

end LinearMap.GeneralLinearGroup
