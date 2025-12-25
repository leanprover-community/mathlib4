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

theorem isUnit_ratio
    [Semiring R] [AddCommMonoid V] [Module R V] [Free R V] [Nontrivial V]
    {f : GeneralLinearGroup R V} {a : R} (hfa : ∀ x, f.val x = a • x) :
    IsUnit a := by
  rw [isUnit_iff_exists]
  let ι := Free.ChooseBasisIndex R V
  let b : Basis ι R V := Free.chooseBasis R V
  have _ : Nonempty ι := inferInstance
  let i : ι := Classical.ofNonempty
  use b.coord i (f⁻¹.toLinearEquiv (b i))
  have hfa (r : R) : f.val (r • b i) = (a * r) • b i := by
    simpa [mul_smul] using hfa (r • b i)
  have isLeftRegular : IsLeftRegular a := by
    intro r s hrs
    replace hrs : (a * r) • b i = (a * s) • b i := by simp [hrs]
    simp only [← hfa, ← coe_toLinearEquiv,
      f.toLinearEquiv.injective.eq_iff] at hrs
    simpa using congr(b.coord i $hrs)
  suffices _ by
    refine ⟨this, ?_⟩
    apply isLeftRegular
    simp only [← mul_assoc, this, one_mul, mul_one]
  have :  a • f⁻¹.toLinearEquiv (b i) = b i := by
    rw [toLinearEquiv_inv, ← LinearEquiv.map_smul, coe_inv,
      LinearEquiv.symm_apply_eq]
    simpa using (hfa 1).symm
  simpa using congr(b.coord i $((this)))

/-- A linear automorphism of a free module of rank at least 2
that commutes with transvections consists of homotheties with central ratio. -/
theorem commute_transvections_iff_of_basis
    [Ring R] [AddCommGroup V] [Module R V]
    {ι : Type*} [Nontrivial ι] (b : Basis ι R V)
    {f : V ≃ₗ[R] V}
    (hcomm : ∀ i j (r : R) (hij : i ≠ j), Commute f (LinearEquiv.transvection (f := b.coord i) (v := r • b j) (by
      simp [Finsupp.single_eq_of_ne hij]))) :
    ∃ a ∈ (center R)ˣ, ∀ x, f x = a.val • x := by
  simp only [Semigroup.mem_center_iff]
  rcases subsingleton_or_nontrivial V with hV | hV
  · use 1
    suffices ∀ x, f x = x by simpa using this
    intro; apply hV.allEq
  simp only [commute_iff_eq] at hcomm
  let t (i j : ι) := LinearMap.transvection (b.coord i) (b j)
  replace hcomm (i j : ι) (hij : i ≠ j) (r : R) :
      r • f (b j) = b.coord i (f (b i)) • r • b j := by
    have := hcomm i j r hij
    rw [LinearMap.ext_iff] at this
    simpa [LinearMap.transvection.apply] using this (b i)
  have h_allEq (i j : ι) : b.coord i (f (b i)) = b.coord j (f (b j)) := by
    by_cases hij : j = i
    · simp [hij]
    simpa using congr_arg (b.coord i) (hcomm j i hij 1)
  have h1 (i : ι) : f (b i) = (b.coord i) (f (b i)) • b i := by
    obtain ⟨j, hji⟩ := exists_ne i
    simpa [h_allEq j i] using hcomm j i hji 1
  obtain ⟨i, j, hij⟩ := Nontrivial.exists_pair_ne (α := ι)
  use b.coord i (f (b i))
  suffices _ by
    refine ⟨this, ?_⟩
    intro x
    rw [← b.linearCombination_repr x, Finsupp.linearCombination_apply,
      map_finsuppSum, Finsupp.smul_sum]
    apply Finsupp.sum_congr
    intro j _
    rw [_root_.map_smul, ← mul_smul, ← this, mul_smul, h1 j, h_allEq j i]
  intro r
  simpa [h_allEq i j] using congr_arg (b.coord j) (hcomm i j hij r)



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
    obtain ⟨a, ha, hfa⟩ := (center_End_of_free (f := f.toLinearEquiv.toLinearMap)).mp (by
      rw [Semigroup.mem_center_iff] at hf ⊢
      intro g
      apply hf
      sorry)
    let ι := Free.ChooseBasisIndex R V
    let b : Basis ι R V := Free.chooseBasis R V
    have : Nonempty ι := inferInstance
    let i : ι := Classical.ofNonempty
    use (isUnit_ratio hfa).unit
    constructor
    · rw [Semigroup.mem_center_iff] at ha ⊢
      simp [← Units.val_inj, ha]
    · intro x
      simpa [this] using hfa x
  · -- the easy direction
    rintro ⟨a, ha, hfa⟩
    rw [Semigroup.mem_center_iff]
    aesop (add norm hfa)

end LinearMap.GeneralLinearGroup
