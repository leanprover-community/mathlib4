/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

module

public import Mathlib.LinearAlgebra.Center

/-!
# Center of the group of linear endomorphisms

-/

@[expose] public section

open Module LinearMap LinearEquiv Set

variable {R V : Type*}

namespace LinearEquiv

theorem isUnit_ratio
    [Semiring R] [AddCommMonoid V] [Module R V] [Free R V] [Nontrivial V]
    {f : V ≃ₗ[R] V} {a : R} (hfa : ∀ x, f x = a • x) :
    IsUnit a := by
  rw [isUnit_iff_exists]
  let ι := Free.ChooseBasisIndex R V
  let b : Basis ι R V := Free.chooseBasis R V
  have _ : Nonempty ι := inferInstance
  let i : ι := Classical.ofNonempty
  use b.coord i (f⁻¹ (b i))
  have hfa (r : R) : f (r • b i) = (a * r) • b i := by
    simpa [mul_smul] using hfa (r • b i)
  have isLeftRegular : IsLeftRegular a := by
    intro r s hrs
    replace hrs : (a * r) • b i = (a * s) • b i := by simp [hrs]
    simp only [← hfa, f.injective.eq_iff] at hrs
    simpa using congr(b.coord i $hrs)
  suffices _ by
    refine ⟨this, ?_⟩
    apply isLeftRegular
    simp only [← mul_assoc, this, one_mul, mul_one]
  have :  a • f⁻¹ (b i) = b i := by
    rw [← LinearEquiv.map_smul, coe_inv, LinearEquiv.symm_apply_eq]
    simpa using (hfa 1).symm
  simpa using congr(b.coord i $((this)))

/-- A linear automorphism of a free module of rank at least 2
that commutes with transvections consists of homotheties with central ratio. -/
theorem commute_transvections_iff_of_basis
    [Ring R] [AddCommGroup V] [Module R V]
    {ι : Type*} [Nontrivial ι] (b : Basis ι R V)
    {f : V ≃ₗ[R] V}
    (hcomm : ∀ i j (r : R) (hij : i ≠ j),
      Commute f (LinearEquiv.transvection (f := b.coord i) (v := r • b j) (by
      simp [Finsupp.single_eq_of_ne hij]))) :
    ∃ a ∈ Subring.center R, IsUnit a ∧ ∀ x, f x = a • x := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · refine ⟨1, by simp, by simp, fun x ↦ Subsingleton.allEq _ _⟩
  have _ : Free R V := Free.of_basis b
  obtain ⟨a, hfa⟩ :=
    LinearMap.commute_transvections_iff_of_basis b (f := f.toLinearMap)
      (fun i j r hij ↦ by
        simpa [← toLinearMap_inj, commute_iff_eq] using hcomm i j r hij)
  refine ⟨a, hfa.1, ?_, fun x ↦ by simpa using hfa.2 x⟩
  apply isUnit_ratio (f := f) (fun x ↦ by simpa using hfa.2 x)

/-- The center of linear automorphisms of a free module of rank ≠ 1
consists of homotheties with central ratio.

This version requires a basis with a nontrivial type of indices.
Under `StrongRankCondition R`, use `LinearEquiv.mem_center_iff`. -/
theorem mem_center_iff_of_basis [Ring R] [AddCommGroup V] [Module R V]
    {ι : Type*} [Nontrivial ι] (b : Basis ι R V) {f : V ≃ₗ[R] V} :
    f ∈ Subgroup.center (V ≃ₗ[R] V) ↔
      ∃ a ∈ Subring.center R, IsUnit a ∧ ∀ x : V, f x = a • x  := by
  constructor
  · intro hf
    apply commute_transvections_iff_of_basis b
    intro i j r hij
    rw [Subgroup.mem_center_iff] at hf
    rw [commute_iff_eq, hf]
  · rintro ⟨a, _, hfa⟩
    rw [Subgroup.mem_center_iff]
    intro g
    ext x
    simp [hfa]

/-- The center of linear automorphisms of a free module of rank ≠ 1
consists of homotheties with central ratio.

This version requires `StrongRankCondition R`. Otherwise, use `LinearEquiv.mem_center_iff`. -/
theorem mem_center_iff
    [Ring R] [StrongRankCondition R]
    [AddCommGroup V] [Module R V] [Free R V] (hV : finrank R V ≠ 1)
    {f : V ≃ₗ[R] V} :
    f ∈ Subgroup.center (V ≃ₗ[R] V) ↔
      ∃ a ∈ Subring.center R, IsUnit a ∧ ∀ x : V, f x = a • x  := by
  let ι := Free.ChooseBasisIndex R V
  let b : Basis ι R V := Free.chooseBasis R V
  rcases subsingleton_or_nontrivial V
  · constructor
    · intro hf
      refine ⟨1, by simp, by simp, fun x ↦ Subsingleton.allEq _ _⟩
    · rintro ⟨a, hcomm, hunt, hf⟩
      simp only [Subgroup.mem_center_iff]
      intro; ext; simp [hf]
  rcases subsingleton_or_nontrivial ι with hι | hι
  · exfalso
    contrapose hV
    have : Nonempty ι := inferInstance
    have : Fintype ι := Fintype.ofFinite ι
    rw [finrank_eq_card_basis b, ← Nat.card_eq_fintype_card,
    Nat.card_eq_one_iff_unique]
    aesop
  exact mem_center_iff_of_basis b

variable [Ring R] [StrongRankCondition R]
    [AddCommGroup V] [Module R V] [Free R V]

end LinearEquiv

namespace LinearMap.GeneralLinearGroup

theorem isUnit_ratio
    [Semiring R] [AddCommMonoid V] [Module R V] [Free R V] [Nontrivial V]
    {f : GeneralLinearGroup R V} {a : R} (hfa : ∀ x, f.val x = a • x) :
    IsUnit a := by
  apply LinearEquiv.isUnit_ratio (f := f.toLinearEquiv)
  aesop

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

def centerMap [Semiring R] [AddCommMonoid V] [Module R V] :
    Subgroup.center Rˣ →* Subgroup.center (V →ₗ[R] V)ˣ :=
  sorry

end LinearMap.GeneralLinearGroup
