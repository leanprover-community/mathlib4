/-
Copyright (c) 2026 Jeromie N. Beasley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeromie N. Beasley
-/
module

public import Mathlib.GroupTheory.Coxeter.Basic
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Group

/-!
# Rank-two Coxeter groups and dihedral groups

This file identifies the Coxeter group associated to `CoxeterMatrix.I m` with the concrete
`DihedralGroup (m + 2)`.

The canonical homomorphism sends the two simple reflections to two adjacent reflections of the
regular `(m + 2)`-gon. We prove a two-coset normal form in the presented Coxeter group and use it
to prove that this homomorphism is bijective.
-/

namespace CoxeterMatrix.I

open DihedralGroup

/-- The two adjacent reflections in the concrete dihedral group. -/
private def dihedralSimple (m : ℕ) : Fin 2 → DihedralGroup (m + 2) := fun i =>
  if i = 0 then sr 0 else sr 1

private theorem dihedralSimple_isLiftable (m : ℕ) :
    CoxeterMatrix.IsLiftable (CoxeterMatrix.I m) (dihedralSimple m) := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [dihedralSimple, CoxeterMatrix.I, DihedralGroup.r_pow]

/-- The canonical homomorphism from the rank-two Coxeter group to the corresponding dihedral
 group. -/
def toDihedral (m : ℕ) :
    (CoxeterMatrix.I m).Group →* DihedralGroup (m + 2) :=
  (CoxeterMatrix.I m).toCoxeterSystem.lift
    ⟨dihedralSimple m, dihedralSimple_isLiftable m⟩

@[simp] theorem toDihedral_simple_zero (m : ℕ) :
    toDihedral m ((CoxeterMatrix.I m).simple (0 : Fin 2)) = sr 0 := by
  simpa [toDihedral, dihedralSimple] using
    (CoxeterMatrix.I m).toCoxeterSystem.lift_apply_simple
      (dihedralSimple_isLiftable m) (0 : Fin 2)

@[simp] theorem toDihedral_simple_one (m : ℕ) :
    toDihedral m ((CoxeterMatrix.I m).simple (1 : Fin 2)) = sr 1 := by
  simpa [toDihedral, dihedralSimple] using
    (CoxeterMatrix.I m).toCoxeterSystem.lift_apply_simple
      (dihedralSimple_isLiftable m) (1 : Fin 2)

@[simp] theorem toDihedral_simple_mul_simple (m : ℕ) :
    toDihedral m
      ((CoxeterMatrix.I m).simple (0 : Fin 2) *
        (CoxeterMatrix.I m).simple (1 : Fin 2)) = r 1 := by
  simp

/-- The canonical homomorphism onto the concrete dihedral group is surjective. -/
theorem toDihedral_surjective (m : ℕ) : Function.Surjective (toDihedral m) := by
  intro d
  cases d with
  | r i =>
      refine ⟨(((CoxeterMatrix.I m).simple (0 : Fin 2) *
        (CoxeterMatrix.I m).simple (1 : Fin 2)) ^ i.val), ?_⟩
      simp
  | sr i =>
      refine ⟨((CoxeterMatrix.I m).simple (0 : Fin 2) *
        (((CoxeterMatrix.I m).simple (0 : Fin 2) *
          (CoxeterMatrix.I m).simple (1 : Fin 2)) ^ i.val)), ?_⟩
      simp

private abbrev IGroup (m : ℕ) := (CoxeterMatrix.I m).Group

private def c0 (m : ℕ) : IGroup m := (CoxeterMatrix.I m).simple (0 : Fin 2)
private def c1 (m : ℕ) : IGroup m := (CoxeterMatrix.I m).simple (1 : Fin 2)
private def rot (m : ℕ) : IGroup m := c0 m * c1 m

@[simp] private theorem c0_sq (m : ℕ) : c0 m * c0 m = 1 := by
  simpa [c0] using
    (CoxeterMatrix.I m).toCoxeterSystem.simple_mul_simple_self (0 : Fin 2)

@[simp] private theorem c1_sq (m : ℕ) : c1 m * c1 m = 1 := by
  simpa [c1] using
    (CoxeterMatrix.I m).toCoxeterSystem.simple_mul_simple_self (1 : Fin 2)

@[simp] private theorem c0_inv (m : ℕ) : (c0 m)⁻¹ = c0 m := by
  exact (eq_inv_of_mul_eq_one_right (c0_sq m)).symm

@[simp] private theorem c1_inv (m : ℕ) : (c1 m)⁻¹ = c1 m := by
  exact (eq_inv_of_mul_eq_one_right (c1_sq m)).symm

private theorem rot_pow_order (m : ℕ) : (rot m) ^ (m + 2) = 1 := by
  change (((CoxeterMatrix.I m).toCoxeterSystem.simple (0 : Fin 2) *
    (CoxeterMatrix.I m).toCoxeterSystem.simple (1 : Fin 2)) ^ (m + 2) = 1)
  simpa [CoxeterMatrix.I] using
    (CoxeterMatrix.I m).toCoxeterSystem.simple_mul_simple_pow
      (0 : Fin 2) (1 : Fin 2)

private theorem c1_eq_c0_mul_rot (m : ℕ) : c1 m = c0 m * rot m := by
  calc
    c1 m = 1 * c1 m := by simp
    _ = (c0 m * c0 m) * c1 m := by rw [c0_sq]
    _ = c0 m * (c0 m * c1 m) := by simp only [mul_assoc]
    _ = c0 m * rot m := by rfl

@[simp] private theorem c0_mul_rot_mul_c0 (m : ℕ) :
    c0 m * rot m * c0 m = (rot m)⁻¹ := by
  rw [rot]
  calc
    c0 m * (c0 m * c1 m) * c0 m
        = (c0 m * c0 m) * c1 m * c0 m := by simp only [mul_assoc]
    _ = c1 m * c0 m := by simp
    _ = (c0 m * c1 m)⁻¹ := by simp [mul_inv_rev]

private theorem c0_mul_rot_zpow_mul_c0 (m : ℕ) (k : ℤ) :
    c0 m * (rot m) ^ k * c0 m = (rot m) ^ (-k) := by
  calc
    c0 m * (rot m) ^ k * c0 m
        = c0 m * (rot m) ^ k * (c0 m)⁻¹ := by simp
    _ = (c0 m * rot m * (c0 m)⁻¹) ^ k := by
          simpa using (conj_zpow (a := c0 m) (b := rot m) (i := k)).symm
    _ = ((rot m)⁻¹) ^ k := by simp
    _ = (rot m) ^ (-k) := by simp

private theorem rot_zpow_mul_c0 (m : ℕ) (k : ℤ) :
    (rot m) ^ k * c0 m = c0 m * (rot m) ^ (-k) := by
  calc
    (rot m) ^ k * c0 m
        = 1 * ((rot m) ^ k * c0 m) := by simp
    _ = (c0 m * c0 m) * ((rot m) ^ k * c0 m) := by rw [c0_sq]
    _ = c0 m * (c0 m * (rot m) ^ k * c0 m) := by simp only [mul_assoc]
    _ = c0 m * (rot m) ^ (-k) := by rw [c0_mul_rot_zpow_mul_c0]

private theorem rot_zpow_mul_c1 (m : ℕ) (k : ℤ) :
    (rot m) ^ k * c1 m = c0 m * (rot m) ^ (-k + 1) := by
  rw [c1_eq_c0_mul_rot, ← mul_assoc, rot_zpow_mul_c0]
  group

private theorem c0_mul_rot_zpow_mul_c1 (m : ℕ) (k : ℤ) :
    c0 m * (rot m) ^ k * c1 m = (rot m) ^ (-k + 1) := by
  rw [c1_eq_c0_mul_rot, ← mul_assoc, c0_mul_rot_zpow_mul_c0]
  group

private def HasDihedralNormalForm (m : ℕ) (w : IGroup m) : Prop :=
  ∃ k : ℤ, w = (rot m) ^ k ∨ w = c0 m * (rot m) ^ k

private theorem hasDihedralNormalForm (m : ℕ) (w : IGroup m) :
    HasDihedralNormalForm m w := by
  let cs := (CoxeterMatrix.I m).toCoxeterSystem
  apply cs.simple_induction_right w
  · refine ⟨0, Or.inl ?_⟩
    simp
  · intro w i hw
    rcases hw with ⟨k, hk | hk⟩
    · subst w
      fin_cases i
      · refine ⟨-k, Or.inr ?_⟩
        exact rot_zpow_mul_c0 m k
      · refine ⟨-k + 1, Or.inr ?_⟩
        exact rot_zpow_mul_c1 m k
    · subst w
      fin_cases i
      · refine ⟨-k, Or.inl ?_⟩
        exact c0_mul_rot_zpow_mul_c0 m k
      · refine ⟨-k + 1, Or.inl ?_⟩
        exact c0_mul_rot_zpow_mul_c1 m k

@[simp] private theorem toDihedral_c0 (m : ℕ) : toDihedral m (c0 m) = sr 0 := by
  simpa [c0] using toDihedral_simple_zero m

@[simp] private theorem toDihedral_rot (m : ℕ) : toDihedral m (rot m) = r 1 := by
  simpa [rot, c0, c1] using toDihedral_simple_mul_simple m

private theorem eq_one_of_toDihedral_eq_one (m : ℕ) {w : IGroup m}
    (hw : toDihedral m w = 1) : w = 1 := by
  obtain ⟨k, hk | hk⟩ := hasDihedralNormalForm m w
  · subst w
    have hr : (r 1 : DihedralGroup (m + 2)) ^ k = 1 := by
      simpa using hw
    have hkdiv : ((m + 2 : ℕ) : ℤ) ∣ k := by
      simpa using (orderOf_dvd_iff_zpow_eq_one.mpr hr)
    have horderNat : orderOf (rot m) ∣ m + 2 :=
      orderOf_dvd_of_pow_eq_one (rot_pow_order m)
    have horderInt : (orderOf (rot m) : ℤ) ∣ ((m + 2 : ℕ) : ℤ) := by
      exact Int.natCast_dvd_natCast.mpr horderNat
    exact orderOf_dvd_iff_zpow_eq_one.mp (horderInt.trans hkdiv)
  · subst w
    exfalso
    have hbad :
        (sr (k : ZMod (m + 2)) : DihedralGroup (m + 2)) = r 0 := by
      simpa [DihedralGroup.r_one_zpow] using hw
    cases hbad

/-- The canonical homomorphism from the rank-two Coxeter group to the dihedral group is
injective. -/
theorem toDihedral_injective (m : ℕ) : Function.Injective (toDihedral m) := by
  rw [injective_iff_map_eq_one]
  intro w hw
  exact eq_one_of_toDihedral_eq_one m hw

/-- The Coxeter group associated to `CoxeterMatrix.I m` is the dihedral group of the regular
`(m + 2)`-gon. -/
noncomputable def groupEquivDihedralGroup (m : ℕ) :
    (CoxeterMatrix.I m).Group ≃* DihedralGroup (m + 2) :=
  MulEquiv.ofBijective (toDihedral m)
    ⟨toDihedral_injective m, toDihedral_surjective m⟩

@[simp] theorem groupEquivDihedralGroup_apply_simple_zero (m : ℕ) :
    groupEquivDihedralGroup m ((CoxeterMatrix.I m).simple (0 : Fin 2)) = sr 0 := by
  exact toDihedral_simple_zero m

@[simp] theorem groupEquivDihedralGroup_apply_simple_one (m : ℕ) :
    groupEquivDihedralGroup m ((CoxeterMatrix.I m).simple (1 : Fin 2)) = sr 1 := by
  exact toDihedral_simple_one m

end CoxeterMatrix.I
