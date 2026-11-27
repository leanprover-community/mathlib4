/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Gareth Ma, Seewoo Lee
-/
module

public import Mathlib.Algebra.Module.Lattice.Even
public import Mathlib.Algebra.Module.Lattice.Full
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The checkerboard lattice `Dₙ`

We define the checkerboard lattice: the `ℤ`-submodule of `Fin n → R` consisting of the integer
vectors whose coordinates have even sum. For `n ≥ 3` this is the root lattice of type `Dₙ`.

## Main definitions

* `Submodule.checkerboardLatticeInt n`: the checkerboard lattice as a submodule of `Fin n → ℤ`.
* `Submodule.checkerboardLattice R n`: the checkerboard lattice as a submodule of `Fin n → R`,
  defined as the image of `Submodule.checkerboardLatticeInt n` under the coordinatewise cast
  `ℤ → R`.
* `EuclideanSpace.checkerboardLattice n`: the checkerboard lattice as a submodule of
  `EuclideanSpace ℝ (Fin n)`.

## Main results

* `Submodule.mem_checkerboardLattice`: if `R` has characteristic zero, then `v : Fin n → R` lies in
  `Submodule.checkerboardLattice R n` if and only if all coordinates of `v` are integers and their
  sum is even.
* `Submodule.checkerboardLattice ℝ n` is a full lattice in `Fin n → ℝ`, in the sense of
  `Submodule.IsFullLattice`. Hence so is `EuclideanSpace.checkerboardLattice n` in
  `EuclideanSpace ℝ (Fin n)`.
* `EuclideanSpace.isEven_checkerboardLattice`: the checkerboard lattice is even.
* `EuclideanSpace.isIntegral_checkerboardLattice`: the checkerboard lattice is integral.
-/

@[expose] public section

namespace Submodule

/-- The checkerboard lattice in `Fin n → ℤ`: the integer vectors whose coordinates have even
sum. -/
def checkerboardLatticeInt (n : ℕ) : Submodule ℤ (Fin n → ℤ) where
  carrier := {v | ∑ i, v i ≡ 0 [PMOD 2]}
  add_mem' ha hb := by simpa [Finset.sum_add_distrib] using ha.add hb
  zero_mem' := by simp
  smul_mem' c _ ha := by simpa [Finset.mul_sum] using ha.zsmul' (z := c)

@[simp]
lemma mem_checkerboardLatticeInt {n : ℕ} {v : Fin n → ℤ} :
    v ∈ checkerboardLatticeInt n ↔ ∑ i, v i ≡ 0 [PMOD 2] :=
  Iff.rfl

/-- The checkerboard lattice in `Fin n → R`: the image of `Submodule.checkerboardLatticeInt n`
under the coordinatewise cast `ℤ → R`. -/
def checkerboardLattice (R : Type*) [Ring R] (n : ℕ) : Submodule ℤ (Fin n → R) :=
  (checkerboardLatticeInt n).map ((Algebra.linearMap ℤ R).compLeft (Fin n))

lemma coe_checkerboardLattice (R : Type*) [Ring R] [CharZero R] (n : ℕ) :
    (checkerboardLattice R n : Set (Fin n → R)) =
      {v | (∀ i, ∃ m : ℤ, (m : R) = v i) ∧ ∑ i, v i ≡ 0 [PMOD 2]} := by
  ext v
  simp only [checkerboardLattice, map_coe, Set.mem_image, SetLike.mem_coe,
    mem_checkerboardLatticeInt, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨fun i ↦ ⟨w i, by simp⟩, by simpa using hw.map (Int.castAddHom R)⟩
  · rintro ⟨hv, hv'⟩
    choose w hw using hv
    refine ⟨w, ?_, by ext; simp [hw]⟩
    rw [← AddCommGroup.map_modEq_iff (Int.castAddHom R) Int.cast_injective]
    simpa [← hw] using hv'

lemma mem_checkerboardLattice {R : Type*} [Ring R] [CharZero R] (n : ℕ) {v : Fin n → R} :
    v ∈ checkerboardLattice R n ↔ (∀ i, ∃ m : ℤ, (m : R) = v i) ∧ ∑ i, v i ≡ 0 [PMOD 2] :=
  Set.ext_iff.1 (coe_checkerboardLattice R n) v

lemma checkerboardLattice_le_span (n : ℕ) :
    checkerboardLattice ℝ n ≤ span ℤ (Set.range (Pi.basisFun ℝ (Fin n))) := fun v hv ↦
  (Module.Basis.mem_span_iff_repr_mem ℤ _ _).2 fun i ↦ by
    simpa using ((mem_checkerboardLattice n).1 hv).1 i

instance (n : ℕ) : IsFullLattice ℝ (checkerboardLattice ℝ n) where
  toIsLattice := IsLattice.mono ℝ (checkerboardLattice_le_span n)
  span_eq_top := by
    refine eq_top_iff.2 ((Pi.basisFun ℝ (Fin n)).span_eq.ge.trans (span_le.2 ?_))
    rintro _ ⟨i, rfl⟩
    have h : Pi.single i (2 : ℝ) ∈ checkerboardLattice ℝ n := by
      refine (mem_checkerboardLattice n).2 ⟨fun j ↦ ?_, by simp⟩
      obtain rfl | h := eq_or_ne j i
      · exact ⟨2, by simp⟩
      · exact ⟨0, by simp [h]⟩
    simpa [← Pi.single_smul] using (span ℝ _).smul_mem (2⁻¹ : ℝ) (subset_span h)

end Submodule

namespace EuclideanSpace

open scoped InnerProductSpace

/-- The checkerboard lattice `Dₙ` as a submodule of `n`-dimensional Euclidean space. -/
noncomputable abbrev checkerboardLattice (n : ℕ) : Submodule ℤ (EuclideanSpace ℝ (Fin n)) :=
  (Submodule.checkerboardLattice ℝ n).comap
    ((EuclideanSpace.equiv (Fin n) ℝ).toLinearEquiv.restrictScalars ℤ).toLinearMap

/-- The checkerboard lattice is even: `‖v‖ ^ 2` is an even integer for every `v ∈ Dₙ`. -/
theorem isEven_checkerboardLattice (n : ℕ) : (checkerboardLattice n).IsEven := by
  intro x hx
  change x.ofLp ∈ Submodule.checkerboardLattice ℝ n at hx
  obtain ⟨w, hw, hx⟩ := Submodule.mem_map.1 hx
  obtain ⟨z, hz⟩ := AddCommGroup.modEq_zero_iff_eq_zsmul.1 hw
  obtain ⟨m, hm⟩ := even_iff_exists_two_mul.1 <|
    Finset.even_sum _ fun i _ ↦ Int.even_mul_pred_self (w i)
  refine ⟨z + m, ?_⟩
  have hxi (i : Fin n) : x.ofLp i = w i := by simp [← hx]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, hxi]
  simp only [mul_sub, mul_one, Finset.sum_sub_distrib, smul_eq_mul] at hm hz
  exact_mod_cast (by linarith : ∑ i, w i * w i = 2 * (z + m))

/-- The checkerboard lattice is integral: `⟪v, w⟫` is an integer for all `v, w ∈ Dₙ`. -/
theorem isIntegral_checkerboardLattice (n : ℕ) : (checkerboardLattice n).IsIntegral :=
  (isEven_checkerboardLattice n).isIntegral

end EuclideanSpace
