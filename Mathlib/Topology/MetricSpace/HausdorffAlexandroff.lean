/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
import Mathlib.Data.Real.OfDigits
import Mathlib.Topology.Instances.CantorSet
import Mathlib.Topology.UnitInterval

/-!
# Hausdorff-Alexandroff theorem

In this file we prove the Hausdorff-Alexandroff theorem stating that every compact metric space is a
continuous image of the Cantor set.

## Proof outline

First note that the Cantor set is homeomorphic to `ℕ → Bool` which is proved in
`Mathlib.Topology.Instances.CantorSet`, so in this file we will be only dealing with the space
`ℕ → Bool` and refer to it as a "Cantor space".

The proofs consists of three steps. Let `X` be a compact metric space.

1. Any compact metric space is homeomorphic to a closed subset of the Hilbert cube.
  This is already proved in `Mathlib.Topology.Compactness.HilberCubeEmbedding`. Using this we can
  assume that `X` is a closed subset of the Hilbert cube.
2. We construct the continuous surjection `cantorToHilbert` from the Cantor space to the Hilbert
  cube.
3. Taking the preimage of the `X` under this surjection it's now enough to prove that any closed
  subset of the Cantor space admits a continuous surjection from the Cantor space.
-/

universe u v w

-- TODO: move
/-- TODO -/
def DiscreteTopology.equiv_to_homeomorph {X : Type u} {Y : Type v}
    [TopologicalSpace X] [DiscreteTopology X]
    [TopologicalSpace Y] [DiscreteTopology Y] (eq : X ≃ Y) : X ≃ₜ Y :=
  eq.toHomeomorph (by simp)

-- TODO: move
/-- TODO -/
def finTwoHomeoBool : Fin 2 ≃ₜ Bool :=
  DiscreteTopology.equiv_to_homeomorph finTwoEquiv

/-- Convert a sequence of binary digits to a real number from `unitInterval`. -/
noncomputable def fromBinary (b : ℕ → Bool) : unitInterval :=
  let φ : (ℕ → Bool) ≃ₜ (ℕ → Fin 2) := Homeomorph.piCongrRight (fun _ ↦ finTwoHomeoBool.symm)
  let x : ℝ := ofDigits (φ b)
  have hx : x ∈ Set.Icc 0 1 := by
    simp [x]
    constructor
    · exact ofDigits_nonneg
    · exact ofDigits_le_one
  ⟨x, hx⟩

theorem fromBinary_continuous : Continuous fromBinary := by
  unfold fromBinary
  apply Continuous.subtype_mk
  have : (fun x ↦ ofDigits ((Homeomorph.piCongrRight fun _ ↦ finTwoHomeoBool.symm) x)) =
      ofDigits ∘ (Homeomorph.piCongrRight fun _ ↦ finTwoHomeoBool.symm) := by
    ext
    simp
  rw [this, Homeomorph.comp_continuous_iff']
  exact ofDigits_continuous

theorem fromBinary_surjective : Function.Surjective fromBinary := by
  intro x
  obtain ⟨x, hx⟩ := x
  by_cases hx_one : x = 1
  · use fun _ ↦ true
    have : fromBinary (fun _ ↦ true) = ofDigits (b := 2) (fun _ ↦ 1) := by
      simp [fromBinary, finTwoHomeoBool, DiscreteTopology.equiv_to_homeomorph]
      congr
    simp only [hx_one, Set.Icc.mk_one, Subtype.eq_iff, this, ofDigits, ofDigitsTerm, Fin.isValue,
      Fin.val_one, Nat.cast_one, Nat.cast_ofNat, pow_succ, mul_inv_rev, ← inv_pow, one_mul,
      Set.Icc.coe_one]
    rw [Summable.tsum_mul_left]
    · rw [tsum_geometric_inv_two]
      simp
    · convert summable_geometric_two
      eta_expand
      simp
  replace hx : x ∈ Set.Ico 0 1 := by
    simp at hx ⊢
    exact ⟨hx.left, by apply hx.right.lt_of_ne' (by symm; simpa)⟩
  use finTwoEquiv ∘ (toDigits x 2)
  simp only [fromBinary, Subtype.mk.injEq]
  conv => rhs; rw [← toDigits_ofDigits 2 x (by simp) hx]
  congr
  ext n
  simp only [Homeomorph.piCongrRight_apply, Function.comp_apply]
  congr
  simp [finTwoHomeoBool, DiscreteTopology.equiv_to_homeomorph]

/-- A continuous surjection from the Cantor space to the Hilbert cube. -/
noncomputable def cantorToHilbert (x : ℕ → Bool) : ℕ → unitInterval :=
  Pi.map (fun _ b ↦ fromBinary b) (cantorSpace_homeomorph_nat_cantorSpace x)

theorem cantorToHilbert_continuous : Continuous cantorToHilbert := by
  unfold cantorToHilbert
  apply continuous_pi
  intro i
  apply fromBinary_continuous.comp
  fun_prop

theorem cantorToHilbert_surjective : Function.Surjective cantorToHilbert := by
  unfold cantorToHilbert
  change Function.Surjective
    ((Pi.map (fun x b ↦ fromBinary b)) ∘ cantorSpace_homeomorph_nat_cantorSpace)
  apply Function.Surjective.comp
  · apply Function.Surjective.piMap
    intro _
    apply fromBinary_surjective
  · exact Homeomorph.surjective cantorSpace_homeomorph_nat_cantorSpace
