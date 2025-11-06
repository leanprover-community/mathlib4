/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
import Mathlib.Topology.Instances.CantorSet
import Mathlib.Topology.UnitInterval

/-!
# Hausdorff–Alexandroff Theorem

In this file, we prove the Hausdorff–Alexandroff theorem, which states that every compact
metric space is a continuous image of the Cantor set.

## Proof Outline

First, note that the Cantor set is homeomorphic to `ℕ → Bool`, as shown in
`Mathlib.Topology.Instances.CantorSet`. Therefore, in this file, we work only with the space
`ℕ → Bool` and refer to it as the "Cantor space".

The proof consists of three steps. Let `X` be a compact metric space.

1. Every compact metric space is homeomorphic to a closed subset of the Hilbert cube.
   This is already proved in `Mathlib.Topology.Compactness.HilbertCubeEmbedding`. Using this result,
   we may assume that `X` is a closed subset of the Hilbert cube.
2. We construct a continuous surjection `cantorToHilbert` from the Cantor space to the Hilbert
   cube.
3. Taking the preimage of `X` under this surjection, it remains to prove that any closed
   subset of the Cantor space is the continuous image of the Cantor space.
-/

open Real

/-- Convert a sequence of binary digits to a real number from `unitInterval`. -/
noncomputable def fromBinary (b : ℕ → Bool) : unitInterval :=
  let φ : (ℕ → Bool) ≃ₜ (ℕ → Fin 2) := Homeomorph.piCongrRight
    (fun _ ↦ finTwoEquiv.toHomeomorphOfDiscrete.symm)
  ⟨ofDigits (φ b), ofDigits_nonneg _, ofDigits_le_one _⟩

theorem fromBinary_continuous : Continuous fromBinary := by
  unfold fromBinary
  apply Continuous.subtype_mk
  have : (fun x ↦ ofDigits
      ((Homeomorph.piCongrRight fun _ ↦ finTwoEquiv.toHomeomorphOfDiscrete.symm) x)) =
      ofDigits ∘ (Homeomorph.piCongrRight fun _ ↦ finTwoEquiv.toHomeomorphOfDiscrete.symm) := by
    ext
    simp
  rw [this, Homeomorph.comp_continuous_iff']
  exact continuous_ofDigits

theorem fromBinary_surjective : Function.Surjective fromBinary := by
  intro x
  obtain ⟨x, hx⟩ := x
  by_cases hx_one : x = 1
  · use fun _ ↦ true
    have : fromBinary (fun _ ↦ true) = ofDigits (b := 2) (fun _ ↦ 1) := by
      simp only [fromBinary, Equiv.toHomeomorphOfDiscrete, Equiv.symm_toHomeomorph, Fin.isValue]
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
  use finTwoEquiv ∘ (digits x 2)
  simp only [fromBinary, Subtype.mk.injEq]
  conv => rhs; rw [← ofDigits_digits (b := 2) (by simp) hx]
  congr
  ext n
  simp only [Homeomorph.piCongrRight_apply, Function.comp_apply]
  congr
  simp [Equiv.toHomeomorphOfDiscrete]

/-- A continuous surjection from the Cantor space to the Hilbert cube. -/
noncomputable def cantorToHilbert (x : ℕ → Bool) : ℕ → unitInterval :=
  Pi.map (fun _ b ↦ fromBinary b) (cantorSpaceHomeomorphNatToCantorSpace x)

theorem cantorToHilbert_continuous : Continuous cantorToHilbert := by
  apply continuous_pi
  intro i
  apply fromBinary_continuous.comp
  fun_prop

theorem cantorToHilbert_surjective : Function.Surjective cantorToHilbert := by
  apply Function.Surjective.comp
  · apply Function.Surjective.piMap
    intro _
    apply fromBinary_surjective
  · exact cantorSpaceHomeomorphNatToCantorSpace.surjective
