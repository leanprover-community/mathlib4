import Mathlib.Algebra.Lie.Sl2
import Mathlib.Algebra.Lie.Weights.Basic
import Mathlib.Algebra.Lie.Weights.Cartan
import Mathlib.Algebra.Lie.Weights.Killing
import Mathlib.Algebra.Lie.Weights.RootSystem
import Mathlib.LinearAlgebra.RootSystem.Finite.Lemmas

set_option maxHeartbeats 1000000

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
variable [LieAlgebra.IsKilling K L] [FiniteDimensional K L]

open LieAlgebra LieModule Module
open IsKilling (sl2SubalgebraOfRoot rootSystem)

variable {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [IsTriangularizable K H L]

/--
Core lemma: If two roots χ and α satisfy that both L(χ + α) and L(χ - α) are trivial,
then their pairing in the root system is zero.

This is the key step that was left as sorry in the main proof.
-/
lemma pairing_zero_of_trivial_sum_diff_spaces
  (χ α : Weight K H L) (hχ : χ.IsNonZero) (hα : α.IsNonZero)
  (w_plus : χ.toLinear + α.toLinear ≠ 0) (w_minus : χ.toLinear - α.toLinear ≠ 0)
  (h_plus_bot : genWeightSpace L (χ.toLinear + α.toLinear) = ⊥)
  (h_minus_bot : genWeightSpace L (χ.toLinear - α.toLinear) = ⊥) :
  let S := LieAlgebra.IsKilling.rootSystem H
  ∃ (i j : { w : Weight K H L // w ∈ H.root }),
    S.root i = χ.toLinear ∧ S.root j = α.toLinear ∧ S.pairing i j = 0 := by

  let S := LieAlgebra.IsKilling.rootSystem H

  -- Get root indices for χ and α
  have hχ_in_root : χ ∈ H.root := by
    simp [LieSubalgebra.root]
    exact hχ
  have hα_in_root : α ∈ H.root := by
    simp [LieSubalgebra.root]
    exact hα

  let i : { w : Weight K H L // w ∈ H.root } := ⟨χ, hχ_in_root⟩
  let j : { w : Weight K H L // w ∈ H.root } := ⟨α, hα_in_root⟩

  use i, j
  constructor
  · -- S.root i = χ.toLinear
    rfl
  constructor
  · -- S.root j = α.toLinear
    rfl
  · -- The main goal: S.pairing i j = 0
    -- Use trichotomy to consider all cases
    have h_trichotomy : S.pairingIn ℤ i j < 0 ∨ S.pairingIn ℤ i j = 0 ∨ 0 < S.pairingIn ℤ i j := by
      exact lt_trichotomy (S.pairingIn ℤ i j) 0

    cases' h_trichotomy with h_neg h_rest
    · -- Case: S.pairingIn ℤ i j < 0 (negative pairing)
      exfalso
      -- Use root_add_root_mem_of_pairingIn_neg to get contradiction
      have h_add_mem : S.root i + S.root j ∈ Set.range S.root := by
        apply RootPairing.root_add_root_mem_of_pairingIn_neg S.toRootPairing h_neg
        -- Need to show S.root i ≠ -S.root j
        intro h_eq
        -- This would contradict w_plus : χ.toLinear + α.toLinear ≠ 0
        have h_sum_zero : S.root i + S.root j = 0 := by rw [h_eq]; simp
        -- But S.root i = χ.toLinear and S.root j = α.toLinear, so χ + α = 0
        have h_contradiction : χ.toLinear + α.toLinear = 0 := h_sum_zero
        exact w_plus h_contradiction
      -- Now χ + α is a root, contradicting h_plus_bot
      have h_chi_plus_alpha_root : χ.toLinear + α.toLinear ∈ Set.range S.root := h_add_mem
      have h_nontriv : genWeightSpace L (χ.toLinear + α.toLinear) ≠ ⊥ := by
        -- Since χ.toLinear + α.toLinear is in the range of S.root, it corresponds to some root
        obtain ⟨idx, hidx⟩ := h_chi_plus_alpha_root
        -- idx is a subtype element, so idx.val is the actual weight and idx.property proves it's in
        -- LieSubalgebra.root
        -- Since LieSubalgebra.root = {α | α.IsNonZero}, membership implies IsNonZero
        have h_nonzero : idx.val.IsNonZero := by
          -- Convert membership in LieSubalgebra.root to IsNonZero using the definition
          -- LieSubalgebra.root is defined as {α | α.IsNonZero}
          have h_mem := idx.property
          simp only [LieSubalgebra.root, Finset.mem_filter, Finset.mem_univ, true_and] at h_mem
          exact h_mem
        -- Non-zero weights have nontrivial weight spaces
        have h_weight_space_nontrivial := idx.val.genWeightSpace_ne_bot
        -- Now we need to use the connection between S.root and the weight space
        -- The key insight: S.root idx should equal idx.val.toLinear, and this should match hidx
        have h_root_eq : S.root idx = idx.val.toLinear := by
          -- This follows from the definition of rootSystem
          exact LieAlgebra.IsKilling.rootSystem_root_apply H idx
        -- Now we can use transitivity to get our result
        have : genWeightSpace L (S.root idx) ≠ ⊥ := by
          rw [h_root_eq]
          exact h_weight_space_nontrivial
        -- Use hidx to substitute: S.root idx = χ.toLinear + α.toLinear
        have h_final : genWeightSpace L (χ.toLinear + α.toLinear) ≠ ⊥ := by
          convert this using 1
          rw [←hidx]
        exact h_final
      exact h_nontriv h_plus_bot

    · cases' h_rest with h_zero h_pos
      · -- Case: S.pairingIn ℤ i j = 0 (zero pairing)
        -- This is what we want to prove, but we need to convert to S.pairing
        -- S.pairingIn ℤ i j = 0 should imply S.pairing i j = 0
        -- Use S.algebraMap_pairingIn ℤ: algebraMap ℤ K (S.pairingIn ℤ i j) = S.pairing i j
        have h_algebraMap : algebraMap ℤ K (S.pairingIn ℤ i j) = S.pairing i j := by
          exact S.algebraMap_pairingIn ℤ i j
        rw [h_zero, map_zero] at h_algebraMap
        exact h_algebraMap.symm

      · -- Case: S.pairingIn ℤ i j > 0 (positive pairing)
        exfalso
        -- Use root_sub_root_mem_of_pairingIn_pos to get contradiction
        -- First, we need the underlying RootPairing from the RootSystem
        have h_sub_mem : S.root i - S.root j ∈ Set.range S.root := by
          -- Apply the root system lemma - S is already a RootPairing instance
          apply RootPairing.root_sub_root_mem_of_pairingIn_pos S.toRootPairing h_pos
          -- Need to show i ≠ j
          intro h_eq
          -- If i = j then χ = α, which contradicts w_minus
          have h_chi_eq_alpha : χ = α := by
            -- h_eq : i = j where i = ⟨χ, _⟩ and j = ⟨α, _⟩
            injection h_eq
          have h_contradiction : χ.toLinear - α.toLinear = 0 := by
            rw [h_chi_eq_alpha]
            simp
          exact w_minus h_contradiction
        -- Now h_sub_mem tells us χ - α is a root, contradicting h_minus_bot
        -- We have: S.root i - S.root j ∈ Set.range S.root
        -- Since S.root i = χ.toLinear and S.root j = α.toLinear
        -- this means χ.toLinear - α.toLinear ∈ Set.range S.root
        -- So χ - α is a root, hence its weight space should be non-trivial
        have h_chi_minus_alpha_root : χ.toLinear - α.toLinear ∈ Set.range S.root := by
          -- h_sub_mem : S.root i - S.root j ∈ Set.range S.root
          -- We know S.root i = χ.toLinear and S.root j = α.toLinear
          exact h_sub_mem
        -- If γ is a root, then genWeightSpace L γ ≠ ⊥
        have h_nontriv : genWeightSpace L (χ.toLinear - α.toLinear) ≠ ⊥ := by
          -- Since χ.toLinear - α.toLinear is in the range of S.root, it corresponds to some root
          obtain ⟨idx, hidx⟩ := h_chi_minus_alpha_root
          -- idx is a subtype element, so idx.val is the actual weight and idx.property proves it's
          -- in LieSubalgebra.root
          -- Since LieSubalgebra.root = {α | α.IsNonZero}, membership implies IsNonZero
          have h_nonzero : idx.val.IsNonZero := by
            -- Convert membership in LieSubalgebra.root to IsNonZero using the definition
            -- LieSubalgebra.root is defined as {α | α.IsNonZero}
            have h_mem := idx.property
            simp only [LieSubalgebra.root, Finset.mem_filter, Finset.mem_univ, true_and] at h_mem
            exact h_mem
          -- Non-zero weights have nontrivial weight spaces
          have h_weight_space_nontrivial := idx.val.genWeightSpace_ne_bot
          -- Now we need to use the connection between S.root and the weight space
          -- The key insight: S.root idx should equal idx.val.toLinear, and this should match hidx
          have h_root_eq : S.root idx = idx.val.toLinear := by
            -- This follows from the definition of rootSystem
            exact LieAlgebra.IsKilling.rootSystem_root_apply H idx
          -- Now we can use transitivity to get our result
          have : genWeightSpace L (S.root idx) ≠ ⊥ := by
            rw [h_root_eq]
            exact h_weight_space_nontrivial
          -- Use hidx to substitute: S.root idx = χ.toLinear - α.toLinear
          have h_final : genWeightSpace L (χ.toLinear - α.toLinear) ≠ ⊥ := by
            convert this using 1
            rw [←hidx]
          exact h_final
        exact h_nontriv h_minus_bot
