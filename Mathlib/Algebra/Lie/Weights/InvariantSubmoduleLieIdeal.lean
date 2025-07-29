/-
Copyright (c) 2025 Janos Wolosz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Janos Wolosz
-/
import Mathlib.Algebra.Lie.Weights.RootSystem

/-!
# Invariant submodule to Lie ideal construction

This file contains the construction of Lie ideals from invariant submodules of the dual space
of a Cartan subalgebra.

## Main definitions
* `invtSubmoduleToLieIdeal`: constructs a Lie ideal from an invariant submodule of the dual space

## Main results
* The constructed object is indeed a Lie ideal
-/

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
variable [LieAlgebra.IsKilling K L] [FiniteDimensional K L]

open LieAlgebra LieModule Module IsKilling

variable {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [IsTriangularizable K H L]

/-- Constructs a Lie ideal from an invariant submodule of the dual space of a Cartan subalgebra.
Given a submodule `q` of the dual space `Dual K H` that is invariant under all root reflections,
this produces a Lie ideal by taking the supremum of all `sl₂` subalgebras corresponding to
roots whose linear forms lie in `q`. -/
noncomputable def invtSubmoduleToLieIdeal (q : Submodule K (Dual K H))
    (hq : ∀ i, q ∈ End.invtSubmodule ((rootSystem H).reflection i)) :
    LieIdeal K L where
    __ := ⨆ α : {α : Weight K H L // α.toLinear ∈ q ∧ α.IsNonZero}, sl2SubmoduleOfRoot α.1 α.2.2
    lie_mem := by
      intro x m hm
      have hx : x ∈ ⨆ χ : Weight K H L, genWeightSpace L χ := by
        simp [LieModule.iSup_genWeightSpace_eq_top']
      induction hx using LieSubmodule.iSup_induction' with
      | mem χ x_χ hx_χ =>
        induction hm using LieSubmodule.iSup_induction' with
        | mem α m_α hm_α =>
          have hm_α_original : m_α ∈ sl2SubmoduleOfRoot α.1 α.2.2 := hm_α
          rw [sl2SubmoduleOfRoot_eq_sup] at hm_α
          obtain ⟨m_αneg, hm_αneg, m_h, hm_h, hm_eq⟩ := Submodule.mem_sup.mp hm_α
          obtain ⟨m_pos, hm_pos, m_neg, hm_neg, hm_αneg_eq⟩ := Submodule.mem_sup.mp hm_αneg

          have hm_α_decomp : m_α = m_pos + m_neg + m_h := by
            rw [← hm_eq, ← hm_αneg_eq]

          have h_bracket_sum : ⁅x_χ, m_α⁆ = ⁅x_χ, m_pos⁆ + ⁅x_χ, m_neg⁆ + ⁅x_χ, m_h⁆ := by
            rw [hm_α_decomp, lie_add, lie_add]

          have h_pos_containment : ⁅x_χ, m_pos⁆ ∈ genWeightSpace L (χ.toLinear + α.1.toLinear) := by
            exact lie_mem_genWeightSpace_of_mem_genWeightSpace hx_χ hm_pos

          have h_neg_containment : ⁅x_χ, m_neg⁆ ∈ genWeightSpace L (χ.toLinear - α.1.toLinear) := by
            rw [sub_eq_add_neg]
            exact lie_mem_genWeightSpace_of_mem_genWeightSpace hx_χ hm_neg

          have h_h_containment : ⁅x_χ, m_h⁆ ∈ genWeightSpace L χ := by
            obtain ⟨y, hy, rfl⟩ := hm_h
            have h_zero_weight : H.toLieSubmodule.incl y ∈ genWeightSpace L (0 : H → K) := by
              apply toLieSubmodule_le_rootSpace_zero
              exact y.property
            convert lie_mem_genWeightSpace_of_mem_genWeightSpace hx_χ h_zero_weight
            ext h; simp

          have h_bracket_decomp : ⁅x_χ, m_α⁆ ∈
              genWeightSpace L (χ.toLinear + α.1.toLinear) ⊔
              genWeightSpace L (χ.toLinear - α.1.toLinear) ⊔ genWeightSpace L χ := by
            rw [h_bracket_sum]
            exact add_mem (add_mem
              (Submodule.mem_sup_left (Submodule.mem_sup_left h_pos_containment))
              (Submodule.mem_sup_left (Submodule.mem_sup_right h_neg_containment)))
              (Submodule.mem_sup_right h_h_containment)

          by_cases w_plus : χ.toLinear + α.1.toLinear = 0
          · apply LieSubmodule.mem_iSup_of_mem α
            have hx_χ_in_sl2 : x_χ ∈ sl2SubalgebraOfRoot α.2.2 := by
              obtain ⟨h, e, f, ht, he, hf⟩ := exists_isSl2Triple_of_weight_isNonZero α.2.2
              rw [mem_sl2SubalgebraOfRoot_iff α.2.2 ht he hf]
              have hx_χ_neg : x_χ ∈ genWeightSpace L (-α.1.toLinear) := by
                rw [← (add_eq_zero_iff_eq_neg.mp w_plus)]
                exact hx_χ
              obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' ⟨f, hf⟩ (by simp [ht.f_ne_zero])).mp
                (finrank_rootSpace_eq_one (-α.1) (by simpa using α.2.2)) ⟨x_χ, hx_χ_neg⟩
              exact ⟨0, c, 0, by simpa using hc.symm⟩
            apply LieSubalgebra.lie_mem <;> [exact hx_χ_in_sl2; exact hm_α_original]
          by_cases w_minus : χ.toLinear - α.1.toLinear = 0
          · apply LieSubmodule.mem_iSup_of_mem α
            have hx_χ_in_sl2 : x_χ ∈ sl2SubalgebraOfRoot α.2.2 := by
              obtain ⟨h, e, f, ht, he, hf⟩ := exists_isSl2Triple_of_weight_isNonZero α.2.2
              rw [mem_sl2SubalgebraOfRoot_iff α.2.2 ht he hf]
              have hx_χ_pos : x_χ ∈ genWeightSpace L α.1.toLinear := by
                rw [← (sub_eq_zero.mp w_minus)]
                exact hx_χ
              obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' ⟨e, he⟩ (by simp [ht.e_ne_zero])).mp
                (finrank_rootSpace_eq_one α.1 α.2.2) ⟨x_χ, hx_χ_pos⟩
              exact ⟨c, 0, 0, by simpa using hc.symm⟩
            apply LieSubalgebra.lie_mem <;> [exact hx_χ_in_sl2; exact hm_α_original]
          by_cases w_chi : χ.toLinear = 0
          · have hx_χ_in_H : x_χ ∈ H.toLieSubmodule := by
              rw [← rootSpace_zero_eq K L H]
              convert hx_χ; ext h; simp only [Pi.zero_apply]
              have h_apply : (χ.toLinear : H → K) h = 0 := by rw [w_chi]; rfl
              exact h_apply.symm
            apply LieSubmodule.mem_iSup_of_mem α
            rw [← (by rfl : ⁅(⟨x_χ, hx_χ_in_H⟩ : H), m_α⁆ = ⁅x_χ, m_α⁆)]
            exact (sl2SubmoduleOfRoot α.1 α.2.2).lie_mem hm_α_original

          have get_isNonZero (w : Weight K H L) (h : w.toLinear ≠ 0) : w.IsNonZero := by
            intro h_zero
            apply h
            ext _; simp [Weight.IsZero.eq h_zero]

          by_cases h_chi_in_q : χ.toLinear ∈ q
          · let I := ⨆ β : {β : Weight K H L // β.toLinear ∈ q ∧ β.IsNonZero},
              sl2SubmoduleOfRoot β.1 β.2.2
            have genWeightSpace_le_I (β_lin : H →ₗ[K] K) (hβ_in_q : β_lin ∈ q)
                (hβ_ne_zero : β_lin ≠ 0) : genWeightSpace L β_lin ≤ I := by
              by_cases h_trivial : genWeightSpace L β_lin = ⊥
              · simp [h_trivial]
              · let β : Weight K H L := ⟨β_lin, h_trivial⟩
                have hβ_nonzero : β.IsNonZero := get_isNonZero β hβ_ne_zero
                refine le_trans ?_ (le_iSup _ ⟨β, hβ_in_q, hβ_nonzero⟩)
                rw [sl2SubmoduleOfRoot_eq_sup]
                exact le_sup_of_le_left (le_sup_of_le_left le_rfl)
            have h_plus_contain : genWeightSpace L (χ.toLinear + α.1.toLinear) ≤ I :=
              genWeightSpace_le_I _ (q.add_mem h_chi_in_q α.2.1) w_plus
            have h_minus_contain : genWeightSpace L (χ.toLinear - α.1.toLinear) ≤ I :=
              genWeightSpace_le_I _ (by
                have : -α.1.toLinear = (-1 : K) • α.1.toLinear := by simp
                rw [sub_eq_add_neg, this]
                exact q.add_mem h_chi_in_q (q.smul_mem (-1) α.2.1)) w_minus
            have h_chi_contain : genWeightSpace L χ.toLinear ≤ I :=
              genWeightSpace_le_I _ h_chi_in_q (fun h_eq => (w_chi h_eq).elim)
            exact sup_le (sup_le h_plus_contain h_minus_contain) h_chi_contain h_bracket_decomp
          · let S := rootSystem H
            have exists_root_index (γ : Weight K H L) (hγ : γ.IsNonZero) :
              ∃ i, S.root i = γ.toLinear := ⟨⟨γ, by simp [LieSubalgebra.root]; exact hγ⟩, rfl⟩
            have h_plus_bot : genWeightSpace L (χ.toLinear + α.1.toLinear) = ⊥ := by
              by_contra h_plus_ne_bot
              let γ : Weight K H L := ⟨χ.toLinear + α.1.toLinear, h_plus_ne_bot⟩
              have hγ_nonzero : γ.IsNonZero := get_isNonZero γ w_plus
              obtain ⟨i, hi⟩ := exists_root_index χ (get_isNonZero χ w_chi)
              obtain ⟨j, hj⟩ := exists_root_index α.1 α.2.2
              have h_sum_in_range : S.root i + S.root j ∈ Set.range S.root := by
                rw [hi, hj]
                exact ⟨⟨γ, by simp [LieSubalgebra.root]; exact hγ_nonzero⟩, rfl⟩
              have h_equiv := RootPairing.root_mem_submodule_iff_of_add_mem_invtSubmodule
                ⟨q, by rw [RootPairing.mem_invtRootSubmodule_iff]; exact hq⟩ h_sum_in_range
              rw [hi] at h_equiv
              exact h_chi_in_q (h_equiv.mpr (by rw [hj]; exact α.2.1))

            have h_minus_bot : genWeightSpace L (χ.toLinear - α.1.toLinear) = ⊥ := by
              by_contra h_minus_ne_bot
              let γ : Weight K H L := ⟨χ.toLinear - α.1.toLinear, h_minus_ne_bot⟩
              have hγ_nonzero : γ.IsNonZero := get_isNonZero γ w_minus
              obtain ⟨i, hi⟩ := exists_root_index χ (get_isNonZero χ w_chi)
              obtain ⟨j, hj⟩ := exists_root_index (-α.1) (Weight.IsNonZero.neg α.2.2)
              have h_sum_in_range : S.root i + S.root j ∈ Set.range S.root := by
                rw [hi, hj, Weight.toLinear_neg, ← sub_eq_add_neg]
                exact ⟨⟨γ, by simp [LieSubalgebra.root]; exact hγ_nonzero⟩, rfl⟩
              have h_equiv := RootPairing.root_mem_submodule_iff_of_add_mem_invtSubmodule
                ⟨q, by rw [RootPairing.mem_invtRootSubmodule_iff]; exact hq⟩ h_sum_in_range
              rw [hi] at h_equiv
              exact h_chi_in_q (h_equiv.mpr (by
                rw [hj, Weight.toLinear_neg]
                convert q.smul_mem (-1) α.2.1 using 1
                rw [neg_smul, one_smul]))

            obtain ⟨i, hi⟩ := exists_root_index χ (get_isNonZero χ w_chi)
            obtain ⟨j, hj⟩ := exists_root_index α.1 α.2.2
            have h_pairing_zero : S.pairing i j = 0 := by
              obtain ⟨i', j', hi', hj', h_zero⟩ := pairing_zero_of_bot_sum_diff_spaces
                H χ α.1 (get_isNonZero χ w_chi) α.2.2 w_plus w_minus h_plus_bot h_minus_bot
              have h_i_eq : i = i' := Function.Embedding.injective S.root (by rw [hi, hi'])
              have h_j_eq : j = j' := Function.Embedding.injective S.root (by rw [hj, hj'])
              rwa [h_i_eq, h_j_eq]

            have h_pos_zero : ⁅x_χ, m_pos⁆ = 0 := by
              have h_in_bot : ⁅x_χ, m_pos⁆ ∈ (⊥ : LieSubmodule K H L) := by
                rw [← h_plus_bot]
                exact h_pos_containment
              rwa [LieSubmodule.mem_bot] at h_in_bot

            have h_neg_zero : ⁅x_χ, m_neg⁆ = 0 := by
              have h_in_bot : ⁅x_χ, m_neg⁆ ∈ (⊥ : LieSubmodule K H L) := by
                rw [← h_minus_bot]
                exact h_neg_containment
              rwa [LieSubmodule.mem_bot] at h_in_bot

            have h_bracket_zero : ⁅x_χ, m_h⁆ = 0 := by
              have h_chi_coroot_zero : χ (coroot α.1) = 0 := by
                have h_pairing_eq : S.pairing i j = i.1 (coroot j.1) := by
                  rw [rootSystem_pairing_apply]
                rw [h_pairing_zero] at h_pairing_eq
                have w_eq {w₁ w₂ : Weight K H L} (h : w₁.toLinear = w₂.toLinear) : w₁ = w₂ := by
                  apply Weight.ext; intro x; exact LinearMap.ext_iff.mp h x
                have hi_val : i.1 = χ := w_eq (by rw [← hi]; rfl)
                have hj_val : j.1 = α.1 := w_eq (by rw [← hj]; rfl)
                rw [hi_val, hj_val] at h_pairing_eq
                exact h_pairing_eq.symm
              obtain ⟨h_elem, hh_elem, hh_eq⟩ := hm_h
              have h_lie_eq_smul : ⁅(h_elem : L), x_χ⁆ = (χ.toLinear) h_elem • x_χ :=
                lie_eq_smul_of_mem_rootSpace hx_χ h_elem
              have h_chi_h_zero : (χ.toLinear) h_elem = 0 := by
                obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp <| by
                  rw [← coe_corootSpace_eq_span_singleton α.1, LieSubmodule.mem_toSubmodule]
                  exact hh_elem
                rw [← hc, LinearMap.map_smul]
                have h_convert : (χ.toLinear) (coroot α.1) = χ (coroot α.1) := rfl
                rw [h_convert, h_chi_coroot_zero, smul_zero]
              have h_bracket_elem : ⁅x_χ, (h_elem : L)⁆ = 0 := by
                rw [← lie_skew, h_lie_eq_smul, h_chi_h_zero, zero_smul, neg_zero]
              rw [← hh_eq]
              exact h_bracket_elem
            rw [h_bracket_sum, h_pos_zero, h_neg_zero, h_bracket_zero]
            simp only [Submodule.carrier_eq_coe, add_zero, SetLike.mem_coe, zero_mem]
        | zero =>
          simp only [ Submodule.carrier_eq_coe, lie_zero, SetLike.mem_coe, zero_mem]
        | add m₁ m₂ _ _ ih₁ ih₂ =>
          simp only [lie_add, Submodule.carrier_eq_coe, SetLike.mem_coe] at ih₁ ih₂ ⊢
          exact add_mem ih₁ ih₂
      | zero =>
        simp only [Submodule.carrier_eq_coe, zero_lie, SetLike.mem_coe, zero_mem]
      | add x₁ x₂ _ _ ih₁ ih₂ =>
        simp only [add_lie, Submodule.carrier_eq_coe, SetLike.mem_coe] at ih₁ ih₂ ⊢
        exact add_mem ih₁ ih₂
