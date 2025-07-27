/-
Copyright (c) 2025 Janos Wolosz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Janos Wolosz
-/
import Mathlib.Algebra.Lie.Sl2
import Mathlib.Algebra.Lie.Weights.Basic
import Mathlib.Algebra.Lie.Weights.Cartan
import Mathlib.Algebra.Lie.Weights.Killing
import Mathlib.Algebra.Lie.Weights.RootSystem
import Mathlib.Algebra.Module.Submodule.Invariant
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.LinearAlgebra.RootSystem.Finite.Lemmas

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

open LieAlgebra LieModule Module
open IsKilling (sl2SubalgebraOfRoot rootSystem)

variable {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [IsTriangularizable K H L]

lemma exists_root_index (γ : Weight K H L) (hγ : γ.IsNonZero) :
    ∃ i, (LieAlgebra.IsKilling.rootSystem H).root i = γ.toLinear :=
  ⟨⟨γ, by simp [LieSubalgebra.root]; exact hγ⟩, rfl⟩

set_option maxHeartbeats 1000000 in
-- The proof involves extensive case analysis.
/-- Constructs a Lie ideal from an invariant submodule of the dual space of a Cartan subalgebra.
Given a submodule `q` of the dual space `Dual K H` that is invariant under all root reflections,
this produces a Lie ideal by taking the supremum of all `sl₂` subalgebras corresponding to
roots whose linear forms lie in `q`. -/
noncomputable def invtSubmoduleToLieIdeal (q : Submodule K (Dual K H))
    (hq : ∀ i, q ∈ End.invtSubmodule ((rootSystem H).reflection i)) :
    LieIdeal K L where
    __ := ⨆ α : {α : Weight K H L // α.toLinear ∈ q ∧ α.IsNonZero},
      IsKilling.sl2SubmoduleOfRoot α.1 α.2.2
    lie_mem := by
      intro x m hm
      have hx : x ∈ ⨆ χ : Weight K H L, genWeightSpace L χ := by
        simp [LieModule.iSup_genWeightSpace_eq_top']
      induction hx using LieSubmodule.iSup_induction' with
      | mem χ x_χ hx_χ =>
        induction hm using LieSubmodule.iSup_induction' with
        | mem α m_α hm_α =>
          have hm_α_original : m_α ∈ IsKilling.sl2SubmoduleOfRoot α.1 α.2.2 := hm_α
          rw [IsKilling.sl2SubmoduleOfRoot_eq_sup] at hm_α
          obtain ⟨m_αneg, hm_αneg, m_h, hm_h, hm_eq⟩ := Submodule.mem_sup.mp hm_α
          obtain ⟨m_pos, hm_pos, m_neg, hm_neg, hm_αneg_eq⟩ := Submodule.mem_sup.mp hm_αneg

          have hm_α_decomp : m_α = m_pos + m_neg + m_h := by
            rw [← hm_eq, ← hm_αneg_eq]

          have hm_pos_weight : m_pos ∈ genWeightSpace L α.1.toLinear := hm_pos
          have hm_neg_weight : m_neg ∈ genWeightSpace L (-α.1).toLinear := hm_neg
          have hm_h_coroot : m_h ∈ IsKilling.corootSubmodule α.1 := hm_h

          have h_bracket_sum : ⁅x_χ, m_α⁆ = ⁅x_χ, m_pos⁆ + ⁅x_χ, m_neg⁆ + ⁅x_χ, m_h⁆ := by
            rw [hm_α_decomp, lie_add, lie_add]

          have h_pos_containment : ⁅x_χ, m_pos⁆ ∈ genWeightSpace L (χ.toLinear + α.1.toLinear) := by
            exact LieAlgebra.lie_mem_genWeightSpace_of_mem_genWeightSpace hx_χ hm_pos

          have h_neg_containment : ⁅x_χ, m_neg⁆ ∈ genWeightSpace L (χ.toLinear - α.1.toLinear) := by
            have h_neg : ⁅x_χ, m_neg⁆ ∈ genWeightSpace L (χ.toLinear + (-α.1).toLinear) := by
              exact LieAlgebra.lie_mem_genWeightSpace_of_mem_genWeightSpace hx_χ hm_neg
            have h_eq : χ.toLinear + (-α.1).toLinear = χ.toLinear - α.1.toLinear := by
              simp [sub_eq_add_neg]
            rw [← h_eq]
            exact h_neg

          have h_h_containment : ⁅x_χ, m_h⁆ ∈ genWeightSpace L χ := by
            obtain ⟨y, hy, rfl⟩ := hm_h
            have h_in_zero : H.toLieSubmodule.incl y ∈ rootSpace H 0 := by
              apply LieAlgebra.toLieSubmodule_le_rootSpace_zero
              exact y.property
            have h_zero_weight : H.toLieSubmodule.incl y ∈ genWeightSpace L (0 : H → K) :=
              h_in_zero
            convert LieAlgebra.lie_mem_genWeightSpace_of_mem_genWeightSpace hx_χ h_zero_weight
            ext h
            simp

          have h_bracket_decomp : ⁅x_χ, m_α⁆ ∈
              genWeightSpace L (χ.toLinear + α.1.toLinear) ⊔
              genWeightSpace L (χ.toLinear - α.1.toLinear) ⊔
              genWeightSpace L χ := by
            rw [h_bracket_sum]
            apply add_mem
            · apply add_mem
              · apply Submodule.mem_sup_left
                apply Submodule.mem_sup_left
                exact h_pos_containment
              · apply Submodule.mem_sup_left
                apply Submodule.mem_sup_right
                exact h_neg_containment
            · apply Submodule.mem_sup_right
              exact h_h_containment

          by_cases w_plus : χ.toLinear + α.1.toLinear = 0
          · have h_chi_neg_alpha : χ.toLinear = -α.1.toLinear := by
              simp only [add_eq_zero_iff_eq_neg] at w_plus; exact w_plus
            apply LieSubmodule.mem_iSup_of_mem α
            simp only [IsKilling.sl2SubmoduleOfRoot]
            have hx_χ_neg_alpha : x_χ ∈ genWeightSpace L (-α.1.toLinear) := by
              rw [← h_chi_neg_alpha]; exact hx_χ
            have hx_χ_in_sl2 : x_χ ∈ sl2SubalgebraOfRoot α.2.2 := by
              have hx_χ_neg : x_χ ∈ rootSpace H (-α.1.toLinear) := hx_χ_neg_alpha
              obtain ⟨h, e, f, ht, heα, hfα⟩ :=
                LieAlgebra.IsKilling.exists_isSl2Triple_of_weight_isNonZero α.2.2
              rw [LieAlgebra.IsKilling.mem_sl2SubalgebraOfRoot_iff α.2.2 ht heα hfα]
              have h_dim : Module.finrank K (rootSpace H (-α.1.toLinear)) = 1 :=
                LieAlgebra.IsKilling.finrank_rootSpace_eq_one (-α.1) (by simpa using α.2.2)
              have hf_subtype_ne_zero : (⟨f, hfα⟩ : rootSpace H (-α.1.toLinear)) ≠ 0 := by
                simp [ne_eq, LieSubmodule.mk_eq_zero]
                exact ht.f_ne_zero
              obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero'
                ⟨f, hfα⟩ hf_subtype_ne_zero).mp h_dim ⟨x_χ, hx_χ_neg⟩
              have hc_proj : x_χ = c • f := by simpa using hc.symm
              exact ⟨0, c, 0, by simp [hc_proj]⟩
            apply LieSubalgebra.lie_mem <;> [exact hx_χ_in_sl2; exact hm_α_original]
          by_cases w_minus : χ.toLinear - α.1.toLinear = 0
          · have h_chi_eq_alpha : χ.toLinear = α.1.toLinear := by
              simp only [sub_eq_zero] at w_minus; exact w_minus
            apply LieSubmodule.mem_iSup_of_mem α
            simp only [IsKilling.sl2SubmoduleOfRoot]
            have hx_χ_alpha : x_χ ∈ genWeightSpace L α.1.toLinear := by
              rw [← h_chi_eq_alpha]; exact hx_χ
            have hx_χ_in_sl2 : x_χ ∈ sl2SubalgebraOfRoot α.2.2 := by
              have hx_χ_pos : x_χ ∈ rootSpace H α.1.toLinear := hx_χ_alpha
              obtain ⟨h, e, f, ht, heα, hfα⟩ :=
                LieAlgebra.IsKilling.exists_isSl2Triple_of_weight_isNonZero α.2.2
              rw [LieAlgebra.IsKilling.mem_sl2SubalgebraOfRoot_iff α.2.2 ht heα hfα]
              have h_dim : Module.finrank K (rootSpace H α.1.toLinear) = 1 :=
                LieAlgebra.IsKilling.finrank_rootSpace_eq_one α.1 α.2.2
              have he_subtype_ne_zero : (⟨e, heα⟩ : rootSpace H α.1.toLinear) ≠ 0 := by
                simp [ne_eq, LieSubmodule.mk_eq_zero]
                exact ht.e_ne_zero
              obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero'
                ⟨e, heα⟩ he_subtype_ne_zero).mp h_dim ⟨x_χ, hx_χ_pos⟩
              have hc_proj : x_χ = c • e := by simpa using hc.symm
              exact ⟨c, 0, 0, by simp [hc_proj]⟩
            apply LieSubalgebra.lie_mem <;> [exact hx_χ_in_sl2; exact hm_α_original]
          by_cases w_chi : χ.toLinear = 0
          · have hx_χ_in_H : x_χ ∈ H.toLieSubmodule := by
              rw [← rootSpace_zero_eq K L H]
              convert hx_χ; ext h; simp only [Pi.zero_apply]
              have h_apply : (χ.toLinear : H → K) h = 0 := by rw [w_chi]; rfl
              exact h_apply.symm
            apply LieSubmodule.mem_iSup_of_mem α
            simp only [IsKilling.sl2SubmoduleOfRoot]
            rw [← (by rfl : ⁅(⟨x_χ, hx_χ_in_H⟩ : H), m_α⁆ = ⁅x_χ, m_α⁆)]
            exact (IsKilling.sl2SubmoduleOfRoot α.1 α.2.2).lie_mem hm_α_original

          have hχ_nonzero : χ.IsNonZero := by
            intro h_zero
            apply w_chi
            have h_zero_eq : (χ.toLinear : H →ₗ[K] K) = 0 := by
              ext h
              simp [Weight.IsZero.eq h_zero]
            exact h_zero_eq

          by_cases h_chi_in_q : χ.toLinear ∈ q
          · have h_chi_plus_alpha_in_q : χ.toLinear + α.1.toLinear ∈ q := by
              exact q.add_mem h_chi_in_q α.2.1

            have h_plus_containment :
              genWeightSpace L (χ.toLinear + α.1.toLinear) ≤
              ⨆ β : {β : Weight K H L // β.toLinear ∈ q ∧ β.IsNonZero},
                IsKilling.sl2SubmoduleOfRoot β.1 β.2.2 := by
              by_cases h_plus_trivial : genWeightSpace L (χ.toLinear + α.1.toLinear) = ⊥
              · simp [h_plus_trivial]
              · let β : Weight K H L := {
                  toFun := χ.toLinear + α.1.toLinear,
                  genWeightSpace_ne_bot' := h_plus_trivial
                }
                have hβ_in_index_set : β.toLinear ∈ q ∧ β.IsNonZero := by
                  constructor
                  · exact h_chi_plus_alpha_in_q
                  · intro h_eq
                    apply w_plus
                    have h_zero_eq : (β.toLinear : H →ₗ[K] K) = 0 := by
                      ext h
                      simp [Weight.IsZero.eq h_eq]
                    have h_beta_def : (β : H → K) = ⇑(χ.toLinear) + ⇑(α.1.toLinear) := rfl
                    have h_coe_zero : ⇑(χ.toLinear) + ⇑(α.1.toLinear) = 0 := by
                      rw [← h_beta_def]
                      exact Weight.IsZero.eq h_eq
                    ext h
                    have := congr_fun h_coe_zero h
                    simpa using this
                have β_mem_index_set : β ∈ {γ : Weight K H L | γ.toLinear ∈ q ∧ γ.IsNonZero} :=
                  hβ_in_index_set
                let β_indexed : {γ : Weight K H L // γ.toLinear ∈ q ∧ γ.IsNonZero} :=
                  ⟨β, hβ_in_index_set⟩
                have β_term_in_supr :
                    IsKilling.sl2SubmoduleOfRoot β β_indexed.property.right ≤
                    ⨆ (γ : {γ : Weight K H L // γ.toLinear ∈ q ∧ γ.IsNonZero}),
                    IsKilling.sl2SubmoduleOfRoot γ γ.property.right := by
                  have h := le_iSup (fun γ : {γ : Weight K H L // γ.toLinear ∈ q ∧ γ.IsNonZero} =>
                    IsKilling.sl2SubmoduleOfRoot γ.1 γ.2.2) β_indexed
                  exact h
                have h_β_contains : genWeightSpace L (χ.toLinear + α.1.toLinear) ≤
                    IsKilling.sl2SubmoduleOfRoot β β_indexed.property.right := by
                  rw [IsKilling.sl2SubmoduleOfRoot_eq_sup]
                  apply le_sup_of_le_left
                  apply le_sup_of_le_left
                  have h_eq : β.toLinear = χ.toLinear + α.1.toLinear := rfl
                  rw [h_eq]
                exact h_β_contains.trans β_term_in_supr

            have h_chi_minus_alpha_in_q : χ.toLinear - α.1.toLinear ∈ q := by
              rw [sub_eq_add_neg]
              apply q.add_mem h_chi_in_q
              have h_neg_smul : -α.1.toLinear = (-1 : K) • α.1.toLinear := by simp
              rw [h_neg_smul]
              exact q.smul_mem (-1) α.2.1

            have h_minus_containment :
              genWeightSpace L (χ.toLinear - α.1.toLinear) ≤
              ⨆ β : {β : Weight K H L // β.toLinear ∈ q ∧ β.IsNonZero},
                IsKilling.sl2SubmoduleOfRoot β.1 β.2.2 := by
              by_cases h_minus_trivial : genWeightSpace L (χ.toLinear - α.1.toLinear) = ⊥
              · simp [h_minus_trivial]
              · let β : Weight K H L := {
                  toFun := χ.toLinear - α.1.toLinear,
                  genWeightSpace_ne_bot' := h_minus_trivial
                }
                have hβ_in_index_set : β.toLinear ∈ q ∧ β.IsNonZero := by
                  constructor
                  · exact h_chi_minus_alpha_in_q
                  · intro h_eq
                    apply w_minus
                    have h_zero_eq : (β.toLinear : H →ₗ[K] K) = 0 := by
                      ext h
                      simp [Weight.IsZero.eq h_eq]
                    have h_beta_def : (β : H → K) = ⇑(χ.toLinear) - ⇑(α.1.toLinear) := rfl
                    have h_coe_zero : ⇑(χ.toLinear) - ⇑(α.1.toLinear) = 0 := by
                      rw [← h_beta_def]
                      exact Weight.IsZero.eq h_eq
                    ext h
                    have := congr_fun h_coe_zero h
                    simpa using this
                have β_mem_index_set : β ∈ {γ : Weight K H L | γ.toLinear ∈ q ∧ γ.IsNonZero} :=
                  hβ_in_index_set
                let β_indexed : {γ : Weight K H L // γ.toLinear ∈ q ∧ γ.IsNonZero} :=
                  ⟨β, hβ_in_index_set⟩
                have β_term_in_supr :
                    IsKilling.sl2SubmoduleOfRoot β β_indexed.property.right ≤
                    ⨆ (γ : {γ : Weight K H L // γ.toLinear ∈ q ∧ γ.IsNonZero}),
                    IsKilling.sl2SubmoduleOfRoot γ γ.property.right := by
                  have h := le_iSup (fun γ : {γ : Weight K H L // γ.toLinear ∈ q ∧ γ.IsNonZero} =>
                    IsKilling.sl2SubmoduleOfRoot γ.1 γ.2.2) β_indexed
                  exact h
                have h_β_contains : genWeightSpace L (χ.toLinear - α.1.toLinear) ≤
                    IsKilling.sl2SubmoduleOfRoot β β_indexed.property.right := by
                  rw [IsKilling.sl2SubmoduleOfRoot_eq_sup]
                  apply le_sup_of_le_left
                  apply le_sup_of_le_left
                  have h_eq : β.toLinear = χ.toLinear - α.1.toLinear := rfl
                  rw [h_eq]
                exact h_β_contains.trans β_term_in_supr

            have h_chi_containment :
              genWeightSpace L χ.toLinear ≤
              ⨆ β : {β : Weight K H L // β.toLinear ∈ q ∧ β.IsNonZero},
                IsKilling.sl2SubmoduleOfRoot β.1 β.2.2 := by
              by_cases h_chi_trivial : genWeightSpace L χ.toLinear = ⊥
              · rw [h_chi_trivial]
                simp
              · have hχ_in_index_set : χ.toLinear ∈ q ∧ χ.IsNonZero := by
                  constructor
                  · exact h_chi_in_q
                  · intro h_eq
                    apply w_chi
                    have h_coe_zero : (χ : H → K) = 0 := Weight.IsZero.eq h_eq
                    convert h_coe_zero
                    simp only [LinearMap.ext_iff, LinearMap.zero_apply]
                    constructor
                    · intro h
                      ext x
                      exact h x
                    · intro h x
                      have := congr_fun h x
                      simp at this
                      exact this
                let χ_indexed : {γ : Weight K H L // γ.toLinear ∈ q ∧ γ.IsNonZero} :=
                  ⟨χ, hχ_in_index_set⟩
                have χ_term_in_supr :
                    IsKilling.sl2SubmoduleOfRoot χ χ_indexed.property.right ≤
                    ⨆ (γ : {γ : Weight K H L // γ.toLinear ∈ q ∧ γ.IsNonZero}),
                    IsKilling.sl2SubmoduleOfRoot γ γ.property.right := by
                  have h := le_iSup (fun γ : {γ : Weight K H L // γ.toLinear ∈ q ∧ γ.IsNonZero} =>
                    IsKilling.sl2SubmoduleOfRoot γ.1 γ.2.2) χ_indexed
                  exact h
                have h_χ_contains : genWeightSpace L χ.toLinear ≤
                    IsKilling.sl2SubmoduleOfRoot χ χ_indexed.property.right := by
                  rw [IsKilling.sl2SubmoduleOfRoot_eq_sup]
                  apply le_sup_of_le_left
                  apply le_sup_of_le_left
                  rfl
                exact h_χ_contains.trans χ_term_in_supr

            have h_total_containment :
              genWeightSpace L (χ.toLinear + α.1.toLinear) ⊔
              genWeightSpace L (χ.toLinear - α.1.toLinear) ⊔
              genWeightSpace L χ.toLinear ≤
              ⨆ β : {β : Weight K H L // β.toLinear ∈ q ∧ β.IsNonZero},
                IsKilling.sl2SubmoduleOfRoot β.1 β.2.2 := by
              apply sup_le
              · apply sup_le
                · exact h_plus_containment
                · exact h_minus_containment
              · exact h_chi_containment
            exact h_total_containment h_bracket_decomp
          · have h_plus_bot : genWeightSpace L (χ.toLinear + α.1.toLinear) = ⊥ := by
              by_contra h_ne_bot
              let S := LieAlgebra.IsKilling.rootSystem H
              have q_invt : q ∈ S.invtRootSubmodule := by
                rw [RootPairing.mem_invtRootSubmodule_iff]
                exact hq
              have h_chi_plus_alpha_is_root : χ.toLinear + α.1.toLinear ∈ Set.range S.root := by
                let γ : Weight K H L := {
                  toFun := χ.toLinear + α.1.toLinear,
                  genWeightSpace_ne_bot' := h_ne_bot
                }
                have hγ_nonzero : γ.IsNonZero := by
                  intro h_zero
                  apply w_plus
                  have h_zero_eq : (γ.toLinear : H →ₗ[K] K) = 0 := by
                    ext h
                    simp [Weight.IsZero.eq h_zero]
                  have h_def : γ.toLinear = χ.toLinear + α.1.toLinear := rfl
                  rw [h_def] at h_zero_eq
                  exact h_zero_eq
                have γ_in_root : γ ∈ H.root := by
                  simp [LieSubalgebra.root]
                  exact hγ_nonzero
                use ⟨γ, γ_in_root⟩
                rfl
              obtain ⟨i, hi⟩ := exists_root_index χ hχ_nonzero
              obtain ⟨j, hj⟩ := exists_root_index α.1 α.2.2
              have h_sum_in_range : S.root i + S.root j ∈ Set.range S.root := by
                rw [hi, hj]
                exact h_chi_plus_alpha_is_root
              let q_as_invt : S.invtRootSubmodule := ⟨q, q_invt⟩
              have h_equiv : S.root i ∈ (q_as_invt : Submodule K (Dual K H)) ↔
                            S.root j ∈ (q_as_invt : Submodule K (Dual K H)) :=
                RootPairing.root_mem_submodule_iff_of_add_mem_invtSubmodule q_as_invt h_sum_in_range
              have h_j_in_q : S.root j ∈ (q_as_invt : Submodule K (Dual K H)) := by
                rw [hj]
                exact α.2.1
              have h_i_in_q : S.root i ∈ (q_as_invt : Submodule K (Dual K H)) :=
                h_equiv.mpr h_j_in_q
              rw [hi] at h_i_in_q
              exact h_chi_in_q h_i_in_q

            have h_minus_bot : genWeightSpace L (χ.toLinear - α.1.toLinear) = ⊥ := by
              by_contra h_ne_bot
              let S := LieAlgebra.IsKilling.rootSystem H
              have q_invt : q ∈ S.invtRootSubmodule := by
                rw [RootPairing.mem_invtRootSubmodule_iff]
                exact hq
              have h_chi_minus_alpha_is_root : χ.toLinear - α.1.toLinear ∈ Set.range S.root := by
                let γ : Weight K H L := {
                  toFun := χ.toLinear - α.1.toLinear,
                  genWeightSpace_ne_bot' := h_ne_bot
                }
                have hγ_nonzero : γ.IsNonZero := by
                  intro h_zero
                  apply w_minus
                  have h_zero_eq : (γ.toLinear : H →ₗ[K] K) = 0 := by
                    ext h
                    simp [Weight.IsZero.eq h_zero]
                  have h_def : γ.toLinear = χ.toLinear - α.1.toLinear := rfl
                  rw [h_def] at h_zero_eq
                  exact h_zero_eq
                have γ_in_root : γ ∈ H.root := by
                  simp [LieSubalgebra.root]
                  exact hγ_nonzero
                use ⟨γ, γ_in_root⟩
                rfl
              obtain ⟨i, hi⟩ := exists_root_index χ hχ_nonzero
              obtain ⟨j, hj⟩ := exists_root_index (-α.1) (Weight.IsNonZero.neg α.2.2)
              have h_sum_in_range : S.root i + S.root j ∈ Set.range S.root := by
                rw [hi, hj]
                have h_eq : χ.toLinear + (-α.1).toLinear = χ.toLinear - α.1.toLinear := by
                  simp only [sub_eq_add_neg]
                  congr 1
                rw [h_eq]
                exact h_chi_minus_alpha_is_root
              let q_as_invt : S.invtRootSubmodule := ⟨q, q_invt⟩
              have h_equiv : S.root i ∈ (q_as_invt : Submodule K (Dual K H)) ↔
                            S.root j ∈ (q_as_invt : Submodule K (Dual K H)) :=
                RootPairing.root_mem_submodule_iff_of_add_mem_invtSubmodule q_as_invt h_sum_in_range
              have h_j_in_q : S.root j ∈ (q_as_invt : Submodule K (Dual K H)) := by
                rw [hj]
                have h_neg_smul : (-α.1).toLinear = (-1 : K) • α.1.toLinear := by
                  simp only [Weight.toLinear_neg, neg_smul, one_smul]
                rw [h_neg_smul]
                exact q.smul_mem (-1) α.2.1
              have h_i_in_q : S.root i ∈ (q_as_invt : Submodule K (Dual K H)) :=
                h_equiv.mpr h_j_in_q
              rw [hi] at h_i_in_q
              exact h_chi_in_q h_i_in_q

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

            have h_simplified : ⁅x_χ, m_α⁆ = ⁅x_χ, m_h⁆ := by
              rw [h_bracket_sum, h_pos_zero, h_neg_zero]
              simp

            let S := LieAlgebra.IsKilling.rootSystem H
            obtain ⟨i, hi⟩ := exists_root_index χ hχ_nonzero
            obtain ⟨j, hj⟩ := exists_root_index α.1 α.2.2
            have h_pairing_zero : S.pairing i j = 0 := by
              obtain ⟨i', j', hi', hj', h_zero⟩ :=
                IsKilling.pairing_zero_of_trivial_sum_diff_spaces H χ α.1 hχ_nonzero α.2.2 w_plus
                  w_minus h_plus_bot h_minus_bot
              have h_i_eq : i = i' := by
                have h_root_eq : S.root i = S.root i' := by
                  rw [hi, hi']
                exact Function.Embedding.injective S.root h_root_eq
              have h_j_eq : j = j' := by
                have h_root_eq : S.root j = S.root j' := by
                  rw [hj, hj']
                exact Function.Embedding.injective S.root h_root_eq
              rw [h_i_eq, h_j_eq]
              exact h_zero

            have h_bracket_zero : ⁅x_χ, m_h⁆ = 0 := by
              have hχ_nonzero : χ.IsNonZero := hχ_nonzero
              have hα_nonzero : α.1.IsNonZero := α.2.2
              have h_chi_coroot_zero : χ (LieAlgebra.IsKilling.coroot α.1) = 0 := by
                have h_pairing_eq : S.pairing i j = i.1 (LieAlgebra.IsKilling.coroot j.1) := by
                  rw [LieAlgebra.IsKilling.rootSystem_pairing_apply]
                rw [h_pairing_zero] at h_pairing_eq
                have hi_val : i.1 = χ := by
                  have h_eq : i.1.toLinear = χ.toLinear := by
                    rw [← hi]
                    rfl
                  apply Weight.ext
                  intro x
                  have := LinearMap.ext_iff.mp h_eq x
                  exact this
                have hj_val : j.1 = α.1 := by
                  have h_eq : j.1.toLinear = α.1.toLinear := by
                    rw [← hj]
                    rfl
                  apply Weight.ext
                  intro x
                  have := LinearMap.ext_iff.mp h_eq x
                  exact this
                rw [hi_val, hj_val] at h_pairing_eq
                exact h_pairing_eq.symm
              simp only [IsKilling.corootSubmodule] at hm_h
              obtain ⟨h_elem, hh_elem, hh_eq⟩ := hm_h
              have h_lie_eq_smul : ⁅(h_elem : L), x_χ⁆ = (χ.toLinear) h_elem • x_χ :=
                LieAlgebra.IsKilling.lie_eq_smul_of_mem_rootSpace hx_χ h_elem
              have h_chi_h_zero : (χ.toLinear) h_elem = 0 := by
                obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp <| by
                  rw [← LieAlgebra.IsKilling.coe_corootSpace_eq_span_singleton α.1]
                  rw [LieSubmodule.mem_toSubmodule]
                  exact hh_elem
                rw [← hc, LinearMap.map_smul]
                have h_convert : (χ.toLinear) (LieAlgebra.IsKilling.coroot α.1) =
                    χ (LieAlgebra.IsKilling.coroot α.1) := rfl
                rw [h_convert, h_chi_coroot_zero, smul_zero]
              have h_bracket_elem : ⁅x_χ, (h_elem : L)⁆ = 0 := by
                rw [← lie_skew, h_lie_eq_smul, h_chi_h_zero, zero_smul, neg_zero]
              rw [← hh_eq]
              exact h_bracket_elem

            rw [h_simplified, h_bracket_zero]
            simp

        | zero =>
          simp only [LieSubmodule.iSup_toSubmodule, Submodule.carrier_eq_coe, lie_zero,
            SetLike.mem_coe, Submodule.zero_mem]
        | add m₁ m₂ _ _ ih₁ ih₂ =>
          rw [lie_add]
          simp only [LieSubmodule.iSup_toSubmodule, Submodule.carrier_eq_coe, SetLike.mem_coe]
            at ih₁ ih₂ ⊢
          exact add_mem ih₁ ih₂
      | zero =>
        simp [zero_lie]
      | add x₁ x₂ _ _ ih₁ ih₂ =>
        rw [add_lie]
        simp only [LieSubmodule.iSup_toSubmodule, Submodule.carrier_eq_coe, SetLike.mem_coe]
          at ih₁ ih₂ ⊢
        exact add_mem ih₁ ih₂
