import Mathlib.Algebra.Lie.Sl2
import Mathlib.Algebra.Lie.Weights.Basic
import Mathlib.Algebra.Lie.Weights.Cartan
import Mathlib.Algebra.Lie.Weights.Killing
import Mathlib.Algebra.Lie.Weights.RootSystem
import Mathlib.Algebra.Module.Submodule.Invariant
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.LinearAlgebra.RootSystem.Finite.Lemmas

set_option maxHeartbeats 1000000

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
variable [LieAlgebra.IsKilling K L] [FiniteDimensional K L]

open LieAlgebra LieModule Module
open IsKilling (sl2SubalgebraOfRoot rootSystem)

variable {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [IsTriangularizable K H L]

lemma zero_pairing_implies_zero_bracket
  (χ α : Weight K H L)
  (x : L) (hx : x ∈ genWeightSpace L χ.toLinear)
  (h : H) (hh : h ∈ LieAlgebra.corootSpace α.toLinear)
  (h_zero : χ (LieAlgebra.IsKilling.coroot α) = 0) :
  ⁅x, (h : L)⁆ = 0 := by
  have h_in_span : h ∈ K ∙ IsKilling.coroot α := by
    rw [← IsKilling.coe_corootSpace_eq_span_singleton]
    rw [LieSubmodule.mem_toSubmodule]
    exact hh
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h_in_span
  have h_chi_h_zero : (χ.toLinear) h = 0 := by
    have : (χ.toLinear) h = (χ.toLinear) (c • IsKilling.coroot α) := by rw [hc]
    rw [this, LinearMap.map_smul]
    have h_convert : (χ.toLinear) (IsKilling.coroot α) = χ (IsKilling.coroot α) := rfl
    rw [h_convert, h_zero, smul_zero]
  rw [genWeightSpace, LieSubmodule.mem_iInf] at hx
  have hx_h := hx h
  rw [h_chi_h_zero] at hx_h
  have hx_maxgen : x ∈ (toEnd K H L h).maxGenEigenspace 0 := by
    change x ∈ (genWeightSpaceOf L 0 h).toSubmodule at hx_h
    rw [genWeightSpaceOf] at hx_h
    exact hx_h
  have h_semisimple : (ad K L (h : L)).IsSemisimple := by
    exact LieAlgebra.IsKilling.isSemisimple_ad_of_mem_isCartanSubalgebra h.property
  have h_gen_eq_eigen : (ad K L (h : L)).maxGenEigenspace 0 = (ad K L (h : L)).eigenspace 0 := by
    exact Module.End.IsFinitelySemisimple.maxGenEigenspace_eq_eigenspace
      h_semisimple.isFinitelySemisimple 0
  have hx_maxgen_ad : x ∈ (ad K L (h : L)).maxGenEigenspace 0 := by
    have h_eq : toEnd K H L h = ad K L (h : L) := by
      ext y
      simp only [LieModule.toEnd_apply_apply, LieAlgebra.ad_apply]
      rfl
    rw [← h_eq]
    exact hx_maxgen
  rw [h_gen_eq_eigen] at hx_maxgen_ad
  rw [Module.End.mem_eigenspace_iff] at hx_maxgen_ad
  have h_ad_zero : (ad K L (h : L)) x = 0 := by
    simp only [zero_smul] at hx_maxgen_ad
    exact hx_maxgen_ad
  rw [LieAlgebra.ad_apply] at h_ad_zero
  rw [← lie_skew] at h_ad_zero
  exact neg_eq_zero.mp h_ad_zero

lemma pairing_zero_of_trivial_sum_diff_spaces
  (χ α : Weight K H L) (hχ : χ.IsNonZero) (hα : α.IsNonZero)
  (w_plus : χ.toLinear + α.toLinear ≠ 0) (w_minus : χ.toLinear - α.toLinear ≠ 0)
  (h_plus_bot : genWeightSpace L (χ.toLinear + α.toLinear) = ⊥)
  (h_minus_bot : genWeightSpace L (χ.toLinear - α.toLinear) = ⊥) :
  let S := LieAlgebra.IsKilling.rootSystem H
  ∃ (i j : { w : Weight K H L // w ∈ H.root }),
    S.root i = χ.toLinear ∧ S.root j = α.toLinear ∧ S.pairing i j = 0 := by
  let S := LieAlgebra.IsKilling.rootSystem H
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
  · rfl
  constructor
  · rfl
  · have h_trichotomy : S.pairingIn ℤ i j < 0 ∨ S.pairingIn ℤ i j = 0 ∨ 0 < S.pairingIn ℤ i j := by
      exact lt_trichotomy (S.pairingIn ℤ i j) 0
    cases h_trichotomy with
    | inl h_neg =>
      exfalso
      have h_add_mem : S.root i + S.root j ∈ Set.range S.root := by
        apply RootPairing.root_add_root_mem_of_pairingIn_neg S.toRootPairing h_neg
        intro h_eq
        have h_sum_zero : S.root i + S.root j = 0 := by rw [h_eq]; simp
        have h_contradiction : χ.toLinear + α.toLinear = 0 := h_sum_zero
        exact w_plus h_contradiction
      have h_chi_plus_alpha_root : χ.toLinear + α.toLinear ∈ Set.range S.root := h_add_mem
      have h_nontriv : genWeightSpace L (χ.toLinear + α.toLinear) ≠ ⊥ := by
        obtain ⟨idx, hidx⟩ := h_chi_plus_alpha_root
        have h_nonzero : idx.val.IsNonZero := by
          have h_mem := idx.property
          simp only [LieSubalgebra.root, Finset.mem_filter, Finset.mem_univ, true_and] at h_mem
          exact h_mem
        have h_weight_space_nontrivial := idx.val.genWeightSpace_ne_bot
        have h_root_eq : S.root idx = idx.val.toLinear := by
          exact LieAlgebra.IsKilling.rootSystem_root_apply H idx
        have : genWeightSpace L (S.root idx) ≠ ⊥ := by
          rw [h_root_eq]
          exact h_weight_space_nontrivial
        have h_final : genWeightSpace L (χ.toLinear + α.toLinear) ≠ ⊥ := by
          convert this using 1
          rw [←hidx]
        exact h_final
      exact h_nontriv h_plus_bot
    | inr h_rest =>
      cases h_rest with
      | inl h_zero =>
        have h_algebraMap : algebraMap ℤ K (S.pairingIn ℤ i j) = S.pairing i j := by
          exact S.algebraMap_pairingIn ℤ i j
        rw [h_zero, map_zero] at h_algebraMap
        exact h_algebraMap.symm
      | inr h_pos =>
        exfalso
        have h_sub_mem : S.root i - S.root j ∈ Set.range S.root := by
          apply RootPairing.root_sub_root_mem_of_pairingIn_pos S.toRootPairing h_pos
          intro h_eq
          have h_chi_eq_alpha : χ = α := by
            injection h_eq
          have h_contradiction : χ.toLinear - α.toLinear = 0 := by
            rw [h_chi_eq_alpha]
            simp
          exact w_minus h_contradiction
        have h_chi_minus_alpha_root : χ.toLinear - α.toLinear ∈ Set.range S.root := by
          exact h_sub_mem
        have h_nontriv : genWeightSpace L (χ.toLinear - α.toLinear) ≠ ⊥ := by
          obtain ⟨idx, hidx⟩ := h_chi_minus_alpha_root
          have h_nonzero : idx.val.IsNonZero := by
            have h_mem := idx.property
            simp only [LieSubalgebra.root, Finset.mem_filter, Finset.mem_univ, true_and] at h_mem
            exact h_mem
          have h_weight_space_nontrivial := idx.val.genWeightSpace_ne_bot
          have h_root_eq : S.root idx = idx.val.toLinear := by
            exact LieAlgebra.IsKilling.rootSystem_root_apply H idx
          have : genWeightSpace L (S.root idx) ≠ ⊥ := by
            rw [h_root_eq]
            exact h_weight_space_nontrivial
          have h_final : genWeightSpace L (χ.toLinear - α.toLinear) ≠ ⊥ := by
            convert this using 1
            rw [←hidx]
          exact h_final
        exact h_nontriv h_minus_bot

variable {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [IsTriangularizable K H L]

noncomputable abbrev H_α (α : Weight K H L) : LieSubmodule K H L :=
  LieSubmodule.map H.toLieSubmodule.incl (LieAlgebra.corootSpace α.toLinear)

lemma sl2SubalgebraOfRoot_stable_under_H (α : Weight K H L) (hα : α.IsNonZero) :
    ∀ (h : H) (x : L), x ∈ sl2SubalgebraOfRoot hα → ⁅(h : L), x⁆ ∈ sl2SubalgebraOfRoot hα := by
  intro h x hx
  obtain ⟨h', e, f, ht, heα, hfα⟩ := LieAlgebra.IsKilling.exists_isSl2Triple_of_weight_isNonZero hα
  rw [LieAlgebra.IsKilling.mem_sl2SubalgebraOfRoot_iff hα ht heα hfα] at hx ⊢
  obtain ⟨c₁, c₂, c₃, hx_eq⟩ := hx
  rw [hx_eq, lie_add, lie_add, lie_smul, lie_smul, lie_smul]
  have he_weight : ⁅(h : L), e⁆ = α h • e := by
    exact LieAlgebra.IsKilling.lie_eq_smul_of_mem_rootSpace heα h
  have hf_weight : ⁅(h : L), f⁆ = (-α) h • f := by
    exact LieAlgebra.IsKilling.lie_eq_smul_of_mem_rootSpace hfα h
  have hef_weight : ⁅(h : L), ⁅e, f⁆⁆ = 0 • ⁅e, f⁆ := by
    have h_coroot : ⁅e, f⁆ = (LieAlgebra.IsKilling.coroot α : L) := by
      have : ⁅e, f⁆ = h' := ht.lie_e_f
      rw [this]
      exact IsSl2Triple.h_eq_coroot hα ht heα hfα
    rw [h_coroot]
    have : ⁅(h : L), (LieAlgebra.IsKilling.coroot α : L)⁆ = 0 := by
      have h_coroot_in_H : (LieAlgebra.IsKilling.coroot α : L) ∈ rootSpace H (0 : H → K) := by
        have h_coroot_mem_H : (LieAlgebra.IsKilling.coroot α : L) ∈ H := by
          exact (LieAlgebra.IsKilling.coroot α).property
        have h_eq : rootSpace H (0 : H → K) = H.toLieSubmodule := rootSpace_zero_eq K L H
        rw [h_eq]
        exact h_coroot_mem_H
      have h_eq : ⁅(h : L), (LieAlgebra.IsKilling.coroot α : L)⁆ =
        (0 : H → K) h • (LieAlgebra.IsKilling.coroot α : L) := by
        exact LieAlgebra.IsKilling.lie_eq_smul_of_mem_rootSpace h_coroot_in_H h
      rw [h_eq]
      simp only [Pi.zero_apply, zero_smul]
    rw [this, zero_smul]
  rw [he_weight, hf_weight, hef_weight, smul_smul, smul_smul, zero_smul]
  simp only [Weight.coe_neg, Pi.neg_apply, smul_zero, add_zero]
  exact ⟨c₁ * α h, c₂ * (-α h), 0, by simp [mul_smul]⟩

noncomputable def sl2SubalgebraOfRoot_as_H_submodule (α : Weight K H L) (hα : α.IsNonZero) :
    LieSubmodule K H L where
  __ := (sl2SubalgebraOfRoot hα).toLieSubmodule
  lie_mem := by
    intro h x hx
    exact sl2SubalgebraOfRoot_stable_under_H α hα h x hx

lemma sl2SubalgebraOfRoot_as_H_submodule_eq_sup (α : Weight K H L) (hα : α.IsNonZero) :
    sl2SubalgebraOfRoot_as_H_submodule α hα =
    genWeightSpace L α.toLinear ⊔ genWeightSpace L (-α).toLinear ⊔ H_α α := by
  ext x
  constructor
  · intro hx
    simp only [sl2SubalgebraOfRoot_as_H_submodule] at hx
    obtain ⟨h', e, f, ht, heα, hfα⟩ :=
      LieAlgebra.IsKilling.exists_isSl2Triple_of_weight_isNonZero hα
    have hx_sl2 : x ∈ sl2SubalgebraOfRoot hα := hx
    rw [LieAlgebra.IsKilling.mem_sl2SubalgebraOfRoot_iff hα ht heα hfα] at hx_sl2
    obtain ⟨c₁, c₂, c₃, hx_eq⟩ := hx_sl2
    rw [hx_eq]
    apply add_mem
    · apply add_mem
      · apply Submodule.smul_mem
        apply Submodule.mem_sup_left
        apply Submodule.mem_sup_left
        exact heα
      · apply Submodule.smul_mem
        apply Submodule.mem_sup_left
        apply Submodule.mem_sup_right
        exact hfα
    · apply Submodule.smul_mem
      apply Submodule.mem_sup_right
      unfold H_α
      have h_coroot_eq : ⁅e, f⁆ = h' := ht.lie_e_f
      rw [h_coroot_eq]
      use (LieAlgebra.IsKilling.coroot α : H)
      constructor
      · have h_eq : (corootSpace α.toLinear).toSubmodule = K ∙ LieAlgebra.IsKilling.coroot α :=
          LieAlgebra.IsKilling.coe_corootSpace_eq_span_singleton α
        change LieAlgebra.IsKilling.coroot α ∈ (corootSpace α.toLinear : Set H)
        rw [LieSubmodule.mem_coe, ← LieSubmodule.mem_toSubmodule, h_eq]
        exact Submodule.mem_span_singleton_self _
      · have h_eq : h' = (LieAlgebra.IsKilling.coroot α : L) :=
          IsSl2Triple.h_eq_coroot hα ht heα hfα
        rw [h_eq]
        rfl
  · intro hx
    obtain ⟨x_αneg, hx_αneg, x_h, hx_h, hx_eq⟩ := Submodule.mem_sup.mp hx
    obtain ⟨x_pos, hx_pos, x_neg, hx_neg, hx_αneg_eq⟩ := Submodule.mem_sup.mp hx_αneg
    rw [← hx_eq, ← hx_αneg_eq]
    simp only [sl2SubalgebraOfRoot_as_H_submodule]
    obtain ⟨h', e, f, ht, heα, hfα⟩ :=
      LieAlgebra.IsKilling.exists_isSl2Triple_of_weight_isNonZero hα

    have hx_pos_in : x_pos ∈ sl2SubalgebraOfRoot hα := by
      rw [LieAlgebra.IsKilling.mem_sl2SubalgebraOfRoot_iff hα ht heα hfα]
      have h_dim : Module.finrank K (rootSpace H α.toLinear) = 1 :=
        LieAlgebra.IsKilling.finrank_rootSpace_eq_one α hα
      have he_ne_zero : e ≠ 0 := ht.e_ne_zero
      have he_subtype_ne_zero : (⟨e, heα⟩ : rootSpace H α.toLinear) ≠ 0 := by
        rwa [ne_eq, LieSubmodule.mk_eq_zero]
      obtain ⟨c₁, hc₁⟩ :=
        (finrank_eq_one_iff_of_nonzero' ⟨e, heα⟩ he_subtype_ne_zero).mp h_dim ⟨x_pos, hx_pos⟩
      have hx_pos_eq : x_pos = c₁ • e := by
        have : x_pos = (⟨x_pos, hx_pos⟩ : rootSpace H α.toLinear).val := rfl
        rw [this, ← hc₁]; simp
      exact ⟨c₁, 0, 0, by simp [hx_pos_eq]⟩

    have hx_neg_in : x_neg ∈ sl2SubalgebraOfRoot hα := by
      rw [LieAlgebra.IsKilling.mem_sl2SubalgebraOfRoot_iff hα ht heα hfα]
      have h_neg_dim : Module.finrank K (rootSpace H (-α).toLinear) = 1 :=
        LieAlgebra.IsKilling.finrank_rootSpace_eq_one (-α) (by simpa using hα)
      have hf_ne_zero : f ≠ 0 := ht.f_ne_zero
      have hf_subtype_ne_zero : (⟨f, hfα⟩ : rootSpace H (-α).toLinear) ≠ 0 := by
        rwa [ne_eq, LieSubmodule.mk_eq_zero]
      obtain ⟨c₂, hc₂⟩ :=
        (finrank_eq_one_iff_of_nonzero' ⟨f, hfα⟩ hf_subtype_ne_zero).mp h_neg_dim ⟨x_neg, hx_neg⟩
      have hx_neg_eq : x_neg = c₂ • f := by
        have : x_neg = (⟨x_neg, hx_neg⟩ : rootSpace H (-α).toLinear).val := rfl
        rw [this, ← hc₂]; simp
      exact ⟨0, c₂, 0, by simp [hx_neg_eq]⟩

    have hx_h_in : x_h ∈ sl2SubalgebraOfRoot hα := by
      rw [LieAlgebra.IsKilling.mem_sl2SubalgebraOfRoot_iff hα ht heα hfα]
      unfold H_α at hx_h
      obtain ⟨y, hy_coroot, hy_eq⟩ := hx_h
      have h_eq : ⁅e, f⁆ = h' := ht.lie_e_f
      have h_coroot : h' = (LieAlgebra.IsKilling.coroot α : L) :=
        IsSl2Triple.h_eq_coroot hα ht heα hfα
      have h_ef_in_sl2 : ⁅e, f⁆ ∈ sl2SubalgebraOfRoot hα := by
        rw [LieAlgebra.IsKilling.mem_sl2SubalgebraOfRoot_iff hα ht heα hfα]
        exact ⟨0, 0, 1, by simp⟩
      have h_coroot_span : (corootSpace α.toLinear).toSubmodule =
        K ∙ (LieAlgebra.IsKilling.coroot α) :=
        LieAlgebra.IsKilling.coe_corootSpace_eq_span_singleton α
      have hy_mem_submodule : y ∈ (corootSpace α.toLinear).toSubmodule := by
        rw [LieSubmodule.mem_toSubmodule]
        exact hy_coroot
      rw [h_coroot_span] at hy_mem_submodule
      obtain ⟨c₃, hc₃⟩ := Submodule.mem_span_singleton.mp hy_mem_submodule
      have hx_h_eq : x_h = c₃ • ⁅e, f⁆ := by
        rw [← hy_eq, ← hc₃, map_smul]
        congr 1
        have h_embed : (LieAlgebra.IsKilling.coroot α : L) =
          H.toLieSubmodule.incl (LieAlgebra.IsKilling.coroot α) := by
          rfl
        exact h_embed ▸ h_coroot ▸ h_eq.symm
      exact ⟨0, 0, c₃, by simp [hx_h_eq]⟩

    apply add_mem (add_mem hx_pos_in hx_neg_in) hx_h_in

lemma exists_root_index_of_weight_nonzero (χ : Weight K H L) (hχ : χ.IsNonZero) :
    ∃ i, (LieAlgebra.IsKilling.rootSystem H).root i = χ.toLinear := by
  let S := LieAlgebra.IsKilling.rootSystem H
  have hχ_in_root : χ ∈ H.root := by
    simp [LieSubalgebra.root]
    exact hχ
  use ⟨χ, hχ_in_root⟩
  rfl

lemma exists_root_index_of_in_index_set (q : Submodule K (Dual K H))
    (α : {α : Weight K H L // α.toLinear ∈ q ∧ α.IsNonZero}) :
    ∃ j, (LieAlgebra.IsKilling.rootSystem H).root j = α.1.toLinear := by
  let S := LieAlgebra.IsKilling.rootSystem H
  have hα_in_root : α.1 ∈ H.root := by
    simp [LieSubalgebra.root]
    exact α.2.2
  use ⟨α.1, hα_in_root⟩
  rfl

noncomputable def invtSubmoduleToLieIdeal (q : Submodule K (Dual K H))
    (hq : ∀ i, q ∈ End.invtSubmodule ((rootSystem H).reflection i)) :
    LieIdeal K L where
    __ := ⨆ α : {α : Weight K H L // α.toLinear ∈ q ∧ α.IsNonZero},
      sl2SubalgebraOfRoot_as_H_submodule α.1 α.2.2
    lie_mem := by
      intro x m hm
      have hx : x ∈ ⨆ χ : Weight K H L, genWeightSpace L χ := by
        simp [LieModule.iSup_genWeightSpace_eq_top']
      induction hx using LieSubmodule.iSup_induction' with
      | mem χ x_χ hx_χ =>
        induction hm using LieSubmodule.iSup_induction' with
        | mem α m_α hm_α =>
          have hm_α_original : m_α ∈ sl2SubalgebraOfRoot_as_H_submodule α.1 α.2.2 := hm_α
          rw [sl2SubalgebraOfRoot_as_H_submodule_eq_sup] at hm_α
          obtain ⟨m_αneg, hm_αneg, m_h, hm_h, hm_eq⟩ := Submodule.mem_sup.mp hm_α
          obtain ⟨m_pos, hm_pos, m_neg, hm_neg, hm_αneg_eq⟩ := Submodule.mem_sup.mp hm_αneg

          have hm_α_decomp : m_α = m_pos + m_neg + m_h := by
            rw [← hm_eq, ← hm_αneg_eq]

          have hm_pos_weight : m_pos ∈ genWeightSpace L α.1.toLinear := hm_pos
          have hm_neg_weight : m_neg ∈ genWeightSpace L (-α.1).toLinear := hm_neg
          have hm_h_coroot : m_h ∈ H_α α.1 := hm_h

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
            simp only [sl2SubalgebraOfRoot_as_H_submodule]
            have hx_χ_neg_alpha : x_χ ∈ genWeightSpace L (-α.1.toLinear) := by
              rw [← h_chi_neg_alpha]; exact hx_χ
            have hx_χ_in_sl2 : x_χ ∈ sl2SubalgebraOfRoot α.2.2 := by
              have hx_χ_neg : x_χ ∈ rootSpace H (-α.1.toLinear) := hx_χ_neg_alpha
              obtain ⟨h, e, f, ht, heα, hfα⟩ :=
                LieAlgebra.IsKilling.exists_isSl2Triple_of_weight_isNonZero α.2.2
              rw [LieAlgebra.IsKilling.mem_sl2SubalgebraOfRoot_iff α.2.2 ht heα hfα]
              have h_dim : Module.finrank K (rootSpace H (-α.1.toLinear)) = 1 :=
                LieAlgebra.IsKilling.finrank_rootSpace_eq_one (-α.1) (by simpa using α.2.2)
              have hf_ne_zero : f ≠ 0 := ht.f_ne_zero
              have hf_subtype_ne_zero : (⟨f, hfα⟩ : rootSpace H (-α.1.toLinear)) ≠ 0 := by
                rwa [ne_eq, LieSubmodule.mk_eq_zero]
              obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero'
                ⟨f, hfα⟩ hf_subtype_ne_zero).mp h_dim ⟨x_χ, hx_χ_neg⟩
              have hc_proj : x_χ = c • f := by
                have : x_χ = (⟨x_χ, hx_χ_neg⟩ : rootSpace H (-α.1.toLinear)).val := rfl
                rw [this, ← hc]; simp
              exact ⟨0, c, 0, by simp [hc_proj]⟩
            have h_bracket_in_sl2 : ⁅x_χ, m_α⁆ ∈ sl2SubalgebraOfRoot α.2.2 := by
              have hm_α_in_sl2 : m_α ∈ sl2SubalgebraOfRoot α.2.2 := by
                simp only [sl2SubalgebraOfRoot_as_H_submodule] at hm_α_original; exact hm_α_original
              apply LieSubalgebra.lie_mem; exact hx_χ_in_sl2; exact hm_α_in_sl2
            exact h_bracket_in_sl2
          by_cases w_minus : χ.toLinear - α.1.toLinear = 0
          · have h_chi_eq_alpha : χ.toLinear = α.1.toLinear := by
              simp only [sub_eq_zero] at w_minus; exact w_minus
            apply LieSubmodule.mem_iSup_of_mem α
            simp only [sl2SubalgebraOfRoot_as_H_submodule]
            have hx_χ_alpha : x_χ ∈ genWeightSpace L α.1.toLinear := by
              rw [← h_chi_eq_alpha]; exact hx_χ
            have hx_χ_in_sl2 : x_χ ∈ sl2SubalgebraOfRoot α.2.2 := by
              have hx_χ_pos : x_χ ∈ rootSpace H α.1.toLinear := hx_χ_alpha
              obtain ⟨h, e, f, ht, heα, hfα⟩ :=
                LieAlgebra.IsKilling.exists_isSl2Triple_of_weight_isNonZero α.2.2
              rw [LieAlgebra.IsKilling.mem_sl2SubalgebraOfRoot_iff α.2.2 ht heα hfα]
              have h_dim : Module.finrank K (rootSpace H α.1.toLinear) = 1 :=
                LieAlgebra.IsKilling.finrank_rootSpace_eq_one α.1 α.2.2
              have he_ne_zero : e ≠ 0 := ht.e_ne_zero
              have he_subtype_ne_zero : (⟨e, heα⟩ : rootSpace H α.1.toLinear) ≠ 0 := by
                rwa [ne_eq, LieSubmodule.mk_eq_zero]
              obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero'
                ⟨e, heα⟩ he_subtype_ne_zero).mp h_dim ⟨x_χ, hx_χ_pos⟩
              have hc_proj : x_χ = c • e := by
                have : x_χ = (⟨x_χ, hx_χ_pos⟩ : rootSpace H α.1.toLinear).val := rfl
                rw [this, ← hc]; simp
              exact ⟨c, 0, 0, by simp [hc_proj]⟩
            have h_bracket_in_sl2 : ⁅x_χ, m_α⁆ ∈ sl2SubalgebraOfRoot α.2.2 := by
              have hm_α_in_sl2 : m_α ∈ sl2SubalgebraOfRoot α.2.2 := by
                simp only [sl2SubalgebraOfRoot_as_H_submodule] at hm_α_original; exact hm_α_original
              apply LieSubalgebra.lie_mem; exact hx_χ_in_sl2; exact hm_α_in_sl2
            exact h_bracket_in_sl2
          by_cases w_chi : χ.toLinear = 0
          · have hx_χ_in_H : x_χ ∈ H.toLieSubmodule := by
              rw [← rootSpace_zero_eq K L H]
              convert hx_χ
              ext h; simp only [Pi.zero_apply]
              have h_apply : (χ.toLinear : H → K) h = 0 := by rw [w_chi]; rfl
              exact h_apply.symm
            apply LieSubmodule.mem_iSup_of_mem α
            simp only [sl2SubalgebraOfRoot_as_H_submodule]
            have hm_α_base : m_α ∈ sl2SubalgebraOfRoot α.2.2 := by
              simp only [sl2SubalgebraOfRoot_as_H_submodule] at hm_α_original; exact hm_α_original
            exact sl2SubalgebraOfRoot_stable_under_H α.1 α.2.2 ⟨x_χ, hx_χ_in_H⟩ m_α hm_α_base

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
                sl2SubalgebraOfRoot_as_H_submodule β.1 β.2.2 := by
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
                    sl2SubalgebraOfRoot_as_H_submodule β β_indexed.property.right ≤
                    ⨆ (γ : {γ : Weight K H L // γ.toLinear ∈ q ∧ γ.IsNonZero}),
                    sl2SubalgebraOfRoot_as_H_submodule γ γ.property.right := by
                  have h := le_iSup (fun γ : {γ : Weight K H L // γ.toLinear ∈ q ∧ γ.IsNonZero} =>
                    sl2SubalgebraOfRoot_as_H_submodule γ.1 γ.2.2) β_indexed
                  exact h
                have h_β_contains : genWeightSpace L (χ.toLinear + α.1.toLinear) ≤
                    sl2SubalgebraOfRoot_as_H_submodule β β_indexed.property.right := by
                  rw [sl2SubalgebraOfRoot_as_H_submodule_eq_sup]
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
                sl2SubalgebraOfRoot_as_H_submodule β.1 β.2.2 := by
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
                    sl2SubalgebraOfRoot_as_H_submodule β β_indexed.property.right ≤
                    ⨆ (γ : {γ : Weight K H L // γ.toLinear ∈ q ∧ γ.IsNonZero}),
                    sl2SubalgebraOfRoot_as_H_submodule γ γ.property.right := by
                  have h := le_iSup (fun γ : {γ : Weight K H L // γ.toLinear ∈ q ∧ γ.IsNonZero} =>
                    sl2SubalgebraOfRoot_as_H_submodule γ.1 γ.2.2) β_indexed
                  exact h
                have h_β_contains : genWeightSpace L (χ.toLinear - α.1.toLinear) ≤
                    sl2SubalgebraOfRoot_as_H_submodule β β_indexed.property.right := by
                  rw [sl2SubalgebraOfRoot_as_H_submodule_eq_sup]
                  apply le_sup_of_le_left
                  apply le_sup_of_le_left
                  have h_eq : β.toLinear = χ.toLinear - α.1.toLinear := rfl
                  rw [h_eq]
                exact h_β_contains.trans β_term_in_supr

            have h_chi_containment :
              genWeightSpace L χ.toLinear ≤
              ⨆ β : {β : Weight K H L // β.toLinear ∈ q ∧ β.IsNonZero},
                sl2SubalgebraOfRoot_as_H_submodule β.1 β.2.2 := by
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
                    sl2SubalgebraOfRoot_as_H_submodule χ χ_indexed.property.right ≤
                    ⨆ (γ : {γ : Weight K H L // γ.toLinear ∈ q ∧ γ.IsNonZero}),
                    sl2SubalgebraOfRoot_as_H_submodule γ γ.property.right := by
                  have h := le_iSup (fun γ : {γ : Weight K H L // γ.toLinear ∈ q ∧ γ.IsNonZero} =>
                    sl2SubalgebraOfRoot_as_H_submodule γ.1 γ.2.2) χ_indexed
                  exact h
                have h_χ_contains : genWeightSpace L χ.toLinear ≤
                    sl2SubalgebraOfRoot_as_H_submodule χ χ_indexed.property.right := by
                  rw [sl2SubalgebraOfRoot_as_H_submodule_eq_sup]
                  apply le_sup_of_le_left
                  apply le_sup_of_le_left
                  rfl
                exact h_χ_contains.trans χ_term_in_supr

            have h_total_containment :
              genWeightSpace L (χ.toLinear + α.1.toLinear) ⊔
              genWeightSpace L (χ.toLinear - α.1.toLinear) ⊔
              genWeightSpace L χ.toLinear ≤
              ⨆ β : {β : Weight K H L // β.toLinear ∈ q ∧ β.IsNonZero},
                sl2SubalgebraOfRoot_as_H_submodule β.1 β.2.2 := by
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
              obtain ⟨i, hi⟩ := exists_root_index_of_weight_nonzero χ hχ_nonzero
              obtain ⟨j, hj⟩ := exists_root_index_of_in_index_set q α
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
              obtain ⟨i, hi⟩ := exists_root_index_of_weight_nonzero χ hχ_nonzero
              have hα_neg_nonzero : (-α.1).IsNonZero := Weight.IsNonZero.neg α.2.2
              obtain ⟨j, hj⟩ := exists_root_index_of_weight_nonzero (-α.1) hα_neg_nonzero
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
            obtain ⟨i, hi⟩ := exists_root_index_of_weight_nonzero χ hχ_nonzero
            obtain ⟨j, hj⟩ := exists_root_index_of_in_index_set q α
            have h_pairing_zero : S.pairing i j = 0 := by
              obtain ⟨i', j', hi', hj', h_zero⟩ :=
                pairing_zero_of_trivial_sum_diff_spaces χ α.1 hχ_nonzero α.2.2 w_plus w_minus
                  h_plus_bot h_minus_bot
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
              simp only [H_α] at hm_h
              obtain ⟨h_elem, hh_elem, hh_eq⟩ := hm_h
              have h_bracket_elem : ⁅x_χ, (h_elem : L)⁆ = 0 :=
                zero_pairing_implies_zero_bracket χ α.1 x_χ hx_χ h_elem hh_elem h_chi_coroot_zero
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
