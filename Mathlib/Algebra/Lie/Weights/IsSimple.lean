/-
Copyright (c) 2025 Janos Wolosz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Janos Wolosz
-/
module

public import Mathlib.Algebra.Lie.Weights.RootSystem
public import Mathlib.LinearAlgebra.RootSystem.Finite.Lemmas

/-!
# Simple Lie algebras

We show the irreducibility of root systems of simple Lie algebras.

## Main definitions
* `LieAlgebra.IsKilling.invtSubmoduleToLieIdeal`: constructs a Lie ideal from an invariant
  submodule of the dual space

## Main results
* `LieAlgebra.IsKilling.instIsIrreducible`: the root system of a simple Lie algebra is irreducible
-/

@[expose] public section

namespace LieAlgebra.IsKilling

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
open LieAlgebra LieModule Module
variable {H : LieSubalgebra K L} [H.IsCartanSubalgebra]

-- Note that after https://github.com/leanprover-community/mathlib4/issues/10068 (Cartan's criterion) is complete we can omit `[IsKilling K L]`
variable [IsKilling K L] [IsTriangularizable K H L]

section aux

variable (q : Submodule K (Dual K H))
  (hq : ∀ i, q ∈ End.invtSubmodule ((rootSystem H).reflection i))
  (χ : Weight K H L)
  (x_χ m_α : L) (hx_χ : x_χ ∈ genWeightSpace L χ)
  (α : Weight K H L) (hαq : ↑α ∈ q) (hα₀ : α.IsNonZero)

section

variable
  (w_plus : χ.toLinear + α.toLinear ≠ 0)
  (w_minus : χ.toLinear - α.toLinear ≠ 0)
  (w_chi : χ.toLinear ≠ 0)
  (m_pos m_neg : L)
  (y : H) (hy : y ∈ corootSpace α)
  (h_bracket_sum : ⁅x_χ, m_α⁆ = ⁅x_χ, m_pos⁆ + ⁅x_χ, m_neg⁆ + ⁅x_χ, (y : L)⁆)
  (h_pos_containment : ⁅x_χ, m_pos⁆ ∈ genWeightSpace L (⇑χ + ⇑α))
  (h_neg_containment : ⁅x_χ, m_neg⁆ ∈ genWeightSpace L (⇑χ - ⇑α))

include hx_χ w_plus w_minus w_chi h_bracket_sum h_pos_containment h_neg_containment hαq

private theorem chi_in_q_aux (h_chi_in_q : ↑χ ∈ q) :
    ⁅x_χ, m_α⁆ ∈ ⨆ α : {α : Weight K H L // ↑α ∈ q ∧ α.IsNonZero}, sl2SubmoduleOfRoot α.2.2 := by
  have h_h_containment : ⁅x_χ, (y : L)⁆ ∈ genWeightSpace L χ := by
    have h_zero_weight : H.toLieSubmodule.incl y ∈ genWeightSpace L (0 : H → K) := by
      apply toLieSubmodule_le_rootSpace_zero
      exact y.property
    convert lie_mem_genWeightSpace_of_mem_genWeightSpace hx_χ h_zero_weight
    ext h; simp
  have h_bracket_decomp : ⁅x_χ, m_α⁆ ∈
      genWeightSpace L (χ.toLinear + α.toLinear) ⊔
      genWeightSpace L (χ.toLinear - α.toLinear) ⊔ genWeightSpace L χ := by
    rw [h_bracket_sum]
    exact add_mem (add_mem
      (Submodule.mem_sup_left (Submodule.mem_sup_left h_pos_containment))
      (Submodule.mem_sup_left (Submodule.mem_sup_right h_neg_containment)))
      (Submodule.mem_sup_right h_h_containment)
  let I := ⨆ β : {β : Weight K H L // ↑β ∈ q ∧ β.IsNonZero}, sl2SubmoduleOfRoot β.2.2
  have genWeightSpace_le_I (β_lin : H →ₗ[K] K) (hβ_in_q : β_lin ∈ q)
      (hβ_ne_zero : β_lin ≠ 0) : genWeightSpace L β_lin ≤ I := by
    by_cases h_trivial : genWeightSpace L β_lin = ⊥
    · simp [h_trivial]
    · let β : Weight K H L := ⟨β_lin, h_trivial⟩
      have hβ_nonzero : β.IsNonZero := Weight.coe_toLinear_ne_zero_iff.mp hβ_ne_zero
      refine le_trans ?_ (le_iSup _ ⟨β, hβ_in_q, hβ_nonzero⟩)
      rw [sl2SubmoduleOfRoot_eq_sup]
      exact le_sup_of_le_left (le_sup_of_le_left le_rfl)
  have h_plus_contain : genWeightSpace L (χ.toLinear + α.toLinear) ≤ I :=
    genWeightSpace_le_I _ (q.add_mem h_chi_in_q hαq) w_plus
  have h_minus_contain : genWeightSpace L (χ.toLinear - α.toLinear) ≤ I :=
    genWeightSpace_le_I _ (by
      have : -α.toLinear = (-1 : K) • α.toLinear := by simp
      rw [sub_eq_add_neg, this]
      exact q.add_mem h_chi_in_q (q.smul_mem (-1) hαq)) w_minus
  have h_chi_contain : genWeightSpace L χ.toLinear ≤ I :=
    genWeightSpace_le_I _ h_chi_in_q (fun h_eq => (w_chi h_eq).elim)
  exact sup_le (sup_le h_plus_contain h_minus_contain) h_chi_contain h_bracket_decomp

include hq hα₀ hy

private theorem chi_not_in_q_aux (h_chi_not_in_q : ↑χ ∉ q) :
    ⁅x_χ, m_α⁆ ∈ ⨆ α : {α : Weight K H L // ↑α ∈ q ∧ α.IsNonZero}, sl2SubmoduleOfRoot α.2.2 := by
  let S := rootSystem H
  have exists_root_index (γ : Weight K H L) (hγ : γ.IsNonZero) : ∃ i, S.root i = ↑γ :=
    ⟨⟨γ, by simpa [LieSubalgebra.root]⟩, rfl⟩
  have h_plus_bot : genWeightSpace L (χ.toLinear + α.toLinear) = ⊥ := by
    by_contra h_plus_ne_bot
    let γ : Weight K H L := ⟨χ.toLinear + α.toLinear, h_plus_ne_bot⟩
    have hγ_nonzero : γ.IsNonZero := Weight.coe_toLinear_ne_zero_iff.mp w_plus
    obtain ⟨i, hi⟩ := exists_root_index χ (Weight.coe_toLinear_ne_zero_iff.mp w_chi)
    obtain ⟨j, hj⟩ := exists_root_index α hα₀
    have h_sum_in_range : S.root i + S.root j ∈ Set.range S.root := by
      rw [hi, hj]
      exact ⟨⟨γ, by simpa [LieSubalgebra.root]⟩, rfl⟩
    have h_equiv := RootPairing.root_mem_submodule_iff_of_add_mem_invtSubmodule
      ⟨q, by rw [RootPairing.mem_invtRootSubmodule_iff]; exact hq⟩ h_sum_in_range
    rw [hi] at h_equiv
    exact h_chi_not_in_q (h_equiv.mpr (by rw [hj]; exact hαq))
  have h_minus_bot : genWeightSpace L (χ.toLinear - α.toLinear) = ⊥ := by
    by_contra h_minus_ne_bot
    let γ : Weight K H L := ⟨χ.toLinear - α.toLinear, h_minus_ne_bot⟩
    have hγ_nonzero : γ.IsNonZero := Weight.coe_toLinear_ne_zero_iff.mp w_minus
    obtain ⟨i, hi⟩ := exists_root_index χ (Weight.coe_toLinear_ne_zero_iff.mp w_chi)
    obtain ⟨j, hj⟩ := exists_root_index (-α) (Weight.IsNonZero.neg hα₀)
    have h_sum_in_range : S.root i + S.root j ∈ Set.range S.root := by
      rw [hi, hj, Weight.toLinear_neg, ← sub_eq_add_neg]
      exact ⟨⟨γ, by simpa [LieSubalgebra.root]⟩, rfl⟩
    have h_equiv := RootPairing.root_mem_submodule_iff_of_add_mem_invtSubmodule
      ⟨q, by rw [RootPairing.mem_invtRootSubmodule_iff]; exact hq⟩ h_sum_in_range
    rw [hi] at h_equiv
    exact h_chi_not_in_q (h_equiv.mpr (by
      rw [hj, Weight.toLinear_neg]
      convert q.smul_mem (-1) hαq using 1
      rw [neg_smul, one_smul]))
  obtain ⟨i, hi⟩ := exists_root_index χ (Weight.coe_toLinear_ne_zero_iff.mp w_chi)
  obtain ⟨j, hj⟩ := exists_root_index α hα₀
  have h_pairing_zero : S.pairing i j = 0 := by
    apply RootPairing.pairing_eq_zero_of_add_notMem_of_sub_notMem S
    · intro h_eq; exact w_minus (by rw [← hi, ← hj, h_eq, sub_self])
    · intro h_eq; exact w_plus (by rw [← hi, ← hj, h_eq, neg_add_cancel])
    · intro ⟨idx, hidx⟩
      have : genWeightSpace L (S.root idx) ≠ ⊥ := idx.val.genWeightSpace_ne_bot
      rw [hidx, hi, hj] at this
      exact this h_plus_bot
    · intro ⟨idx, hidx⟩
      have : genWeightSpace L (S.root idx) ≠ ⊥ := idx.val.genWeightSpace_ne_bot
      rw [hidx, hi, hj] at this
      exact this h_minus_bot
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
  have h_bracket_zero : ⁅x_χ, (y : L)⁆ = 0 := by
    have h_chi_coroot_zero : χ (coroot α) = 0 := by
      have h_pairing_eq : S.pairing i j = i.1 (coroot j.1) := by
        rw [rootSystem_pairing_apply]
      rw [h_pairing_zero] at h_pairing_eq
      have w_eq {w₁ w₂ : Weight K H L} (h : w₁.toLinear = w₂.toLinear) : w₁ = w₂ := by
        apply Weight.ext; intro x; exact LinearMap.ext_iff.mp h x
      have hi_val : i.1 = χ := w_eq (by rw [← hi]; rfl)
      have hj_val : j.1 = α := w_eq (by rw [← hj]; rfl)
      rw [hi_val, hj_val] at h_pairing_eq
      exact h_pairing_eq.symm
    have h_lie_eq_smul : ⁅(y : L), x_χ⁆ = χ y • x_χ := lie_eq_smul_of_mem_rootSpace hx_χ y
    have h_chi_h_zero : χ y = 0 := by
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp <| by
        rw [← coe_corootSpace_eq_span_singleton α, LieSubmodule.mem_toSubmodule]
        exact hy
      rw [← hc, map_smul, h_chi_coroot_zero, smul_zero]
    have h_bracket_elem : ⁅x_χ, (y : L)⁆ = 0 := by
      rw [← lie_skew, h_lie_eq_smul, h_chi_h_zero, zero_smul, neg_zero]
    exact h_bracket_elem
  rw [h_bracket_sum, h_pos_zero, h_neg_zero, h_bracket_zero]
  simp only [add_zero, zero_mem]

end

include hq hx_χ hαq in
private theorem invtSubmoduleToLieIdeal_aux (hm_α : m_α ∈ sl2SubmoduleOfRoot hα₀) :
    ⁅x_χ, m_α⁆ ∈ ⨆ α : {α : Weight K H L // ↑α ∈ q ∧ α.IsNonZero}, sl2SubmoduleOfRoot α.2.2 := by
  have hm_α_original : m_α ∈ sl2SubmoduleOfRoot hα₀ := hm_α
  rw [sl2SubmoduleOfRoot_eq_sup] at hm_α
  obtain ⟨m_αneg, hm_αneg, m_h, hm_h, hm_eq⟩ := Submodule.mem_sup.mp hm_α
  obtain ⟨m_pos, hm_pos, m_neg, hm_neg, hm_αneg_eq⟩ := Submodule.mem_sup.mp hm_αneg
  have hm_α_decomp : m_α = m_pos + m_neg + m_h := by
    rw [← hm_eq, ← hm_αneg_eq]
  have h_bracket_sum : ⁅x_χ, m_α⁆ = ⁅x_χ, m_pos⁆ + ⁅x_χ, m_neg⁆ + ⁅x_χ, m_h⁆ := by
    rw [hm_α_decomp, lie_add, lie_add]
  by_cases w_plus : χ.toLinear + α.toLinear = 0
  · apply LieSubmodule.mem_iSup_of_mem ⟨α, hαq, hα₀⟩
    have hx_χ_in_sl2 : x_χ ∈ sl2SubalgebraOfRoot hα₀ := by
      obtain ⟨h, e, f, ht, he, hf⟩ := exists_isSl2Triple_of_weight_isNonZero hα₀
      rw [mem_sl2SubalgebraOfRoot_iff hα₀ ht he hf]
      have hx_χ_neg : x_χ ∈ genWeightSpace L (-α.toLinear) := by
        rw [← (add_eq_zero_iff_eq_neg.mp w_plus)]
        exact hx_χ
      obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' ⟨f, hf⟩ (by simp [ht.f_ne_zero])).mp
        (finrank_rootSpace_eq_one (-α) (by simpa using hα₀)) ⟨x_χ, hx_χ_neg⟩
      exact ⟨0, c, 0, by simpa using hc.symm⟩
    apply LieSubalgebra.lie_mem <;> [exact hx_χ_in_sl2; exact hm_α_original]
  by_cases w_minus : χ.toLinear - α.toLinear = 0
  · apply LieSubmodule.mem_iSup_of_mem ⟨α, hαq, hα₀⟩
    have hx_χ_in_sl2 : x_χ ∈ sl2SubalgebraOfRoot hα₀ := by
      obtain ⟨h, e, f, ht, he, hf⟩ := exists_isSl2Triple_of_weight_isNonZero hα₀
      rw [mem_sl2SubalgebraOfRoot_iff hα₀ ht he hf]
      have hx_χ_pos : x_χ ∈ genWeightSpace L α.toLinear := by
        rw [← (sub_eq_zero.mp w_minus)]
        exact hx_χ
      obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' ⟨e, he⟩ (by simp [ht.e_ne_zero])).mp
        (finrank_rootSpace_eq_one α hα₀) ⟨x_χ, hx_χ_pos⟩
      exact ⟨c, 0, 0, by simpa using hc.symm⟩
    apply LieSubalgebra.lie_mem <;> [exact hx_χ_in_sl2; exact hm_α_original]
  by_cases w_chi : χ.toLinear = 0
  · have hx_χ_in_H : x_χ ∈ H.toLieSubmodule := by
      rw [← rootSpace_zero_eq K L H]
      convert hx_χ; ext h; simp only [Pi.zero_apply]
      have h_apply : (χ.toLinear : H → K) h = 0 := by rw [w_chi, LinearMap.zero_apply]
      exact h_apply.symm
    apply LieSubmodule.mem_iSup_of_mem ⟨α, hαq, hα₀⟩
    rw [← (by rfl : ⁅(⟨x_χ, hx_χ_in_H⟩ : H), m_α⁆ = ⁅x_χ, m_α⁆)]
    exact (sl2SubmoduleOfRoot hα₀).lie_mem hm_α_original
  have h_pos_containment : ⁅x_χ, m_pos⁆ ∈ genWeightSpace L (χ.toLinear + α.toLinear) :=
    lie_mem_genWeightSpace_of_mem_genWeightSpace hx_χ hm_pos
  have h_neg_containment : ⁅x_χ, m_neg⁆ ∈ genWeightSpace L (χ.toLinear - α.toLinear) := by
    rw [sub_eq_add_neg]; exact lie_mem_genWeightSpace_of_mem_genWeightSpace hx_χ hm_neg
  obtain ⟨y, hy, rfl⟩ := hm_h
  by_cases h_chi_in_q : ↑χ ∈ q
  · exact chi_in_q_aux q χ x_χ m_α hx_χ α hαq w_plus w_minus w_chi m_pos m_neg y h_bracket_sum
      h_pos_containment h_neg_containment h_chi_in_q
  · exact chi_not_in_q_aux q hq χ x_χ m_α hx_χ α hαq hα₀ w_plus w_minus w_chi m_pos m_neg y hy
      h_bracket_sum h_pos_containment h_neg_containment h_chi_in_q

end aux

/-- Constructs a Lie ideal from an invariant submodule of the dual space of a Cartan subalgebra.

Given a submodule `q` of the dual space `Dual K H` that is invariant under all root reflections,
this produces a Lie ideal by taking the sum of all `sl₂` subalgebras corresponding to roots
whose linear forms lie in `q`. -/
noncomputable def invtSubmoduleToLieIdeal (q : Submodule K (Dual K H))
    (hq : ∀ i, q ∈ End.invtSubmodule ((rootSystem H).reflection i)) : LieIdeal K L where
  __ := ⨆ α : {α : Weight K H L // ↑α ∈ q ∧ α.IsNonZero}, sl2SubmoduleOfRoot α.2.2
  lie_mem := by
    intro x m hm
    have hx : x ∈ ⨆ χ : Weight K H L, genWeightSpace L χ := by
      simp [LieModule.iSup_genWeightSpace_eq_top']
    induction hx using LieSubmodule.iSup_induction' with
    | mem χ x_χ hx_χ =>
      induction hm using LieSubmodule.iSup_induction' with
      | mem α m_α hm_α => exact invtSubmoduleToLieIdeal_aux q hq χ x_χ m_α hx_χ α.1 α.2.1 α.2.2 hm_α
      | zero =>
        simp only [Submodule.carrier_eq_coe, lie_zero, SetLike.mem_coe, zero_mem]
      | add m₁ m₂ _ _ ih₁ ih₂ =>
        simp only [lie_add, Submodule.carrier_eq_coe, SetLike.mem_coe] at ih₁ ih₂ ⊢
        exact add_mem ih₁ ih₂
    | zero =>
      simp only [Submodule.carrier_eq_coe, zero_lie, SetLike.mem_coe, zero_mem]
    | add x₁ x₂ _ _ ih₁ ih₂ =>
      simp only [add_lie, Submodule.carrier_eq_coe, SetLike.mem_coe] at ih₁ ih₂ ⊢
      exact add_mem ih₁ ih₂

@[simp] lemma coe_invtSubmoduleToLieIdeal_eq_iSup (q : Submodule K (Dual K H))
    (hq : ∀ i, q ∈ End.invtSubmodule ((rootSystem H).reflection i).toLinearMap) :
    (invtSubmoduleToLieIdeal q hq).toSubmodule =
      ⨆ α : {α : Weight K H L // ↑α ∈ q ∧ α.IsNonZero}, sl2SubmoduleOfRoot α.2.2 :=
  rfl

open LieSubmodule in
@[simp] lemma invtSubmoduleToLieIdeal_top :
    invtSubmoduleToLieIdeal (⊤ : Submodule K (Module.Dual K H)) (by simp) = ⊤ := by
  simp_rw [← toSubmodule_inj, coe_invtSubmoduleToLieIdeal_eq_iSup, iSup_toSubmodule,
    top_toSubmodule, iSup_toSubmodule_eq_top, eq_top_iff, ← cartan_sup_iSup_rootSpace_eq_top H,
    iSup_subtype, Submodule.mem_top, true_and, sup_le_iff, iSup_le_iff, sl2SubmoduleOfRoot_eq_sup]
  refine ⟨?_, fun α hα ↦ le_iSup₂_of_le α hα <| le_sup_of_le_left <| le_sup_of_le_left <| le_refl _⟩
  suffices H.toLieSubmodule ≤ ⨆ α : Weight K H L, ⨆ (_ : α.IsNonZero), corootSubmodule α from
    this.trans <| iSup₂_mono fun α hα ↦ le_sup_right
  simp

@[simp] lemma invtSubmoduleToLieIdeal_apply_eq_top_iff (q : Submodule K (Dual K H))
    (hq : ∀ i, q ∈ End.invtSubmodule ((rootSystem H).reflection i).toLinearMap) :
    invtSubmoduleToLieIdeal q hq = ⊤ ↔ q = ⊤ := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  have h : (⨆ α : {α : Weight K H L // ↑α ∈ q ∧ α.IsNonZero}, sl2SubmoduleOfRoot α.2.2) = ⊤ := by
    rw [← LieSubmodule.toSubmodule_inj] at h
    have := coe_invtSubmoduleToLieIdeal_eq_iSup q hq
    exact (LieSubmodule.toSubmodule_eq_top (⨆ α, sl2SubmoduleOfRoot α.property.right)).mp h
  by_contra hq_ne_top
  have h_ne_bot : q.dualCoannihilator ≠ ⊥ := by
    contrapose! hq_ne_top
    have := Subspace.finrank_add_finrank_dualCoannihilator_eq q
    rw [hq_ne_top, finrank_bot, add_zero] at this
    exact Submodule.eq_top_of_finrank_eq (this.trans Subspace.dual_finrank_eq.symm)
  obtain ⟨y, hy_mem, hy_ne_zero⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h_ne_bot
  have hy_ortho : ∀ f ∈ q, f y = 0 := (Submodule.mem_dualCoannihilator y).mp hy_mem
  have h_comm : ∀ α : {α : Weight K H L // ↑α ∈ q ∧ α.IsNonZero},
      ∀ z ∈ sl2SubmoduleOfRoot α.2.2, ⁅(y : L), z⁆ = 0 := fun α z hz => by
    have hy : (α.1 : H → K) y = 0 := hy_ortho _ α.2.1
    rw [sl2SubmoduleOfRoot_eq_sup] at hz
    obtain ⟨z_αneg, hz_αneg, z_cor, ⟨h_cor, _, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hz
    obtain ⟨z_α, hz_α, z_negα, hz_negα, rfl⟩ := Submodule.mem_sup.mp hz_αneg
    simp only [lie_add, ← LieSubalgebra.coe_bracket_of_module]
    rw [lie_eq_smul_of_mem_rootSpace hz_α, hy, zero_smul, zero_add,
        lie_eq_smul_of_mem_rootSpace hz_negα, Pi.neg_apply, hy, neg_zero, zero_smul, zero_add]
    have h_cor_in_zero : (h_cor : L) ∈ rootSpace H (0 : H → K) := by
      rw [rootSpace_zero_eq]; exact h_cor.property
    convert lie_eq_smul_of_mem_rootSpace h_cor_in_zero y using 1; simp
  have h_comm_all : ∀ z : L, ⁅(y : L), z⁆ = 0 := fun z => by
    have hz : z ∈ ⨆ α : {α : Weight K H L // ↑α ∈ q ∧ α.IsNonZero},
        (sl2SubmoduleOfRoot α.2.2).toSubmodule := by
      convert Submodule.mem_top using 1
      rw [← LieSubmodule.iSup_toSubmodule, h]; rfl
    rw [Submodule.mem_iSup] at hz
    exact hz (LinearMap.ker (ad K L y)) fun α z hz => by simpa using h_comm α z hz
  have h_y_center : (y : L) ∈ LieAlgebra.center K L := fun z => by
    rw [← lie_skew, h_comm_all, neg_zero]
  simp only [center_eq_bot, LieSubmodule.mem_bot, ZeroMemClass.coe_eq_zero] at h_y_center
  exact hy_ne_zero h_y_center

@[simp] lemma invtSubmoduleToLieIdeal_apply_eq_bot_iff (q : Submodule K (Module.Dual K H))
    (hq : ∀ i, q ∈ Module.End.invtSubmodule ((rootSystem H).reflection i).toLinearMap) :
    invtSubmoduleToLieIdeal q hq = ⊥ ↔ q = ⊥ := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · by_contra hq_nonzero
    have hq_invt : q ∈ (rootSystem H).invtRootSubmodule := by
      rw [RootPairing.mem_invtRootSubmodule_iff]; exact hq
    have h_ne_bot : (⟨q, hq_invt⟩ : (rootSystem H).invtRootSubmodule) ≠ ⊥ :=
      fun h_eq => hq_nonzero (Subtype.ext_iff.mp h_eq)
    rw [Ne, RootPairing.invtRootSubmodule.eq_bot_iff, not_forall] at h_ne_bot
    obtain ⟨i, hi⟩ := h_ne_bot
    rw [not_not] at hi
    have hα₀ : i.val.IsNonZero := (Finset.mem_filter.mp i.property).2
    have h_sl2_le : (sl2SubmoduleOfRoot hα₀ : Submodule K L) ≤ invtSubmoduleToLieIdeal q hq := by
      rw [LieIdeal.toLieSubalgebra_toSubmodule, coe_invtSubmoduleToLieIdeal_eq_iSup,
        LieSubmodule.iSup_toSubmodule]
      exact le_iSup_of_le ⟨i.val, hi, hα₀⟩ le_rfl
    rw [h] at h_sl2_le
    simp only [LieIdeal.toLieSubalgebra_toSubmodule, LieSubmodule.bot_toSubmodule, le_bot_iff,
      LieSubmodule.toSubmodule_eq_bot] at h_sl2_le
    exact sl2SubmoduleOfRoot_ne_bot i.1 hα₀ h_sl2_le
  · simp [h, invtSubmoduleToLieIdeal]

instance [IsSimple K L] : (rootSystem H).IsIrreducible := by
  have _i := nontrivial_of_isIrreducible K L L
  exact RootPairing.IsIrreducible.mk' (rootSystem H) <| fun q h₀ h₁ ↦ by
    have := IsSimple.eq_bot_or_eq_top (invtSubmoduleToLieIdeal q h₀)
    aesop

end LieAlgebra.IsKilling
