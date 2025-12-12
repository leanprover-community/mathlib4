/-
Copyright (c) 2025 Janos Wolosz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Janos Wolosz
-/
module

public import Mathlib.Algebra.Lie.Weights.RootSystem
public import Mathlib.LinearAlgebra.RootSystem.Finite.Lemmas
import Mathlib.CategoryTheory.Category.Basic

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

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
    apply RootPairing.pairing_eq_zero_of_add_notMem_of_sub_notMem S.toRootPairing
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
        simp only [ Submodule.carrier_eq_coe, lie_zero, SetLike.mem_coe, zero_mem]
      | add m₁ m₂ _ _ ih₁ ih₂ =>
        simp only [lie_add, Submodule.carrier_eq_coe, SetLike.mem_coe] at ih₁ ih₂ ⊢
        exact add_mem ih₁ ih₂
    | zero =>
      simp only [Submodule.carrier_eq_coe, zero_lie, SetLike.mem_coe, zero_mem]
    | add x₁ x₂ _ _ ih₁ ih₂ =>
      simp only [add_lie, Submodule.carrier_eq_coe, SetLike.mem_coe] at ih₁ ih₂ ⊢
      exact add_mem ih₁ ih₂

lemma LieAlgebra.IsKilling.root_isNonZero (α : Weight K H L) (h : α ∈ H.root) : α.IsNonZero := by
  grind


lemma LieAlgebra.IsKilling.exists_coroot_pairing_ne_zero
    (β : Dual K H) (hβ : β ≠ 0) :
    ∃ i, (rootSystem H).toRootPairing.toLinearMap β ((rootSystem H).coroot i) ≠ 0 := by
      -- Assume for contradiction that for all roots i, β applied to the coroot of i is zero.
      by_contra h_contra
      have h_zero_on_span : ∀ x ∈ Submodule.span K (Set.range (rootSystem H).coroot), β x = 0 := by
        intro x hx; induction hx using Submodule.span_induction <;> aesop;
        rw [ ← right, h_contra _ left ];
      exact hβ ( by ext x; aesop )


lemma LieAlgebra.IsKilling.exists_root_mem_q_of_ne_bot
    (q : Submodule K (Dual K H))
    (hq : ∀ i, q ∈ End.invtSubmodule ((rootSystem H).reflection i))
    (h : q ≠ ⊥) :
    ∃ α ∈ H.root, ↑α ∈ q := by
      -- Since $q \neq \bot$, there exists $\beta \in q$ with $\beta \neq 0$.
      obtain ⟨β, hβ⟩ : ∃ β : Dual K H, β ∈ q ∧ β ≠ 0 := by
        exact ( Submodule.ne_bot_iff _ ).mp h;
      -- Since $q$ is invariant under the reflection corresponding to a root $\alpha_i$, we have $\alpha_i \in q$.
      obtain ⟨i, hi⟩ : ∃ i : H.root, (rootSystem H).toRootPairing.toLinearMap β ((rootSystem H).coroot i) ≠ 0 := by
        have := LieAlgebra.IsKilling.exists_coroot_pairing_ne_zero β;
        exact this hβ.2;
      -- Since $q$ is invariant under the reflection corresponding to $\alpha_i$, we have $\alpha_i \in q$.
      have h_alpha_i_in_q : (rootSystem H).toLinearMap β ((rootSystem H).coroot i) • (rootSystem H).root i ∈ q := by
        have h_alpha_i_in_q : (rootSystem H).reflection i β ∈ q := by
          -- Since $q$ is invariant under the reflection corresponding to $i$, we have $s_i(\beta) \in q$ by definition of invariance.
          apply hq i;
          exact hβ.1;
        -- Since $q$ is a submodule, subtracting $(β, α_i) * α_i$ from $β$ should keep it in $q$.
        have h_sub : β - ((rootSystem H).toLinearMap β ((rootSystem H).coroot i)) • (rootSystem H).root i ∈ q := by
          convert h_alpha_i_in_q using 1;
        simpa using q.sub_mem hβ.1 h_sub;
      use i.val; aesop;
      simpa [ smul_smul, hi ] using q.smul_mem ( β ( coroot val ) ) ⁻¹ h_alpha_i_in_q

lemma LieAlgebra.IsKilling.coroot_ne_zero
    {α : Weight K H L} (hα : α.IsNonZero) :
    coroot α ≠ 0 := by
      aesop

open Weight in
lemma LieAlgebra.IsKilling.sl2SubmoduleOfRoot_le_invtSubmoduleToLieIdeal
    (q : Submodule K (Dual K H))
    (_hq : ∀ (i : H.root), q ∈ End.invtSubmodule ((rootSystem H).reflection i))
    {α : Weight K H L} (hα : α.IsNonZero) (hαq : ↑α ∈ q) :
    (sl2SubmoduleOfRoot hα).toSubmodule ≤
      ⨆ α : {α : Weight K H L // ↑α ∈ q ∧ α.IsNonZero}, (sl2SubmoduleOfRoot α.2.2).toSubmodule := by
      exact le_iSup_of_le ⟨ α, hαq, hα ⟩ le_rfl



lemma LieAlgebra.IsKilling.sl2SubmoduleOfRoot_ne_bot
    {α : Weight K H L} (hα : α.IsNonZero) :
    sl2SubmoduleOfRoot hα ≠ ⊥ := by
      -- Since the coroot α is non-zero, the corootSubmodule α is not the zero submodule.
      have h_corootSubmodule_ne_bot : corootSubmodule α ≠ ⊥ := by
        intro h_eq
        have h_mem : (coroot α : L) ∈ corootSubmodule α := by
          rw [corootSubmodule, LieSubmodule.mem_map]
          exact ⟨coroot α, coroot_mem_corootSpace α, rfl⟩
        rw [h_eq, LieSubmodule.mem_bot] at h_mem
        have : coroot α = 0 := by exact_mod_cast h_mem
        exact coroot_ne_zero hα this
      -- Since the corootSubmodule α is non-zero, the sum of the three submodules (genWeightSpace L α, genWeightSpace L (-α), and corootSubmodule α) must also be non-zero.
      have h_sum_ne_bot : genWeightSpace L α ⊔ genWeightSpace L (-α) ⊔ corootSubmodule α ≠ ⊥ := by
        exact ne_bot_of_gt ( lt_of_lt_of_le ( lt_of_le_of_ne bot_le ( Ne.symm h_corootSubmodule_ne_bot ) ) ( le_sup_right ) );
      -- Since sl2SubmoduleOfRoot hα is defined as the sum of the three submodules, it follows directly that sl2SubmoduleOfRoot hα is also not the bottom submodule.
      convert h_sum_ne_bot using 1;
      exact sl2SubmoduleOfRoot_eq_sup α hα


lemma LieAlgebra.IsKilling.sl2SubmoduleOfRoot_toSubmodule_ne_bot
    {α : Weight K H L} (hα : α.IsNonZero) :
    (sl2SubmoduleOfRoot hα).toSubmodule ≠ ⊥ := by
      convert LieAlgebra.IsKilling.sl2SubmoduleOfRoot_ne_bot hα
      -- The submodule of a Lie submodule is the same as the original submodule.
      simp


lemma LieAlgebra.IsKilling.exists_orthogonal_element_of_ne_top
    (q : Submodule K (Dual K H)) (hq : q ≠ ⊤) :
    ∃ y : H, y ≠ 0 ∧ ∀ f ∈ q, f y = 0 := by
      have h_dual_seq : q.dualAnnihilator ≠ ⊥ := by
        norm_num +zetaDelta at *;
        exact hq;
      obtain ⟨ y, hy ⟩ := ( Submodule.ne_bot_iff _ ).mp h_dual_seq;
      -- Since the dual space of H is isomorphic to H itself, there exists a non-zero element in H corresponding to y.
      obtain ⟨x, hx⟩ : ∃ x : H, y = (Module.Dual.eval K H) x := by
        have h_iso : Function.Surjective (Module.Dual.eval K H) := by
          exact?;
        exact h_iso y |> Exists.imp fun x hx => hx.symm;
      simp +zetaDelta at *;
      exact ⟨ x, x.2, by aesop_cat, fun f hf => by simpa [ hx ] using hy.1 f hf ⟩

lemma LieAlgebra.IsKilling.ad_mem_sl2_eq_zero_of_root_eval_eq_zero
    {y : H} {α : Weight K H L} (hα : α.IsNonZero) (hy : (α : H → K) y = 0)
    (z : L) (hz : z ∈ sl2SubmoduleOfRoot hα) : ⁅(y : L), z⁆ = 0 := by
      -- Since `ad y` is semisimple, it acts as scalar multiplication by `α(y)` on the generalized eigenspace of `ad y` with eigenvalue `α(y)`.
      have h_semisimple : ∀ m ∈ genWeightSpace L α, ⁅↑y, m⁆ = α y • m := by
        have h_semisimple : ∀ m ∈ genWeightSpace L α, ⁅↑y, m⁆ = α y • m := by
          intro m hm
          have h_semisimple_ad : (ad K L y).IsSemisimple := by
            convert LieAlgebra.IsKilling.isSemisimple_ad_of_mem_isCartanSubalgebra y.2 using 1
          exact?;
        exact h_semisimple;
      -- Since `ad y` is semisimple, it acts as scalar multiplication by `-α(y)` on the generalized eigenspace of `ad y` with eigenvalue `-α(y)`.
      have h_semisimple_neg : ∀ m ∈ genWeightSpace L (-α), ⁅↑y, m⁆ = -(α y) • m := by
        intro m hm;
        exact?;
      -- The coroot space `corootSubmodule α` is spanned by `[u, v]` with `u ∈ genWeightSpace L α` and `v ∈ genWeightSpace L (-α)`.
      have h_coroot : ∀ m ∈ corootSubmodule α, ⁅↑y, m⁆ = 0 := by
        intro m hm
        have h_comm : ∀ u ∈ genWeightSpace L α, ∀ v ∈ genWeightSpace L (-α), ⁅↑y, ⁅u, v⁆⁆ = ⁅⁅↑y, u⁆, v⁆ + ⁅u, ⁅↑y, v⁆⁆ := by
          simp +zetaDelta at *;
        simp_all +decide [ LieSubmodule.mem_top, SetLike.mem_coe ];
        obtain ⟨ u, hu, v, hv, rfl ⟩ := hm.2;
        refine' TensorProduct.induction_on u _ _ _;
        · simp ( config := { decide := Bool.true } );
        · aesop;
        · simp +contextual [ h_comm ];
      -- Since `sl2SubmoduleOfRoot hα` is generated by these spaces, `y` commutes with everything in it.
      have h_comm : ∀ m ∈ sl2SubmoduleOfRoot hα, ⁅↑y, m⁆ = 0 := by
        rw [ sl2SubmoduleOfRoot_eq_sup ];
        intro m hm;
        rcases Submodule.mem_sup.mp hm with ⟨ m₁, hm₁, m₂, hm₂, rfl ⟩;
        rcases Submodule.mem_sup.mp hm₁ with ⟨ m₁', hm₁', m₂', hm₂', rfl ⟩;
        simp_all +decide [ lie_add ];
        rcases hm₂ with ⟨ m₂, hm₂, hm₂', rfl ⟩ ; exact h_coroot _ hm₂ hm₂';
      exact h_comm z hz

lemma LieAlgebra.IsKilling.center_eq_bot : LieAlgebra.center K L = ⊥ := by
  -- Let $x$ be an arbitrary element of the center.
  ext x
  simp [LieAlgebra.center]

open Weight in
lemma LieAlgebra.IsKilling.l2 (q : Submodule K (Dual K H))
    (h₁ : ∀ (i : H.root), q ∈ End.invtSubmodule ((rootSystem H).reflection i))
    (h₂ : ((⨆ α : {α : Weight K H L // ↑α ∈ q ∧ α.IsNonZero}, sl2SubmoduleOfRoot α.2.2)) = ⊤) :
    q = ⊤ := by
  -- If `q ≠ ⊤`, then there exists a non-zero `y ∈ H` such that `∀ f ∈ q, f(y) = 0`.
  by_contra hq_ne_top
  obtain ⟨y, hy_ne_zero, hy_ortho⟩ : ∃ y : H, y ≠ 0 ∧ ∀ f ∈ q, f y = 0 := by
    exact?;
  -- By `LieAlgebra.IsKilling.ad_mem_sl2_eq_zero_of_root_eval_eq_zero`, `[y, z] = 0` for all `z ∈ sl2SubmoduleOfRoot α`.
  have h_comm : ∀ α : {α : LieModule.Weight K H L // ↑α ∈ q ∧ α.IsNonZero}, ∀ z ∈ LieAlgebra.IsKilling.sl2SubmoduleOfRoot α.2.2, ⁅(y : L), z⁆ = 0 := by
    exact fun α z hz => LieAlgebra.IsKilling.ad_mem_sl2_eq_zero_of_root_eval_eq_zero α.2.2 ( hy_ortho _ α.2.1 ) z hz;
  -- Since `L` is generated by `sl2SubmoduleOfRoot α` for `α` such that `↑α ∈ q` (by `h₂`), it follows that `[y, L] = 0`.
  have h_comm_all : ∀ z : L, ⁅(y : L), z⁆ = 0 := by
    intro z;
    have h_comm_all : z ∈ ⨆ α : {α : LieModule.Weight K H L // ↑α ∈ q ∧ α.IsNonZero}, (LieAlgebra.IsKilling.sl2SubmoduleOfRoot α.2.2).toSubmodule := by
      convert Submodule.mem_top;
      convert h₂ using 1;
      simp +decide [ LieSubmodule.ext_iff ];
    rw [ Submodule.mem_iSup ] at h_comm_all;
    specialize h_comm_all ( LinearMap.ker ( LieAlgebra.ad K L y ) );
    exact h_comm_all fun α => fun z hz => by simpa using h_comm α z hz;
  -- Since `y ∈ Z(L)`, by `LieAlgebra.IsKilling.center_eq_bot`, `y = 0`.
  have h_y_zero : (y : L) ∈ LieAlgebra.center K L := by
    intro z;
    rw [ ← lie_skew, h_comm_all, neg_zero ];
  rw [ LieAlgebra.IsKilling.center_eq_bot ] at h_y_zero ; aesop

section IsSimple

variable [IsSimple K L]

open Weight in
lemma eq_top_of_invtSubmodule_ne_bot (q : Submodule K (Dual K H))
    (h₀ : ∀ (i : H.root), q ∈ End.invtSubmodule ((rootSystem H).reflection i))
    (h₁ : q ≠ ⊥) : q = ⊤ := by
  let J := (invtSubmoduleToLieIdeal q h₀)
  have r_j2 : J ≠ ⊥ := by
    have hJ_nonzero : ∃ α : Weight K H L, (α : Dual K H) ∈ q ∧ α.IsNonZero := by
      have := LieAlgebra.IsKilling.exists_root_mem_q_of_ne_bot q h₀ h₁;
      exact ⟨ this.choose, this.choose_spec.2, LieAlgebra.IsKilling.root_isNonZero _ this.choose_spec.1 ⟩;
    -- If $J$ were zero, then the submodule generated by the $\mathfrak{sl}_2$-triple corresponding to $\alpha$ would also be zero.
    by_contra hJ_zero
    have h_submodule_zero : (sl2SubmoduleOfRoot hJ_nonzero.choose_spec.2).toSubmodule = ⊥ := by
      have h_submodule_zero : (sl2SubmoduleOfRoot hJ_nonzero.choose_spec.2).toSubmodule ≤ J := by
        convert LieAlgebra.IsKilling.sl2SubmoduleOfRoot_le_invtSubmoduleToLieIdeal q h₀ _ _ using 1
        all_goals generalize_proofs at *;
        · -- By definition of $J$, we know that it is the supremum of the submodules generated by the $\mathfrak{sl}_2$-triples corresponding to the roots in $q$.
          simp [J, LieAlgebra.IsKilling.invtSubmoduleToLieIdeal];
        · exact hJ_nonzero.choose_spec.1;
      aesop;
    exact LieAlgebra.IsKilling.sl2SubmoduleOfRoot_toSubmodule_ne_bot hJ_nonzero.choose_spec.2 h_submodule_zero
  have : IsSimple K L := inferInstance
  have : J = ⊥ ∨ J = ⊤ := this.eq_bot_or_eq_top J
  have c₂ : J ≠ ⊥ := r_j2
  have c₃ : J = ⊤ := by grind
  apply LieAlgebra.IsKilling.l2 q h₀
  -- Unfold J in c₃ and extract the needed equality
  show (⨆ α : {α : Weight K H L // ↑α ∈ q ∧ α.IsNonZero}, sl2SubmoduleOfRoot α.2.2) = ⊤
  unfold J invtSubmoduleToLieIdeal at c₃
  simpa using c₃

instance : (rootSystem H).IsIrreducible := by
  have _i := nontrivial_of_isIrreducible K L L
  exact RootPairing.IsIrreducible.mk' (rootSystem H).toRootPairing <|
    eq_top_of_invtSubmodule_ne_bot

end IsSimple

end LieAlgebra.IsKilling
