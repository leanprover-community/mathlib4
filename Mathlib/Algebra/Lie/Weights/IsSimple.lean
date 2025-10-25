/-
Copyright (c) 2025 Janos Wolosz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Janos Wolosz
-/
import Mathlib.Algebra.Lie.Weights.RootSystem
import Mathlib.LinearAlgebra.RootSystem.Finite.Lemmas

/-!
# Simple Lie algebras

We show the irreducibility of root systems of simple Lie algebras.

## Main definitions
* `LieAlgebra.IsKilling.invtSubmoduleToLieIdeal`: constructs a Lie ideal from an invariant
  submodule of the dual space

## Main results
* `LieAlgebra.IsKilling.instIsIrreducible`: the root system of a simple Lie algebra is irreducible
-/

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
    ⟨⟨γ, by simp [LieSubalgebra.root]; exact hγ⟩, rfl⟩
  have h_plus_bot : genWeightSpace L (χ.toLinear + α.toLinear) = ⊥ := by
    by_contra h_plus_ne_bot
    let γ : Weight K H L := ⟨χ.toLinear + α.toLinear, h_plus_ne_bot⟩
    have hγ_nonzero : γ.IsNonZero := Weight.coe_toLinear_ne_zero_iff.mp w_plus
    obtain ⟨i, hi⟩ := exists_root_index χ (Weight.coe_toLinear_ne_zero_iff.mp w_chi)
    obtain ⟨j, hj⟩ := exists_root_index α hα₀
    have h_sum_in_range : S.root i + S.root j ∈ Set.range S.root := by
      rw [hi, hj]
      exact ⟨⟨γ, by simp [LieSubalgebra.root]; exact hγ_nonzero⟩, rfl⟩
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
      exact ⟨⟨γ, by simp [LieSubalgebra.root]; exact hγ_nonzero⟩, rfl⟩
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
      have h_apply : (χ.toLinear : H → K) h = 0 := by rw [w_chi]; rfl
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

section IsSimple

variable [IsSimple K L]

-- TODO Golf the below proof using `LieAlgebra.IsKilling.invtSubmoduleToLieIdeal` above
open Weight in
lemma eq_top_of_invtSubmodule_ne_bot (q : Submodule K (Dual K H))
    (h₀ : ∀ (i : H.root), q ∈ End.invtSubmodule ((rootSystem H).reflection i))
    (h₁ : q ≠ ⊥) : q = ⊤ := by
  have _i := nontrivial_of_isIrreducible K L L
  let S := rootSystem H
  by_contra h₃
  suffices h₂ : ∀ Φ, Φ.Nonempty → S.root '' Φ ⊆ q → (∀ i ∉ Φ, q ≤ LinearMap.ker (S.coroot' i)) →
      Φ = Set.univ by
    have := (S.eq_top_of_mem_invtSubmodule_of_forall_eq_univ q h₁ h₀) h₂
    apply False.elim (h₃ this)
  intro Φ hΦ₁ hΦ₂ hΦ₃
  by_contra hc
  have hΦ₂' : ∀ i ∈ Φ, (S.root i) ∈ q := by
    intro i hi
    apply hΦ₂
    exact Set.mem_image_of_mem S.root hi
  have s₁ (i j : H.root) (h₁ : i ∈ Φ) (h₂ : j ∉ Φ) : S.root i (S.coroot j) = 0 :=
    (hΦ₃ j h₂) (hΦ₂' i h₁)
  have s₁' (i j : H.root) (h₁ : i ∈ Φ) (h₂ : j ∉ Φ) : S.root j (S.coroot i) = 0 :=
    (S.pairing_eq_zero_iff (i := i) (j := j)).1 (s₁ i j h₁ h₂)
  have s₂ (i j : H.root) (h₁ : i ∈ Φ) (h₂ : j ∉ Φ) : i.1 (coroot j) = 0 := s₁ i j h₁ h₂
  have s₂' (i j : H.root) (h₁ : i ∈ Φ) (h₂ : j ∉ Φ) : j.1 (coroot i) = 0 := s₁' i j h₁ h₂
  have s₃ (i j : H.root) (h₁ : i ∈ Φ) (h₂ : j ∉ Φ) : genWeightSpace L (i.1.1 + j.1.1) = ⊥ := by
    by_contra h
    have i_non_zero : i.1.IsNonZero := by grind
    have j_non_zero : j.1.IsNonZero := by grind
    let r := Weight.mk (R := K) (L := H) (M := L) (i.1.1 + j.1.1) h
    have r₁ : r ≠ 0 := by
      intro a
      have h_eq : i.1 = -j.1 := Weight.ext <| congrFun (eq_neg_of_add_eq_zero_left
        (congr_arg Weight.toFun a))
      have := s₂ i j h₁ h₂
      rw [h_eq, coe_neg, Pi.neg_apply, root_apply_coroot j_non_zero] at this
      simp at this
    have r₂ : r ∈ H.root := by simp [isNonZero_iff_ne_zero, r₁]
    cases Classical.em (⟨r, r₂⟩ ∈ Φ) with
    | inl hl =>
      have e₁ : i.1.1 (coroot j) = 0 := s₂ i j h₁ h₂
      have e₂ : j.1.1 (coroot j) = 2 := root_apply_coroot j_non_zero
      have : (0 : K) = 2 := calc
        0 = (i.1.1 + j.1.1) (coroot j) := (s₂ ⟨r, r₂⟩ j hl h₂).symm
        _ = i.1.1 (coroot j) + j.1.1 (coroot j) := rfl
        _ = 2 := by rw [e₁, e₂, zero_add]
      simp at this
    | inr hr =>
      have e₁ : j.1.1 (coroot i) = 0 := s₂' i j h₁ h₂
      have e₂ : i.1.1 (coroot i) = 2 := root_apply_coroot i_non_zero
      have : (0 : K) = 2 := calc
        0 = (i.1.1 + j.1.1) (coroot i) := (s₂' i ⟨r, r₂⟩ h₁ hr).symm
        _ = i.1.1 (coroot i) + j.1.1 (coroot i) := rfl
        _ = 2 := by rw [e₁, e₂, add_zero]
      simp at this
  have s₄ (i j : H.root) (h1 : i ∈ Φ) (h2 : j ∉ Φ) (li : rootSpace H i.1.1)
      (lj : rootSpace H j.1.1) : ⁅li.1, lj.1⁆ = 0 := by
    have h₃ := lie_mem_genWeightSpace_of_mem_genWeightSpace li.2 lj.2
    rw [s₃ i j h1 h2] at h₃
    exact h₃
  let g := ⋃ i ∈ Φ, (rootSpace H i : Set L)
  let I := LieSubalgebra.lieSpan K L g
  have s₅ : I ≠ ⊤ := by
    obtain ⟨j, hj⟩ := (Set.ne_univ_iff_exists_notMem Φ).mp hc
    obtain ⟨z, hz₁, hz₂⟩ := exists_ne_zero (R := K) (L := H) (M := L) j
    by_contra! hI
    have center_element : z ∈ center K L := by
      have commutes_with_all (x : L) : ⁅x, z⁆ = 0 := by
        have x_mem_I : x ∈ I := by rw [hI]; exact trivial
        induction x_mem_I using LieSubalgebra.lieSpan_induction with
        | mem x hx =>
          obtain ⟨i, hi, hx1_mem⟩ := Set.mem_iUnion₂.mp hx
          have := s₄ i j hi hj
          simp only [Subtype.forall] at this
          exact (this x hx1_mem) z hz₁
        | zero => exact zero_lie z
        | add _ _ _ _ e f => rw [add_lie, e, f, add_zero]
        | smul _ _ _ d =>
          simp only [smul_lie, smul_eq_zero]
          right
          exact d
        | lie _ _ _ _ e f => rw [lie_lie, e, f, lie_zero, lie_zero, sub_self]
      exact commutes_with_all
    rw [center_eq_bot] at center_element
    exact hz₂ center_element
  have s₆ : I ≠ ⊥ := by
    obtain ⟨r, hr⟩ := Set.nonempty_def.mp hΦ₁
    obtain ⟨x, hx₁, hx₂⟩ := exists_ne_zero (R := K) (L := H) (M := L) r
    have x_in_g : x ∈ g := by
      apply Set.mem_iUnion_of_mem r
      simp only [Set.mem_iUnion]
      exact ⟨hr, hx₁⟩
    have x_mem_I : x ∈ I := LieSubalgebra.mem_lieSpan.mpr (fun _ a ↦ a x_in_g)
    by_contra h
    exact hx₂ (I.eq_bot_iff.mp h x x_mem_I)
  have s₇ : ∀ x y : L, y ∈ I → ⁅x, y⁆ ∈ I := by
    have gen : ⨆ χ : Weight K H L, (genWeightSpace L χ).toSubmodule = ⊤ := by
      simp only [LieSubmodule.iSup_toSubmodule_eq_top]
      exact iSup_genWeightSpace_eq_top' K H L
    intro x y hy
    have hx : x ∈ ⨆ χ : Weight K H L, (genWeightSpace L χ).toSubmodule := by
      simp only [gen, Submodule.mem_top]
    induction hx using Submodule.iSup_induction' with
    | mem j x hx =>
      induction hy using LieSubalgebra.lieSpan_induction with
      | mem x₁ hx₁ =>
        obtain ⟨i, hi, x₁_mem⟩ := Set.mem_iUnion₂.mp hx₁
        have r₁ (j : Weight K H L) : j = 0 ∨ j ∈ H.root := by
          rcases (eq_or_ne j 0) with h | h
          · left
            exact h
          · right
            refine Finset.mem_filter.mpr ?_
            exact ⟨Finset.mem_univ j, isNonZero_iff_ne_zero.mpr h⟩
        rcases (r₁ j) with h | h
        · have h₁ : ⁅x, x₁⁆ ∈ g := by
            have h₂ := lie_mem_genWeightSpace_of_mem_genWeightSpace hx x₁_mem
            rw [h, coe_zero, zero_add] at h₂
            exact Set.mem_biUnion hi h₂
          exact LieSubalgebra.mem_lieSpan.mpr fun _ a ↦ a h₁
        rcases (Classical.em (⟨j, h⟩ ∈ Φ)) with h₁ | h₁
        · exact I.lie_mem
            (LieSubalgebra.mem_lieSpan.mpr fun _ a ↦ a (Set.mem_biUnion h₁ hx))
            (LieSubalgebra.mem_lieSpan.mpr fun _ a ↦ a hx₁)
        have : ⁅x, x₁⁆ = 0 := by
          rw [← neg_eq_zero, lie_skew x₁ x, (s₄ i ⟨j, h⟩ hi h₁ ⟨x₁, x₁_mem⟩ ⟨x, hx⟩)]
        rw [this]
        exact I.zero_mem
      | zero => simp only [lie_zero, zero_mem, I]
      | add _ _ _ _ e f =>
        simp only [lie_add]
        exact add_mem e f
      | smul a _ _ d =>
        simp only [lie_smul]
        exact I.smul_mem a d
      | lie a b c d e f =>
        have : ⁅x, ⁅a, b⁆⁆ = ⁅⁅x, a⁆, b⁆ + ⁅a, ⁅x, b⁆⁆ := by
          simp only [lie_lie, sub_add_cancel]
        rw [this]
        exact add_mem (I.lie_mem e d) (I.lie_mem c f)
    | zero => simp only [zero_lie, zero_mem]
    | add x1 y1 _ _ hx hy =>
      simp only [add_lie]
      exact add_mem hx hy
  obtain ⟨I', h⟩ := (LieSubalgebra.exists_lieIdeal_coe_eq_iff (K := I)).2 s₇
  have : IsSimple K L := inferInstance
  have : I' = ⊥ ∨ I' = ⊤ := this.eq_bot_or_eq_top I'
  have c₁ : I' ≠ ⊤ := by
    rw [← h] at s₅
    exact ne_of_apply_ne (LieIdeal.toLieSubalgebra K L) s₅
  have c₂ : I' ≠ ⊥ := by
    rw [← h] at s₆
    exact ne_of_apply_ne (LieIdeal.toLieSubalgebra K L) s₆
  grind

instance : (rootSystem H).IsIrreducible := by
  have _i := nontrivial_of_isIrreducible K L L
  exact RootPairing.IsIrreducible.mk' (rootSystem H).toRootPairing <|
    eq_top_of_invtSubmodule_ne_bot

end IsSimple

end LieAlgebra.IsKilling
