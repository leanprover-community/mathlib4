/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.Algebra.Lie.Weights.Killing
import Mathlib.LinearAlgebra.RootSystem.Basic

/-!
# The root system associated with a Lie algebra

We show that the roots of a finite dimensional splitting semisimple Lie algebra over a field of
characteristic 0 form a root system. We achieve this by studying root chains.

## Main results

- `LieAlgebra.IsKilling.apply_coroot_eq_cast`:
  If `β - qα ... β ... β + rα` is the `α`-chain through `β`, then
  `β (coroot α) = q - r`. In particular, it is an integer.

- `LieAlgebra.IsKilling.rootSpace_zsmul_add_ne_bot_iff`:
  The `α`-chain through `β` (`β - qα ... β ... β + rα`) are the only roots of the form `β + kα`.

- `LieAlgebra.IsKilling.eq_neg_or_eq_of_eq_smul`:
  `±α` are the only `K`-multiples of a root `α` that are also (non-zero) roots.

- `LieAlgebra.IsKilling.rootSystem`: The root system of a finite-dimensional Lie algebra with
  non-degenerate Killing form over a field of characteristic zero,
  relative to a splitting Cartan subalgebra.

-/

noncomputable section

namespace LieAlgebra.IsKilling

open LieModule Module

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [IsTriangularizable K H L]

variable (α β : Weight K H L) (hα : α.IsNonZero)

private lemma chainLength_aux {x} (hx : x ∈ rootSpace H (chainTop α β)) :
    ∃ n : ℕ, n • x = ⁅coroot α, x⁆ := by
  by_cases hx' : x = 0
  · exact ⟨0, by simp [hx']⟩
  obtain ⟨h, e, f, isSl2, he, hf⟩ := exists_isSl2Triple_of_weight_isNonZero hα
  obtain rfl := isSl2.h_eq_coroot hα he hf
  have : isSl2.HasPrimitiveVectorWith x (chainTop α β (coroot α)) :=
    have := lie_mem_weightSpace_of_mem_weightSpace he hx
    ⟨hx', by rw [← lie_eq_smul_of_mem_rootSpace hx]; rfl,
      by rwa [weightSpace_add_chainTop α β hα] at this⟩
  obtain ⟨μ, hμ⟩ := this.exists_nat
  exact ⟨μ, by rw [nsmul_eq_smul_cast K, ← hμ, lie_eq_smul_of_mem_rootSpace hx]⟩

/-- The length of the `α`-chain through `β`. See `chainBotCoeff_add_chainTopCoeff`. -/
def chainLength (α β : Weight K H L) : ℕ :=
  letI := Classical.propDecidable
  if hα : α.IsZero then 0 else
    (chainLength_aux α β hα (chainTop α β).exists_ne_zero.choose_spec.1).choose

lemma chainLength_of_isZero (hα : α.IsZero) : chainLength α β = 0 := dif_pos hα

lemma chainLength_nsmul {x} (hx : x ∈ rootSpace H (chainTop α β)) :
    chainLength α β • x = ⁅coroot α, x⁆ := by
  by_cases hα : α.IsZero
  · rw [coroot_eq_zero_iff.mpr hα, chainLength_of_isZero _ _ hα, zero_smul, zero_lie]
  let x' := (chainTop α β).exists_ne_zero.choose
  have h : x' ∈ rootSpace H (chainTop α β) ∧ x' ≠ 0 :=
    (chainTop α β).exists_ne_zero.choose_spec
  obtain ⟨k, rfl⟩ : ∃ k : K, k • x' = x := by
    simpa using (finrank_eq_one_iff_of_nonzero' ⟨x', h.1⟩ (by simpa using h.2)).mp
      (finrank_rootSpace_eq_one _ (chainTop_isNonZero α β hα)) ⟨_, hx⟩
  rw [lie_smul, smul_comm, chainLength, dif_neg hα, (chainLength_aux α β hα h.1).choose_spec]

lemma chainLength_smul {x} (hx : x ∈ rootSpace H (chainTop α β)) :
    (chainLength α β : K) • x = ⁅coroot α, x⁆ := by
  rw [← nsmul_eq_smul_cast, chainLength_nsmul _ _ hx]

lemma apply_coroot_eq_cast' :
    β (coroot α) = ↑(chainLength α β - 2 * chainTopCoeff α β : ℤ) := by
  by_cases hα : α.IsZero
  · rw [coroot_eq_zero_iff.mpr hα, chainLength, dif_pos hα, hα.eq, chainTopCoeff_zero, map_zero,
      CharP.cast_eq_zero, mul_zero, sub_self, Int.cast_zero]
  obtain ⟨x, hx, x_ne0⟩ := (chainTop α β).exists_ne_zero
  have := chainLength_smul _ _ hx
  rw [lie_eq_smul_of_mem_rootSpace hx, ← sub_eq_zero, ← sub_smul,
    smul_eq_zero_iff_left x_ne0, sub_eq_zero, coe_chainTop', nsmul_eq_mul, Pi.natCast_def,
    Pi.add_apply, Pi.mul_apply, root_apply_coroot hα] at this
  simp only [Int.cast_sub, Int.cast_natCast, Int.cast_mul, Int.cast_ofNat, eq_sub_iff_add_eq',
    this, mul_comm (2 : K)]

lemma rootSpace_neg_nsmul_add_chainTop_of_le {n : ℕ} (hn : n ≤ chainLength α β) :
    rootSpace H (- (n • α) + chainTop α β) ≠ ⊥ := by
  by_cases hα : α.IsZero
  · simpa only [hα.eq, smul_zero, neg_zero, chainTop_zero, zero_add, ne_eq] using β.2
  obtain ⟨x, hx, x_ne0⟩ := (chainTop α β).exists_ne_zero
  obtain ⟨h, e, f, isSl2, he, hf⟩ := exists_isSl2Triple_of_weight_isNonZero hα
  obtain rfl := isSl2.h_eq_coroot hα he hf
  have prim : isSl2.HasPrimitiveVectorWith x (chainLength α β : K) :=
    have := lie_mem_weightSpace_of_mem_weightSpace he hx
    ⟨x_ne0, (chainLength_smul _ _ hx).symm, by rwa [weightSpace_add_chainTop _ _ hα] at this⟩
  simp only [← smul_neg, ne_eq, LieSubmodule.eq_bot_iff, not_forall]
  exact ⟨_, toEnd_pow_apply_mem hf hx n, prim.pow_toEnd_f_ne_zero_of_eq_nat rfl hn⟩

lemma rootSpace_neg_nsmul_add_chainTop_of_lt {n : ℕ} (hn : chainLength α β < n) :
    rootSpace H (- (n • α) + chainTop α β) = ⊥ := by
  by_contra e
  let W : Weight K H L := ⟨_, e⟩
  have hW : (W : H → K) = - (n • α) + chainTop α β := rfl
  have H₁ : 1 + n + chainTopCoeff (-α) W ≤ chainLength (-α) W := by
    have := apply_coroot_eq_cast' (-α) W
    simp only [coroot_neg, map_neg, hW, nsmul_eq_mul, Pi.natCast_def, coe_chainTop, zsmul_eq_mul,
      Int.cast_natCast, Pi.add_apply, Pi.neg_apply, Pi.mul_apply, root_apply_coroot hα, mul_two,
      neg_add_rev, apply_coroot_eq_cast' α β, Int.cast_sub, Int.cast_mul, Int.cast_ofNat,
      mul_comm (2 : K), add_sub_cancel, neg_neg, add_sub, Nat.cast_inj,
      eq_sub_iff_add_eq, ← Nat.cast_add, ← sub_eq_neg_add, sub_eq_iff_eq_add] at this
    linarith [this, hn]
  have H₂ : ((1 + n + chainTopCoeff (-α) W) • α + chainTop (-α) W : H → K) =
      (chainTopCoeff α β + 1) • α + β := by
    simp only [Weight.coe_neg, nsmul_eq_smul_cast ℤ, Nat.cast_add, Nat.cast_one, coe_chainTop,
      smul_neg, ← neg_smul, hW, ← add_assoc, ← add_smul, ← sub_eq_add_neg]
    congr 2
    ring
  have := rootSpace_neg_nsmul_add_chainTop_of_le (-α) W H₁
  rw [Weight.coe_neg, ← smul_neg, neg_neg, ← Weight.coe_neg, H₂] at this
  exact this (weightSpace_chainTopCoeff_add_one_nsmul_add α β hα)

lemma chainTopCoeff_le_chainLength : chainTopCoeff α β ≤ chainLength α β := by
  by_cases hα : α.IsZero
  · simp only [hα.eq, chainTopCoeff_zero, zero_le]
  rw [← not_lt, ← Nat.succ_le]
  intro e
  apply weightSpace_nsmul_add_ne_bot_of_le α β
    (Nat.sub_le (chainTopCoeff α β) (chainLength α β).succ)
  rw [nsmul_eq_smul_cast ℤ, Nat.cast_sub e, sub_smul, sub_eq_neg_add,
    add_assoc, ← coe_chainTop, ← nsmul_eq_smul_cast]
  exact rootSpace_neg_nsmul_add_chainTop_of_lt α β hα (Nat.lt_succ_self _)

lemma chainBotCoeff_add_chainTopCoeff :
    chainBotCoeff α β + chainTopCoeff α β = chainLength α β := by
  by_cases hα : α.IsZero
  · rw [hα.eq, chainTopCoeff_zero, chainBotCoeff_zero, zero_add, chainLength_of_isZero α β hα]
  apply le_antisymm
  · rw [← Nat.le_sub_iff_add_le (chainTopCoeff_le_chainLength α β),
      ← not_lt, ← Nat.succ_le, chainBotCoeff, ← Weight.coe_neg]
    intro e
    apply weightSpace_nsmul_add_ne_bot_of_le _ _ e
    rw [nsmul_eq_smul_cast ℤ, Nat.cast_succ, Nat.cast_sub (chainTopCoeff_le_chainLength α β),
      LieModule.Weight.coe_neg, smul_neg, ← neg_smul, neg_add_rev, neg_sub, sub_eq_neg_add,
      ← add_assoc, ← neg_add_rev, add_smul, add_assoc, ← coe_chainTop, neg_smul,
      ← @Nat.cast_one ℤ, ← Nat.cast_add, ← nsmul_eq_smul_cast]
    exact rootSpace_neg_nsmul_add_chainTop_of_lt α β hα (Nat.lt_succ_self _)
  · rw [← not_lt]
    intro e
    apply rootSpace_neg_nsmul_add_chainTop_of_le α β e
    rw [← Nat.succ_add, nsmul_eq_smul_cast ℤ, ← neg_smul, coe_chainTop, ← add_assoc, ← add_smul,
      Nat.cast_add, neg_add, add_assoc, neg_add_self, add_zero, neg_smul, ← smul_neg,
      ← nsmul_eq_smul_cast]
    exact weightSpace_chainTopCoeff_add_one_nsmul_add (-α) β (Weight.IsNonZero.neg hα)

lemma chainTopCoeff_add_chainBotCoeff :
    chainTopCoeff α β + chainBotCoeff α β = chainLength α β := by
  rw [add_comm, chainBotCoeff_add_chainTopCoeff]

lemma chainBotCoeff_le_chainLength : chainBotCoeff α β ≤ chainLength α β :=
  (Nat.le_add_left _ _).trans_eq (chainTopCoeff_add_chainBotCoeff α β)

@[simp]
lemma chainLength_neg :
    chainLength (-α) β = chainLength α β := by
  rw [← chainBotCoeff_add_chainTopCoeff, ← chainBotCoeff_add_chainTopCoeff, add_comm,
    Weight.coe_neg, chainTopCoeff_neg, chainBotCoeff_neg]

@[simp]
lemma chainLength_zero [Nontrivial L] : chainLength 0 β = 0 := by
  simp [← chainBotCoeff_add_chainTopCoeff]

/-- If `β - qα ... β ... β + rα` is the `α`-chain through `β`, then
  `β (coroot α) = q - r`. In particular, it is an integer. -/
lemma apply_coroot_eq_cast :
    β (coroot α) = (chainBotCoeff α β - chainTopCoeff α β : ℤ) := by
  rw [apply_coroot_eq_cast', ← chainTopCoeff_add_chainBotCoeff]; congr 1; omega

lemma le_chainBotCoeff_of_rootSpace_ne_top (n : ℤ) (hn : rootSpace H (-n • α + β) ≠ ⊥) :
    n ≤ chainBotCoeff α β := by
  contrapose! hn
  lift n to ℕ using (Nat.cast_nonneg _).trans hn.le
  rw [Nat.cast_lt, ← @Nat.add_lt_add_iff_right (chainTopCoeff α β),
    chainBotCoeff_add_chainTopCoeff] at hn
  have := rootSpace_neg_nsmul_add_chainTop_of_lt α β hα hn
  rwa [nsmul_eq_smul_cast ℤ, ← neg_smul, coe_chainTop, ← add_assoc,
    ← add_smul, Nat.cast_add, neg_add, add_assoc, neg_add_self, add_zero] at this

/-- Members of the `α`-chain through `β` are the only roots of the form `β - kα`. -/
lemma rootSpace_zsmul_add_ne_bot_iff (n : ℤ) :
    rootSpace H (n • α + β) ≠ ⊥ ↔ n ≤ chainTopCoeff α β ∧ -n ≤ chainBotCoeff α β := by
  constructor
  · refine (fun hn ↦ ⟨?_, le_chainBotCoeff_of_rootSpace_ne_top α β hα _ (by rwa [neg_neg])⟩)
    rw [← chainBotCoeff_neg, ← Weight.coe_neg]
    apply le_chainBotCoeff_of_rootSpace_ne_top _ _ hα.neg
    rwa [neg_smul, Weight.coe_neg, smul_neg, neg_neg]
  · rintro ⟨h₁, h₂⟩
    set k := chainTopCoeff α β - n with hk; clear_value k
    lift k to ℕ using (by rw [hk, le_sub_iff_add_le, zero_add]; exact h₁)
    rw [eq_sub_iff_add_eq, ← eq_sub_iff_add_eq'] at hk
    subst hk
    simp only [neg_sub, tsub_le_iff_right, ← Nat.cast_add, Nat.cast_le,
      chainBotCoeff_add_chainTopCoeff] at h₂
    have := rootSpace_neg_nsmul_add_chainTop_of_le α β h₂
    rwa [coe_chainTop, nsmul_eq_smul_cast ℤ, ← neg_smul,
      ← add_assoc, ← add_smul, ← sub_eq_neg_add] at this

lemma rootSpace_zsmul_add_ne_bot_iff_mem (n : ℤ) :
    rootSpace H (n • α + β) ≠ ⊥ ↔ n ∈ Finset.Icc (-chainBotCoeff α β : ℤ) (chainTopCoeff α β) := by
  rw [rootSpace_zsmul_add_ne_bot_iff α β hα n, Finset.mem_Icc, and_comm, neg_le]

lemma chainTopCoeff_of_eq_zsmul_add (β' : Weight K H L) (n : ℤ) (hβ' : (β' : H → K) = n • α + β) :
    chainTopCoeff α β' = chainTopCoeff α β - n := by
  apply le_antisymm
  · refine le_sub_iff_add_le.mpr ((rootSpace_zsmul_add_ne_bot_iff α β hα _).mp ?_).1
    rw [add_smul, add_assoc, ← hβ', ← coe_chainTop]
    exact (chainTop α β').2
  · refine ((rootSpace_zsmul_add_ne_bot_iff α β' hα _).mp ?_).1
    rw [hβ', ← add_assoc, ← add_smul, sub_add_cancel, ← coe_chainTop]
    exact (chainTop α β).2

lemma chainBotCoeff_of_eq_zsmul_add (β' : Weight K H L) (n : ℤ) (hβ' : (β' : H → K) = n • α + β) :
    chainBotCoeff α β' = chainBotCoeff α β + n := by
  have : (β' : H → K) = -n • (-α) + β := by rwa [neg_smul, smul_neg, neg_neg]
  rw [chainBotCoeff, chainBotCoeff, ← Weight.coe_neg,
    chainTopCoeff_of_eq_zsmul_add (-α) β hα.neg β' (-n) this, sub_neg_eq_add]

lemma chainLength_of_eq_zsmul_add (β' : Weight K H L) (n : ℤ) (hβ' : (β' : H → K) = n • α + β) :
    chainLength α β' = chainLength α β := by
  by_cases hα : α.IsZero
  · rw [chainLength_of_isZero _ _ hα, chainLength_of_isZero _ _ hα]
  · apply Nat.cast_injective (R := ℤ)
    rw [← chainTopCoeff_add_chainBotCoeff, ← chainTopCoeff_add_chainBotCoeff,
      Nat.cast_add, Nat.cast_add, chainTopCoeff_of_eq_zsmul_add α β hα β' n hβ',
      chainBotCoeff_of_eq_zsmul_add α β hα β' n hβ', sub_eq_add_neg, add_add_add_comm,
      neg_add_self, add_zero]

lemma chainTopCoeff_zero_right [Nontrivial L] :
    chainTopCoeff α (0 : Weight K H L) = 1 := by
  symm
  apply eq_of_le_of_not_lt
  · rw [Nat.one_le_iff_ne_zero]
    intro e
    exact α.2 (by simpa [e, Weight.coe_zero] using
      weightSpace_chainTopCoeff_add_one_nsmul_add α (0 : Weight K H L) hα)
  obtain ⟨x, hx, x_ne0⟩ := (chainTop α (0 : Weight K H L)).exists_ne_zero
  obtain ⟨h, e, f, isSl2, he, hf⟩ := exists_isSl2Triple_of_weight_isNonZero hα
  obtain rfl := isSl2.h_eq_coroot hα he hf
  have prim : isSl2.HasPrimitiveVectorWith x (chainLength α (0 : Weight K H L) : K) :=
    have := lie_mem_weightSpace_of_mem_weightSpace he hx
    ⟨x_ne0, (chainLength_smul _ _ hx).symm, by rwa [weightSpace_add_chainTop _ _ hα] at this⟩
  obtain ⟨k, hk⟩ : ∃ k : K, k • f =
      (toEnd K L L f ^ (chainTopCoeff α (0 : Weight K H L) + 1)) x := by
    have : (toEnd K L L f ^ (chainTopCoeff α (0 : Weight K H L) + 1)) x ∈ rootSpace H (-α) := by
      convert toEnd_pow_apply_mem hf hx (chainTopCoeff α (0 : Weight K H L) + 1) using 2
      rw [coe_chainTop', Weight.coe_zero, add_zero, succ_nsmul',
        add_assoc, smul_neg, neg_add_self, add_zero]
    simpa using (finrank_eq_one_iff_of_nonzero' ⟨f, hf⟩ (by simpa using isSl2.f_ne_zero)).mp
      (finrank_rootSpace_eq_one _ hα.neg) ⟨_, this⟩
  apply_fun (⁅f, ·⁆) at hk
  simp only [lie_smul, lie_self, smul_zero, prim.lie_f_pow_toEnd_f] at hk
  intro e
  refine prim.pow_toEnd_f_ne_zero_of_eq_nat rfl ?_ hk.symm
  have := (apply_coroot_eq_cast' α 0).symm
  simp only [← @Nat.cast_two ℤ, ← Nat.cast_mul, Weight.zero_apply, Int.cast_eq_zero, sub_eq_zero,
    Nat.cast_inj] at this
  rwa [this, Nat.succ_le, two_mul, add_lt_add_iff_left]

lemma chainBotCoeff_zero_right [Nontrivial L] : chainBotCoeff α (0 : Weight K H L) = 1 :=
  chainTopCoeff_zero_right (-α) hα.neg

lemma chainLength_zero_right [Nontrivial L] : chainLength α 0 = 2 := by
  rw [← chainBotCoeff_add_chainTopCoeff, chainTopCoeff_zero_right α hα,
    chainBotCoeff_zero_right α hα]

lemma rootSpace_two_smul : rootSpace H (2 • α) = ⊥ := by
  cases subsingleton_or_nontrivial L
  · exact IsEmpty.elim inferInstance α
  simpa [chainTopCoeff_zero_right α hα] using
    weightSpace_chainTopCoeff_add_one_nsmul_add α (0 : Weight K H L) hα

lemma rootSpace_one_div_two_smul : rootSpace H ((2⁻¹ : K) • α) = ⊥ := by
  by_contra h
  let W : Weight K H L := ⟨_, h⟩
  have hW : 2 • (W : H → K) = α := by
    show 2 • (2⁻¹ : K) • (α : H → K) = α
    rw [nsmul_eq_smul_cast K, smul_smul]; simp
  apply α.weightSpace_ne_bot
  have := rootSpace_two_smul W (fun (e : (W : H → K) = 0) ↦ hα <| by
    apply_fun (2 • ·) at e; simpa [hW] using e)
  rwa [hW] at this

lemma eq_neg_one_or_eq_zero_or_eq_one_of_eq_smul (k : K) (h : (β : H → K) = k • α) :
    k = -1 ∨ k = 0 ∨ k = 1 := by
  cases subsingleton_or_nontrivial L
  · exact IsEmpty.elim inferInstance α
  have H := apply_coroot_eq_cast' α β
  rw [h] at H
  simp only [Pi.smul_apply, root_apply_coroot hα] at H
  rcases (chainLength α β).even_or_odd with (⟨n, hn⟩|⟨n, hn⟩)
  · rw [hn, ← two_mul] at H
    simp only [smul_eq_mul, Nat.cast_mul, Nat.cast_ofNat, ← mul_sub, ← mul_comm (2 : K),
      Int.cast_sub, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast,
      mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false] at H
    rw [← Int.cast_natCast, ← Int.cast_natCast (chainTopCoeff α β), ← Int.cast_sub] at H
    have := (rootSpace_zsmul_add_ne_bot_iff_mem α 0 hα (n - chainTopCoeff α β)).mp
      (by rw [zsmul_eq_smul_cast K, ← H, ← h, Weight.coe_zero, add_zero]; exact β.2)
    rw [chainTopCoeff_zero_right α hα, chainBotCoeff_zero_right α hα, Nat.cast_one] at this
    set k' : ℤ := n - chainTopCoeff α β
    subst H
    have : k' ∈ ({-1, 0, 1} : Finset ℤ) := by
      show k' ∈ Finset.Icc (-1 : ℤ) (1 : ℤ)
      exact this
    simpa only [Int.reduceNeg, Finset.mem_insert, Finset.mem_singleton, ← @Int.cast_inj K,
      Int.cast_zero, Int.cast_neg, Int.cast_one] using this
  · apply_fun (· / 2) at H
    rw [hn, smul_eq_mul] at H
    have hk : k = n + 2⁻¹ - chainTopCoeff α β := by simpa [sub_div, add_div] using H
    have := (rootSpace_zsmul_add_ne_bot_iff α β hα (chainTopCoeff α β - n)).mpr ?_
    swap
    · simp only [tsub_le_iff_right, le_add_iff_nonneg_right, Nat.cast_nonneg, neg_sub, true_and]
      rw [← Nat.cast_add, chainBotCoeff_add_chainTopCoeff, hn]
      omega
    rw [h, hk, zsmul_eq_smul_cast K, ← add_smul] at this
    simp only [Int.cast_sub, Int.cast_natCast,
      sub_add_sub_cancel', add_sub_cancel_left, ne_eq] at this
    cases this (rootSpace_one_div_two_smul α hα)

/-- `±α` are the only `K`-multiples of a root `α` that are also (non-zero) roots. -/
lemma eq_neg_or_eq_of_eq_smul (hβ : β.IsNonZero) (k : K) (h : (β : H → K) = k • α) :
    β = -α ∨ β = α := by
  by_cases hα : α.IsZero
  · rw [hα, smul_zero] at h; cases hβ h
  rcases eq_neg_one_or_eq_zero_or_eq_one_of_eq_smul α β hα k h with (rfl | rfl | rfl)
  · exact .inl (by ext; rw [h, neg_one_smul]; rfl)
  · cases hβ (by rwa [zero_smul] at h)
  · exact .inr (by ext; rw [h, one_smul])

/-- The reflection of a root along another. -/
def reflectRoot (α β : Weight K H L) : Weight K H L where
  toFun := β - β (coroot α) • α
  weightSpace_ne_bot' := by
    by_cases hα : α.IsZero
    · simpa [hα.eq] using β.weightSpace_ne_bot
    rw [sub_eq_neg_add, apply_coroot_eq_cast α β, ← neg_smul, ← Int.cast_neg, ← zsmul_eq_smul_cast,
      rootSpace_zsmul_add_ne_bot_iff α β hα]
    omega

lemma reflectRoot_isNonZero (α β : Weight K H L) (hβ : β.IsNonZero) :
    (reflectRoot α β).IsNonZero := by
  intro e
  have : β (coroot α) = 0 := by
    by_cases hα : α.IsZero
    · simp [coroot_eq_zero_iff.mpr hα]
    apply add_left_injective (β (coroot α))
    simpa [root_apply_coroot hα, mul_two] using congr_fun (sub_eq_zero.mp e) (coroot α)
  have : reflectRoot α β = β := by ext; simp [reflectRoot, this]
  exact hβ (this ▸ e)

variable (H)

/-- The root system of a finite-dimensional Lie algebra with non-degenerate Killing form over a
field of characteristic zero, relative to a splitting Cartan subalgebra. -/
def rootSystem :
    RootSystem {α : Weight K H L // α.IsNonZero} K (Dual K H) H :=
  RootSystem.mk'
    IsReflexive.toPerfectPairingDual
    { toFun := (↑)
      inj' := by
        intro α β h; ext x; simpa using LinearMap.congr_fun h x  }
    { toFun := coroot ∘ (↑)
      inj' := by rintro ⟨α, hα⟩ ⟨β, hβ⟩ h; simpa using h }
    (fun α ↦ by simpa using root_apply_coroot α.property)
    (by
      rintro ⟨α, hα⟩ - ⟨⟨β, hβ⟩, rfl⟩
      simp only [Function.Embedding.coeFn_mk, IsReflexive.toPerfectPairingDual_toLin,
        Function.comp_apply, Set.mem_range, Subtype.exists, exists_prop]
      exact ⟨reflectRoot α β, reflectRoot_isNonZero α β hβ, rfl⟩)
    (by convert span_weight_isNonZero_eq_top K L H; ext; simp)

@[simp] lemma rootSystem_toLin_apply (f x) : (rootSystem H).toLin f x = f x := rfl
@[simp] lemma rootSystem_pairing_apply (α β) : (rootSystem H).pairing β α = β.1 (coroot α.1) := rfl
@[simp] lemma rootSystem_root_apply (α) : (rootSystem H).root α = α := rfl
@[simp] lemma rootSystem_coroot_apply (α) : (rootSystem H).coroot α = coroot α := rfl

theorem isCrystallographic_rootSystem : (rootSystem H).IsCrystallographic := by
  rintro α _ ⟨β, rfl⟩
  exact ⟨chainBotCoeff β.1 α.1 - chainTopCoeff β.1 α.1, by simp [apply_coroot_eq_cast β.1 α.1]⟩

theorem isReduced_rootSystem : (rootSystem H).IsReduced := by
  intro α β e
  rw [LinearIndependent.pair_iff' ((rootSystem H).ne_zero _), not_forall] at e
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, rootSystem_root_apply, ne_eq, not_not] at e
  obtain ⟨u, hu⟩ := e
  obtain (h | h) :=
    eq_neg_or_eq_of_eq_smul α.1 β.1 β.2 u (by ext x; exact DFunLike.congr_fun hu.symm x)
  · right; ext x; simpa [neg_eq_iff_eq_neg] using DFunLike.congr_fun h.symm x
  · left; ext x; simpa using DFunLike.congr_fun h.symm x

end LieAlgebra.IsKilling
