/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.RingTheory.AdicCompletion.Algebra

/-! # Evaluating an element of adic completion -/

variable {R : Type*} [CommRing R] (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M]
variable [IsAdicComplete I M]

namespace AdicCompletion

/-- Evaluating the limit of an element of the adic completion, given `IsAdicComplete I M`. -/
@[simps! symm_apply] noncomputable def limit : AdicCompletion I M ≃ₗ[R] M := by
  refine .symm
    { __ := of I M
      invFun x := (IsPrecomplete.prec' _ x.mk_surjective.choose.2).choose
      left_inv x := ?_
      right_inv x := ?_ }
  · dsimp only
    refine (IsHausdorff.eq_iff_smodEq (I := I)).mpr fun n ↦ ?_
    generalize_proofs _ _ _ h₁ h₂
    grw [← h₂.choose_spec]
    rw [SModEq, ← Submodule.mkQ_apply, ← mk_apply_coe, h₁.choose_spec]
    rfl
  · dsimp only
    ext n
    generalize_proofs _ _ _ _ _ h₁ h₂
    conv_rhs => rw [← h₁.choose_spec]
    exact (h₂.choose_spec n).symm

variable {I M}

@[simp] theorem mk_limit (x : AdicCompletion I M) (n : ℕ) :
    Submodule.Quotient.mk (p := I ^ n • (⊤ : Submodule R M)) (limit I M x) = x.val n :=
  congr($((limit I M).left_inv x).val n)

@[simp] theorem mk_limit' [IsAdicComplete I R] (x : AdicCompletion I R) (n : ℕ) :
    Ideal.Quotient.mk (I ^ n * (⊤ : Ideal R)) (limit I R x) = x.val n :=
  mk_limit x n

lemma limit_mk_sModEq {x : AdicCauchySequence I M} {n : ℕ} :
    limit I M (mk I M x) ≡ x n [SMOD I ^ n • (⊤ : Submodule R M)] := by
  rw [SModEq, mk_limit]; rfl

lemma limit_mk_spec {x : AdicCauchySequence I M} {y : M}
    (h : ∀ n, x n ≡ y [SMOD I ^ n • (⊤ : Submodule R M)]) :
    limit I M (mk I M x) = y :=
  (LinearEquiv.eq_symm_apply _).mp <| ext h

variable (I M)

/-- `limit` as an algebra isomorphism. -/
@[simps!] noncomputable def limitₐ [IsAdicComplete I R] : AdicCompletion I R ≃ₐ[R] R := by
  refine .ofLinearEquiv (limit I R) ?_ fun x y ↦ ?_ <;>
    rw [← LinearEquiv.eq_symm_apply] <;> ext <;> simp

omit [IsAdicComplete I M] in
/-- `I`-adic expansion: given any sequence `a : ℕ → M` and `ϖ ∈ I`, we form the `I`-adic expansion
`∑ ϖ ^ i • a i` as a Cauchy sequence. -/
@[simps!] noncomputable def adicExpansion (ϖ : R) (hϖ : ϖ ∈ I) :
    (ℕ → M) →ₗ[R] AdicCauchySequence I M where
  toFun a := .mk _ _ (fun n ↦ ∑ i ∈ Finset.range n, ϖ ^ i • a i) fun n ↦ by
    dsimp only
    have : ϖ ^ n • a n ∈ I ^ n • (⊤ : Submodule R M) :=
      Submodule.smul_mem_smul (Ideal.pow_mem_pow hϖ n) trivial
    rw [Finset.sum_range_succ]
    grw [SModEq.zero.mpr this]
    rw [add_zero]
  map_add' a b := by simp_rw [Pi.add_apply, smul_add, Finset.sum_add_distrib]; rfl
  map_smul' r a := by simp_rw [Pi.smul_apply, smul_comm _ r, ← Finset.smul_sum]; rfl

end AdicCompletion
