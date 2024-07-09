/-
Copyright (c) 2024 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.RingTheory.Artinian

/-!
# Results on the eigenvalue 0

In this file we provide equivalent characterizations of properties related to the eigenvalue 0,
such as being nilpotent, having determinant equal to 0, having a non-trivial kernel, etc...

## Main results

* `LinearMap.charpoly_nilpotent_tfae`:
  equivalent characterizations of nilpotent endomorphisms
* `LinearMap.hasEigenvalue_zero_tfae`:
  equivalent characterizations of endomorphisms with eigenvalue 0
* `LinearMap.not_hasEigenvalue_zero_tfae`:
  endomorphisms without eigenvalue 0
* `LinearMap.finrank_maxGenEigenspace`:
  the dimension of the maximal generalized eigenspace of an endomorphism
  is the trailing degree of its characteristic polynomial

-/

variable {R K M : Type*} [CommRing R] [IsDomain R] [Field K] [AddCommGroup M]
variable [Module R M] [Module.Finite R M] [Module.Free R M]
variable [Module K M] [Module.Finite K M]

open FiniteDimensional Module.Free Polynomial

lemma IsNilpotent.charpoly_eq_X_pow_finrank (φ : Module.End R M) (h : IsNilpotent φ) :
    φ.charpoly = X ^ finrank R M := by
  rw [← sub_eq_zero]
  apply IsNilpotent.eq_zero
  rw [finrank_eq_card_chooseBasisIndex]
  apply Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent
  exact h.map (LinearMap.toMatrixAlgEquiv (chooseBasis R M))

namespace LinearMap

open Module.Free in
lemma charpoly_nilpotent_tfae [IsNoetherian R M] (φ : Module.End R M) :
    List.TFAE [
      IsNilpotent φ,
      φ.charpoly = X ^ finrank R M,
      ∀ m : M, ∃ (n : ℕ), (φ ^ n) m = 0,
      natTrailingDegree φ.charpoly = finrank R M ] := by
  tfae_have 1 → 2
  · apply IsNilpotent.charpoly_eq_X_pow_finrank
  tfae_have 2 → 3
  · intro h m
    use finrank R M
    suffices φ ^ finrank R M = 0 by simp only [this, LinearMap.zero_apply]
    simpa only [h, map_pow, aeval_X] using φ.aeval_self_charpoly
  tfae_have 3 → 1
  · intro h
    obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp <| φ.eventually_iSup_ker_pow_eq
    use n
    ext x
    rw [zero_apply, ← mem_ker, ← hn n le_rfl]
    obtain ⟨k, hk⟩ := h x
    rw [← mem_ker] at hk
    exact Submodule.mem_iSup_of_mem _ hk
  tfae_have 2 ↔ 4
  · rw [← φ.charpoly_natDegree, φ.charpoly_monic.eq_X_pow_iff_natTrailingDegree_eq_natDegree]
  tfae_finish

lemma charpoly_eq_X_pow_iff [IsNoetherian R M] (φ : Module.End R M) :
    φ.charpoly = X ^ finrank R M ↔ ∀ m : M, ∃ (n : ℕ), (φ ^ n) m = 0 :=
  (charpoly_nilpotent_tfae φ).out 1 2

open Module.Free in
lemma hasEigenvalue_zero_tfae (φ : Module.End K M) :
    List.TFAE [
      Module.End.HasEigenvalue φ 0,
      IsRoot (minpoly K φ) 0,
      constantCoeff φ.charpoly = 0,
      LinearMap.det φ = 0,
      ⊥ < ker φ,
      ∃ (m : M), m ≠ 0 ∧ φ m = 0 ] := by
  tfae_have 1 ↔ 2
  · exact Module.End.hasEigenvalue_iff_isRoot
  tfae_have 2 → 3
  · obtain ⟨F, hF⟩ := minpoly_dvd_charpoly φ
    simp only [IsRoot.def, constantCoeff_apply, coeff_zero_eq_eval_zero, hF, eval_mul]
    intro h; rw [h, zero_mul]
  tfae_have 3 → 4
  · rw [← LinearMap.det_toMatrix (chooseBasis K M), Matrix.det_eq_sign_charpoly_coeff,
      constantCoeff_apply, charpoly]
    intro h; rw [h, mul_zero]
  tfae_have 4 → 5
  · exact bot_lt_ker_of_det_eq_zero
  tfae_have 5 → 6
  · contrapose!
    simp only [not_bot_lt_iff, eq_bot_iff]
    intro h x
    simp only [mem_ker, Submodule.mem_bot]
    contrapose!
    apply h
  tfae_have 6 → 1
  · rintro ⟨x, h1, h2⟩
    apply Module.End.hasEigenvalue_of_hasEigenvector ⟨_, h1⟩
    simpa only [Module.End.eigenspace_zero, mem_ker] using h2
  tfae_finish

lemma charpoly_constantCoeff_eq_zero_iff (φ : Module.End K M) :
    constantCoeff φ.charpoly = 0 ↔ ∃ (m : M), m ≠ 0 ∧ φ m = 0 :=
  (hasEigenvalue_zero_tfae φ).out 2 5

open Module.Free in
lemma not_hasEigenvalue_zero_tfae (φ : Module.End K M) :
    List.TFAE [
      ¬ Module.End.HasEigenvalue φ 0,
      ¬ IsRoot (minpoly K φ) 0,
      constantCoeff φ.charpoly ≠ 0,
      LinearMap.det φ ≠ 0,
      ker φ = ⊥,
      ∀ (m : M), φ m = 0 → m = 0 ] := by
  have := (hasEigenvalue_zero_tfae φ).not
  dsimp only [List.map] at this
  push_neg at this
  have aux₁ : ∀ m, (m ≠ 0 → φ m ≠ 0) ↔ (φ m = 0 → m = 0) := by intro m; apply not_imp_not
  have aux₂ : ker φ = ⊥ ↔ ¬ ⊥ < ker φ := by rw [bot_lt_iff_ne_bot, not_not]
  simpa only [aux₁, aux₂] using this

open Module.Free in
lemma finrank_maxGenEigenspace (φ : Module.End K M) :
    finrank K (φ.maxGenEigenspace 0) = natTrailingDegree (φ.charpoly) := by
  set V := φ.maxGenEigenspace 0
  have hV : V = ⨆ (n : ℕ), ker (φ ^ n) := by
    simp [V, Module.End.maxGenEigenspace, Module.End.genEigenspace]
  let W := ⨅ (n : ℕ), LinearMap.range (φ ^ n)
  have hVW : IsCompl V W := by
    rw [hV]
    exact LinearMap.isCompl_iSup_ker_pow_iInf_range_pow φ
  have hφV : ∀ x ∈ V, φ x ∈ V := by
    simp only [V, Module.End.mem_maxGenEigenspace, zero_smul, sub_zero,
      forall_exists_index]
    intro x n hx
    use n
    rw [← LinearMap.mul_apply, ← pow_succ, pow_succ', LinearMap.mul_apply, hx, map_zero]
  have hφW : ∀ x ∈ W, φ x ∈ W := by
    simp only [W, Submodule.mem_iInf, mem_range]
    intro x H n
    obtain ⟨y, rfl⟩ := H n
    use φ y
    rw [← LinearMap.mul_apply, ← pow_succ, pow_succ', LinearMap.mul_apply]
  let F := φ.restrict hφV
  let G := φ.restrict hφW
  let ψ := F.prodMap G
  let e := Submodule.prodEquivOfIsCompl V W hVW
  let bV := chooseBasis K V
  let bW := chooseBasis K W
  let b := bV.prod bW
  have hψ : ψ = e.symm.conj φ := by
    apply b.ext
    simp only [Basis.prod_apply, coe_inl, coe_inr, prodMap_apply, LinearEquiv.conj_apply,
      LinearEquiv.symm_symm, Submodule.coe_prodEquivOfIsCompl, coe_comp, LinearEquiv.coe_coe,
      Function.comp_apply, coprod_apply, Submodule.coeSubtype, map_add, Sum.forall, Sum.elim_inl,
      map_zero, ZeroMemClass.coe_zero, add_zero, LinearEquiv.eq_symm_apply, and_self,
      Submodule.coe_prodEquivOfIsCompl', restrict_coe_apply, implies_true, Sum.elim_inr, zero_add,
      e, V, W, ψ, F, G, b]
  rw [← e.symm.charpoly_conj φ, ← hψ, charpoly_prodMap,
    natTrailingDegree_mul (charpoly_monic _).ne_zero (charpoly_monic _).ne_zero]
  have hG : natTrailingDegree (charpoly G) = 0 := by
    apply Polynomial.natTrailingDegree_eq_zero_of_constantCoeff_ne_zero
    apply ((not_hasEigenvalue_zero_tfae G).out 2 5).mpr
    intro x hx
    apply Subtype.ext
    suffices x.1 ∈ V ⊓ W by rwa [hVW.inf_eq_bot, Submodule.mem_bot] at this
    suffices x.1 ∈ V from ⟨this, x.2⟩
    simp only [Module.End.mem_maxGenEigenspace, zero_smul, sub_zero, V]
    use 1
    rw [pow_one]
    rwa [Subtype.ext_iff] at hx
  rw [hG, add_zero, eq_comm]
  apply ((charpoly_nilpotent_tfae F).out 2 3).mp
  simp only [Subtype.forall, Module.End.mem_maxGenEigenspace, zero_smul, sub_zero, V, F]
  rintro x ⟨n, hx⟩
  use n
  apply Subtype.ext
  rw [ZeroMemClass.coe_zero]
  refine .trans ?_ hx
  generalize_proofs h'
  clear hx
  induction n with
  | zero => simp only [Nat.zero_eq, pow_zero, one_apply]
  | succ n ih => simp only [pow_succ', LinearMap.mul_apply, ih, restrict_apply]

end LinearMap
