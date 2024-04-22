/-
Copyright (c) 2024 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import Mathlib.Algebra.Lie.EngelSubalgebra
import Mathlib.Algebra.Lie.CartanSubalgebra
import Mathlib.Algebra.Lie.Rank
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Eigenspace.Minpoly

-- move this
namespace LinearMap

variable {K M : Type*}
variable [Field K] [AddCommGroup M] [Module K M]
variable [Module.Finite K M]
variable (φ : Module.End K M)

open FiniteDimensional Polynomial


open Module.Free in
lemma charpoly_nilpotent_tfae :
    List.TFAE [
      IsNilpotent φ,
      φ.charpoly = X ^ finrank K M,
      ∀ m : M, ∃ (n : ℕ), (φ ^ n) m = 0,
      natTrailingDegree φ.charpoly = finrank K M ] := by
  tfae_have 1 → 2
  · intro h
    rw [← sub_eq_zero]
    apply IsNilpotent.eq_zero
    rw [finrank_eq_card_chooseBasisIndex]
    apply Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent
    exact h.map (toMatrixAlgEquiv (chooseBasis K M))
  tfae_have 2 → 3
  · intro h m
    use finrank K M
    suffices φ ^ finrank K M = 0 by simp only [this, LinearMap.zero_apply]
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
  · rw [← φ.charpoly_natDegree]
    refine ⟨?_, φ.charpoly_monic.eq_X_pow_of_natTrailingDegree_eq_natDegree⟩
    intro h
    rw [← natTrailingDegree_X_pow (R := K) φ.charpoly.natDegree, ← h]
  tfae_finish

open Module.Free in
lemma hasEigenvalue_zero_tfae :
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

open Module.Free in
lemma not_hasEigenvalue_zero_tfae :
    List.TFAE [
      ¬ Module.End.HasEigenvalue φ 0,
      ¬ IsRoot (minpoly K φ) 0,
      constantCoeff φ.charpoly ≠ 0,
      LinearMap.det φ ≠ 0,
      ker φ ≤ ⊥,
      ∀ (m : M), φ m = 0 → m = 0 ] := by
  have := (hasEigenvalue_zero_tfae φ).not
  dsimp only [List.map] at this
  push_neg at this
  have aux₁ : ∀ m, (m ≠ 0 → φ m ≠ 0) ↔ (φ m = 0 → m = 0) := by intro m; apply not_imp_not
  have aux₂ : ker φ ≤ ⊥ ↔ ¬ ⊥ < ker φ := by rw [le_bot_iff, bot_lt_iff_ne_bot, not_not]
  simpa only [aux₁, aux₂] using this

open Module.Free in
lemma charpoly_eq_X_pow_iff :
    φ.charpoly = X ^ finrank K M ↔ ∀ m : M, ∃ (n : ℕ), (φ ^ n) m = 0 :=
  (charpoly_nilpotent_tfae φ).out 1 2

lemma charpoly_constantCoeff_eq_zero_iff :
    constantCoeff φ.charpoly = 0 ↔ ∃ (m : M), m ≠ 0 ∧ φ m = 0 :=
  (hasEigenvalue_zero_tfae φ).out 2 5

open Module.Free in
lemma charpoly_eq_of_equiv {M₁ M₂ : Type*} [AddCommGroup M₁] [AddCommGroup M₂]
    [Module K M₁] [Module K M₂] [Module.Finite K M₁] [Module.Finite K M₂]
    [Module.Free K M₁] [Module.Free K M₂]
    (φ₁ : Module.End K M₁) (φ₂ : Module.End K M₂) (e : M₁ ≃ₗ[K] M₂)
    (H : (e.toLinearMap.comp <| φ₁.comp e.symm.toLinearMap) = φ₂) :
    φ₁.charpoly = φ₂.charpoly := by
  let b₁ := chooseBasis K M₁
  let b₂ := b₁.map e
  rw [← charpoly_toMatrix φ₁ b₁, ← charpoly_toMatrix φ₂ b₂]
  -- extract the following idiom
  dsimp only [Matrix.charpoly, b₂]
  congr 1
  ext i j : 1
  simp [Matrix.charmatrix, toMatrix, Matrix.diagonal, ← H]

open Module.Free in
lemma finrank_maximalGeneralizedEigenspace :
    finrank K (φ.maximalGeneralizedEigenspace 0) = natTrailingDegree (φ.charpoly) := by
  set V := φ.maximalGeneralizedEigenspace 0
  have hV : V = ⨆ (n : ℕ), ker (φ ^ n) := by
    simp [V, Module.End.maximalGeneralizedEigenspace, Module.End.generalizedEigenspace]
  let W := ⨅ (n : ℕ), LinearMap.range (φ ^ n)
  have hVW : IsCompl V W := by
    rw [hV]
    exact LinearMap.isCompl_iSup_ker_pow_iInf_range_pow φ
  have hφV : ∀ x ∈ V, φ x ∈ V := by
    simp only [V, Module.End.mem_maximalGeneralizedEigenspace, zero_smul, sub_zero,
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
  rw [charpoly_eq_of_equiv φ ψ e.symm, charpoly_prodMap]
  swap
  · dsimp only [e, V, W]
    rw [LinearEquiv.symm_symm, LinearEquiv.toLinearMap_symm_comp_eq]
    apply b.ext
    simp only [Submodule.coe_prodEquivOfIsCompl, Basis.prod_apply, coe_inl, coe_inr, coe_comp,
      Function.comp_apply, coprod_apply, Submodule.coeSubtype, map_add, prodMap_apply,
      restrict_coe_apply, Sum.forall, implies_true, and_self, e, V, W, b, ψ, F, G]
  rw [natTrailingDegree_mul (charpoly_monic _).ne_zero (charpoly_monic _).ne_zero]
  have hG : natTrailingDegree (charpoly G) = 0 := by
    apply Polynomial.natTrailingDegree_eq_zero_of_constantCoeff_ne_zero
    apply ((not_hasEigenvalue_zero_tfae G).out 2 5).mpr
    intro x hx
    suffices x.1 ∈ V ⊓ W by
      rw [hVW.inf_eq_bot, Submodule.mem_bot] at this
      rwa [Subtype.ext_iff]
    have hxV : x.1 ∈ V := by
      simp only [Module.End.mem_maximalGeneralizedEigenspace, zero_smul, sub_zero, V]
      use 1
      rw [Subtype.ext_iff] at hx
      rwa [pow_one]
    exact ⟨hxV, x.2⟩
  rw [hG, add_zero, eq_comm]
  apply ((charpoly_nilpotent_tfae F).out 2 3).mp
  simp only [Subtype.forall, Module.End.mem_maximalGeneralizedEigenspace, zero_smul, sub_zero, V, F]
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

namespace LieAlgebra

section CommRing

variable {K R L M : Type*}
variable [Field K] [CommRing R] [Nontrivial R]
variable [LieRing L] [LieAlgebra K L] [LieAlgebra R L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
variable [Module.Finite K L]
variable [Module.Finite R L] [Module.Free R L]
variable [Module.Finite R M] [Module.Free R M]

open FiniteDimensional LieSubalgebra Module.Free Polynomial

local notation "φ" => LieModule.toEndomorphism R L M

variable (R)

lemma engel_zero : engel R (0 : L) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  rw [mem_engel_iff, LieHom.map_zero]
  use 1
  simp only [pow_one, LinearMap.zero_apply]

lemma natTrailingDegree_charpoly_ad_le_finrank_engel (x : L) :
    (ad K L x).charpoly.natTrailingDegree ≤ finrank K (engel K x) := by
  erw [engel, (ad K L x).finrank_maximalGeneralizedEigenspace]

lemma rank_le_finrank_engel (x : L) :
    rank K L ≤ finrank K (engel K x) :=
  (rank_le_natTrailingDegree_charpoly_ad K x).trans
    (natTrailingDegree_charpoly_ad_le_finrank_engel x)

lemma finrank_engel (x : L) :
    finrank K (engel K x) = (ad K L x).charpoly.natTrailingDegree :=
  (ad K L x).finrank_maximalGeneralizedEigenspace

lemma isRegular_iff_finrank_engel_eq_rank (x : L) :
    IsRegular K x ↔ finrank K (engel K x) = rank K L := by
  rw [isRegular_iff_natTrailingDegree_charpoly_eq_rank, finrank_engel]

variable {R}

namespace engel_le_engel

variable (x y : L)

variable (R M)

open LieModule LinearMap

noncomputable
def lieCharpoly₁ : Polynomial R[X] :=
  letI bL := chooseBasis R L
  letI bM := chooseBasis R M
  (LinearMap.polyCharpoly (toEndomorphism R L M).toLinearMap bL).map <| RingHomClass.toRingHom <|
    MvPolynomial.aeval fun i ↦ C (bL.repr y i) * X + C (bL.repr x i)

lemma lieCharpoly₁_monic : (lieCharpoly₁ R M x y).Monic :=
  (polyCharpoly_monic _ _).map _

lemma lieCharpoly₁_natDegree : (lieCharpoly₁ R M x y).natDegree = finrank R M := by
    rw [lieCharpoly₁, (polyCharpoly_monic _ _).natDegree_map, polyCharpoly_natDegree,
      finrank_eq_card_chooseBasisIndex]

lemma lieCharpoly₁_map_eval (r : R) :
    (lieCharpoly₁ R M x y).map (evalRingHom r) = (φ (r • y + x)).charpoly := by
  rw [lieCharpoly₁, map_map]
  -- TODO: rename `polyCharpoly_coeff_map`, since the `coeff` shouldn't be there
  erw [← polyCharpoly_coeff_map (LieHom.toLinearMap φ) (chooseBasis R L) (r • y + x)]
  congr 1
  apply MvPolynomial.ringHom_ext
  · intro;
    simp? [algebraMap_apply] says
      simp only [RingHom.coe_comp, coe_evalRingHom, RingHom.coe_coe,
        Function.comp_apply, MvPolynomial.aeval_C, algebraMap_apply, Algebra.id.map_eq_id,
        RingHom.id_apply, eval_C, map_add, map_smul, Finsupp.coe_add, Finsupp.coe_smul,
        MvPolynomial.eval_C]
  · intro;
    simp? [mul_comm r] says
      simp only [RingHom.coe_comp, coe_evalRingHom, RingHom.coe_coe,
        Function.comp_apply, MvPolynomial.aeval_X, eval_add, eval_mul, eval_C, eval_X, map_add,
        map_smul, Finsupp.coe_add, Finsupp.coe_smul, MvPolynomial.eval_X, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul, mul_comm r]

lemma lieCharpoly₁_coeff_natDegree (i j : ℕ) (hij : i + j = finrank R M) :
    ((lieCharpoly₁ R M x y).coeff i).natDegree ≤ j := by
  -- rw [finrank_eq_card_chooseBasisIndex] at hij
  classical
  have := polyCharpoly_coeff_isHomogeneous (toEndomorphism R L M).toLinearMap (chooseBasis R L) _ _ hij
  rw [← mul_one j, lieCharpoly₁, coeff_map]
  apply MvPolynomial.aeval_natDegree_le _ this.totalDegree_le _ _
  intro k
  apply Polynomial.natDegree_add_le_of_degree_le
  · apply (Polynomial.natDegree_C_mul_le _ _).trans
    simp only [natDegree_X, le_rfl]
  · simp only [natDegree_C, zero_le]

end engel_le_engel

end CommRing

section Field

variable {K L : Type*}
variable [Field K] [LieRing L] [LieAlgebra K L] [Module.Finite K L]

open FiniteDimensional LieSubalgebra Module.Free Polynomial

open Cardinal LieModule LieSubalgebra Polynomial engel_le_engel in
lemma engel_le_engel (hLK : finrank K L ≤ #K)
    (U : LieSubalgebra K L) (x : L) (hx : x ∈ U) (hUx : U ≤ engel K x)
    (hmin : ∀ y : L, y ∈ U → engel K y ≤ engel K x → engel K y = engel K x)
    (y : L) (hy : y ∈ U) :
    engel K x ≤ engel K y := by
  let E : LieSubmodule K U L :=
  { engel K x with
    lie_mem := by rintro ⟨u, hu⟩ y hy; exact (engel K x).lie_mem (hUx hu) hy }
  obtain rfl|hx₀ := eq_or_ne x 0
  · simp only [engel_zero] at hmin ⊢
    rw [hmin y hy le_top]
  let Q := L ⧸ E
  let r := finrank K E
  obtain hr|hr : r = finrank K L ∨ r < finrank K L := (Submodule.finrank_le _).eq_or_lt
  · rw [hmin y hy]
    have : engel K x = ⊤ := by
      apply LieSubalgebra.to_submodule_injective
      apply eq_of_le_of_finrank_le le_top _
      dsimp only [r] at hr
      simp_rw [finrank_top, hr, le_refl]
    rw [this]
    exact le_top
  let χ : U → Polynomial (K[X]) := fun u₁ ↦ lieCharpoly₁ K E ⟨x, hx⟩ u₁
  let ψ : U → Polynomial (K[X]) := fun u₁ ↦ lieCharpoly₁ K Q ⟨x, hx⟩ u₁
  suffices ∀ u, χ u = X ^ r by -- sorry
    specialize this (⟨y, hy⟩ - ⟨x, hx⟩)
    apply_fun (fun p ↦ p.map (evalRingHom 1)) at this
    simp only [lieCharpoly₁_map_eval, coe_bracket_of_module, one_smul, sub_add_cancel,
      Polynomial.map_pow, map_X, LinearMap.charpoly_eq_X_pow_iff, Subtype.ext_iff,
      LieSubmodule.coe_toEndomorphism_pow, toEndomorphism_mk, χ, r] at this
    intro z hz
    obtain ⟨n, hn⟩ := this ⟨z, hz⟩
    rw [mem_engel_iff]
    use n
    simpa only [ZeroMemClass.coe_zero] using hn
  suffices ∀ u, ∀ i < r, (χ u).coeff i = 0 by -- sorry
    intro u
    specialize this u
    ext i : 1
    obtain hi|rfl|hi := lt_trichotomy i r
    · rw [this i hi, coeff_X_pow, if_neg hi.ne]
    · simp_rw [coeff_X_pow, if_true, r, ← lieCharpoly₁_natDegree K E ⟨x, hx⟩ u]
      have := (lieCharpoly₁_monic K E ⟨x, hx⟩ u).leadingCoeff
      rwa [leadingCoeff] at this
    · rw [coeff_eq_zero_of_natDegree_lt, coeff_X_pow, if_neg hi.ne']
      rwa [lieCharpoly₁_natDegree K E ⟨x, hx⟩ u]
  intro u i hi
  obtain rfl|hi0 := eq_or_ne i 0
  · -- sorry
    apply eq_zero_of_forall_eval_zero_of_natDegree_lt_card _ _ ?deg
    case deg =>
      apply lt_of_lt_of_le _ hLK
      rw [Nat.cast_lt]
      apply lt_of_le_of_lt _ hr
      apply lieCharpoly₁_coeff_natDegree _ _ _ _ 0 r (zero_add r)
    intro α
    -- extract the following idiom, it is also used in the proof of `hψ` below, and more
    rw [← coe_evalRingHom, ← coeff_map, lieCharpoly₁_map_eval,
      ← constantCoeff_apply, LinearMap.charpoly_constantCoeff_eq_zero_iff]
    let z := α • u + ⟨x, hx⟩
    obtain hz₀|hz₀ := eq_or_ne z 0
    · refine ⟨⟨x, self_mem_engel K x⟩, ?_, ?_⟩
      · simpa only [coe_bracket_of_module, ne_eq, Submodule.mk_eq_zero] using hx₀
      · dsimp only [z] at hz₀
        simp only [coe_bracket_of_module, hz₀, LieHom.map_zero, LinearMap.zero_apply]
    refine ⟨⟨z, hUx z.2⟩, ?_, ?_⟩
    · simpa only [coe_bracket_of_module, ne_eq, Submodule.mk_eq_zero, Subtype.ext_iff] using hz₀
    · show ⁅z, _⁆ = (0 : E)
      ext
      exact lie_self z.1
  have hψ : ∀ u, constantCoeff (ψ u) ≠ 0 := by -- sorry
    intro u H
    obtain ⟨z, hz0, hxz⟩ : ∃ z : L ⧸ E, z ≠ 0 ∧ ⁅(⟨x, hx⟩ : U), z⁆ = 0 := by
      apply_fun (evalRingHom 0) at H
      rw [constantCoeff_apply, ← coeff_map, lieCharpoly₁_map_eval,
        ← constantCoeff_apply, map_zero, LinearMap.charpoly_constantCoeff_eq_zero_iff] at H
      simpa only [coe_bracket_of_module, ne_eq, zero_smul, zero_add,
        LieModule.toEndomorphism_apply_apply] using H
    apply hz0
    obtain ⟨z, rfl⟩ := LieSubmodule.Quotient.surjective_mk' E z
    have : ⁅(⟨x, hx⟩ : U), z⁆ ∈ E := by rwa [← LieSubmodule.Quotient.mk_eq_zero']
    simp [mem_engel_iff, E] at this ⊢
    obtain ⟨n, hn⟩ := this
    use n+1
    rwa [pow_succ]
  obtain ⟨s, hs, hsψ⟩ : ∃ s : Finset K, r ≤ s.card ∧ ∀ α ∈ s, (constantCoeff (ψ u)).eval α ≠ 0 := by
    specialize hψ u
    classical
    let t := (constantCoeff (ψ u)).roots.toFinset
    have ht : t.card ≤ finrank K L - r := by
      refine (Multiset.toFinset_card_le _).trans ?_
      refine (card_roots' _).trans ?_
      rw [constantCoeff_apply]
      apply lieCharpoly₁_coeff_natDegree
      suffices finrank K Q + r = finrank K L by rw [← this, zero_add, Nat.add_sub_cancel]
      apply Submodule.finrank_quotient_add_finrank
    obtain ⟨s, hs⟩ := exists_finset_le_card K _ hLK
    use s \ t
    refine ⟨?_, ?_⟩
    · refine le_trans ?_ (Finset.le_card_sdiff _ _)
      omega
    · intro α hα
      simp only [Finset.mem_sdiff, Multiset.mem_toFinset, mem_roots', IsRoot.def, not_and, t] at hα
      exact hα.2 hψ
  -- sorry -- the proof below works
  have hcard : natDegree (coeff (χ u) i) < s.card := by
    apply lt_of_le_of_lt (lieCharpoly₁_coeff_natDegree _ _ _ _ i (r - i) _)
    · omega
    · dsimp only [r] at hi ⊢
      -- omega fails???
      rw [Nat.add_sub_cancel' hi.le]
  apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ s _ hcard
  intro α hα
  let y := α • u + ⟨x, hx⟩
  suffices engel K (y : L) ≤ engel K x by -- sorry
    rw [← coe_evalRingHom, ← coeff_map, lieCharpoly₁_map_eval,
      (LinearMap.charpoly_eq_X_pow_iff _).mpr, coeff_X_pow, if_neg hi.ne]
    specialize hmin y y.2 this
    intro z
    simpa only [mem_engel_iff, Subtype.ext_iff, LieSubmodule.coe_toEndomorphism_pow]
      using hmin.ge z.2
  intro z hz
  show z ∈ E
  have hz' : ∃ n : ℕ, ((toEndomorphism K U Q) y ^ n) (LieSubmodule.Quotient.mk' E z) = 0 := by
    rw [mem_engel_iff] at hz
    obtain ⟨n, hn⟩ := hz
    use n
    apply_fun LieSubmodule.Quotient.mk' E at hn
    rw [LieModuleHom.map_zero] at hn
    rw [← hn]
    clear hn
    induction n with
    | zero => simp only [Nat.zero_eq, pow_zero, LinearMap.one_apply]
    | succ n ih => rw [pow_succ', pow_succ', LinearMap.mul_apply, ih]; rfl
  classical
  set n := Nat.find hz' with hn'
  have hn := Nat.find_spec hz'
  rw [← hn'] at hn
  rw [← LieSubmodule.Quotient.mk_eq_zero']
  obtain hn₀|⟨k, hk⟩ : n = 0 ∨ ∃ k, n = k + 1 := by cases n <;> simp
  · simpa only [hn₀, pow_zero, LinearMap.one_apply] using hn
  specialize hsψ α hα
  rw [← coe_evalRingHom, constantCoeff_apply, ← coeff_map, lieCharpoly₁_map_eval,
    ← constantCoeff_apply, ne_eq, LinearMap.charpoly_constantCoeff_eq_zero_iff] at hsψ
  contrapose! hsψ
  use ((LieModule.toEndomorphism K U Q) y ^ k) (LieSubmodule.Quotient.mk' E z)
  refine ⟨?_, ?_⟩
  · apply Nat.find_min hz'; omega
  · rw [← hn, hk, pow_succ', LinearMap.mul_apply]

open Cardinal in
lemma exists_IsCartanSubalgebra_of_finrank_le_card (h : finrank K L ≤ #K) :
    ∃ H : LieSubalgebra K L, IsCartanSubalgebra H := by
  obtain ⟨x, hx⟩ := exists_isRegular_of_finrank_le_card K L h
  use engel K x
  refine ⟨?_, normalizer_engel _ _⟩
  apply isNilpotent_of_forall_le_engel
  apply engel_le_engel h _ x (self_mem_engel _ _) le_rfl
  rintro y - hyx
  suffices finrank K (engel K x) ≤ finrank K (engel K y) by
    apply LieSubalgebra.to_submodule_injective
    apply eq_of_le_of_finrank_le hyx this
  rw [(isRegular_iff_finrank_engel_eq_rank x).mp hx]
  apply rank_le_finrank_engel

lemma exists_IsCartanSubalgebra [Infinite K] :
    ∃ H : LieSubalgebra K L, IsCartanSubalgebra H := by
  apply exists_IsCartanSubalgebra_of_finrank_le_card
  exact (Cardinal.nat_lt_aleph0 _).le.trans <| Cardinal.infinite_iff.mp ‹Infinite K›

end Field

end LieAlgebra
