/-
Copyright (c) 2024 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import Mathlib.Algebra.Lie.EngelSubalgebra
import Mathlib.Algebra.Lie.CartanSubalgebra
import Mathlib.Algebra.Lie.Rank
import Mathlib.LinearAlgebra.Eigenspace.Minpoly


-- move this
namespace LinearMap

variable {K M : Type*}
variable [Field K] [IsDomain K] [AddCommGroup M] [Module K M]
variable [Module.Finite K M] [Module.Free K M]
variable (φ : Module.End K M)

open FiniteDimensional Polynomial

lemma finrank_maximalGeneralizedEigenspace :
    finrank K (φ.maximalGeneralizedEigenspace 0) = natTrailingDegree (φ.charpoly) := by
  sorry

lemma charpoly_eq_X_pow_iff :
    φ.charpoly = X ^ finrank K M ↔ ∀ m : M, ∃ (n : ℕ), (φ ^ n) m = 0 := by
  constructor
  · intro h m
    use finrank K M
    suffices φ ^ finrank K M = 0 by simp only [this, LinearMap.zero_apply]
    simpa only [h, map_pow, aeval_X] using φ.aeval_self_charpoly
  · intro h
    rw [← sub_eq_zero]
    apply IsNilpotent.eq_zero
    rw [finrank_eq_card_chooseBasisIndex]
    apply Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent
    sorry

lemma charpoly_constantCoeff_eq_zero_iff :
    constantCoeff φ.charpoly = 0 ↔ ∃ (m : M), m ≠ 0 ∧ φ m = 0 := by
  -- have := Module.End.hasEigenvalue_iff_isRoot (f := φ) 0
  sorry

end LinearMap

namespace LieAlgebra

section CommRing

variable {R L M : Type*}
variable [CommRing R] [Nontrivial R] [LieRing L] [LieAlgebra R L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
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

lemma rank_le_finrank_engel (x : L) :
    rank R L ≤ finrank R (engel R x) := by
  sorry

lemma isRegular_iff_finrank_engel_eq_rank (x : L) :
    IsRegular R x ↔ finrank R (engel R x) = rank R L := by
  rw [LieAlgebra.isRegular_iff_coeff_rank_ne_zero]
  refine ⟨?_, ?_⟩
  · intro h
    apply le_antisymm _ (rank_le_finrank_engel R x)
    sorry
  · intro h
    rw [← h]
    simp only [lieCharpoly_eval, ne_eq]
    sorry

variable {R}

namespace engel_le_engel

variable (x y : L)

variable (R M)

noncomputable
def lieCharpoly₁ : Polynomial R[X] :=
  letI bL := chooseBasis R L
  letI bM := chooseBasis R M
  (lieCharpoly bL bM).map <| RingHomClass.toRingHom <|
    MvPolynomial.aeval fun i ↦ C (bL.repr y i) * X + C (bL.repr x i)

lemma lieCharpoly₁_monic : (lieCharpoly₁ R M x y).Monic :=
  (lieCharpoly_monic _ _).map _

lemma lieCharpoly₁_natDegree : (lieCharpoly₁ R M x y).natDegree = finrank R M := by
    rw [lieCharpoly₁, (lieCharpoly_monic _ _).natDegree_map, lieCharpoly_natDegree,
      finrank_eq_card_chooseBasisIndex]

lemma lieCharpoly₁_map_eval (r : R) :
    (lieCharpoly₁ R M x y).map (evalRingHom r) = (φ (r • y + x)).charpoly := by
  rw [lieCharpoly₁, map_map, ← lieCharpoly_map (chooseBasis R L) (chooseBasis R M)]
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
    ((lieCharpoly₁ R M x y).coeff i).natDegree = j := by
  sorry

end engel_le_engel

-- move
open Cardinal in
lemma eq_zero_of_forall_eval_zero_of_natDegree_lt_card [IsDomain R] (f : R[X])
    (hf : ∀ r, f.eval r = 0) (hfR : f.natDegree < #R) :
    f = 0 := by
  contrapose! hf
  exact exists_eval_ne_zero_of_natDegree_lt_card f hf hfR

end CommRing

open Cardinal in
lemma exists_subset_le_card (α : Type*) (n : ℕ) (h : n ≤ #α) :
    ∃ s : Finset α, n ≤ s.card := by
  obtain hα|hα := finite_or_infinite α
  · let hα := Fintype.ofFinite α
    use Finset.univ
    simpa only [ge_iff_le, mk_fintype, Nat.cast_le] using h
  · obtain ⟨s, hs⟩ := Infinite.exists_subset_card_eq α n
    exact ⟨s, hs.ge⟩

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
      simp only [finrank_top, hr, le_refl]
    rw [this]
    exact le_top
  let χ : U → Polynomial (K[X]) := fun u₁ ↦ lieCharpoly₁ K E ⟨x, hx⟩ u₁
  let ψ : U → Polynomial (K[X]) := fun u₁ ↦ lieCharpoly₁ K Q ⟨x, hx⟩ u₁
  suffices ∀ u, χ u = X ^ r by sorry
    -- specialize this (⟨y, hy⟩ - ⟨x, hx⟩)
    -- apply_fun (fun p ↦ p.map (evalRingHom 1)) at this
    -- simp only [lieCharpoly₁_map_eval, coe_bracket_of_module, one_smul, sub_add_cancel,
    --   Polynomial.map_pow, map_X, charpoly_eq_X_pow_iff, Subtype.ext_iff,
    --   LieSubmodule.coe_toEndomorphism_pow, toEndomorphism_mk] at this
    -- intro z hz
    -- obtain ⟨n, hn⟩ := this ⟨z, hz⟩
    -- rw [mem_engel_iff]
    -- use n
    -- simpa only [ZeroMemClass.coe_zero] using hn
  suffices ∀ u, ∀ i < r, (χ u).coeff i = 0 by sorry
    -- intro u
    -- specialize this u
    -- ext i : 1
    -- obtain hi|rfl|hi := lt_trichotomy i r
    -- · rw [this i hi, coeff_X_pow, if_neg hi.ne]
    -- · simp only [coeff_X_pow, ← lieCharpoly₁_natDegree K E ⟨x, hx⟩ u, if_true]
    --   have := (lieCharpoly₁_monic K E ⟨x, hx⟩ u).leadingCoeff
    --   rwa [leadingCoeff] at this
    -- · rw [coeff_eq_zero_of_natDegree_lt, coeff_X_pow, if_neg hi.ne']
    --   rwa [lieCharpoly₁_natDegree K E ⟨x, hx⟩ u]
  intro u i hi
  obtain rfl|hi0 := eq_or_ne i 0
  · sorry
    -- apply eq_zero_of_forall_eval_zero_of_natDegree_lt_card _ _ ?deg
    -- case deg =>
    --   rw [lieCharpoly₁_coeff_natDegree _ _ _ _ 0 r (zero_add r)]
    --   apply lt_of_lt_of_le _ hLK
    --   rwa [Nat.cast_lt]
    -- intro α
    -- -- extract the following idiom, it is also used in the proof of `hψ` below, and more
    -- rw [← coe_evalRingHom, ← coeff_map, lieCharpoly₁_map_eval,
    --   ← constantCoeff_apply, charpoly_constantCoeff_eq_zero_iff]
    -- let z := α • u + ⟨x, hx⟩
    -- obtain hz₀|hz₀ := eq_or_ne z 0
    -- · refine ⟨⟨x, self_mem_engel K x⟩, ?_, ?_⟩
    --   · simpa only [coe_bracket_of_module, ne_eq, Submodule.mk_eq_zero] using hx₀
    --   · dsimp only at hz₀
    --     simp only [coe_bracket_of_module, hz₀, LieHom.map_zero, LinearMap.zero_apply]
    -- refine ⟨⟨z, hUx z.2⟩, ?_, ?_⟩
    -- · simpa only [coe_bracket_of_module, ne_eq, Submodule.mk_eq_zero, Subtype.ext_iff] using hz₀
    -- · show ⁅z, _⁆ = (0 : E)
    --   ext
    --   exact lie_self z.1
  have hψ : ∀ u, constantCoeff (ψ u) ≠ 0 := by sorry
    -- intro u H
    -- obtain ⟨z, hz0, hxz⟩ : ∃ z : L ⧸ E, z ≠ 0 ∧ ⁅(⟨x, hx⟩ : U), z⁆ = 0 := by
    --   apply_fun (evalRingHom 0) at H
    --   rw [constantCoeff_apply, ← coeff_map, lieCharpoly₁_map_eval,
    --     ← constantCoeff_apply, map_zero, charpoly_constantCoeff_eq_zero_iff] at H
    --   simpa only [coe_bracket_of_module, ne_eq, zero_smul, zero_add,
    --     LieModule.toEndomorphism_apply_apply] using H
    -- apply hz0
    -- obtain ⟨z, rfl⟩ := LieSubmodule.Quotient.surjective_mk' E z
    -- have : ⁅(⟨x, hx⟩ : U), z⁆ ∈ E := by rwa [← LieSubmodule.Quotient.mk_eq_zero']
    -- simp [mem_engel_iff] at this ⊢
    -- obtain ⟨n, hn⟩ := this
    -- use n+1
    -- rwa [pow_succ']
  obtain ⟨s, hs, hsψ⟩ : ∃ s : Finset K, r ≤ s.card ∧ ∀ α ∈ s, (constantCoeff (ψ u)).eval α ≠ 0 := by
    specialize hψ u
    classical
    let t := (constantCoeff (ψ u)).roots.toFinset
    have ht : t.card ≤ finrank K L - r := by
      refine (Multiset.toFinset_card_le _).trans ?_
      refine (card_roots' _).trans ?_
      rw [constantCoeff_apply, lieCharpoly₁_coeff_natDegree _ _ _ _ 0 (finrank K L - r)]
      suffices finrank K Q + r = finrank K L by omega
      apply Submodule.finrank_quotient_add_finrank
    obtain ⟨s, hs⟩ := exists_subset_le_card K _ hLK
    use s \ t
    refine ⟨?_, ?_⟩
    · refine le_trans ?_ (Finset.le_card_sdiff _ _)
      omega
    · intro α hα
      simp only [Finset.mem_sdiff, Multiset.mem_toFinset, mem_roots', IsRoot.def, not_and] at hα
      exact hα.2 hψ
  sorry -- the proof below works
  -- have hcard : natDegree (coeff (χ u) i) < s.card := by
  --   rw [lieCharpoly₁_coeff_natDegree _ _ _ _ i (r - i)] <;> omega
  -- apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ s _ hcard
  -- intro α hα
  -- let y := α • u + ⟨x, hx⟩
  -- suffices engel K (y : L) ≤ engel K x by sorry
  --   -- rw [← coe_evalRingHom, ← coeff_map, lieCharpoly₁_map_eval, (charpoly_eq_X_pow_iff _ _ _).mpr,
  --   --   coeff_X_pow, if_neg hi.ne]
  --   -- specialize hmin y y.2 this
  --   -- intro z
  --   -- simpa only [mem_engel_iff, Subtype.ext_iff, LieSubmodule.coe_toEndomorphism_pow]
  --   --   using hmin.ge z.2
  -- intro z hz
  -- show z ∈ E
  -- have hz' : ∃ n : ℕ, ((toEndomorphism K U Q) y ^ n) (LieSubmodule.Quotient.mk' E z) = 0 := by
  --   rw [mem_engel_iff] at hz
  --   obtain ⟨n, hn⟩ := hz
  --   use n
  --   apply_fun LieSubmodule.Quotient.mk' E at hn
  --   rw [LieModuleHom.map_zero] at hn
  --   rw [← hn]
  --   clear hn
  --   induction n with
  --   | zero => simp only [Nat.zero_eq, pow_zero, LinearMap.one_apply]
  --   | succ n ih => rw [pow_succ, pow_succ, LinearMap.mul_apply, ih]; rfl
  -- classical
  -- set n := Nat.find hz' with hn'
  -- have hn := Nat.find_spec hz'
  -- rw [← hn'] at hn
  -- rw [← LieSubmodule.Quotient.mk_eq_zero']
  -- obtain hn₀|⟨k, hk⟩ : n = 0 ∨ ∃ k, n = k + 1 := by cases n <;> simp
  -- · simpa only [hn₀, pow_zero, LinearMap.one_apply] using hn
  -- specialize hsψ α hα
  -- rw [← coe_evalRingHom, constantCoeff_apply, ← coeff_map, lieCharpoly₁_map_eval,
  --   ← constantCoeff_apply, ne_eq, charpoly_constantCoeff_eq_zero_iff] at hsψ
  -- contrapose! hsψ
  -- use ((LieModule.toEndomorphism K U Q) y ^ k) (LieSubmodule.Quotient.mk' E z)
  -- refine ⟨?_, ?_⟩
  -- · apply Nat.find_min hz'; omega
  -- · rw [← hn, hk, pow_succ, LinearMap.mul_apply]

lemma foo {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V]
    (W₁ W₂ : Submodule K V) (h1 : W₁ ≤ W₂) (h2 : finrank K W₂ ≤ finrank K W₁) :
    W₁ = W₂ := by
  exact eq_of_le_of_finrank_le h1 h2

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
  rw [(isRegular_iff_finrank_engel_eq_rank K x).mp hx]
  apply rank_le_finrank_engel

lemma exists_IsCartanSubalgebra [Infinite K] :
    ∃ H : LieSubalgebra K L, IsCartanSubalgebra H := by
  apply exists_IsCartanSubalgebra_of_finrank_le_card
  exact (Cardinal.nat_lt_aleph0 _).le.trans <| Cardinal.infinite_iff.mp ‹Infinite K›

end Field

end LieAlgebra
