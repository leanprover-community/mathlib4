/-
Copyright (c) 2024 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import Mathlib.Algebra.Lie.EngelSubalgebra
import Mathlib.Algebra.Lie.CartanSubalgebra
import Mathlib.Algebra.Lie.Rank
import Mathlib.LinearAlgebra.Eigenspace.Zero

/-!
# Existence of Cartan subalgebras

In this file we prove existence of Cartan subalgebras in finite-dimensional Lie algebras,
following [barnes1967].

## Main results

* `exists_IsCartanSubalgebra_of_finrank_le_card`:
  A Lie algebra `L` over a field `K` has a Cartan subalgebra,
  provided that the dimension of `L` over `K` is less than or equal to the cardinality of `K`.
* `exists_IsCartanSubalgebra`:
  A finite-dimensional Lie algebra `L` over an infinite field `K` has a Cartan subalgebra.

## References

* [barnes1967]: "On Cartan subalgebras of Lie algebras" by D.W. Barnes.

-/

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

variable (K)

lemma finrank_engel (x : L) :
    finrank K (engel K x) = (ad K L x).charpoly.natTrailingDegree :=
  (ad K L x).finrank_maximalGeneralizedEigenspace

lemma rank_le_finrank_engel (x : L) :
    rank K L ≤ finrank K (engel K x) :=
  (rank_le_natTrailingDegree_charpoly_ad K x).trans
    (finrank_engel K x).ge

lemma isRegular_iff_finrank_engel_eq_rank (x : L) :
    IsRegular K x ↔ finrank K (engel K x) = rank K L := by
  rw [isRegular_iff_natTrailingDegree_charpoly_eq_rank, finrank_engel]

variable {K}

namespace engel_le_engel

/-!
## Implementation details for the proof of `LieAlgebra.engel_le_engel`

We follow the proof strategy of Lemma 2 in [barnes1967].
-/

variable (x y : L)

variable (R M)

open LieModule LinearMap

local notation "φ" => LieModule.toEndomorphism R L M

noncomputable
def lieCharpoly₁ : Polynomial R[X] :=
  letI bL := chooseBasis R L
  letI bM := chooseBasis R M
  (LinearMap.polyCharpoly (LieHom.toLinearMap φ) bL).map <| RingHomClass.toRingHom <|
    MvPolynomial.aeval fun i ↦ C (bL.repr y i) * X + C (bL.repr x i)

lemma lieCharpoly₁_monic : (lieCharpoly₁ R M x y).Monic :=
  (polyCharpoly_monic _ _).map _

lemma lieCharpoly₁_natDegree : (lieCharpoly₁ R M x y).natDegree = finrank R M := by
    rw [lieCharpoly₁, (polyCharpoly_monic _ _).natDegree_map, polyCharpoly_natDegree,
      finrank_eq_card_chooseBasisIndex]

lemma lieCharpoly₁_map_eval (r : R) :
    (lieCharpoly₁ R M x y).map (evalRingHom r) = (φ (r • y + x)).charpoly := by
  rw [lieCharpoly₁, map_map]
  erw [← polyCharpoly_map_eq_charpoly (LieHom.toLinearMap φ) (chooseBasis R L) (r • y + x)]
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
  rw [(isRegular_iff_finrank_engel_eq_rank K x).mp hx]
  apply rank_le_finrank_engel

lemma exists_IsCartanSubalgebra [Infinite K] :
    ∃ H : LieSubalgebra K L, IsCartanSubalgebra H := by
  apply exists_IsCartanSubalgebra_of_finrank_le_card
  exact (Cardinal.nat_lt_aleph0 _).le.trans <| Cardinal.infinite_iff.mp ‹Infinite K›

end Field

end LieAlgebra
