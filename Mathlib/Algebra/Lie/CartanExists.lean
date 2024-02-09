/-
Copyright (c) 2024 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import Mathlib.Algebra.Lie.EngelSubalgebra
import Mathlib.Algebra.Lie.CartanSubalgebra
import Mathlib.Algebra.Lie.Rank

namespace LieAlgebra

section CommRing

variable {R L M : Type*}
variable [Field R] [LieRing L] [LieAlgebra R L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
variable [Module.Finite R L] [Module.Free R L]
variable [Module.Finite R M] [Module.Free R M]

open FiniteDimensional LieSubalgebra Module.Free Polynomial

local notation "φ" => LieModule.toEndomorphism R L M

lemma isRegular_iff_finrank_engel_eq_rank (x : L) :
    IsRegular R x ↔ finrank R (engel R x) = rank R L := by
  sorry

lemma rank_le_finrank_engel (x : L) :
    rank R L ≤ finrank R (engel R x) := by
  sorry

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

-- generalize and move
lemma charpoly_eq_X_pow_iff :
    (φ x).charpoly = X ^ finrank R M ↔ ∀ m : M, ∃ (n : ℕ), ((φ x) ^ n) m = 0 := by
  constructor
  · intro h m
    use finrank R M
    suffices (φ x) ^ finrank R M = 0 by simp only [this, LinearMap.zero_apply]
    simpa only [h, map_pow, aeval_X] using (φ x).aeval_self_charpoly
  · sorry -- We don't need this direction

-- generalize and move
lemma charpoly_constantCoeff_eq_zero_iff :
    constantCoeff (φ x).charpoly = 0 ↔ ∃ (m : M), m ≠ 0 ∧ (φ x) m = 0 := by
  sorry

lemma lieCharpoly₁_coeff_natDegree (i j : ℕ) (hij : i + j = finrank R M) :
    ((lieCharpoly₁ R M x y).coeff i).natDegree = j := by
  sorry

end engel_le_engel

-- move
open Cardinal in
lemma eq_zero_of_forall_eval_zero_of_natDegree_lt_card (f : R[X])
    (hf : ∀ r, f.eval r = 0) (hfR : f.natDegree < #R) :
    f = 0 := by
  contrapose! hf
  exact exists_eval_ne_zero_of_natDegree_lt_card f hf hfR

end CommRing

section Field

variable {K L : Type*}
variable [Field K] [LieRing L] [LieAlgebra K L] [Module.Finite K L]

open FiniteDimensional LieSubalgebra Module.Free Polynomial

open Cardinal LieSubalgebra Polynomial engel_le_engel in
lemma engel_le_engel (hLK : finrank K L ≤ #K)
    (U : LieSubalgebra K L) (x : L) (hx : x ∈ U) (hUx : U ≤ engel K x)
    (hmin : ∀ y : L, y ∈ U → engel K y ≤ engel K x → engel K y = engel K x)
    (y : L) (hy : y ∈ U) :
    engel K x ≤ engel K y := by
  let E : LieSubmodule K U L :=
  { engel K x with
    lie_mem := by rintro ⟨u, hu⟩ y hy; exact (engel K x).lie_mem (hUx hu) hy }
  obtain hE|hE := subsingleton_or_nontrivial E
  · intro z hz
    obtain rfl : z = 0 := by simpa only [Subtype.ext_iff] using Subsingleton.elim (⟨z, hz⟩ : E) 0
    apply LieSubalgebra.zero_mem
  let Q := L ⧸ E
  let r := finrank K E
  let χ : U → Polynomial (K[X]) := fun u₁ ↦ lieCharpoly₁ K E ⟨x, hx⟩ u₁
  let ψ : U → Polynomial (K[X]) := fun u₁ ↦ lieCharpoly₁ K Q ⟨x, hx⟩ u₁
  suffices ∀ u, χ u = X ^ r by
    specialize this (⟨y, hy⟩ - ⟨x, hx⟩)
    apply_fun (fun p ↦ p.map (evalRingHom 1)) at this
    simp only [lieCharpoly₁_map_eval, coe_bracket_of_module, one_smul, sub_add_cancel,
      Polynomial.map_pow, map_X, charpoly_eq_X_pow_iff, Subtype.ext_iff,
      LieSubmodule.coe_toEndomorphism_pow, toEndomorphism_mk] at this
    intro z hz
    obtain ⟨n, hn⟩ := this ⟨z, hz⟩
    rw [mem_engel_iff]
    use n
    simpa only [ZeroMemClass.coe_zero] using hn
  suffices ∀ u, ∀ i < r, (χ u).coeff i = 0 by
    intro u
    specialize this u
    ext i : 1
    obtain hi|rfl|hi := lt_trichotomy i r
    · rw [this i hi, coeff_X_pow, if_neg hi.ne]
    · simp only [coeff_X_pow, ← lieCharpoly₁_natDegree K E ⟨x, hx⟩ u, if_true]
      have := (lieCharpoly₁_monic K E ⟨x, hx⟩ u).leadingCoeff
      rwa [leadingCoeff] at this
    · rw [coeff_eq_zero_of_natDegree_lt, coeff_X_pow, if_neg hi.ne']
      rwa [lieCharpoly₁_natDegree K E ⟨x, hx⟩ u]
  intro u i hi
  obtain rfl|hi0 := eq_or_ne i 0
  · apply eq_zero_of_forall_eval_zero_of_natDegree_lt_card _ _ ?deg
    case deg =>
      rw [lieCharpoly₁_coeff_natDegree _ _ _ _ 0 r (zero_add r)]
      apply lt_of_lt_of_le _ hLK
      rw [Nat.cast_lt]
      sorry
    intro α
    -- extract the following idiom, it is also used in the proof of `hψ` below
    rw [← coe_evalRingHom, ← coeff_map, lieCharpoly₁_map_eval,
      ← constantCoeff_apply, charpoly_constantCoeff_eq_zero_iff]
    simp only [coe_bracket_of_module, ne_eq, LieHom.map_add, LieHom.map_smul, LinearMap.add_apply,
      LinearMap.smul_apply, Subtype.exists, Submodule.mk_eq_zero, mem_coe_submodule,
      exists_and_left]
    obtain ⟨z, hz⟩ := exists_ne (0 : E)
    have hz' : (z : L) ∈ engel K x := z.2
    rw [mem_engel_iff] at hz'
    classical
    let n := Nat.find hz'
    sorry
  have hψ : ∀ u, constantCoeff (ψ u) ≠ 0 := by
    intro u H
    obtain ⟨z, hz0, hxz⟩ : ∃ z : L ⧸ E, z ≠ 0 ∧ ⁅(⟨x, hx⟩ : U), z⁆ = 0 := by
      apply_fun (evalRingHom 0) at H
      rw [constantCoeff_apply, ← coeff_map, lieCharpoly₁_map_eval,
        ← constantCoeff_apply, map_zero, charpoly_constantCoeff_eq_zero_iff] at H
      simpa only [coe_bracket_of_module, ne_eq, zero_smul, zero_add,
        LieModule.toEndomorphism_apply_apply] using H
    apply hz0
    obtain ⟨z, rfl⟩ := LieSubmodule.Quotient.surjective_mk' E z
    have : ⁅(⟨x, hx⟩ : U), z⁆ ∈ E := by rwa [← LieSubmodule.Quotient.mk_eq_zero']
    simp [mem_engel_iff] at this ⊢
    obtain ⟨n, hn⟩ := this
    use n+1
    rwa [pow_succ']
  sorry

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
  rw [(isRegular_iff_finrank_engel_eq_rank x).mp hx]
  apply rank_le_finrank_engel

lemma exists_IsCartanSubalgebra [Infinite K] :
    ∃ H : LieSubalgebra K L, IsCartanSubalgebra H := by
  apply exists_IsCartanSubalgebra_of_finrank_le_card
  exact (Cardinal.nat_lt_aleph0 _).le.trans <| Cardinal.infinite_iff.mp ‹Infinite K›

end Field

end LieAlgebra
