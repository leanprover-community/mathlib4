/-
Copyright (c) 2025 Sihan Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Sihan Su, Wan Lin, Xiaoyang Su
-/
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Data.List.Indexes
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
/-!
# Noether Normalizaton
This file contains a proof of Noether normalization lemma by Nagata.

## Main Results
Let `A` be a finitely generated algebra over a field `k`.
Then there exists natural number `r` and an injective homomorphism
from `k[X_1, X_2, ..., X_r]` to `A` such that `A` is integral over `k[X_1, X_2, ..., X_r]`.

## Reference
* <https://stacks.math.columbia.edu/tag/00OW>

-/
open Polynomial MvPolynomial Ideal BigOperators Nat RingHom List

variable {k : Type*} [Field k] {n : ℕ} (f : MvPolynomial (Fin (n + 1)) k)
variable (v w : Fin (n + 1) →₀ ℕ)

namespace NoetherNormalization

/-- Suppose `f` is a nonzero polynomial of `n+1` variables : `X_0,...,X_n`.
`up` is a number which is big enough. -/
local notation3 "up" => 2 + f.totalDegree

private lemma up_lt (hv : v ∈ f.support) (i : Fin (n + 1)) : v i < up := by
  have := (monomial_le_degreeOf i hv).trans <| degreeOf_le_totalDegree f i
  omega

/-- `r` maps i to `up ^ i`-/
local notation3 "r" => fun (i : Fin (n + 1)) ↦ up ^ i.1

/-- We construct an algebra map `T1` which maps `X_i` into `X_i + X_0 ^ r_i` when `i ≠ 0`,
and maps `f` into some monic polynomial (regarded as a polynomial of `X_0`).-/
noncomputable abbrev T1 (c : k) :
    MvPolynomial (Fin (n + 1)) k →ₐ[k] MvPolynomial (Fin (n + 1)) k :=
  aeval fun i ↦ if i = 0 then X 0 else X i + c • X 0 ^ r i

private lemma inv_pair (c : k) :
    (T1 f c).comp (T1 f (-c)) = AlgHom.id _ _ := by
  rw [comp_aeval, ← MvPolynomial.aeval_X_left]
  congr
  ext i v
  cases' i using Fin.cases with d
  · simp only [if_pos, MvPolynomial.aeval_X]
  · simp only [Fin.succ_ne_zero, ite_false, map_add, map_smul, map_pow,
      MvPolynomial.aeval_X, if_pos, add_assoc, ← add_smul c, add_neg_cancel, zero_smul, add_zero]

/-- `T1` leads to an algebra equiv `T`.-/
private noncomputable abbrev T := AlgEquiv.ofAlgHom (T1 f 1) (T1 f (-1))
  (inv_pair f 1) (by convert (inv_pair f (-1)); exact (InvolutiveNeg.neg_neg 1).symm)

variable {f v} in
private lemma lt (vlt : ∀ i, v i < up) : ∀ l ∈ ofFn v, l < up := by
  intro l h
  rw [mem_ofFn, Set.mem_range] at h
  obtain ⟨y, hy⟩ := h
  exact hy ▸ vlt y

private lemma r_ne (vlt : ∀ i, v i < up) (wlt : ∀ i, w i < up) (neq : v ≠ w) :
    ∑ x : Fin (n + 1), r x * v x ≠ ∑ x : Fin (n + 1), r x * w x := by
  intro h
  have : ofFn v = ofFn w := by
    apply list_eq_of_ofDigits_eq (Nat.lt_add_right f.totalDegree one_lt_two)
      (by simp) (lt vlt) (lt wlt)
    simp only [ofDigits_eq_sum_mapIdx, mapIdx_eq_ofFn, get_ofFn, length_ofFn,
      Fin.coe_cast, mul_comm]
    simpa only [sum_ofFn] using h
  exact neq <| Finsupp.ext <| congrFun <| ofFn_inj.mp this

private lemma T_monomial {a : k} (ha : a ≠ 0) : ((T f) (monomial v a)).degreeOf 0 =
    ∑ i : Fin (n + 1), (r i) * v i := by
  rw [← natDegree_finSuccEquiv, monomial_eq, Finsupp.prod_pow v fun a ↦ X a]
  simp only [Fin.prod_univ_succ, Fin.sum_univ_succ, _root_.map_mul, map_prod, map_pow,
    AlgEquiv.ofAlgHom_apply, MvPolynomial.aeval_C, MvPolynomial.aeval_X, if_pos, Fin.succ_ne_zero,
    ite_false, one_smul, map_add, finSuccEquiv_X_zero, finSuccEquiv_X_succ, algebraMap_eq]
  have h1 : (finSuccEquiv k n) (C a) ≠ 0 :=
    (map_ne_zero_iff _ (AlgEquiv.injective _)).mpr ((map_ne_zero_iff _ (C_injective _ _)).mpr ha)
  have h2 : Polynomial.X (R := (MvPolynomial (Fin n) k))^ v 0 ≠ 0 := pow_ne_zero (v 0) X_ne_zero
  have h3 : ∀ i : Fin n, (Polynomial.C (X (R := k) i) + Polynomial.X ^ r i.succ)
    ^ v i.succ ≠ 0 := by
    intro i
    apply pow_ne_zero (v i.succ) (leadingCoeff_ne_zero.mp ?_)
    rw [add_comm, leadingCoeff_X_pow_add_C]
    · exact one_ne_zero
    · simp only [add_pos_iff, ofNat_pos, true_or, pow_pos]
  rw [natDegree_mul h1 (mul_ne_zero h2 (Finset.prod_ne_zero_iff.mpr (fun i _ ↦ h3 i))),
    natDegree_mul h2 (Finset.prod_ne_zero_iff.mpr (fun i _ ↦ h3 i)),
    natDegree_prod _  _ (fun i _ ↦ h3 i), natDegree_finSuccEquiv, degreeOf_C]
  simp only [natDegree_pow, zero_add]
  have e1 : r 0 = 1 := by simp
  rw [natDegree_X, mul_one, Fin.val_zero, pow_zero, one_mul, add_right_inj]
  apply Finset.sum_congr rfl
  intro i _
  rw [add_comm (Polynomial.C (X i)), natDegree_X_pow_add_C, mul_comm]

private lemma T_degree (hv : v ∈ f.support) (hw : w ∈ f.support) (neq : v ≠ w) :
    (T f <| monomial v <| coeff v f).degreeOf 0 ≠
    (T f <| monomial w <| coeff w f).degreeOf 0 := by
  rw [T_monomial _ _ <| mem_support_iff.mp hv, T_monomial _ _ <| mem_support_iff.mp hw]
  exact r_ne f v w (up_lt f v hv) (up_lt f w hw) neq

private lemma T_coeff :
    (finSuccEquiv k n ((T f) ((monomial v) (coeff v f)))).leadingCoeff =
    algebraMap k _ (coeff v f) := by
  rw [monomial_eq, Finsupp.prod_fintype]
  · simp only [_root_.map_mul, map_prod, leadingCoeff_mul, leadingCoeff_prod]
    rw [AlgEquiv.ofAlgHom_apply, algHom_C, algebraMap_eq, finSuccEquiv_apply,
      eval₂Hom_C, coe_comp]
    simp only [AlgEquiv.ofAlgHom_apply, Function.comp_apply, leadingCoeff_C, map_pow,
      leadingCoeff_pow, algebraMap_eq]
    have : ∀ j, ((finSuccEquiv k n) ((T1 f) 1 (X j))).leadingCoeff = 1 := by
      intro j
      by_cases h : j = 0
      · simp only [aeval_eq_bind₁, bind₁_X_right, if_pos h, finSuccEquiv_apply, eval₂Hom_X',
          Fin.cases_zero, monic_X, Monic.leadingCoeff]
      · simp only [aeval_eq_bind₁, bind₁_X_right, if_neg h, one_smul, map_add, map_pow]
        obtain ⟨i, hi⟩ := Fin.exists_succ_eq.mpr h
        rw [← hi, finSuccEquiv_X_succ, finSuccEquiv_X_zero, add_comm]
        apply leadingCoeff_X_pow_add_C
        simp only [add_pos_iff, ofNat_pos, true_or, pow_pos]
    · simp only [this, one_pow, Finset.prod_const_one, mul_one]
  · exact fun i ↦ pow_zero _

private lemma T_leadingcoeff (fne : f ≠ 0) :
    ∃ c : (MvPolynomial (Fin n) k)ˣ, (c.val • (finSuccEquiv k n (T f f))).Monic := by
  obtain ⟨v, vin, vs⟩ := Finset.exists_max_image f.support
    (fun v ↦ (T f ((monomial v) (coeff v f))).degreeOf 0) (support_nonempty.mpr fne)
  set h := fun w ↦ (MvPolynomial.monomial w) (coeff w f)
  simp only [← natDegree_finSuccEquiv] at vs
  replace vs : ∀ x ∈ f.support \ {v}, (finSuccEquiv k n ((T f) (h x))).degree <
      (finSuccEquiv k n ((T f) (h v))).degree := by
    intro x hx
    obtain ⟨h1, h2⟩ := Finset.mem_sdiff.mp hx
    apply degree_lt_degree <| lt_of_le_of_ne (vs x h1) ?_
    simpa only [natDegree_finSuccEquiv] using T_degree f _ _ h1 vin <| ne_of_not_mem_cons h2
  have coeff : (finSuccEquiv k n ((T f) (h v + ∑ x ∈ f.support \ {v}, h x))).leadingCoeff =
      (finSuccEquiv k n ((T f) (h v))).leadingCoeff := by
    simp only [map_add, map_sum]
    rw [add_comm]
    apply leadingCoeff_add_of_degree_lt <| (lt_of_le_of_lt <| degree_sum_le _ _) ?_
    set degv := (finSuccEquiv k n ((T f) (h v))).degree
    set els := ∑ x ∈ f.support \ {v}, (finSuccEquiv k n) ((T f) (h x))
    have h2 : h v ≠ 0 := by simpa [h] using mem_support_iff.mp vin
    replace h2 : (finSuccEquiv k n ((T f) (h v))) ≠ 0 := fun eq ↦ h2 <|
      by simpa only [map_eq_zero_iff _ (AlgEquiv.injective _)] using eq
    apply (Finset.sup_lt_iff (Ne.bot_lt (fun x ↦ h2 (degree_eq_bot.mp x)))).mpr vs
  nth_rw 2 [← support_sum_monomial_coeff f]
  rw [Finset.sum_eq_add_sum_diff_singleton vin h]
  rw [T_coeff] at coeff
  have u : IsUnit (finSuccEquiv k n
      ((T f) (h v + ∑ x ∈ f.support \ {v}, h x))).leadingCoeff := by
    rw [coeff, algebraMap_eq]
    exact IsUnit.map MvPolynomial.C <| Ne.isUnit <| mem_support_iff.mp vin
  exact ⟨u.unit⁻¹, monic_of_isUnit_leadingCoeff_inv_smul u⟩

/-`I` is an ideal containing `f`.-/
variable (I : Ideal (MvPolynomial (Fin (n + 1)) k))

/-`hom1` is a homomorphism from `k[X_0,...X_{n-1}]` into `k[X_1,...X_n][X]/φ(T(I))`,
where `φ` is the isomorphism from `k[X_0,...X_{n-1}]` to `k[X_1,...X_n][X]`.
And it is integral by the lemma above.-/
private noncomputable abbrev hom1 : MvPolynomial (Fin n) k →ₐ[MvPolynomial (Fin n) k]
    (MvPolynomial (Fin n) k)[X] ⧸ (I.map <| T f).map (MvPolynomial.finSuccEquiv k n) :=
  (Quotient.mkₐ (MvPolynomial (Fin n) k) (map (finSuccEquiv k n) (map (T f) I))).comp
  (Algebra.ofId (MvPolynomial (Fin n) k) ((MvPolynomial (Fin n) k)[X]))

private lemma hom1_int (fne : f ≠ 0) (fi : f ∈ I): (hom1 f I).IsIntegral := by
  obtain ⟨c, eq⟩ := T_leadingcoeff f fne
  exact eq.quotient_isIntegral <| Submodule.smul_of_tower_mem _ c.val <|
    mem_map_of_mem _ <| mem_map_of_mem _ fi

/-`eqv1` is the isomorphism from `k[X_1,...X_n][X]/φ(T(I))`
to `k[X_0,...,X_n]/T(I)`, induced by `φ`.-/
private noncomputable abbrev eqv1 := quotientEquivAlg ((I.map (T f)).map
    (finSuccEquiv k n)) (I.map (T f)) (finSuccEquiv k n).symm (by
  set g := (finSuccEquiv k n)
  symm
  have : g.symm.toRingEquiv.toRingHom.comp g = RingHom.id _ :=
    RingEquiv.symm_toRingHom_comp_toRingHom g.toRingEquiv
  calc
    _ = map (g.symm.toAlgHom.toRingHom.comp g) (map (T f) I) := by
      rw [← Ideal.map_map]; rfl
    _ = map (RingHom.id _) (map (T f) I) := by congr
    _ = Ideal.map ((RingHom.id _).comp <| T f) I := by rw [← Ideal.map_map]; rfl
    _ = _ := by rw [id_comp]; rfl)

/-`eqv2` is the isomorphism from `k[X_0,...,X_n]/T(I)` into `k[X_0,...,X_n]/I`,
induce by `T`.-/
private noncomputable abbrev eqv2 := quotientEquivAlg (R₁ := k) (I.map (T f)) I (T f).symm (by
  symm
  calc
    _ = Ideal.map ((T f).symm.toRingEquiv.toRingHom.comp (T f)) I := by rw [← Ideal.map_map]; rfl
    _ = _ := by
      have : (T f).symm.toRingEquiv.toRingHom.comp (T f) = RingHom.id _ :=
        RingEquiv.symm_toRingHom_comp_toRingHom _
      rw [this, Ideal.map_id])

/-`hom2` is the composition of maps above, from `k[X_1,...X_n]` to `k[X_0,...X_n]/I`,
and it's integral.-/
private noncomputable def hom2 : MvPolynomial (Fin n) k →ₐ[k] MvPolynomial (Fin (n + 1)) k ⧸ I :=
  (eqv2 f I).toAlgHom.comp ((eqv1 f I).toAlgHom.comp ((hom1 f I).restrictScalars k))

end NoetherNormalization

open NoetherNormalization

/-Use induction to prove there is an injective map from `k[X_0,...X_{r-1}]` to `k[X_0,...X_n]/I`.-/
theorem exists_integral_inj_algHom_of_quotient (I : Ideal (MvPolynomial (Fin n) k))
    (hi : I ≠ ⊤) : ∃ s ≤ n, ∃ g : (MvPolynomial (Fin s) k) →ₐ[k] ((MvPolynomial (Fin n) k) ⧸ I),
    Function.Injective g ∧ g.IsIntegral := by
  induction' n with d hd
  · refine ⟨0, by rfl, Quotient.mkₐ k I, ?_⟩
    constructor
    · intro a b hab
      rw [Quotient.mkₐ_eq_mk, Ideal.Quotient.eq] at hab
      by_contra neq
      apply sub_ne_zero_of_ne at neq
      have eq := eq_C_of_isEmpty (a - b)
      have ne : coeff 0 (a - b) ≠ 0 := fun h ↦ h ▸ eq ▸ neq <| map_zero _
      obtain ⟨c, _, eqr⟩ := isUnit_iff_exists.mp (Ne.isUnit ne)
      have one : c • (a - b) = 1 := by
        rw [MvPolynomial.smul_eq_C_mul, eq, ← RingHom.map_mul, eqr, MvPolynomial.C_1]
      exact hi ((eq_top_iff_one I).mpr (one ▸ Submodule.smul_of_tower_mem I c hab))
    · apply isIntegral_of_surjective _ (Quotient.mkₐ_surjective k I)
  by_cases eqi : I = 0
  · set q := Quotient.mkₐ k I
    have bij : Function.Bijective q := by
      unfold q
      simp only [Quotient.mkₐ_eq_mk]
      constructor
      · intro a b hab
        rw [Ideal.Quotient.eq, eqi, Submodule.zero_eq_bot, mem_bot] at hab
        rw [← add_zero b, ← hab, add_sub_cancel]
      · exact Quotient.mk_surjective
    exact ⟨d + 1, by rfl, q, bij.1, q.isIntegral_of_surjective bij.2⟩
  · obtain ⟨f, fi, fne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot eqi
    set ϕ := kerLiftAlg <| hom2 f I
    have ne : ker (hom2 f I) ≠ ⊤ := @ker_ne_top _ _ _ _ _ _ _ (Quotient.nontrivial hi) (hom2 f I)
    obtain ⟨s, _, g, injg, intg⟩ := hd (ker <| hom2 f I) ne
    have comp : (kerLiftAlg (hom2 f I)).comp (Quotient.mkₐ k (ker (hom2 f I)))
        = (hom2 f I) := AlgHom.ext fun a ↦ by
      simp only [AlgHom.coe_comp, Quotient.mkₐ_eq_mk, Function.comp_apply, kerLiftAlg_mk]
    have : (hom2 f I).IsIntegral := IsIntegral.trans _ _ (IsIntegral.trans _ _
      (hom1_int f I fne fi) (isIntegral_of_surjective _ (eqv1 f I).surjective))
      (isIntegral_of_surjective _ (eqv2 f I).surjective)
    rw [← comp] at this
    exact ⟨s, by linarith, ϕ.comp g,
      (ϕ.coe_comp  g) ▸ (Function.Injective.comp (kerLiftAlg_injective _) injg),
      IsIntegral.trans _ _ intg (RingHom.IsIntegral.tower_top _ _ this)⟩

/- Noether Normalization.-/
theorem exists_integral_inj_algHom_of_finite {R : Type*} [CommRing R] [Nontrivial R] [Algebra k R]
    [fin : Algebra.FiniteType k R] : ∃ s, ∃ g : (MvPolynomial (Fin s) k) →ₐ[k] R,
    Function.Injective g ∧ g.IsIntegral := by
  obtain ⟨n, f, fsurj⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp fin
  set ϕ := quotientKerAlgEquivOfSurjective fsurj
  have ne : ker f ≠ ⊤ := fun h ↦ (h ▸ (not_one_mem_ker f)) trivial
  obtain ⟨s, _, g, injg, intg⟩ := exists_integral_inj_algHom_of_quotient (ker f) ne
  use s, ϕ.toAlgHom.comp g
  simp only [AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_comp, AlgHom.coe_coe,
    EmbeddingLike.comp_injective, AlgHom.toRingHom_eq_coe]
  exact ⟨injg, IsIntegral.trans _ _ intg (isIntegral_of_surjective _ ϕ.surjective)⟩
