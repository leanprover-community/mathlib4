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
This file contains a proof by Nagata of the Noether normalization lemma.

## Main Results
Let `A` be a finitely generated algebra over a field `k`.
Then there exists a natural number `r` and an injective homomorphism
from `k[X_1, X_2, ..., X_r]` to `A` such that `A` is integral over `k[X_1, X_2, ..., X_r]`.

## Reference
* <https://stacks.math.columbia.edu/tag/00OW>

-/
open Polynomial MvPolynomial Ideal BigOperators Nat RingHom List

variable {k : Type*} [Field k] {n : ℕ} (f : MvPolynomial (Fin (n + 1)) k)
variable (v w : Fin (n + 1) →₀ ℕ)

namespace NoetherNormalization

section equivT
/-!
Suppose `f` is a nonzero polynomial of `n+1` variables : `X_0,...,X_n`.
First we construct an algebra equivalence `T` from `k[X_0,...,X_n]` to `k[X_0,...,X_n]`, such that
  `f` is mapped to a polynomial of `X_0` with invertible leading coefficient.
More precisely, `T` maps `X_i` to `X_i + X_0 ^ r_i` when `i ≠ 0`, and `X_0` to `X_0`.
Here we choose `r_i` to be `up ^ i` where `up` is big enought, so that `T` maps
  different monomials of `f` to mvpolynomials with different degrees of `X_0`. See `Nat.ofDigits`.
-/

/-- `up` is defined as `2 + f.totalDegree`. Any big enough number would work. -/
local notation3 "up" => 2 + f.totalDegree

variable {f v} in
private lemma lt (vlt : ∀ i, v i < up) : ∀ l ∈ ofFn v, l < up := by
  intro l h
  rw [mem_ofFn, Set.mem_range] at h
  obtain ⟨y, hy⟩ := h
  exact hy ▸ vlt y

/-- `r` maps `(i : Fin (n + 1))` to `up ^ i`-/
local notation3 "r" => fun (i : Fin (n + 1)) ↦ up ^ i.1

/-- We construct an algebra map `T1` which maps `X_i` into `X_i + X_0 ^ r_i` when `i ≠ 0`,
and `X_0` to `X_0`. -/
noncomputable abbrev T1 (c : k) :
    MvPolynomial (Fin (n + 1)) k →ₐ[k] MvPolynomial (Fin (n + 1)) k :=
  aeval fun i ↦ if i = 0 then X 0 else X i + c • X 0 ^ r i

private lemma inv_pair (c : k) :
    (T1 f c).comp (T1 f (-c)) = AlgHom.id _ _ := by
  rw [comp_aeval, ← MvPolynomial.aeval_X_left]
  ext i v
  cases i using Fin.cases <;>
  simp [Fin.succ_ne_zero]

/- `T1 f 1` leads to an algebra equiv `T f`.-/
private noncomputable abbrev T := AlgEquiv.ofAlgHom (T1 f 1) (T1 f (-1))
  (inv_pair f 1) (by simpa using inv_pair f (-1))

private lemma r_ne (vlt : ∀ i, v i < up) (wlt : ∀ i, w i < up) (neq : v ≠ w) :
    ∑ x : Fin (n + 1), r x * v x ≠ ∑ x : Fin (n + 1), r x * w x := by
  intro h
  refine neq <| Finsupp.ext <| congrFun <| ofFn_inj.mp ?_
  apply ofDigits_inj_of_len_eq (Nat.lt_add_right f.totalDegree one_lt_two)
      (by simp) (lt vlt) (lt wlt)
  simpa only [ofDigits_eq_sum_mapIdx, mapIdx_eq_ofFn, get_ofFn, length_ofFn,
      Fin.coe_cast, mul_comm, sum_ofFn] using h

private lemma T_monomial {a : k} (ha : a ≠ 0) : ((T f) (monomial v a)).degreeOf 0 =
    ∑ i : Fin (n + 1), (r i) * v i := by
  rw [← natDegree_finSuccEquiv, monomial_eq, Finsupp.prod_pow v fun a ↦ X a]
  simp only [Fin.prod_univ_succ, Fin.sum_univ_succ, _root_.map_mul, map_prod, map_pow,
    AlgEquiv.ofAlgHom_apply, MvPolynomial.aeval_C, MvPolynomial.aeval_X, if_pos, Fin.succ_ne_zero,
    ite_false, one_smul, map_add, finSuccEquiv_X_zero, finSuccEquiv_X_succ, algebraMap_eq]
  have h1 : (finSuccEquiv k n) (C a) ≠ 0 :=
    (map_ne_zero_iff _ (AlgEquiv.injective _)).mpr ((map_ne_zero_iff _ (C_injective _ _)).mpr ha)
  have h2 : Polynomial.X (R := (MvPolynomial (Fin n) k)) ^ v 0 ≠ 0 := pow_ne_zero (v 0) X_ne_zero
  have h3 (i : Fin n) :
      (Polynomial.C (X (R := k) i) + Polynomial.X ^ r i.succ) ^ v i.succ ≠ 0 := by
    apply pow_ne_zero (v i.succ) (leadingCoeff_ne_zero.mp ?_)
    rw [add_comm, leadingCoeff_X_pow_add_C (by simp)]
    exact one_ne_zero
  rw [natDegree_mul h1 (mul_ne_zero h2 (Finset.prod_ne_zero_iff.mpr (fun i _ ↦ h3 i))),
    natDegree_mul h2 (Finset.prod_ne_zero_iff.mpr (fun i _ ↦ h3 i)),
    natDegree_prod _  _ (fun i _ ↦ h3 i), natDegree_finSuccEquiv, degreeOf_C]
  simpa only [natDegree_pow, zero_add, natDegree_X, mul_one, Fin.val_zero, pow_zero, one_mul,
    add_right_inj] using Finset.sum_congr rfl (fun i _ ↦ by
    rw [add_comm (Polynomial.C _), natDegree_X_pow_add_C, mul_comm])

/- `T` maps different monomials of `f` to mvpolynomials with different degrees of `X_0`. -/
private lemma T_degree (hv : v ∈ f.support) (hw : w ∈ f.support) (neq : v ≠ w) :
    (T f <| monomial v <| coeff v f).degreeOf 0 ≠
    (T f <| monomial w <| coeff w f).degreeOf 0 := by
  rw [T_monomial _ _ <| mem_support_iff.mp hv, T_monomial _ _ <| mem_support_iff.mp hw]
  refine r_ne f v w (fun i ↦ ?_) (fun i ↦ ?_) neq <;>
  exact lt_of_le_of_lt ((monomial_le_degreeOf i ‹_›).trans (degreeOf_le_totalDegree f i))
    (by omega)

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
      simp only [aeval_eq_bind₁, bind₁_X_right]
      by_cases h : j = 0
      · simp only [if_pos h, finSuccEquiv_apply, eval₂Hom_X', Fin.cases_zero, monic_X,
          Monic.leadingCoeff]
      · simp only [if_neg h, one_smul, map_add, map_pow]
        obtain ⟨i, hi⟩ := Fin.exists_succ_eq.mpr h
        rw [← hi, finSuccEquiv_X_succ, finSuccEquiv_X_zero, add_comm]
        apply leadingCoeff_X_pow_add_C
        simp only [add_pos_iff, ofNat_pos, true_or, pow_pos]
    · simp only [this, one_pow, Finset.prod_const_one, mul_one]
  · exact fun i ↦ pow_zero _

/- `T` maps `f` into some polynomial of `X_0` such that the leading coeff is invertible. -/
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
    have h2 : h v ≠ 0 := by simpa [h] using mem_support_iff.mp vin
    replace h2 : (finSuccEquiv k n ((T f) (h v))) ≠ 0 := fun eq ↦ h2 <|
      by simpa only [map_eq_zero_iff _ (AlgEquiv.injective _)] using eq
    exact (Finset.sup_lt_iff <| Ne.bot_lt (fun x ↦ h2 <| degree_eq_bot.mp x)).mpr vs
  nth_rw 2 [← f.support_sum_monomial_coeff]
  rw [Finset.sum_eq_add_sum_diff_singleton vin h]
  rw [T_coeff] at coeff
  have u : IsUnit (finSuccEquiv k n ((T f) (h v + ∑ x ∈ f.support \ {v}, h x))).leadingCoeff := by
    simpa only [coeff, algebraMap_eq] using (mem_support_iff.mp vin).isUnit.map MvPolynomial.C
  exact ⟨u.unit⁻¹, monic_of_isUnit_leadingCoeff_inv_smul u⟩

end equivT

section intmaps
/-!
Second we construct the following maps: Let `I` be an ideal containing `f`.
  φ : k[X_0,...X_{n-1}] ≃ k[X_1,...X_n][X];
  hom1 : k[X_0,...X_{n-1}] → k[X_1,...X_n][X]/φ(T(I));
  eqv1 : k[X_1,...X_n][X]/φ(T(I)) ≃ k[X_0,...,X_n]/T(I);
  eqv2 : k[X_0,...,X_n]/T(I) ≃ k[X_0,...,X_n]/I;
  hom2 : k[X_0,...X_(n-1)] → k[X_0,...X_n]/I.
hom1 is integral because φ(T(I)) contains a monic polynomial.
hom2 is integral because it's the composition of integral maps.
-/
variable (I : Ideal (MvPolynomial (Fin (n + 1)) k))

/- `hom1` is a homomorphism from `k[X_0,...X_{n-1}]` to `k[X_1,...X_n][X]/φ(T(I))`,
where `φ` is the isomorphism from `k[X_0,...X_{n-1}]` to `k[X_1,...X_n][X]`. -/
private noncomputable abbrev hom1 : MvPolynomial (Fin n) k →ₐ[MvPolynomial (Fin n) k]
    (MvPolynomial (Fin n) k)[X] ⧸ (I.map <| T f).map (finSuccEquiv k n) :=
  (Quotient.mkₐ (MvPolynomial (Fin n) k) (map (finSuccEquiv k n) (map (T f) I))).comp
  (Algebra.ofId (MvPolynomial (Fin n) k) ((MvPolynomial (Fin n) k)[X]))

/- `hom1 f I` is integral.-/
private lemma hom1_int (fne : f ≠ 0) (fi : f ∈ I): (hom1 f I).IsIntegral := by
  obtain ⟨c, eq⟩ := T_leadingcoeff f fne
  exact eq.quotient_isIntegral <| Submodule.smul_of_tower_mem _ c.val <|
    mem_map_of_mem _ <| mem_map_of_mem _ fi

/- `eqv1` is the isomorphism from `k[X_1,...X_n][X]/φ(T(I))`
to `k[X_0,...,X_n]/T(I)`, induced by `φ`. -/
private noncomputable abbrev eqv1 :
    ((MvPolynomial (Fin n) k)[X] ⧸ (I.map (T f)).map (finSuccEquiv k n)) ≃ₐ[k]
    MvPolynomial (Fin (n + 1)) k ⧸ I.map (T f) := quotientEquivAlg
  ((I.map (T f)).map (finSuccEquiv k n)) (I.map (T f)) (finSuccEquiv k n).symm (by
  set g := (finSuccEquiv k n)
  symm
  have : g.symm.toRingEquiv.toRingHom.comp g = RingHom.id _ :=
    g.toRingEquiv.symm_toRingHom_comp_toRingHom
  calc
    _ = map (g.symm.toAlgHom.toRingHom.comp g) (map (T f) I) := by rw [← Ideal.map_map]; rfl
    _ = map (RingHom.id _) (map (T f) I) := by congr
    _ = Ideal.map ((RingHom.id _).comp <| T f) I := by rw [← Ideal.map_map]; rfl
    _ = _ := by rw [id_comp]; rfl)

/- `eqv2` is the isomorphism from `k[X_0,...,X_n]/T(I)` into `k[X_0,...,X_n]/I`,
induced by `T`. -/
private noncomputable abbrev eqv2 :
    (MvPolynomial (Fin (n + 1)) k ⧸ I.map (T f)) ≃ₐ[k] MvPolynomial (Fin (n + 1)) k ⧸ I
  := quotientEquivAlg (R₁ := k) (I.map (T f)) I (T f).symm (by
  symm
  calc
    _ = Ideal.map ((T f).symm.toRingEquiv.toRingHom.comp (T f)) I := by rw [← Ideal.map_map]; rfl
    _ = _ := by
      have : (T f).symm.toRingEquiv.toRingHom.comp (T f) = RingHom.id _ :=
        RingEquiv.symm_toRingHom_comp_toRingHom _
      rw [this, Ideal.map_id])

/- `hom2` is the composition of maps above, from `k[X_0,...X_(n-1)]` to `k[X_0,...X_n]/I`. -/
private noncomputable def hom2 : MvPolynomial (Fin n) k →ₐ[k] MvPolynomial (Fin (n + 1)) k ⧸ I :=
  (eqv2 f I).toAlgHom.comp ((eqv1 f I).toAlgHom.comp ((hom1 f I).restrictScalars k))

/- `hom2 f I` is integral. -/
private lemma hom2_int (fne : f ≠ 0) (fi : f ∈ I): (hom2 f I).IsIntegral :=
  ((hom1_int f I fne fi).trans _ _ <| isIntegral_of_surjective _ (eqv1 f I).surjective).trans _ _
    <| isIntegral_of_surjective _ (eqv2 f I).surjective

end intmaps
end NoetherNormalization

section mainthm
/-!
We use induction to prove there is an injective map from `k[X_0,...,X_{r-1}]`
  to `k[X_0,...,X_(n-1)]/I`.`n=0` is trivial.
For `n+1`, I = 0 is trivial. Otherwise, `hom2` induces a map `φ` by quotient kernel.
  We use the inductive hypothesis on k[X_1,...,X_n] and the kernel of `hom2` to get `s, g`.
Compose `φ` and `g` and we get the desired map since both `φ` and `g` are injective and integral.
-/
open NoetherNormalization

/-- There exists some `s ≤ n` and an integral injective algebra homomorphism
from `k[X_0,...,X_(r-1)]` to `k[X_0,...,X_(n-1)]/I` if `I` is not top.-/
theorem exists_integral_inj_algHom_of_quotient (I : Ideal (MvPolynomial (Fin n) k))
    (hi : I ≠ ⊤) : ∃ s ≤ n, ∃ g : (MvPolynomial (Fin s) k) →ₐ[k] ((MvPolynomial (Fin n) k) ⧸ I),
    Function.Injective g ∧ g.IsIntegral := by
  induction' n with d hd
  · refine ⟨0, le_rfl, Quotient.mkₐ k I, ?_⟩
    constructor
    · intro a b hab
      rw [Quotient.mkₐ_eq_mk, Ideal.Quotient.eq] at hab
      by_contra neq
      have eq := eq_C_of_isEmpty (a - b)
      have ne : coeff 0 (a - b) ≠ 0 := fun h ↦ h ▸ eq ▸ sub_ne_zero_of_ne neq <| map_zero _
      obtain ⟨c, _, eqr⟩ := isUnit_iff_exists.mp ne.isUnit
      have one : c • (a - b) = 1 := by
        rw [MvPolynomial.smul_eq_C_mul, eq, ← RingHom.map_mul, eqr, MvPolynomial.C_1]
      exact hi ((eq_top_iff_one I).mpr (one ▸ I.smul_of_tower_mem c hab))
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
    exact ⟨d + 1, le_rfl, q, bij.1, q.isIntegral_of_surjective bij.2⟩
  · obtain ⟨f, fi, fne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot eqi
    set ϕ := kerLiftAlg <| hom2 f I
    letI := Quotient.nontrivial hi
    obtain ⟨s, _, g, injg, intg⟩ := hd (ker <| hom2 f I) (ker_ne_top <| hom2 f I)
    have comp : (kerLiftAlg (hom2 f I)).comp (Quotient.mkₐ k <| ker <| hom2 f I) = (hom2 f I) :=
      AlgHom.ext fun a ↦ by
        simp only [AlgHom.coe_comp, Quotient.mkₐ_eq_mk, Function.comp_apply, kerLiftAlg_mk]
    exact ⟨s, by linarith, ϕ.comp g, (ϕ.coe_comp  g) ▸ (kerLiftAlg_injective _).comp injg,
      intg.trans _ _ <| (comp ▸ hom2_int f I fne fi).tower_top _ _⟩

/-- **Noether Normalization**
Proved by the theorem above since finitely generated algebra
  is a quotient of a polynomial ring in n variables.-/
theorem exists_integral_inj_algHom_of_fg {R : Type*} [CommRing R] [Nontrivial R] [Algebra k R]
    [fin : Algebra.FiniteType k R] : ∃ s, ∃ g : (MvPolynomial (Fin s) k) →ₐ[k] R,
    Function.Injective g ∧ g.IsIntegral := by
  obtain ⟨n, f, fsurj⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp fin
  set ϕ := quotientKerAlgEquivOfSurjective fsurj
  obtain ⟨s, _, g, injg, intg⟩ := exists_integral_inj_algHom_of_quotient (ker f) (ker_ne_top _)
  use s, ϕ.toAlgHom.comp g
  simp only [AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_comp, AlgHom.coe_coe,
    EmbeddingLike.comp_injective, AlgHom.toRingHom_eq_coe]
  exact ⟨injg, intg.trans _ _ (isIntegral_of_surjective _ ϕ.surjective)⟩

end mainthm
