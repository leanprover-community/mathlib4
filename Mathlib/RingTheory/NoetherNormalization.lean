/-
Copyright (c) 2024 Sihan Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Sihan Su, Wan Lin, Xiaoyang Su
-/
import Mathlib.Data.List.Indexes
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
/-!
# Norther Normalizaton
This file contains a proof of Noether normalization lemma by Nagata.

## Main Results
Let $A$ be a finitely generated algebra over a field $k$.
Then there exists natural number $r$ and an injective homomorphism
from $k[X_1, X_2, ..., X_r]$ to $A$ such that $A$ is integral over $k[X_1, X_2, ..., X_r]$.

## Reference
* <https://stacks.math.columbia.edu/tag/00OW>

-/
open Polynomial MvPolynomial Ideal BigOperators Nat RingHom

variable {k : Type*} [Field k] {n : ℕ} (f : MvPolynomial (Fin (n + 1)) k)
variable (v w : Fin (n + 1) →₀ ℕ)

/-Suppose $f$ is a nonzero polynomial of $n+1$ variables : $X_0,...,X_n$.
`up` is a number which is big enough. -/
private noncomputable abbrev up := 2 + f.totalDegree

private lemma up_spec (hv : v ∈ f.support) : ∀ i, v i < up f := by
  intro i
  have := lt_one_add_iff.mpr <| le_trans (monomial_le_degreeOf i hv) <| degreeOf_le_totalDegree f i
  linarith

private lemma ltup : 1 < up f := Nat.lt_add_right f.totalDegree Nat.one_lt_two

private noncomputable abbrev r : Fin (n + 1) → ℕ := fun i ↦ up f ^ i.1

/-We construct a ring homomorphism $T$ which maps $X_i$ into $X_i + X_0^{r_i}$ when $i \neq 0$,
and maps $f$ into some monic polynomial (regarded as a polynomial of $X_0$).-/
private noncomputable abbrev T1 : MvPolynomial (Fin (n + 1)) k →ₐ[k] MvPolynomial (Fin (n + 1)) k :=
  aeval fun i ↦  if i = 0 then X 0 else X i + X 0 ^ r f i

private noncomputable abbrev T_inv :
    MvPolynomial (Fin (n + 1)) k →ₐ[k] MvPolynomial (Fin (n + 1)) k :=
  aeval fun i ↦  if i = 0 then X 0 else X i - X 0 ^ r f i

private lemma T_left_inv : (T_inv f).comp (T1 f) = AlgHom.id _ _ := by
  rw [comp_aeval, ← MvPolynomial.aeval_X_left]
  congr
  ext i v
  cases' i using Fin.cases with d
  · simp only [if_pos, MvPolynomial.aeval_X]
  · simp only [Fin.succ_ne_zero, ite_false, map_add, map_pow,
      MvPolynomial.aeval_X, if_pos, sub_add_cancel]

private lemma T_right_inv : (T1 f).comp (T_inv f) = AlgHom.id _ _ := by
  rw [comp_aeval, ← MvPolynomial.aeval_X_left]
  congr
  ext i v
  cases' i using Fin.cases with d
  · simp only [if_pos, MvPolynomial.aeval_X]
  · simp only [Fin.succ_ne_zero, ite_false, map_sub, map_pow,
      MvPolynomial.aeval_X, if_pos, add_sub_cancel_right]

private noncomputable abbrev T := AlgEquiv.ofAlgHom (T1 f) (T_inv f) (T_right_inv f) (T_left_inv f)

lemma lt {f : MvPolynomial (Fin (n + 1)) k} {v : Fin (n + 1) →₀ ℕ}
  (vlt : ∀ i, v i < up f) : ∀ l ∈ List.ofFn v, l < up f := by
  intro l h
  rw [List.mem_ofFn, Set.mem_range] at h
  obtain ⟨y, hy⟩ := h
  exact hy ▸ vlt y

lemma dig (b : ℕ) (hb : 1 < b) (L1 : List ℕ) (L2 : List ℕ) (len : L1.length = L2.length)
    (w1 : ∀ l ∈ L1, l < b) (w2 : ∀ l ∈ L2, l < b) (h : ofDigits b L1 = ofDigits b L2) :
    L1 = L2 := by
  induction' L1 with D L ih generalizing L2
  · simp only [List.length_nil] at len
    exact (List.length_eq_zero.mp len.symm).symm
  obtain ⟨d, l, eq⟩ := List.exists_cons_of_length_eq_add_one len.symm
  rw [eq]
  simp only [eq, List.length_cons, add_left_inj] at len
  simp only [eq, Nat.ofDigits_cons] at h
  rw [eq] at w2
  have eqd : D = d := by
    have H : (D + b * ofDigits b L) % b = (d + b * ofDigits b l) % b := by rw [h]
    simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (w2 d <| List.mem_cons_self d l),
    Nat.mod_eq_of_lt (w1 D <| List.mem_cons_self D L)] at H
    exact H
  simp only [eqd, add_right_inj, mul_left_cancel_iff_of_pos (zero_lt_of_lt hb)] at h
  have := ih l len (fun a ha ↦ w1 a <| List.mem_cons_of_mem D ha)
    (fun a ha ↦ w2 a <| List.mem_cons_of_mem d ha) h
  rw [eqd, this]

private lemma r_spec (vlt : ∀ i, v i < up f) (wlt : ∀ i, w i < up f) (neq : v ≠ w) :
    ∑ x : Fin (n + 1), r f x * v x ≠ ∑ x : Fin (n + 1), r f x * w x := by
  unfold r
  by_contra h
  have : List.ofFn v = List.ofFn w := by
    apply dig (up f) (ltup f) (List.ofFn v) (List.ofFn w)
      (by simp only [List.length_ofFn]) (lt vlt) (lt wlt)
    simp only [Nat.ofDigits_eq_sum_mapIdx, List.mapIdx_eq_ofFn, List.get_ofFn]
    repeat rw [← List.sum_ofFn] at h
    simp only [List.length_ofFn, Fin.cast_trans, Fin.cast_eq_self, Fin.coe_cast, mul_comm]
    exact h
  exact neq <| Finsupp.ext <| congrFun <| List.ofFn_inj.mp this

private lemma T_spec_monomial (a : k) (ha : a ≠ 0) : ((T f) (monomial v a)).degreeOf 0 =
    ∑ i : Fin (n + 1), (r f i) * v i := by
  rw [← natDegree_finSuccEquiv]
  nth_rw 1 [monomial_eq]
  rw [Finsupp.prod_pow v fun a ↦ X a, Fin.prod_univ_succ]
  simp only [Fin.sum_univ_succ, _root_.map_mul, map_prod, map_pow]
  simp only [AlgEquiv.ofAlgHom_apply, MvPolynomial.aeval_C, MvPolynomial.aeval_X, if_pos,
    Fin.succ_ne_zero, ite_false, map_add, map_pow, finSuccEquiv_X_zero,
    finSuccEquiv_X_succ, algebraMap_eq]
  have h1 : (finSuccEquiv k n) (C a) ≠ 0 :=
    (map_ne_zero_iff _ (AlgEquiv.injective _)).mpr ((map_ne_zero_iff _ (C_injective _ _)).mpr ha)
  have h2 : Polynomial.X (R := (MvPolynomial (Fin n) k))^ v 0 ≠ 0 := pow_ne_zero (v 0) X_ne_zero
  have h3 : ∀ i : Fin n, (Polynomial.C (X (R := k) i) + Polynomial.X ^ r f i.succ)
    ^ v i.succ ≠ 0 := by
    intro i
    apply pow_ne_zero (v i.succ) (leadingCoeff_ne_zero.mp ?_)
    rw [add_comm, leadingCoeff_X_pow_add_C]
    exact one_ne_zero
    simp only [add_pos_iff, ofNat_pos, true_or, pow_pos]
  rw [natDegree_mul h1 (mul_ne_zero h2 (Finset.prod_ne_zero_iff.mpr (fun i _ ↦ h3 i))),
    natDegree_mul h2 (Finset.prod_ne_zero_iff.mpr (fun i _ ↦ h3 i)),
    natDegree_prod _  _ (fun i _ ↦ h3 i), natDegree_finSuccEquiv, degreeOf_C]
  simp only [natDegree_pow, zero_add]
  have e1 : r f 0 = 1 := by
    unfold r
    simp only [Fin.val_zero, pow_zero]
  rw [natDegree_X, mul_one, e1, one_mul, add_left_cancel_iff]
  apply Finset.sum_congr rfl
  intro i _
  rw [add_comm (Polynomial.C (X i)), natDegree_X_pow_add_C, mul_comm]

private lemma T_spec_degree (hv : v ∈ f.support) (hw : w ∈ f.support) (neq : v ≠ w) :
    (T f <| monomial v <| coeff v f).degreeOf 0 ≠
    (T f <| monomial w <| coeff w f).degreeOf 0 := by
  have nv := mem_support_iff.mp hv
  have nw := mem_support_iff.mp hw
  rw [T_spec_monomial _ _ _ nv, T_spec_monomial _ _ _ nw]
  exact r_spec f v w (up_spec f v hv) (up_spec f w hw) neq

private lemma T_spec_coeff :
    (finSuccEquiv k n ((T f) ((monomial v) (coeff v f)))).leadingCoeff =
    algebraMap k _ (coeff v f) := by
  rw [monomial_eq, Finsupp.prod_fintype]
  · simp only [_root_.map_mul, map_prod, leadingCoeff_mul, leadingCoeff_prod]
    rw [AlgEquiv.ofAlgHom_apply, algHom_C, algebraMap_eq, finSuccEquiv_apply,
      eval₂Hom_C, coe_comp]
    simp only[AlgEquiv.ofAlgHom_apply, Function.comp_apply, leadingCoeff_C, map_pow,
      leadingCoeff_pow, algebraMap_eq]
    have : ∀ j, ((finSuccEquiv k n) ((T1 f) (X j))).leadingCoeff = 1 := by
      intro j
      by_cases h : j = 0
      · simp only [aeval_eq_bind₁, bind₁_X_right, if_pos h, finSuccEquiv_apply, eval₂Hom_X',
          Fin.cases_zero, monic_X, Monic.leadingCoeff]
      · simp only [aeval_eq_bind₁, bind₁_X_right, if_neg h, map_add, map_pow]
        obtain ⟨i, hi⟩ := Fin.exists_succ_eq.mpr h
        rw [← hi, finSuccEquiv_X_succ, finSuccEquiv_X_zero, add_comm]
        apply leadingCoeff_X_pow_add_C
        simp only [add_pos_iff, ofNat_pos, true_or, pow_pos]
    · simp only [this, one_pow, Finset.prod_const_one, mul_one]
  · exact fun i ↦ pow_zero _

private lemma T_spec_leadingcoeff (fne : f ≠ 0) :
    ∃ c : (MvPolynomial (Fin n) k)ˣ, (c.val • (finSuccEquiv k n (T f f))).Monic := by
  obtain ⟨v, vin, vspec⟩ := Finset.exists_max_image f.support
    (fun v ↦ (T f ((monomial v) (coeff v f))).degreeOf 0) (support_nonempty.mpr fne)
  set h := fun w ↦ (MvPolynomial.monomial w) (coeff w f)
  simp only [← natDegree_finSuccEquiv] at vspec
  replace vspec : ∀ x ∈ f.support \ {v}, (finSuccEquiv k n ((T f) (h x))).degree <
      (finSuccEquiv k n ((T f) (h v))).degree := by
    intro x hx
    obtain ⟨h1, h2⟩ := Finset.mem_sdiff.mp hx
    apply degree_lt_degree
    apply lt_of_le_of_ne (vspec x h1)
    repeat rw [natDegree_finSuccEquiv]
    apply T_spec_degree f _ _ h1 vin <| List.ne_of_not_mem_cons h2
  have coeff : (finSuccEquiv k n ((T f) (h v + ∑ x ∈ f.support \ {v}, h x))).leadingCoeff =
      (finSuccEquiv k n ((T f) (h v))).leadingCoeff := by
    simp only [map_add, map_sum]
    rw [add_comm]
    apply leadingCoeff_add_of_degree_lt
    apply lt_of_le_of_lt <| degree_sum_le _ _
    set degv := (finSuccEquiv k n ((T f) (h v))).degree
    set els := ∑ x ∈ f.support \ {v}, (finSuccEquiv k n) ((T f) (h x))
    have h2 : h v ≠ 0 := by
      unfold h
      simp only [ne_eq, monomial_eq_zero]
      exact mem_support_iff.mp vin
    replace h2 : (finSuccEquiv k n ((T f) (h v))) ≠ 0 := by
      by_contra eq
      repeat rw [map_eq_zero_iff _ (AlgEquiv.injective _)] at eq
      exact h2 eq
    apply (Finset.sup_lt_iff (Ne.bot_lt (fun x ↦ h2 (degree_eq_bot.mp x)))).mpr
    exact vspec
  nth_rw 2 [← support_sum_monomial_coeff f]
  have := Finset.sum_eq_add_sum_diff_singleton vin h
  rw [this]
  rw [T_spec_coeff] at coeff
  have := mem_support_iff.mp vin
  have u : IsUnit (finSuccEquiv k n
      ((T f) (h v + ∑ x ∈ f.support \ {v}, h x))).leadingCoeff := by
    rw [coeff]
    simp only [algebraMap_eq]
    refine IsUnit.map MvPolynomial.C <| Ne.isUnit this
  use u.unit⁻¹
  exact monic_of_isUnit_leadingCoeff_inv_smul u

/-$I$ is an ideal containing $f$.-/
variable (I : Ideal (MvPolynomial (Fin (n + 1)) k))

/-$hom1$ is a homomorphism from $k[X_0,...X_{n-1}]$ into $k[X_1,...X_n][X]/\phi(T(I))$,
where $\phi$ is the isomorphism from $k[X_0,...X_{n-1}]$ to $k[X_1,...X_n][X]$.
And it is integral by the lemma above.-/
private noncomputable abbrev hom1 :=
  (Quotient.mkₐ (MvPolynomial (Fin n) k) (map (finSuccEquiv k n) (map (T f) I))).comp
  (Algebra.ofId (MvPolynomial (Fin n) k) ((MvPolynomial (Fin n) k)[X]))

set_option synthInstance.maxHeartbeats 40000
private lemma hom1_int (fne : f ≠ 0) (fi : f ∈ I): (hom1 f I).IsIntegral := by
  obtain ⟨c, eq⟩ := T_spec_leadingcoeff f fne
  exact eq.quotient_isIntegral <| Submodule.smul_of_tower_mem _ c.val <|
    mem_map_of_mem _ <| mem_map_of_mem _ fi

/-$eqv1$ is the isomorphism from $k[X_1,...X_n][X]/\phi(T(I))$
to $k[X_0,...,X_n]/T(I)$, induced by $\phi$.-/
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
    _ = _ := by rw [id_comp]; rfl
  )

/-$eqv2$ is the isomorphism from $k[X_0,...,X_n]/T(I)$ into $k[X_0,...,X_n]/I$,
induce by $T$.-/
private noncomputable abbrev eqv2 := quotientEquivAlg (R₁ := k) (I.map (T f)) I (T f).symm (by
  symm
  calc
    _ = Ideal.map ((T f).symm.toRingEquiv.toRingHom.comp (T f)) I := by rw [← Ideal.map_map]; rfl
    _ = _ := by
      have : (T f).symm.toRingEquiv.toRingHom.comp (T f) = RingHom.id _ := by
        apply RingEquiv.symm_toRingHom_comp_toRingHom
      rw [this, Ideal.map_id])

/-$hom2$ is the composition of maps above, from $k[X_1,...X_n]$ to $k[X_0,...X_n]/I$,
and it's integral.-/
private noncomputable def hom2 :=
  (eqv2 f I).toAlgHom.comp ((eqv1 f I).toAlgHom.comp ((hom1 f I).restrictScalars k))

/-Use induction to prove there is an injective map from $k[X_0,...X_{r-1}]$ to $k[X_0,...X_n]/I$.-/
theorem exists_integral_inj (I : Ideal (MvPolynomial (Fin n) k))
    (hi : I ≠ ⊤) : ∃ r ≤ n, ∃ g : (MvPolynomial (Fin r) k) →ₐ[k] ((MvPolynomial (Fin n) k) ⧸ I),
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
    have ne : RingHom.ker (hom2 f I) ≠ ⊤ := by
      by_contra eq
      replace eq := (mem_ker (f := hom2 f I) (r := 1)).mp (eq ▸ trivial)
      simp only [AlgEquiv.toAlgHom_eq_coe, map_one] at eq
      exact hi <| Quotient.zero_eq_one_iff.mp eq.symm
    obtain ⟨r, _, g, injg, intg⟩ := hd (RingHom.ker <| hom2 f I) ne
    have comp : (kerLiftAlg (hom2 f I)).comp (Quotient.mkₐ k (RingHom.ker (hom2 f I)))
        = (hom2 f I) := AlgHom.ext fun a ↦ by
      simp only [AlgHom.coe_comp, Quotient.mkₐ_eq_mk, Function.comp_apply, kerLiftAlg_mk]
    have : (hom2 f I).IsIntegral := IsIntegral.trans _ _ (IsIntegral.trans _ _
      (hom1_int f I fne fi) (isIntegral_of_surjective _ (eqv1 f I).surjective))
      (isIntegral_of_surjective _ (eqv2 f I).surjective)
    rw [← comp] at this
    exact ⟨r, by linarith, ϕ.comp g,
      (ϕ.coe_comp  g) ▸ (Function.Injective.comp (kerLiftAlg_injective _) injg),
      IsIntegral.trans _ _ intg (RingHom.IsIntegral.tower_top _ _ this)⟩

theorem Noether_Normalization {R : Type*} [CommRing R] [Nontrivial R] [Algebra k R]
    [fin : Algebra.FiniteType k R] : ∃ r, ∃ g : (MvPolynomial (Fin r) k) →ₐ[k] R,
    Function.Injective g ∧ g.IsIntegral := by
  obtain ⟨n, f, fsurj⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp fin
  set ϕ := quotientKerAlgEquivOfSurjective fsurj
  have ne : RingHom.ker f ≠ ⊤ := fun h ↦ (h ▸ (not_one_mem_ker f)) trivial
  obtain ⟨r, _, g, injg, intg⟩ := exists_integral_inj (RingHom.ker f) ne
  use r, ϕ.toAlgHom.comp g
  simp only [AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_comp, AlgHom.coe_coe,
    EmbeddingLike.comp_injective, AlgHom.toRingHom_eq_coe]
  exact ⟨injg, IsIntegral.trans _ _ intg (isIntegral_of_surjective _ ϕ.surjective)⟩
