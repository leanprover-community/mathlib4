/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Eric Wieser
-/
import Mathlib.Algebra.DirectSum.Internal
import Mathlib.Algebra.GradedMonoid
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.SetTheory.Cardinal.Basic

/-!
# Homogeneous polynomials

A multivariate polynomial `φ` is homogeneous of degree `n`
if all monomials occurring in `φ` have degree `n`.

## Main definitions/lemmas

* `IsHomogeneous φ n`: a predicate that asserts that `φ` is homogeneous of degree `n`.
* `homogeneousSubmodule σ R n`: the submodule of homogeneous polynomials of degree `n`.
* `homogeneousComponent n`: the additive morphism that projects polynomials onto
  their summand that is homogeneous of degree `n`.
* `sum_homogeneousComponent`: every polynomial is the sum of its homogeneous components.

-/


namespace MvPolynomial

variable {σ : Type*} {τ : Type*} {R : Type*} {S : Type*}

/-
TODO
* show that `MvPolynomial σ R ≃ₐ[R] ⨁ i, homogeneousSubmodule σ R i`
-/

open Finsupp

/-- A multivariate polynomial `φ` is homogeneous of degree `n`
if all monomials occurring in `φ` have degree `n`. -/
def IsHomogeneous [CommSemiring R] (φ : MvPolynomial σ R) (n : ℕ) :=
  IsWeightedHomogeneous 1 φ n

variable [CommSemiring R]

theorem weightedTotalDegree_one (φ : MvPolynomial σ R) :
    weightedTotalDegree (1 : σ → ℕ) φ = φ.totalDegree := by
  simp only [totalDegree, weightedTotalDegree, weight, LinearMap.toAddMonoidHom_coe,
    linearCombination, Pi.one_apply, Finsupp.coe_lsum, LinearMap.coe_smulRight, LinearMap.id_coe,
    id, Algebra.id.smul_eq_mul, mul_one]

theorem weightedTotalDegree_rename_of_injective {σ τ : Type*} {e : σ → τ}
    {w : τ → ℕ} {P : MvPolynomial σ R} (he : Function.Injective e) :
    weightedTotalDegree w (rename e P) = weightedTotalDegree (w ∘ e) P := by
  classical
  unfold weightedTotalDegree
  rw [support_rename_of_injective he, Finset.sup_image]
  congr; ext; unfold weight; simp

variable (σ R)

/-- The submodule of homogeneous `MvPolynomial`s of degree `n`. -/
def homogeneousSubmodule (n : ℕ) : Submodule R (MvPolynomial σ R) where
  carrier := { x | x.IsHomogeneous n }
  smul_mem' r a ha c hc := by
    rw [coeff_smul] at hc
    apply ha
    intro h
    apply hc
    rw [h]
    exact smul_zero r
  zero_mem' _ hd := False.elim (hd <| coeff_zero _)
  add_mem' {a b} ha hb c hc := by
    rw [coeff_add] at hc
    obtain h | h : coeff c a ≠ 0 ∨ coeff c b ≠ 0 := by
      contrapose! hc
      simp only [hc, add_zero]
    · exact ha h
    · exact hb h

@[simp]
lemma weightedHomogeneousSubmodule_one (n : ℕ) :
    weightedHomogeneousSubmodule R 1 n = homogeneousSubmodule σ R n := rfl

variable {σ R}

@[simp]
theorem mem_homogeneousSubmodule (n : ℕ) (p : MvPolynomial σ R) :
    p ∈ homogeneousSubmodule σ R n ↔ p.IsHomogeneous n := Iff.rfl

variable (σ R)

/-- While equal, the former has a convenient definitional reduction. -/
theorem homogeneousSubmodule_eq_finsupp_supported (n : ℕ) :
    homogeneousSubmodule σ R n = Finsupp.supported _ R { d | d.degree = n } := by
  simp_rw [degree_eq_weight_one]
  exact weightedHomogeneousSubmodule_eq_finsupp_supported R 1 n

variable {σ R}

theorem homogeneousSubmodule_mul (m n : ℕ) :
    homogeneousSubmodule σ R m * homogeneousSubmodule σ R n ≤ homogeneousSubmodule σ R (m + n) :=
  weightedHomogeneousSubmodule_mul 1 m n

section

theorem isHomogeneous_monomial {d : σ →₀ ℕ} (r : R) {n : ℕ} (hn : d.degree = n) :
    IsHomogeneous (monomial d r) n := by
  rw [degree_eq_weight_one] at hn
  exact isWeightedHomogeneous_monomial 1 d r hn

variable (σ)

theorem totalDegree_eq_zero_iff (p : MvPolynomial σ R) :
    p.totalDegree = 0 ↔ ∀ (m : σ →₀ ℕ) (_ : m ∈ p.support) (x : σ), m x = 0 := by
  rw [← weightedTotalDegree_one, weightedTotalDegree_eq_zero_iff _ p]
  exact nonTorsionWeight_of (Function.const σ one_ne_zero)

theorem totalDegree_zero_iff_isHomogeneous {p : MvPolynomial σ R} :
    p.totalDegree = 0 ↔ IsHomogeneous p 0 := by
  rw [← weightedTotalDegree_one,
    ← isWeightedHomogeneous_zero_iff_weightedTotalDegree_eq_zero, IsHomogeneous]

alias ⟨isHomogeneous_of_totalDegree_zero, _⟩ := totalDegree_zero_iff_isHomogeneous

theorem isHomogeneous_C (r : R) : IsHomogeneous (C r : MvPolynomial σ R) 0 := by
  apply isHomogeneous_monomial
  simp only [Finsupp.degree, Finsupp.zero_apply, Finset.sum_const_zero]

variable (R)

theorem isHomogeneous_zero (n : ℕ) : IsHomogeneous (0 : MvPolynomial σ R) n :=
  (homogeneousSubmodule σ R n).zero_mem

theorem isHomogeneous_one : IsHomogeneous (1 : MvPolynomial σ R) 0 :=
  isHomogeneous_C _ _

variable {σ}

theorem isHomogeneous_X (i : σ) : IsHomogeneous (X i : MvPolynomial σ R) 1 := by
  apply isHomogeneous_monomial
  rw [Finsupp.degree, Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton]
  exact Finsupp.single_eq_same

end

namespace IsHomogeneous

variable [CommSemiring S] {φ ψ : MvPolynomial σ R} {m n : ℕ}

theorem coeff_eq_zero (hφ : IsHomogeneous φ n) {d : σ →₀ ℕ} (hd : d.degree ≠ n) :
    coeff d φ = 0 := by
  rw [degree_eq_weight_one] at hd
  exact IsWeightedHomogeneous.coeff_eq_zero hφ d hd

theorem inj_right (hm : IsHomogeneous φ m) (hn : IsHomogeneous φ n) (hφ : φ ≠ 0) : m = n := by
  obtain ⟨d, hd⟩ : ∃ d, coeff d φ ≠ 0 := exists_coeff_ne_zero hφ
  rw [← hm hd, ← hn hd]

theorem add (hφ : IsHomogeneous φ n) (hψ : IsHomogeneous ψ n) : IsHomogeneous (φ + ψ) n :=
  (homogeneousSubmodule σ R n).add_mem hφ hψ

theorem sum {ι : Type*} (s : Finset ι) (φ : ι → MvPolynomial σ R) (n : ℕ)
    (h : ∀ i ∈ s, IsHomogeneous (φ i) n) : IsHomogeneous (∑ i ∈ s, φ i) n :=
  (homogeneousSubmodule σ R n).sum_mem h

theorem mul (hφ : IsHomogeneous φ m) (hψ : IsHomogeneous ψ n) : IsHomogeneous (φ * ψ) (m + n) :=
  homogeneousSubmodule_mul m n <| Submodule.mul_mem_mul hφ hψ

theorem prod {ι : Type*} (s : Finset ι) (φ : ι → MvPolynomial σ R) (n : ι → ℕ)
    (h : ∀ i ∈ s, IsHomogeneous (φ i) (n i)) : IsHomogeneous (∏ i ∈ s, φ i) (∑ i ∈ s, n i) := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro
    simp only [isHomogeneous_one, Finset.sum_empty, Finset.prod_empty]
  · intro i s his IH h
    simp only [his, Finset.prod_insert, Finset.sum_insert, not_false_iff]
    apply (h i (by grind)).mul (IH _)
    grind

lemma C_mul (hφ : φ.IsHomogeneous m) (r : R) :
    (C r * φ).IsHomogeneous m := by
  simpa only [zero_add] using (isHomogeneous_C _ _).mul hφ

lemma _root_.MvPolynomial.isHomogeneous_C_mul_X (r : R) (i : σ) :
    (C r * X i).IsHomogeneous 1 :=
  (isHomogeneous_X _ _).C_mul _

lemma pow (hφ : φ.IsHomogeneous m) (n : ℕ) : (φ ^ n).IsHomogeneous (m * n) := by
  rw [show φ ^ n = ∏ _i ∈ Finset.range n, φ by simp]
  rw [show m * n = ∑ _i ∈ Finset.range n, m by simp [mul_comm]]
  apply IsHomogeneous.prod _ _ _ (fun _ _ ↦ hφ)

lemma _root_.MvPolynomial.isHomogeneous_X_pow (i : σ) (n : ℕ) :
    (X (R := R) i ^ n).IsHomogeneous n := by
  simpa only [one_mul] using (isHomogeneous_X _ _).pow n

lemma _root_.MvPolynomial.isHomogeneous_C_mul_X_pow (r : R) (i : σ) (n : ℕ) :
    (C r * X i ^ n).IsHomogeneous n :=
  (isHomogeneous_X_pow _ _).C_mul _

lemma eval₂ (hφ : φ.IsHomogeneous m) (f : R →+* MvPolynomial τ S) (g : σ → MvPolynomial τ S)
    (hf : ∀ r, (f r).IsHomogeneous 0) (hg : ∀ i, (g i).IsHomogeneous n) :
    (eval₂ f g φ).IsHomogeneous (n * m) := by
  apply IsHomogeneous.sum
  intro i hi
  rw [← zero_add (n * m)]
  apply IsHomogeneous.mul (hf _) _
  convert IsHomogeneous.prod _ _ (fun k ↦ n * i k) _
  · rw [Finsupp.mem_support_iff] at hi
    rw [← Finset.mul_sum, ← hφ hi, weight_apply]
    simp_rw [smul_eq_mul, Finsupp.sum, Pi.one_apply, mul_one]
  · rintro k -
    apply (hg k).pow

lemma map (hφ : φ.IsHomogeneous n) (f : R →+* S) : (map f φ).IsHomogeneous n := by
  simpa only [one_mul] using hφ.eval₂ _ _ (fun r ↦ isHomogeneous_C _ (f r)) (isHomogeneous_X _)

lemma aeval [Algebra R S] (hφ : φ.IsHomogeneous m)
    (g : σ → MvPolynomial τ S) (hg : ∀ i, (g i).IsHomogeneous n) :
    (aeval g φ).IsHomogeneous (n * m) :=
  hφ.eval₂ _ _ (fun _ ↦ isHomogeneous_C _ _) hg

section CommRing

-- In this section we shadow the semiring `R` with a ring `R`.
variable {R σ : Type*} [CommRing R] {φ ψ : MvPolynomial σ R} {n : ℕ}

theorem neg (hφ : IsHomogeneous φ n) : IsHomogeneous (-φ) n :=
  (homogeneousSubmodule σ R n).neg_mem hφ

theorem sub (hφ : IsHomogeneous φ n) (hψ : IsHomogeneous ψ n) : IsHomogeneous (φ - ψ) n :=
  (homogeneousSubmodule σ R n).sub_mem hφ hψ

end CommRing

/-- The homogeneous degree bounds the total degree.

See also `MvPolynomial.IsHomogeneous.totalDegree` when `φ` is non-zero. -/
lemma totalDegree_le (hφ : IsHomogeneous φ n) : φ.totalDegree ≤ n := by
  apply Finset.sup_le
  intro d hd
  rw [mem_support_iff] at hd
  simp_rw [Finsupp.sum, ← hφ hd, weight_apply, Pi.one_apply, smul_eq_mul, mul_one, Finsupp.sum,
    le_rfl]

theorem totalDegree (hφ : IsHomogeneous φ n) (h : φ ≠ 0) : totalDegree φ = n := by
  apply le_antisymm hφ.totalDegree_le
  obtain ⟨d, hd⟩ : ∃ d, coeff d φ ≠ 0 := exists_coeff_ne_zero h
  simp only [← hφ hd, MvPolynomial.totalDegree, Finsupp.sum]
  replace hd := Finsupp.mem_support_iff.mpr hd
  simp only [weight_apply, Pi.one_apply, smul_eq_mul, mul_one]
  -- Porting note: Original proof did not define `f`
  exact Finset.le_sup (f := fun s ↦ ∑ x ∈ s.support, s x) hd

theorem rename_isHomogeneous {f : σ → τ} (h : φ.IsHomogeneous n) :
    (rename f φ).IsHomogeneous n := by
  rw [← φ.support_sum_monomial_coeff, map_sum]; simp_rw [rename_monomial]
  apply IsHomogeneous.sum _ _ _ fun d hd ↦ isHomogeneous_monomial _ _
  intro d hd
  apply (Finsupp.sum_mapDomain_index_addMonoidHom fun _ ↦ .id ℕ).trans
  convert h (mem_support_iff.mp hd)
  simp only [weight_apply, AddMonoidHom.id_apply, Pi.one_apply, smul_eq_mul, mul_one]

theorem rename_isHomogeneous_iff {f : σ → τ} (hf : f.Injective) :
    (rename f φ).IsHomogeneous n ↔ φ.IsHomogeneous n := by
  refine ⟨fun h d hd ↦ ?_, rename_isHomogeneous⟩
  convert ← @h (d.mapDomain f) _
  · simp only [weight_apply, Pi.one_apply, smul_eq_mul, mul_one]
    exact Finsupp.sum_mapDomain_index_inj (h := fun _ ↦ id) hf
  · rwa [coeff_rename_mapDomain f hf]

lemma finSuccEquiv_coeff_isHomogeneous {N : ℕ} {φ : MvPolynomial (Fin (N + 1)) R} {n : ℕ}
    (hφ : φ.IsHomogeneous n) (i j : ℕ) (h : i + j = n) :
    ((finSuccEquiv _ _ φ).coeff i).IsHomogeneous j := by
  intro d hd
  rw [finSuccEquiv_coeff_coeff] at hd
  have h' : (weight 1) (Finsupp.cons i d) = i + j := by
    simpa [Finset.sum_subset_zero_on_sdiff (g := d.cons i)
     (d.cons_support (y := i)) (by simp) (fun _ _ ↦ rfl), ← h] using hφ hd
  simp only [weight_apply, Pi.one_apply, smul_eq_mul, mul_one, Finsupp.sum_cons,
    add_right_inj] at h' ⊢
  exact h'

-- TODO: develop API for `optionEquivLeft` and get rid of the `[Fintype σ]` assumption
lemma coeff_isHomogeneous_of_optionEquivLeft_symm
    [hσ : Finite σ] {p : Polynomial (MvPolynomial σ R)}
    (hp : ((optionEquivLeft R σ).symm p).IsHomogeneous n) (i j : ℕ) (h : i + j = n) :
    (p.coeff i).IsHomogeneous j := by
  obtain ⟨k, ⟨e⟩⟩ := Finite.exists_equiv_fin σ
  let e' := e.optionCongr.trans (_root_.finSuccEquiv _).symm
  let F := renameEquiv R e
  let F' := renameEquiv R e'
  let φ := F' ((optionEquivLeft R σ).symm p)
  have hφ : φ.IsHomogeneous n := hp.rename_isHomogeneous
  suffices IsHomogeneous (F (p.coeff i)) j by
    rwa [← (IsHomogeneous.rename_isHomogeneous_iff e.injective)]
  convert hφ.finSuccEquiv_coeff_isHomogeneous i j h using 1
  dsimp only [φ, F', F, renameEquiv_apply]
  rw [finSuccEquiv_rename_finSuccEquiv, AlgEquiv.apply_symm_apply]
  simp

open Polynomial in
private
lemma exists_eval_ne_zero_of_coeff_finSuccEquiv_ne_zero_aux
    {N : ℕ} {F : MvPolynomial (Fin (Nat.succ N)) R} {n : ℕ} (hF : IsHomogeneous F n)
    (hFn : ((finSuccEquiv R N) F).coeff n ≠ 0) :
    ∃ r, eval r F ≠ 0 := by
  have hF₀ : F ≠ 0 := by contrapose! hFn; simp [hFn]
  have hdeg : natDegree (finSuccEquiv R N F) < n + 1 := by
    linarith [natDegree_finSuccEquiv F, degreeOf_le_totalDegree F 0, hF.totalDegree hF₀]
  use Fin.cons 1 0
  have aux : ∀ i ∈ Finset.range n, constantCoeff ((finSuccEquiv R N F).coeff i) = 0 := by
    intro i hi
    rw [Finset.mem_range] at hi
    apply (hF.finSuccEquiv_coeff_isHomogeneous i (n-i) (by cutsat)).coeff_eq_zero
    simp only [Finsupp.degree_zero]
    rw [← Nat.sub_ne_zero_iff_lt] at hi
    exact hi.symm
  simp_rw [eval_eq_eval_mv_eval', eval_one_map, Polynomial.eval_eq_sum_range' hdeg,
    eval_zero, one_pow, mul_one, map_sum, Finset.sum_range_succ, Finset.sum_eq_zero aux, zero_add]
  contrapose! hFn
  ext d
  rw [coeff_zero]
  obtain rfl | hd := eq_or_ne d 0
  · apply hFn
  · contrapose! hd
    ext i
    rw [Finsupp.coe_zero, Pi.zero_apply]
    by_cases hi : i ∈ d.support
    · have := hF.finSuccEquiv_coeff_isHomogeneous n 0 (add_zero _) hd
      simp only [weight_apply, Pi.one_apply, smul_eq_mul, mul_one, Finsupp.sum] at this
      rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ ↦ zero_le')] at this
      exact this i hi
    · simpa using hi

section IsDomain

-- In this section we shadow the semiring `R` with a domain `R`.
variable {R σ : Type*} [CommRing R] [IsDomain R] {F G : MvPolynomial σ R} {n : ℕ}

open Cardinal Polynomial

private
lemma exists_eval_ne_zero_of_totalDegree_le_card_aux {N : ℕ} {F : MvPolynomial (Fin N) R} {n : ℕ}
    (hF : F.IsHomogeneous n) (hF₀ : F ≠ 0) (hnR : n ≤ #R) :
    ∃ r, eval r F ≠ 0 := by
  induction N generalizing n with
  | zero =>
    use 0
    contrapose! hF₀
    ext d
    simpa only [Subsingleton.elim d 0, eval_zero, coeff_zero] using hF₀
  | succ N IH =>
    have hdeg : natDegree (finSuccEquiv R N F) < n + 1 := by
      linarith [natDegree_finSuccEquiv F, degreeOf_le_totalDegree F 0, hF.totalDegree hF₀]
    obtain ⟨i, hi⟩ : ∃ i : ℕ, (finSuccEquiv R N F).coeff i ≠ 0 := by
      contrapose! hF₀
      exact (finSuccEquiv _ _).injective <| Polynomial.ext <| by simpa using hF₀
    have hin : i ≤ n := by
      contrapose! hi
      exact coeff_eq_zero_of_natDegree_lt <| (Nat.le_of_lt_succ hdeg).trans_lt hi
    obtain hFn | hFn := ne_or_eq ((finSuccEquiv R N F).coeff n) 0
    · exact hF.exists_eval_ne_zero_of_coeff_finSuccEquiv_ne_zero_aux hFn
    have hin : i < n := hin.lt_or_eq.elim id <| by aesop
    obtain ⟨j, hj⟩ : ∃ j, i + (j + 1) = n := (Nat.exists_eq_add_of_lt hin).imp <| by cutsat
    obtain ⟨r, hr⟩ : ∃ r, (eval r) (Polynomial.coeff ((finSuccEquiv R N) F) i) ≠ 0 :=
      IH (hF.finSuccEquiv_coeff_isHomogeneous _ _ hj) hi (.trans (by norm_cast; cutsat) hnR)
    set φ : R[X] := Polynomial.map (eval r) (finSuccEquiv _ _ F) with hφ
    have hφ₀ : φ ≠ 0 := fun hφ₀ ↦ hr <| by
      rw [← coeff_eval_eq_eval_coeff, ← hφ, hφ₀, Polynomial.coeff_zero]
    have hφR : φ.natDegree < #R := by
      refine lt_of_lt_of_le ?_ hnR
      norm_cast
      refine lt_of_le_of_lt natDegree_map_le ?_
      suffices (finSuccEquiv _ _ F).natDegree ≠ n by cutsat
      rintro rfl
      refine leadingCoeff_ne_zero.mpr ?_ hFn
      simpa using (finSuccEquiv R N).injective.ne hF₀
    obtain ⟨r₀, hr₀⟩ : ∃ r₀, Polynomial.eval r₀ φ ≠ 0 :=
      φ.exists_eval_ne_zero_of_natDegree_lt_card hφ₀ hφR
    use Fin.cons r₀ r
    rwa [eval_eq_eval_mv_eval']

/-- See `MvPolynomial.IsHomogeneous.eq_zero_of_forall_eval_eq_zero`
for a version that assumes `Infinite R`. -/
lemma eq_zero_of_forall_eval_eq_zero_of_le_card
    (hF : F.IsHomogeneous n) (h : ∀ r : σ → R, eval r F = 0) (hnR : n ≤ #R) :
    F = 0 := by
  contrapose! h
  -- reduce to the case where σ is finite
  obtain ⟨k, f, hf, F, rfl⟩ := exists_fin_rename F
  have hF₀ : F ≠ 0 := by rintro rfl; simp at h
  have hF : F.IsHomogeneous n := by rwa [rename_isHomogeneous_iff hf] at hF
  obtain ⟨r, hr⟩ := exists_eval_ne_zero_of_totalDegree_le_card_aux hF hF₀ hnR
  obtain ⟨r, rfl⟩ := (Function.factorsThrough_iff _).mp <| (hf.factorsThrough r)
  use r
  rwa [eval_rename]

/-- See `MvPolynomial.IsHomogeneous.funext`
for a version that assumes `Infinite R`. -/
lemma funext_of_le_card (hF : F.IsHomogeneous n) (hG : G.IsHomogeneous n)
    (h : ∀ r : σ → R, eval r F = eval r G) (hnR : n ≤ #R) :
    F = G := by
  rw [← sub_eq_zero]
  apply eq_zero_of_forall_eval_eq_zero_of_le_card (hF.sub hG) _ hnR
  simpa [sub_eq_zero] using h

/-- See `MvPolynomial.IsHomogeneous.eq_zero_of_forall_eval_eq_zero_of_le_card`
for a version that assumes `n ≤ #R`. -/
lemma eq_zero_of_forall_eval_eq_zero [Infinite R] {F : MvPolynomial σ R} {n : ℕ}
    (hF : F.IsHomogeneous n) (h : ∀ r : σ → R, eval r F = 0) : F = 0 := by
  apply eq_zero_of_forall_eval_eq_zero_of_le_card hF h
  exact (Cardinal.nat_lt_aleph0 _).le.trans <| Cardinal.infinite_iff.mp ‹Infinite R›

/-- See `MvPolynomial.IsHomogeneous.funext_of_le_card`
for a version that assumes `n ≤ #R`. -/
lemma funext [Infinite R] {F G : MvPolynomial σ R} {n : ℕ}
    (hF : F.IsHomogeneous n) (hG : G.IsHomogeneous n)
    (h : ∀ r : σ → R, eval r F = eval r G) : F = G := by
  apply funext_of_le_card hF hG h
  exact (Cardinal.nat_lt_aleph0 _).le.trans <| Cardinal.infinite_iff.mp ‹Infinite R›

end IsDomain

/-- The homogeneous submodules form a graded ring. This instance is used by `DirectSum.commSemiring`
and `DirectSum.algebra`. -/
instance HomogeneousSubmodule.gcommSemiring : SetLike.GradedMonoid (homogeneousSubmodule σ R) where
  one_mem := isHomogeneous_one σ R
  mul_mem _ _ _ _ := IsHomogeneous.mul

end IsHomogeneous

noncomputable section

open Finset

/-- `homogeneousComponent n φ` is the part of `φ` that is homogeneous of degree `n`.
See `sum_homogeneousComponent` for the statement that `φ` is equal to the sum
of all its homogeneous components. -/
def homogeneousComponent [CommSemiring R] (n : ℕ) : MvPolynomial σ R →ₗ[R] MvPolynomial σ R :=
  weightedHomogeneousComponent 1 n

section HomogeneousComponent

open Finset Finsupp

variable (n : ℕ) (φ ψ : MvPolynomial σ R)

theorem homogeneousComponent_mem :
    homogeneousComponent n φ ∈ homogeneousSubmodule σ R n :=
  weightedHomogeneousComponent_mem _ φ n

theorem coeff_homogeneousComponent (d : σ →₀ ℕ) :
    coeff d (homogeneousComponent n φ) = if d.degree = n then coeff d φ else 0 := by
  rw [degree_eq_weight_one]
  convert coeff_weightedHomogeneousComponent n φ d

theorem homogeneousComponent_apply :
    homogeneousComponent n φ = ∑ d ∈ φ.support with d.degree = n, monomial d (coeff d φ) := by
  simp_rw [degree_eq_weight_one]
  convert weightedHomogeneousComponent_apply n φ

theorem homogeneousComponent_isHomogeneous : (homogeneousComponent n φ).IsHomogeneous n :=
  weightedHomogeneousComponent_isWeightedHomogeneous n φ

@[simp]
theorem homogeneousComponent_zero : homogeneousComponent 0 φ = C (coeff 0 φ) :=
  weightedHomogeneousComponent_zero φ (fun _ => Nat.succ_ne_zero Nat.zero)

@[simp]
theorem homogeneousComponent_C_mul (n : ℕ) (r : R) :
    homogeneousComponent n (C r * φ) = C r * homogeneousComponent n φ :=
  weightedHomogeneousComponent_C_mul φ n r

theorem homogeneousComponent_eq_zero'
    (h : ∀ d : σ →₀ ℕ, d ∈ φ.support → d.degree ≠ n) :
    homogeneousComponent n φ = 0 := by
  simp_rw [degree_eq_weight_one] at h
  exact weightedHomogeneousComponent_eq_zero' n φ h

theorem homogeneousComponent_eq_zero (h : φ.totalDegree < n) : homogeneousComponent n φ = 0 := by
  apply homogeneousComponent_eq_zero'
  rw [totalDegree, Finset.sup_lt_iff (lt_of_le_of_lt (Nat.zero_le _) h)] at h
  intro d hd; exact ne_of_lt (h d hd)

theorem sum_homogeneousComponent :
    (∑ i ∈ range (φ.totalDegree + 1), homogeneousComponent i φ) = φ := by
  ext1 d
  suffices φ.totalDegree < d.support.sum d → 0 = coeff d φ by
    simpa [coeff_sum, coeff_homogeneousComponent]
  exact fun h => (coeff_eq_zero_of_totalDegree_lt h).symm

theorem homogeneousComponent_of_mem {m n : ℕ} {p : MvPolynomial σ R}
    (h : p ∈ homogeneousSubmodule σ R n) :
    homogeneousComponent m p = if m = n then p else 0 :=
  weightedHomogeneousComponent_of_mem h

end HomogeneousComponent

end

noncomputable section GradedAlgebra

/-- The homogeneous submodules form a graded ring.
This instance is used by `DirectSum.commSemiring` and `DirectSum.algebra`. -/
lemma HomogeneousSubmodule.gradedMonoid :
    SetLike.GradedMonoid (homogeneousSubmodule σ R) :=
  WeightedHomogeneousSubmodule.gradedMonoid

/-- The decomposition of `MvPolynomial σ R` into homogeneous submodules. -/
abbrev decomposition :
    DirectSum.Decomposition (homogeneousSubmodule σ R) :=
  weightedDecomposition R (1 : σ → ℕ)

/-- `MvPolynomial σ R` as a graded algebra, graded by the degree.
We do not make this a global instance because one may want to consider a different
graded algebra structure on `MvPolynomial σ R`, induced by another weight function.
To make it a local instance, you may use
`attribute [local instance] MvPolynomial.gradedAlgebra`.
-/
abbrev gradedAlgebra : GradedAlgebra (homogeneousSubmodule σ R) :=
  weightedGradedAlgebra R (1 : σ → ℕ)

theorem decomposition.decompose'_apply (φ : MvPolynomial σ R) (i : ℕ) :
    (decomposition.decompose' φ i : MvPolynomial σ R) = homogeneousComponent i φ :=
  weightedDecomposition.decompose'_apply R _ φ i

theorem decomposition.decompose'_eq :
    decomposition.decompose' = fun φ : MvPolynomial σ R =>
      DirectSum.mk (fun i : ℕ => ↥(homogeneousSubmodule σ R i)) (φ.support.image Finsupp.degree)
        fun m => ⟨homogeneousComponent m φ, homogeneousComponent_mem m φ⟩ := by
  rw [degree_eq_weight_one]
  rfl

end GradedAlgebra

end MvPolynomial
