/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.Algebra.MvPolynomial.Division
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.RingTheory.MvPolynomial.MonomialOrder.DegLex
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Tactic.ComputeDegree

/-!
# Irreducibility of linear and quadratic polynomials

* For `c : n →₀ R`, `MvPolynomial.sum_smul_X c` is the linear polynomial
  $\sum_i c_i X_i$ of $R[X_1\dots,X_n]$.

* `MvPolynomial.irreducible_sum_smul_X` : if the support of `c` is nontrivial,
  if `R` is a domain,
  and if the only common divisors to all `c i` are units,
  then `MvPolynomial.sum_smul_X c` is irreducible.

* For `c : n →₀ R`, `MvPolynomial.sum_X_mul_Y c` is the quadratic polynomial
  $\sum_i c_i X_i Y_i$ of $R[X_1\dots,X_n,Y_1,\dots,Y_n]$.
  It is constructed as an object of `MvPolynomial (n ⊕ n) R`,
  the first component of `n ⊕ n` represents the `X` indeterminates,
  and the second component represents the `Y` indeterminates.

* `MvPolynomial.irreducible_sum_smul_X_mul_Y` :
  if the support of `c` is nontrivial,
  the ring `R` is a domain,
  and the only divisors common to all `c i` are units,
  then `MvPolynomial.sum_smul_X_mul_Y c` is irreducible.

## TODO

* Treat the case of diagonal quadratic polynomials,
  $ \sum c_i X_i ^ 2$. For irreducibility, one will need that
  there are at least 3 nonzero values of `c`,
  and that the only common divisors to all `c i` are units.

* Addition of quadratic polynomial of both kinds are relevant too.

* Prove, over a field, that a polynomial of degree at most 2 whose quadratic
  part has rank at least 3 is irreducible.

* Cases of ranks 1 and 2 can be treated as well, but the answer depends
  on the terms of degree 0 and 1.
  Eg, $X^2-Y$ is irreducible, but $X^2$, $X^2-1$, $X^2-Y^2$, $X^2-Y$ are not.
  And $X^2+Y^2$ is irreducible over the reals but not over the complex numbers.

-/

@[expose] public section

theorem Function.nontrivial_of_nontrivial (α β : Type*) [Nontrivial (α → β)] :
    Nontrivial β := by
  obtain ⟨x, y, h⟩ := exists_pair_ne (α → β)
  rw [ne_eq, funext_iff, not_forall] at h
  obtain ⟨a, h⟩ := h
  exact nontrivial_of_ne _ _ h

theorem Finsupp.nontrivial_of_nontrivial (α β : Type*) [Zero β] [Nontrivial (α →₀ β)] :
    Nontrivial β := by
  obtain ⟨x, y, h⟩ := exists_pair_ne (α →₀ β)
  rw [ne_eq, Finsupp.ext_iff, not_forall] at h
  obtain ⟨a, h⟩ := h
  exact nontrivial_of_ne _ _ h

def RelativelyIrreducible (R : Type*) {A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (x : A) : Prop :=
  ∀ y z : A, y * z = x → (∃ r : R, algebraMap R A r = y) ∨ (∃ r : R, algebraMap R A r = z)

namespace RelativelyIrreducible

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

variable (R A) in
lemma zero [IsDomain A] :
    RelativelyIrreducible R (0 : A) := by
  intro y z h
  rw [mul_eq_zero] at h
  apply h.imp
  all_goals
    rintro rfl
    use 0
    rw [map_zero]

lemma of_map_of_injective {B : Type*} [CommRing B] [Algebra R B]
    (f : A →ₐ[R] B) (hf : Function.Injective f)
    (x : A) (hx : RelativelyIrreducible R (f x)) :
    RelativelyIrreducible R x := by
  rintro y z rfl
  specialize hx (f y) (f z) (map_mul f y z).symm
  apply hx.imp
  all_goals
    rintro ⟨r, hr⟩
    use r
    apply hf
    simpa

end RelativelyIrreducible

namespace Polynomial


variable {R : Type*} [CommRing R]

-- move this
instance : IsLocalHom (C : _ →+* Polynomial R) where
  map_nonunit := by classical simp +contextual [isUnit_iff_coeff_isUnit_isNilpotent, coeff_C]

/-- The degree 1 polynomial `a • X + C b` is relatively irreducible. -/
theorem relativelyIrreducible_smul_X_add_C [IsDomain R] (a : R) (b : R) :
    RelativelyIrreducible R (a • X + C b : Polynomial R) := by
  intro f g h
  have hd : (f * g).degree ≤ 1 := by
    rw [h]; compute_degree!
  rw [degree_mul] at hd
  have : f.degree ≤ 0 ∨ g.degree ≤ 0 := by
    clear h
    contrapose! hd
    rcases hd with ⟨hf, hg⟩
    obtain ⟨hf0, hg0⟩ : f ≠ 0 ∧ g ≠ 0 := by
      rw [← not_or]
      rintro (rfl | rfl) <;> simp_all
    rw [degree_eq_natDegree hf0, degree_eq_natDegree hg0, Nat.cast_withBot, Nat.cast_withBot] at *
    rw [← WithBot.coe_add, ← WithBot.coe_one, WithBot.coe_lt_coe]
    rw [WithBot.coe_pos] at hf hg
    grind
  apply this.imp
  all_goals
    intro H
    rw [eq_C_of_degree_le_zero H]
    simp

end Polynomial

namespace MvPolynomial

open scoped Polynomial

section

variable {n : Type*} {R : Type*} [CommRing R]

theorem optionEquivLeft_coeff_coeff'
    (p : MvPolynomial (Option n) R) (m : ℕ) (d : n →₀ ℕ) :
    coeff d (((optionEquivLeft R n) p).coeff m) = p.coeff (d.optionElim m) := by
  induction p using MvPolynomial.induction_on' generalizing d m with
  | monomial j r =>
    rw [optionEquivLeft_monomial]
    classical
    simp +contextual [Finsupp.ext_iff, Option.forall, Polynomial.coeff_monomial, apply_ite]
  | add p q hp hq => simp only [map_add, Polynomial.coeff_add, coeff_add, hp, hq]

lemma irreducible_mul_X_add [IsDomain R]
    (f g : MvPolynomial n R) (i : n) (hf0 : f ≠ 0) (hif : i ∉ f.vars) (hig : i ∉ g.vars)
    (h : ∀ p, p ∣ f → p ∣ g → IsUnit p) :
    Irreducible (f * X i + g) := by
  classical
  let e₁ := renameEquiv R (σ := n) (Equiv.optionSubtypeNe i).symm
  let e₂ := optionEquivLeft R {j // j ≠ i}
  let e := e₁.trans e₂
  have heX : e (X i) = .X := by simp [e, e₁, e₂, optionEquivLeft_X_none]
  suffices ∀ {p}, i ∉ p.vars → e p = .C ((e p).coeff 0) by
    rw [← MulEquiv.irreducible_iff e, map_add, map_mul, heX, this hif, this hig,
      ← Polynomial.smul_eq_C_mul]
    apply Polynomial.irreducible_smul_X_add_C
    · contrapose! hf0
      apply e.injective
      rw [this hif, hf0, map_zero, map_zero]
    · intro p hpf hpg
      refine isUnit_of_map_unit Polynomial.C _ (isUnit_of_map_unit e.symm _ ?_)
      apply h
      · replace hpf := map_dvd e.symm <| map_dvd Polynomial.C hpf
        rwa [← this hif, e.symm_apply_apply] at hpf
      · replace hpg := map_dvd e.symm <| map_dvd Polynomial.C hpg
        rwa [← this hig, e.symm_apply_apply] at hpg
  intro p hp
  apply Polynomial.eq_C_of_degree_le_zero
  rw [Polynomial.degree_le_iff_coeff_zero]
  intro m hm
  ext d
  suffices ((rename (Equiv.optionSubtypeNe i).symm) p).coeff (d.optionElim m) = 0 by
    simpa [e, e₁, e₂, optionEquivLeft_coeff_coeff']
  rw [coeff_rename_eq_zero]
  intro d' hd'
  contrapose! hp
  rw [mem_vars]
  rw [← mem_support_iff] at hp
  refine ⟨_, hp, ?_⟩
  rw [Finsupp.mem_support_iff]
  obtain rfl : d' i = m := by simpa [Finsupp.mapDomain_equiv_apply] using congr($hd' none)
  simp_all [ne_of_gt]

lemma irreducible_of_pairwise_disjoint [IsDomain R]
    (f : MvPolynomial n R) (h0 : f.support.Nontrivial)
    (h1 : Set.PairwiseDisjoint (f.support : Set (n →₀ ℕ)) (fun d ↦ d.support))
    (h2 : ∀ r, (∀ d, r ∣ f.coeff d) → IsUnit r) :
    Irreducible f := by
  obtain ⟨d, hd, hd0⟩ := h0.exists_ne 0
  rw [ne_eq, ← Finsupp.support_eq_empty, ← ne_eq, ← Finset.nonempty_iff_ne_empty] at hd0
  rcases hd0 with ⟨i, hi⟩
  have hfd : f.coeff d ≠ 0 := by simpa [mem_support_iff] using hd
  let φ : MvPolynomial n R := monomial (d - .single i 1) (f.coeff d)
  let ψ : MvPolynomial n R := f - φ * X i
  have hf : f = φ * X i + ψ := by grind
  rw [hf]
  apply irreducible_mul_X_add
  · simp [φ, monomial_eq_zero, hfd]
  · sorry
  · sorry
  · intro p hpφ hpψ
    simp_rw [φ, dvd_monomial_iff_exists hfd] at hpφ
    obtain ⟨m, b, hm, hb, rfl⟩ := hpφ
    obtain rfl : m = 0 := by sorry
    simp_rw [isUnit_iff_eq_C_of_isReduced, ← C_apply, C_inj]
    refine ⟨b, ?_, rfl⟩
    apply h2
    intro k
    obtain rfl | hk := eq_or_ne k d
    · exact hb
    by_cases hkf : coeff k f = 0
    · simp [hkf]
    suffices coeff k (φ * X i) = 0 by
      rw [hf, coeff_add, this, zero_add]
      rw [← C_apply, C_dvd_iff_dvd_coeff] at hpψ
      apply hpψ
    classical
    rw [coeff_mul_X', ite_eq_right_iff]
    intro hik
    rw [← ne_eq, ← mem_support_iff] at hkf
    have := h1 hkf hd hk
    simp_all [Function.onFun, disjoint_iff, Finset.eq_empty_iff_forall_notMem]

lemma irreducible_mul_X_add' [IsDomain R]
    (f g : MvPolynomial n R) (i : n) (hf0 : f ≠ 0) (hif : i ∉ f.vars) (hig : i ∉ g.vars) :
    Irreducible (f * X i + g) where
  not_isUnit h := by
    rw [isUnit_iff_eq_C_of_isReduced] at h
    obtain ⟨r, hr, h⟩ := h
    obtain ⟨j, hj⟩ := exists_coeff_ne_zero hf0
    apply hj
    suffices coeff (j + Finsupp.single i 1) g = 0 ∧ coeff (j + Finsupp.single i 1) (C r) = 0 by
      have aux := congr(coeff (j + Finsupp.single i 1) $h)
      simpa [this] using aux
    clear hj
    constructor
    · contrapose! hig
      rw [mem_vars]
      simp_rw [← mem_support_iff] at hig
      refine ⟨_, hig, ?_⟩
      simp
    · classical
      rw [coeff_C, if_neg]
      intro hji
      simpa using congr($hji i)
  isUnit_or_isUnit := by
    intro p q hpq
    have hd : (p * q).degreeOf i ≤ 1 := by
      sorry
    sorry

lemma irreducible_of_relativelyIrreducible
    (f : MvPolynomial n R) (hf : RelativelyIrreducible R f)
    (h0 : ¬ IsUnit f) (h : ∀ r, (∀ i, r ∣ f.coeff i) → IsUnit r) :
    Irreducible f where
  not_isUnit := h0
  isUnit_or_isUnit p q hpq := by
    apply (hf p q hpq.symm).imp
    all_goals
      rintro ⟨r, rfl⟩
      apply IsUnit.map
      apply h
      intro i
      rw [hpq]
      simp [mul_comm _ (C _)]

lemma relativelyIrreducible_of_irreducible [IsReduced R]
    (f : MvPolynomial n R) (hf : Irreducible f) :
    RelativelyIrreducible R f := by
  intro y z hyz
  apply (hf.isUnit_or_isUnit hyz.symm).imp
  all_goals
    rw [isUnit_iff_eq_C_of_isReduced]
    rintro ⟨r, hr, rfl⟩
    simp

lemma eq_C_and_dvd_or_eq_C_and_dvd_aux [IsDomain R] (n : ℕ)
    (c : Fin n → R) :
    RelativelyIrreducible R (∑ i, C (c i) * X i) := by
  induction n with
  | zero => simpa using RelativelyIrreducible.zero R (MvPolynomial _ R)
  | succ n ih =>
    let e := finSuccEquiv R n
    apply RelativelyIrreducible.of_map_of_injective e.toAlgHom e.injective
    rw [Fin.sum_univ_succ]
    simp [e, finSuccEquiv_X_zero, finSuccEquiv_X_succ]
    simp only [← algebraMap_eq, AlgEquiv.commutes, Polynomial.C_eq_algebraMap,
      IsScalarTower.algebraMap_eq R (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) R)[X],
      RingHom.comp_apply, ← map_mul, ← map_sum]
    simp only [← Polynomial.C_eq_algebraMap, ← Polynomial.smul_eq_C_mul]
    sorry

lemma eq_C_and_dvd_or_eq_C_and_dvd
    (p : MvPolynomial n R) (hp : p.totalDegree = 1)
    (f g : MvPolynomial n R) (hfg : f * g = p) :
    (∃ r : R, f = C r ∧ ∀ i, r ∣ coeff (Finsupp.single i 1) p) ∨
    (∃ r : R, g = C r ∧ ∀ i, r ∣ coeff (Finsupp.single i 1) p) := by
  sorry

end

section
/-! ## The quadratic polynomial $$\sum_{i=1}^n X_i Y_i$$. -/

open Polynomial

variable {n : Type*} {R : Type*} [CommRing R]

/-- The linear polynomial $$\sum_i c_i X_i$$. -/
noncomputable def sum_smul_X :
    (n →₀ R) →ₗ[R] MvPolynomial n R :=
  Finsupp.linearCombination R X

variable (c : n →₀ R)

theorem sum_smul_X_eq :
    sum_smul_X c = c.sum (fun i r ↦ r • X i) := by
  rw [sum_smul_X, Finsupp.linearCombination_apply]

@[simp] theorem coeff_zero_sum_smul_X (c : n →₀ R) :
    coeff 0 (sum_smul_X c) = 0 := by
  classical
  rw [sum_smul_X_eq, ← lcoeff_apply, map_finsuppSum]
  aesop

@[simp]
theorem coeff_single_sum_smul_X (i : n) :
    coeff (Finsupp.single i 1) (sum_smul_X c) = c i := by
  classical
  rw [sum_smul_X, Finsupp.linearCombination_apply, ← lcoeff_apply,
    map_finsuppSum, Finsupp.sum_eq_single i]
  · simp [map_smul, lcoeff_apply]
  · intro j _ hj
    rw [map_smul, lcoeff_apply, coeff_X', if_neg, smul_zero]
    contrapose hj
    apply Finsupp.single_left_injective one_ne_zero hj
  · simp

theorem totalDegree_sum_smul_X (hc_ne_zero : c ≠ 0) :
    (sum_smul_X c).totalDegree = 1 := by
  classical
  have : Nontrivial (n →₀ R) := nontrivial_of_ne c 0 hc_ne_zero
  have : Nontrivial R := Finsupp.nontrivial_of_nontrivial n R
  apply le_antisymm
  · rw [sum_smul_X_eq, Finsupp.sum]
    apply totalDegree_finsetSum_le
    simp [le_trans (totalDegree_smul_le _ _)]
  · rw [Nat.one_le_iff_ne_zero, ne_eq, totalDegree_eq_zero_iff_eq_C,
      coeff_zero_sum_smul_X, map_zero]
    intro h
    apply hc_ne_zero
    ext i
    rw [← coeff_single_sum_smul_X]
    simp [h]

variable (R) in
/-- The isomorphism from multivariate polynomials in `n` indeterminates to
polynomials with coefficients in `n - 1` indeterminates. -/
private noncomputable
def φ [DecidableEq n] (i : n) :
    MvPolynomial n R ≃ₐ[R] (MvPolynomial {x // x ≠ i} R)[X] :=
  (renameEquiv R (Equiv.optionSubtypeNe i).symm).trans (optionEquivLeft R {x // x ≠ i})

private
theorem φ_X_self (i : n) [DecidableEq n] :
    φ R i (X i) = Polynomial.X := by
  simp only [φ, ne_eq, AlgEquiv.trans_apply, renameEquiv_apply, rename_X,
    Equiv.optionSubtypeNe_symm_apply, ↓reduceDIte]
  apply optionEquivLeft_X_none

private
theorem φ_X_of_ne [DecidableEq n] {i j : n} (hj : j ≠ i) :
    φ R i (X j) = Polynomial.C (X ⟨j, hj⟩) := by
  simp only [φ, AlgEquiv.trans_apply, renameEquiv_apply,
    rename_X, Equiv.optionSubtypeNe_symm_apply]
  rw [dif_neg hj, optionEquivLeft_X_some]

private
theorem φ_sum_smul_X_eq [DecidableEq n] (i : n) :
    φ R i (sum_smul_X c) = c i • Polynomial.X +
      Polynomial.C (sum_smul_X (c.subtypeDomain (fun x ↦ x ≠ i))) := by
  simp only [sum_smul_X_eq, Finsupp.sum]
  rw [Finset.sum_subset (s₂ := insert i c.support)
    (Finset.subset_insert i c.support) (fun x _ hx' ↦ by aesop)]
  rw [Finset.sum_eq_add_sum_diff_singleton (Finset.mem_insert_self i c.support),
    map_add, map_smul, φ_X_self, add_right_inj]
  rw [map_sum]
  rw [Finset.sum_bij'
    (f := fun x ↦ φ R i (c x • X x))
    (g := fun y : {x : n // x ≠ i} ↦ Polynomial.C (c (y : n) • X (R := R) y))
    (i := fun x hx ↦ (⟨x, And.right (by simpa using hx)⟩ : {x // x ≠ i}))
    (j := fun y hy ↦ y)]
  pick_goal 6
  · intro j hj
    simp only [ne_eq, map_smul]
    rw [φ_X_of_ne (And.right (by simpa using hj)),
      MvPolynomial.smul_eq_C_mul, map_mul]
    simp [Algebra.smul_def]
  all_goals aesop

theorem X_dvd_sum_smul_X_iff (i : n) :
    X i ∣ sum_smul_X c ↔ c.support ⊆ {i} := by
  refine ⟨fun h_dvd ↦ ?_, fun hci ↦ ?_⟩
  · by_contra hci
    classical
    have : ∃ j, c j ≠ 0 ∧ j ≠ i := by
      simpa [Finset.subset_iff] using hci
    obtain ⟨j, hj, hji⟩ := this
    apply hj
    have : φ R i (X i) ∣ φ R i (sum_smul_X c) := by
      simpa using (φ R i).toRingHom.map_dvd h_dvd
    rw [φ_sum_smul_X_eq c, φ_X_self] at this
    rw [← algebraMap_smul (MvPolynomial {x // x ≠ i} R) (c i), Polynomial.smul_eq_C_mul,
        dvd_add_right (dvd_mul_left ..), Polynomial.X_dvd_iff, Polynomial.coeff_C_zero] at this
    simpa using congr(coeff (Finsupp.single ⟨j, hji⟩ 1) $this)
  · rw [sum_smul_X_eq, Finsupp.sum_eq_single i]
    · rw [smul_eq_C_mul]
      exact dvd_mul_left (X i) (C (c i))
    · intro j hj hji
      suffices c j = 0 by simp [this]
      rw [← Finsupp.notMem_support_iff]
      contrapose hji
      simpa using hci hji
    · simp

theorem irreducible_sum_smul_X [IsDomain R]
    (hc_nontrivial : c.support.Nontrivial)
    (hc_gcd : ∀ r, (∀ i, r ∣ c i) → IsUnit r) :
    Irreducible (sum_smul_X c) where
  not_isUnit h := by
    apply not_isUnit_zero (M₀ := R)
    simp [MvPolynomial.isUnit_iff_totalDegree_of_isReduced] at h
  isUnit_or_isUnit p q hpq := by
    wlog hp : p.totalDegree ≤ q.totalDegree generalizing p q hpq
    · rw [mul_comm] at hpq
      rw [or_comm]
      exact this q p hpq (Nat.le_of_not_le hp)
    have hpq' := congr(MvPolynomial.totalDegree $hpq)
    rw [totalDegree_sum_smul_X c ?_, eq_comm, totalDegree_mul_of_isDomain,
      Nat.add_eq_one_iff] at hpq'
    · rcases hpq' with (h | h)
      · left
        rw [totalDegree_eq_zero_iff_eq_C] at h
        rw [h.1]
        apply IsUnit.map
        apply hc_gcd (coeff 0 p)
        intro i
        rw [← coeff_single_sum_smul_X c i, hpq]
        nth_rewrite 2 [h.1]
        simp
      · exfalso
        simp [h.1, h.2] at hp
    all_goals aesop

/-- The quadratic polynomial $$\sum_i c_i X_i Y_i$$. -/
noncomputable def sum_smul_X_mul_Y :
    (n →₀ R) →ₗ[R] MvPolynomial (n ⊕ n) R :=
  Finsupp.linearCombination R (fun i ↦ X (.inl i) * X (.inr i))

variable (c : n →₀ R)

lemma sum_smul_X_mul_Y_eq :
    sum_smul_X_mul_Y c = c.sum fun i a ↦ a • X (.inl i) * X (.inr i) := by
  simp [sum_smul_X_mul_Y, Finsupp.linearCombination_apply]

theorem irreducible_sum_smul_X_mul_Y [IsDomain R]
    (hc : c.support.Nontrivial)
    (h_dvd : ∀ r, (∀ i, r ∣ c i) → IsUnit r) :
    Irreducible (sum_smul_X_mul_Y c) := by
  classical
  let d : n →₀ MvPolynomial n R :=
  { toFun i := c i • X i
    support := c.support
    mem_support_toFun i := by aesop }
  let h := sumRingEquiv R n n
  suffices h (sum_smul_X_mul_Y c) = sum_smul_X d by
    rw [← MulEquiv.irreducible_iff (sumRingEquiv R n n)]
    rw [this]
    refine irreducible_sum_smul_X d hc ?_
    intro r hr
    simp only [Finsupp.coe_mk, d] at hr
    suffices r.totalDegree = 0 by
      rw [totalDegree_eq_zero_iff_eq_C] at this
      rw [this]
      apply IsUnit.map C
      apply h_dvd
      intro i
      obtain ⟨p, hp⟩ := hr i
      replace hp := congr(coeff (Finsupp.single i 1) $hp)
      rw [this] at hp
      exact ⟨coeff (Finsupp.single i 1) p, by simpa using hp⟩
    suffices ∃ i ∈ c.support, r ∣ C (c i) by
      obtain ⟨i, hi, hri⟩ := this
      rw [← Nat.le_zero]
      convert totalDegree_le_of_dvd_of_isDomain hri ?_
      · simp
      · simpa using hi
    by_contra! hr'
    obtain ⟨i, hi : i ∈ c.support, j, hj : j ∈ c.support, hij⟩ := hc
    have hri := hr i
    simp only [smul_eq_C_mul, mul_comm, dvd_X_mul_iff] at hri
    obtain ⟨⟨s, hrs⟩, hrs'⟩ := Or.resolve_left hri (hr' i hi)
    have hrj := hr j
    simp only [smul_eq_C_mul, mul_comm, hrs] at hrj
    obtain ⟨t, ht⟩ := hrj
    rw [mul_assoc, mul_comm s, mul_assoc] at ht
    have : X i ∣ X j * (C (c j)) :=
      dvd_of_mul_right_eq (t * s) ht.symm
    rw [dvd_X_mul_iff] at this
    rcases this with (this | this)
    · obtain ⟨u, hu⟩ := this
      have : X i ∣ C (c j) := dvd_of_mul_right_eq u hu.symm
      rw [Finsupp.mem_support_iff] at hj
      rw [dvd_C_iff_exists hj] at this
      obtain ⟨u, ⟨v, huv⟩, this⟩ := this
      apply hj
      rw [huv]
      convert zero_mul _
      simpa using congr(coeff 0 $this.symm)
    · apply hij
      exact (X_dvd_X.mp this.1).symm
  simp only [sum_smul_X_mul_Y_eq, sum_smul_X_eq, map_finsuppSum]
  rw [Finsupp.sum, Finsupp.sum]
  rw [Finset.sum_congr rfl]
  intro i _
  simp [h, d, sumRingEquiv, Algebra.smul_def, mul_assoc,
    mul_comm (X i) (C _)]

end

end MvPolynomial
