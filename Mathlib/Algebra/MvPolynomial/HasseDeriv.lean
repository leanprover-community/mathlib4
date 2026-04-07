/-
Copyright (c) 2026 Elias Judin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin
-/
module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.MvChoose
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Algebra.Polynomial.HasseDeriv
public import Mathlib.Data.Finsupp.Antidiagonal
public import Mathlib.Data.Finsupp.Weight

/-!
# Hasse derivatives of multivariate polynomials

This file defines Hasse derivatives for multivariate polynomials. For a multi-index
`i : σ →₀ ℕ`, the map `MvPolynomial.hasseDeriv i` is the `R`-linear endomorphism of
`MvPolynomial σ R` sending the monomial $r X^k$ to $\binom{k}{i} r X^{k-i}$, where
$\binom{k}{i}$ is the multivariate binomial coefficient `MvPolynomial.mvChoose k i`
(see `Mathlib.Algebra.MvPolynomial.MvChoose`).

## Main declarations

* `MvPolynomial.hasseDeriv`
* `MvPolynomial.hasseDeriv_monomial`
* `MvPolynomial.hasseDeriv_coeff`
* `MvPolynomial.hasseDeriv_zero`
* `MvPolynomial.hasseDeriv_comp`
* `MvPolynomial.hasseDeriv_single_one`
* `MvPolynomial.hasseDeriv_rename`
* `MvPolynomial.finOneAlgEquiv_hasseDeriv`
* `MvPolynomial.hasseDeriv_eq_zero_of_totalDegree_lt_degree`
* `MvPolynomial.totalDegree_hasseDeriv_le`

See `Mathlib.RingTheory.MvPolynomial.HasseDeriv` for the interaction with homogeneous
components.

## Tags

multivariate polynomial, Hasse derivative
-/

@[expose] public section

noncomputable section

namespace MvPolynomial

open Finsupp
open scoped BigOperators

variable {σ τ R : Type*} [CommSemiring R]

/-! ### Hasse derivatives -/

/-- The Hasse derivative $\partial^{[i]}$ of multivariate polynomials. -/
def hasseDeriv (i : σ →₀ ℕ) : MvPolynomial σ R →ₗ[R] MvPolynomial σ R :=
  Finsupp.lsum R fun k ↦ (mvChoose k i : R) • MvPolynomial.monomial (k - i)

/-- On a monomial $r X^k$, the Hasse derivative is $\binom{k}{i} r X^{k-i}$. -/
@[simp]
theorem hasseDeriv_monomial (i k : σ →₀ ℕ) (r : R) :
    hasseDeriv i (MvPolynomial.monomial k r) =
      MvPolynomial.monomial (k - i) ((mvChoose k i : R) * r) := by
  classical
  have h : hasseDeriv i (MvPolynomial.monomial k r) =
      ((mvChoose k i : R) • MvPolynomial.monomial (k - i)) r := by
    simpa [hasseDeriv, MvPolynomial.single_eq_monomial] using
      Finsupp.lsum_single (σ := RingHom.id R) (S := R)
        (f := fun k ↦ (mvChoose k i : R) • MvPolynomial.monomial (k - i)) k r
  simpa [LinearMap.smul_apply, MvPolynomial.smul_monomial, smul_eq_mul] using h

lemma hasseDeriv_monomial_eq_prod_choose [Fintype σ] (i k : σ →₀ ℕ) (r : R) :
    hasseDeriv i (MvPolynomial.monomial k r) =
      MvPolynomial.monomial (k - i) (((∏ j : σ, (k j).choose (i j)) : R) * r) := by
  classical
  simp [mvChoose_eq_prod_choose, hasseDeriv_monomial]

/-- The coefficient of $X^m$ in `hasseDeriv i P` is $\binom{m + i}{i}$ times the
coefficient of $X^{m+i}$ in `P`. -/
theorem hasseDeriv_coeff (i : σ →₀ ℕ) (P : MvPolynomial σ R) (m : σ →₀ ℕ) :
    coeff m (hasseDeriv i P) = (mvChoose (m + i) i : R) * coeff (m + i) P := by
  classical
  refine MvPolynomial.induction_on' P (fun k r => ?_) (fun p q hp hq => ?_)
  · by_cases hk : k = m + i
    · subst hk
      have hik : i ≤ m + i := Finsupp.le_def.2 fun x =>
        (Nat.le_add_right (i x) (m x)).trans (le_of_eq (add_comm (i x) (m x)))
      simp [hasseDeriv_monomial, coeff_monomial, mvChoose_of_le hik]
    · have hcoeff : coeff (m + i) (MvPolynomial.monomial k r : MvPolynomial σ R) = 0 := by
        simp [coeff_monomial, hk]
      by_cases hik : i ≤ k
      · have hkm : k - i ≠ m := by
          intro hkm
          have hk' : k - i + i = m + i := by simp [hkm]
          have hk'' : k = m + i := by
            rw [tsub_add_cancel_of_le hik] at hk'
            exact hk'
          exact hk hk''
        simp [hasseDeriv_monomial, coeff_monomial, hkm, hcoeff]
      · simp [hasseDeriv_monomial, mvChoose_of_not_le (k := k) (i := i) hik, hcoeff]
  · simp [hp, hq, coeff_add, mul_add]

/-- The Hasse derivative of order $0$ is the identity. -/
@[simp]
theorem hasseDeriv_zero :
    hasseDeriv (R := R) (0 : σ →₀ ℕ) =
      (LinearMap.id : MvPolynomial σ R →ₗ[R] MvPolynomial σ R) := by
  classical
  refine LinearMap.ext fun p ↦ ?_
  refine MvPolynomial.induction_on' p (fun k r => ?_) (fun p q hp hq => ?_)
  · simp
  · simp [hp, hq]

/-- The composition formula
$\partial^{[i]} \circ \partial^{[j]} = \binom{i + j}{i} \partial^{[i+j]}$. -/
theorem hasseDeriv_comp (i j : σ →₀ ℕ) :
    (hasseDeriv (R := R) i).comp (hasseDeriv j) =
      (mvChoose (i + j) i : R) • hasseDeriv (R := R) (i + j) := by
  classical
  refine LinearMap.ext fun p ↦ ?_
  refine MvPolynomial.induction_on' p (fun k r => ?_) (fun p q hp hq => ?_)
  · have h :
        mvChoose k j * mvChoose (k - j) i =
          mvChoose k (i + j) * mvChoose (i + j) i := by
      have hsymm : mvChoose (i + j) j = mvChoose (i + j) i := by
        simpa [add_comm] using (mvChoose_symm_add (σ := σ) j i)
      calc
        mvChoose k j * mvChoose (k - j) i =
            mvChoose k (i + j) * mvChoose (i + j) j := by
          simpa [add_comm, add_left_comm, add_assoc] using (mvChoose_mul (σ := σ) k j i)
        _ = mvChoose k (i + j) * mvChoose (i + j) i := by simp only [hsymm]
    have h' :
        (mvChoose k j : R) * (mvChoose (k - j) i : R) =
          (mvChoose k (i + j) : R) * (mvChoose (i + j) i : R) := by
      have hcast :
          ((mvChoose k j * mvChoose (k - j) i : ℕ) : R) =
            ((mvChoose k (i + j) * mvChoose (i + j) i : ℕ) : R) :=
        congrArg (fun n : ℕ => (n : R)) h
      simpa [Nat.cast_mul] using hcast
    have h'' :
        r * (mvChoose k j : R) * (mvChoose (k - j) i : R) =
          r * (mvChoose k (i + j) : R) * (mvChoose (i + j) i : R) := by
      calc
        r * (mvChoose k j : R) * (mvChoose (k - j) i : R) =
            r * ((mvChoose k j : R) * (mvChoose (k - j) i : R)) := by
          rw [mul_assoc]
        _ = r * ((mvChoose k (i + j) : R) * (mvChoose (i + j) i : R)) := by
          rw [h']
        _ = r * (mvChoose k (i + j) : R) * (mvChoose (i + j) i : R) := by
          rw [mul_assoc]
    simp [LinearMap.comp_apply, LinearMap.smul_apply, hasseDeriv_monomial,
      MvPolynomial.smul_monomial, smul_eq_mul, tsub_tsub, add_comm, mul_comm, h'']
  · have hp' :
        hasseDeriv i (hasseDeriv j p) =
          (mvChoose (i + j) i : R) • hasseDeriv (i + j) p := by
      simpa [LinearMap.comp_apply] using hp
    have hq' :
        hasseDeriv i (hasseDeriv j q) =
          (mvChoose (i + j) i : R) • hasseDeriv (i + j) q := by
      simpa [LinearMap.comp_apply] using hq
    simp [hp', hq']

/-- The multivariate Leibniz rule
$\partial^{[i]} (P Q) = \sum_{p + q = i} \partial^{[p]} P \, \partial^{[q]} Q$. -/
theorem hasseDeriv_mul [DecidableEq σ] (i : σ →₀ ℕ) (P Q : MvPolynomial σ R) :
    hasseDeriv i (P * Q) =
      ∑ p ∈ Finset.antidiagonal i, hasseDeriv p.1 P * hasseDeriv p.2 Q := by
  classical
  refine MvPolynomial.induction_on' P (fun a r ↦ ?_) (fun P₁ P₂ hP₁ hP₂ ↦ ?_)
  · refine MvPolynomial.induction_on' Q (fun b s ↦ ?_) (fun Q₁ Q₂ hQ₁ hQ₂ ↦ ?_)
    · have hsum :
          ∑ p ∈ Finset.antidiagonal i,
              MvPolynomial.monomial (a + b - i)
                ((((mvChoose a p.1 * mvChoose b p.2 : ℕ) : R) * (r * s))) =
            MvPolynomial.monomial (a + b - i)
              ((((∑ p ∈ Finset.antidiagonal i, mvChoose a p.1 * mvChoose b p.2 : ℕ) : R) *
                (r * s))) := by
        ext m
        by_cases hm : m = a + b - i
        · subst hm
          simp [MvPolynomial.coeff_sum, Nat.cast_sum, Finset.sum_mul]
        · simp [MvPolynomial.coeff_sum, hm, eq_comm]
      have haux :
          ∀ p : (σ →₀ ℕ) × (σ →₀ ℕ), p ∈ Finset.antidiagonal i →
            hasseDeriv p.1 (MvPolynomial.monomial a r) *
                hasseDeriv p.2 (MvPolynomial.monomial b s) =
              MvPolynomial.monomial (a + b - i)
                ((((mvChoose a p.1 * mvChoose b p.2 : ℕ) : R) * (r * s))) := by
        intro p hp
        have hp₁₂ : p.1 + p.2 = i := Finset.mem_antidiagonal.mp hp
        by_cases hpa : p.1 ≤ a
        · by_cases hpb : p.2 ≤ b
          · have hexp :
                a - p.1 + (b - p.2) = a + b - i := by
              calc
                a - p.1 + (b - p.2) = a + (b - p.2) - p.1 := by
                  rw [tsub_add_eq_add_tsub hpa]
                _ = a + b - p.2 - p.1 := by
                  rw [← add_tsub_assoc_of_le hpb]
                _ = a + b - (p.2 + p.1) := by
                  rw [tsub_add_eq_tsub_tsub]
                _ = a + b - (p.1 + p.2) := by simp [add_comm]
                _ = a + b - i := by simp [hp₁₂]
            simp [hasseDeriv_monomial, MvPolynomial.monomial_mul, hexp, mul_assoc,
              mul_left_comm, mul_comm]
          · have hmv : mvChoose b p.2 = 0 := mvChoose_of_not_le (k := b) (i := p.2) hpb
            simp [hasseDeriv_monomial, hmv]
        · have hmv : mvChoose a p.1 = 0 := mvChoose_of_not_le (k := a) (i := p.1) hpa
          simp [hasseDeriv_monomial, hmv]
      calc
        hasseDeriv i (MvPolynomial.monomial a r * MvPolynomial.monomial b s) =
            MvPolynomial.monomial (a + b - i) ((mvChoose (a + b) i : R) * (r * s)) := by
          simp [MvPolynomial.monomial_mul, hasseDeriv_monomial]
        _ =
            MvPolynomial.monomial (a + b - i)
              ((((∑ p ∈ Finset.antidiagonal i, mvChoose a p.1 * mvChoose b p.2 : ℕ) : R) *
                (r * s))) := by
          congr 2
          rw [mvChoose_add]
        _ =
            ∑ p ∈ Finset.antidiagonal i,
              MvPolynomial.monomial (a + b - i)
                ((((mvChoose a p.1 * mvChoose b p.2 : ℕ) : R) * (r * s))) := by
          simpa using hsum.symm
        _ =
            ∑ p ∈ Finset.antidiagonal i,
              hasseDeriv p.1 (MvPolynomial.monomial a r) *
                hasseDeriv p.2 (MvPolynomial.monomial b s) := by
          refine Finset.sum_congr rfl fun p hp ↦ ?_
          exact (haux p hp).symm
    · rw [mul_add, map_add, hQ₁, hQ₂, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun p hp ↦ ?_
      rw [← mul_add]
      simp [hasseDeriv_monomial]
  · rw [add_mul, map_add, hP₁, hP₂, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p hp ↦ ?_
    rw [← add_mul]
    simp

/-- The Hasse derivative indexed by `Finsupp.single i 1` is the partial derivative
`pderiv i`. -/
theorem hasseDeriv_single_one (i : σ) :
    hasseDeriv (R := R) (Finsupp.single i 1) = pderiv (R := R) i := by
  classical
  refine LinearMap.ext fun p ↦ ?_
  refine MvPolynomial.induction_on' p (fun k r => ?_) (fun p q hp hq => ?_)
  · rw [hasseDeriv_monomial]
    simp [pderiv_monomial, mvChoose_single, Nat.choose_one_right, mul_comm]
  · simp [hp, hq]

/-! ### Naturality and one-variable compatibility -/

/-- Renaming variables along an equivalence commutes with Hasse differentiation. -/
theorem hasseDeriv_rename (e : σ ≃ τ) (i : σ →₀ ℕ) (P : MvPolynomial σ R) :
    hasseDeriv (i.mapDomain e) (MvPolynomial.rename e P) =
      MvPolynomial.rename e (hasseDeriv i P) := by
  classical
  refine MvPolynomial.induction_on' P (fun k r => ?_) (fun p q hp hq => ?_)
  · have htsub :
        k.mapDomain e - i.mapDomain e = (k - i).mapDomain e := by
      ext a
      simp [Finsupp.mapDomain_equiv_apply, Finsupp.tsub_apply]
    simp [MvPolynomial.rename_monomial, hasseDeriv_monomial, htsub,
      mvChoose_mapDomain_equiv]
  · simp [hp, hq]

private lemma mvChoose_mapDomain_succ {n : ℕ} (J : Fin (n + 1) →₀ ℕ)
    (i : Fin n →₀ ℕ) :
    mvChoose J (Finsupp.mapDomain Fin.succ i) =
      mvChoose (Finsupp.comapDomain Fin.succ J
        (Set.injOn_of_injective (Fin.succ_injective n))) i := by
  set i' : Fin (n + 1) →₀ ℕ := Finsupp.mapDomain Fin.succ i
  set J' : Fin n →₀ ℕ :=
    Finsupp.comapDomain Fin.succ J (Set.injOn_of_injective (Fin.succ_injective n))
  have hi0 : i' 0 = 0 := by
    refine Finsupp.mapDomain_notin_range (x := i) (a := 0) (fun h ↦ ?_)
    rcases h with ⟨j, hj⟩
    exact (Fin.succ_ne_zero j) hj
  have hle_iff : i' ≤ J ↔ i ≤ J' := by
    refine ⟨fun h j ↦ ?_, fun h ↦ ?_⟩
    · have h' := (Finsupp.le_def.mp h) (Fin.succ j)
      simpa [i', J', Finsupp.comapDomain_apply, Finsupp.mapDomain_apply,
        Fin.succ_injective] using h'
    · refine (Finsupp.le_def).2 (fun x ↦ ?_)
      refine Fin.cases ?_ ?_ x
      · simp [hi0]
      · intro j
        have h' := (Finsupp.le_def.mp h) j
        simpa [i', J', Finsupp.comapDomain_apply, Finsupp.mapDomain_apply,
          Fin.succ_injective] using h'
  by_cases hle : i' ≤ J
  · have hle' : i ≤ J' := hle_iff.mp hle
    have hprod_left :
        J.prod (fun x n ↦ n.choose (i' x)) =
          (J.support.erase 0).prod (fun x ↦ (J x).choose (i' x)) := by
      by_cases h0mem : (0 : Fin (n + 1)) ∈ J.support
      · have h0 : (J 0).choose (i' 0) = 1 := by simp [hi0]
        calc
          J.prod (fun x n ↦ n.choose (i' x)) =
              J.support.prod (fun x ↦ (J x).choose (i' x)) := by
                simp [Finsupp.prod]
          _ = (insert 0 (J.support.erase 0)).prod (fun x ↦ (J x).choose (i' x)) := by
                simp [Finset.insert_erase h0mem]
          _ =
              (J 0).choose (i' 0) *
                (J.support.erase 0).prod (fun x ↦ (J x).choose (i' x)) := by
                simp [Finset.prod_insert]
          _ = (J.support.erase 0).prod (fun x ↦ (J x).choose (i' x)) := by
                simp [h0]
      · simp [Finsupp.prod, Finset.erase_eq_of_notMem h0mem]
    have himage :
        Finset.image Fin.succ J'.support = J.support.erase 0 := by
      ext x
      refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
      · rcases Finset.mem_image.1 hx with ⟨y, hy, rfl⟩
        have hy' : Fin.succ y ∈ J.support := by
          simpa [J'] using hy
        exact Finset.mem_erase.2 ⟨Fin.succ_ne_zero y, hy'⟩
      · rcases Finset.mem_erase.1 hx with ⟨hxne, hxmem⟩
        cases x using Fin.cases with
        | zero => exact (hxne rfl).elim
        | succ y =>
            have hy : y ∈ J'.support := by
              simpa [J'] using (by simpa using hxmem : Fin.succ y ∈ J.support)
            exact Finset.mem_image.2 ⟨y, hy, rfl⟩
    have hprod_image :
        J'.support.prod (fun x ↦ (J (Fin.succ x)).choose (i x)) =
          (Finset.image Fin.succ J'.support).prod (fun x ↦ (J x).choose (i' x)) := by
      have hinj : Set.InjOn (fun x => Fin.succ x) (J'.support : Set (Fin n)) := by
        intro x hx y hy hxy
        exact Fin.succ_injective _ hxy
      have h :=
        (Finset.prod_image (s := J'.support) (g := fun x => Fin.succ x)
          (f := fun x => (J x).choose (i' x)) hinj)
      convert h.symm using 1
      simp [i', Finsupp.mapDomain_apply, Fin.succ_injective]
    have hprod_right :
        J'.prod (fun x n ↦ n.choose (i x)) =
          (J.support.erase 0).prod (fun x ↦ (J x).choose (i' x)) := by
      calc
        J'.prod (fun x n ↦ n.choose (i x)) =
            J'.support.prod (fun x ↦ (J' x).choose (i x)) := by
              simp [Finsupp.prod]
        _ = J'.support.prod (fun x ↦ (J (Fin.succ x)).choose (i x)) := by
              simp [J', Finsupp.comapDomain_apply]
        _ = (Finset.image Fin.succ J'.support).prod (fun x ↦ (J x).choose (i' x)) := by
              simpa using hprod_image
        _ = (J.support.erase 0).prod (fun x ↦ (J x).choose (i' x)) := by
              simp [himage]
    have hprod :
        J.prod (fun x n ↦ n.choose (i' x)) =
          J'.prod (fun x n ↦ n.choose (i x)) := by
      simpa [hprod_right] using hprod_left
    simp [mvChoose_of_le (k := J) (i := i') hle, mvChoose_of_le (k := J') (i := i) hle', hprod]
  · have hle' : ¬ i ≤ J' := fun hle' => hle (hle_iff.mpr hle')
    simp [mvChoose_of_not_le hle, mvChoose_of_not_le hle']

private lemma cons_add_mapDomain_succ {n : ℕ} (m i : Fin n →₀ ℕ) (k : ℕ) :
    m.cons k + Finsupp.mapDomain Fin.succ i = (m + i).cons k := by
  ext x
  refine Fin.cases ?_ ?_ x
  · have h0 : (Finsupp.mapDomain Fin.succ i) 0 = 0 := by
      refine Finsupp.mapDomain_notin_range (x := i) (a := 0) (fun h ↦ ?_)
      rcases h with ⟨j, hj⟩
      exact (Fin.succ_ne_zero j) hj
    simp [h0]
  · intro j
    simp [Finsupp.mapDomain_apply, Fin.succ_injective]

/-- In the `finSuccEquiv` description of a polynomial in `Fin (n + 1)` variables, Hasse
differentiation in the trailing `n` variables commutes with taking coefficients in the leading
variable. -/
theorem coeff_finSuccEquiv_hasseDeriv_mapDomain {n : ℕ}
    (P : MvPolynomial (Fin (n + 1)) R) (i : Fin n →₀ ℕ) (k : ℕ) :
    (MvPolynomial.finSuccEquiv R n
          (hasseDeriv (Finsupp.mapDomain Fin.succ i) P)).coeff k =
      hasseDeriv i ((MvPolynomial.finSuccEquiv R n P).coeff k) := by
  classical
  have hmv_cons (m : Fin n →₀ ℕ) :
      mvChoose ((m + i).cons k) (Finsupp.mapDomain Fin.succ i) =
        mvChoose (m + i) i := by
    have hcomap :
        Finsupp.comapDomain Fin.succ ((m + i).cons k)
            (Set.injOn_of_injective (Fin.succ_injective n)) =
          m + i := by
      ext j
      simp [Finsupp.comapDomain_apply]
    simpa [hcomap] using
      (mvChoose_mapDomain_succ (J := (m + i).cons k) (i := i))
  ext m
  simp [MvPolynomial.finSuccEquiv_coeff_coeff, hasseDeriv_coeff, hmv_cons,
    cons_add_mapDomain_succ]

/-- In the `finSuccEquiv` description of a polynomial in `Fin (n + 1)` variables, Hasse
differentiation in the trailing `n` variables acts coefficientwise on the coefficients of the
leading variable. -/
theorem finSuccEquiv_hasseDeriv_mapDomain {n : ℕ}
    (P : MvPolynomial (Fin (n + 1)) R) (i : Fin n →₀ ℕ) :
    MvPolynomial.finSuccEquiv R n (hasseDeriv (Finsupp.mapDomain Fin.succ i) P) =
      Finset.sum (MvPolynomial.finSuccEquiv R n P).support fun k =>
        Polynomial.monomial k (hasseDeriv i ((MvPolynomial.finSuccEquiv R n P).coeff k)) := by
  classical
  ext k m
  rw [coeff_finSuccEquiv_hasseDeriv_mapDomain]
  conv_rhs => rw [Polynomial.finset_sum_coeff, MvPolynomial.coeff_sum]
  by_cases hk : k ∈ (MvPolynomial.finSuccEquiv R n P).support
  · have hcoeff :
        Finset.sum (MvPolynomial.finSuccEquiv R n P).support
            (fun b ↦
              coeff m
                ((Polynomial.monomial b
                  (hasseDeriv i ((MvPolynomial.finSuccEquiv R n P).coeff b))).coeff k)) =
          coeff m (hasseDeriv i ((MvPolynomial.finSuccEquiv R n P).coeff k)) := by
      rw [Finset.sum_eq_single_of_mem k hk]
      · simp only [Polynomial.coeff_monomial, if_true]
      · intro b _ hb
        simp [Polynomial.coeff_monomial, hb]
    exact hcoeff.symm
  · have hkcoeff : (MvPolynomial.finSuccEquiv R n P).coeff k = 0 := by
      exact Polynomial.notMem_support_iff.mp hk
    have hcoeff :
        Finset.sum (MvPolynomial.finSuccEquiv R n P).support
            (fun b ↦
              coeff m
                ((Polynomial.monomial b
                  (hasseDeriv i ((MvPolynomial.finSuccEquiv R n P).coeff b))).coeff k)) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro b hb
      have hb' : b ≠ k := fun h => hk (h ▸ hb)
      simp [Polynomial.coeff_monomial, hb']
    simpa [hkcoeff] using hcoeff.symm

/-- Under `finOneAlgEquiv`, one-variable Hasse derivatives agree with the univariate Hasse
derivatives. -/
theorem finOneAlgEquiv_hasseDeriv (P : MvPolynomial (Fin 1) R) (k : ℕ) :
    finOneAlgEquiv R (hasseDeriv (Finsupp.single 0 k) P) =
      Polynomial.hasseDeriv k (finOneAlgEquiv R P) := by
  classical
  ext n
  have hsingle :
      (Finsupp.single (0 : Fin 1) n + Finsupp.single 0 k) = Finsupp.single 0 (n + k) := by
    apply Finsupp.ext
    intro i
    have hi : i = 0 := by simpa using (Fin.eq_zero i)
    subst hi
    simp [add_comm]
  calc
    (finOneAlgEquiv R (hasseDeriv (Finsupp.single 0 k) P)).coeff n
        = coeff (Finsupp.single 0 n) (hasseDeriv (Finsupp.single 0 k) P) :=
      coeff_finOneAlgEquiv R (hasseDeriv (Finsupp.single 0 k) P) n
    _ = (mvChoose (Finsupp.single 0 n + Finsupp.single 0 k) (Finsupp.single 0 k) : R) *
          coeff (Finsupp.single 0 n + Finsupp.single 0 k) P :=
      hasseDeriv_coeff (Finsupp.single 0 k) P (Finsupp.single 0 n)
    _ = ((Nat.choose (n + k) k) : R) * coeff (Finsupp.single 0 (n + k)) P := by
      rw [hsingle]
      simp [mvChoose_single]
    _ = ((Nat.choose (n + k) k) : R) * (finOneAlgEquiv R P).coeff (n + k) := by
      congr 1
      rw [← coeff_finOneAlgEquiv R P (n + k)]
    _ = (Polynomial.hasseDeriv k (finOneAlgEquiv R P)).coeff n := by
      rw [← Polynomial.hasseDeriv_coeff (k := k) (f := finOneAlgEquiv R P) (n := n)]

/-! ### Degree bounds -/

/-- If the total order of `i` is larger than the total degree of `P`, then
`hasseDeriv i P` is zero. -/
theorem hasseDeriv_eq_zero_of_totalDegree_lt_degree (P : MvPolynomial σ R)
    (i : σ →₀ ℕ) (h : P.totalDegree < i.degree) : hasseDeriv i P = 0 := by
  classical
  ext m
  have hm : P.totalDegree < (m + i).degree := by
    simpa [map_add] using lt_of_lt_of_le h (Nat.le_add_left _ _)
  have hcoeff : coeff (m + i) P = 0 := by
    exact MvPolynomial.coeff_eq_zero_of_totalDegree_lt (by simpa [Finsupp.degree] using hm)
  simp [hasseDeriv_coeff, hcoeff]

/-- Hasse differentiation lowers total degree by at least the total order of `i`. -/
theorem totalDegree_hasseDeriv_le (P : MvPolynomial σ R) (i : σ →₀ ℕ) :
    (hasseDeriv i P).totalDegree ≤ P.totalDegree - i.degree := by
  classical
  refine Finset.sup_le (fun m hm ↦ ?_)
  have hcoeff : coeff m (hasseDeriv i P) ≠ 0 := Finsupp.mem_support_iff.mp hm
  have hcoeff' : coeff (m + i) P ≠ 0 := by
    intro hzero
    have : coeff m (hasseDeriv i P) = 0 := by simp [hasseDeriv_coeff, hzero]
    exact hcoeff this
  have hmP : m + i ∈ P.support := MvPolynomial.mem_support_iff.mpr hcoeff'
  have hdeg : (m + i).degree ≤ P.totalDegree := by
    simpa [Finsupp.degree] using (MvPolynomial.le_totalDegree (p := P) (s := m + i) hmP)
  have hdeg' : m.degree + i.degree ≤ P.totalDegree := by simpa [map_add] using hdeg
  exact Nat.le_sub_of_add_le hdeg'

end MvPolynomial
