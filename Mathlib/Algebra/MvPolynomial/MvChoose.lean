/-
Copyright (c) 2026 Elias Judin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Data.Nat.Choose.Vandermonde

/-!
# Multivariate binomial coefficients

This file defines `MvPolynomial.mvChoose`, the multivariate binomial coefficient
$\binom{k}{i}=\prod_j \binom{k_j}{i_j}$ for finitely supported `k, i : σ →₀ ℕ`, and proves
identities used for Hasse derivatives and related algebra.

## Main declarations

* `MvPolynomial.mvChoose`
* `MvPolynomial.mvChoose_mul`
* `MvPolynomial.mvChoose_add`

Hasse derivatives that use these coefficients are in `Mathlib.Algebra.MvPolynomial.HasseDeriv`.

## Naming

`mvChoose` is namespaced under `MvPolynomial`. The `mv` prefix marks multivariate-polynomial-local
notions. It is the coordinatewise product $\prod_j \binom{k_j}{i_j}$, hence distinct from
`Nat.multinomial` (multinomial coefficients in the usual multinomial-theorem sense).

## Tags

multivariate polynomial, binomial coefficient
-/

@[expose] public section

namespace MvPolynomial

open Finsupp
open scoped BigOperators

variable {σ τ R : Type*} [CommSemiring R]

/-! ### Multivariate binomial coefficients -/

/-- The multivariate binomial coefficient $\binom{k}{i}$. -/
def mvChoose (k i : σ →₀ ℕ) : ℕ :=
  i.prod (fun j m ↦ (k j).choose m)

lemma mvChoose_of_le {k i : σ →₀ ℕ} (h : i ≤ k) :
    mvChoose k i = k.prod (fun j n ↦ n.choose (i j)) := by
  classical
  simp only [mvChoose, Finsupp.prod]
  refine Finset.prod_subset (Finsupp.support_mono h) fun j _ hj ↦ ?_
  rw [Finsupp.notMem_support_iff.mp hj, Nat.choose_zero_right]

lemma mvChoose_of_not_le {k i : σ →₀ ℕ} (h : ¬ i ≤ k) : mvChoose k i = 0 := by
  classical
  simp only [Finsupp.le_def, not_forall] at h
  obtain ⟨x, hx⟩ := h
  simp only [mvChoose, Finsupp.prod]
  have hxlt : k x < i x := lt_of_not_ge hx
  refine Finset.prod_eq_zero (i := x) ?_ (Nat.choose_eq_zero_of_lt hxlt)
  · exact Finsupp.mem_support_iff.mpr (Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le _) hxlt))

@[simp]
lemma mvChoose_zero (k : σ →₀ ℕ) : mvChoose k 0 = 1 := by
  simp [mvChoose]

@[simp]
lemma mvChoose_self (k : σ →₀ ℕ) : mvChoose k k = 1 := by
  simp [mvChoose, Finsupp.prod]

/-- For a single-coordinate multi-index, `mvChoose` is the usual binomial coefficient. -/
lemma mvChoose_single (k : σ →₀ ℕ) (i : σ) (j : ℕ) :
    mvChoose k (Finsupp.single i j) = Nat.choose (k i) j := by
  classical
  by_cases h : Finsupp.single i j ≤ k
  · have hji : j ≤ k i := Finsupp.single_le_iff.mp h
    rw [mvChoose_of_le (k := k) (i := Finsupp.single i j) h, Finsupp.prod]
    have hprod :
        ∏ x ∈ k.support, Nat.choose (k x) (Finsupp.single i j x) =
          Nat.choose (k i) (Finsupp.single i j i) := by
      refine Finset.prod_eq_single (s := k.support)
        i (fun b _ hb ↦ ?_) ?_
      · have hb0 : Finsupp.single i j b = 0 := by simp [hb]
        simp [hb0]
      · intro hi
        have hk : k i = 0 := Finsupp.notMem_support_iff.mp hi
        have hj : j = 0 := Nat.eq_zero_of_le_zero (by simpa [hk] using hji)
        simp [hk, hj]
    simpa using hprod
  · have hji : k i < j := by
      refine lt_of_not_ge (fun hji ↦ ?_)
      exact h (Finsupp.single_le_iff.mpr hji)
    simp [mvChoose_of_not_le (k := k) (i := Finsupp.single i j) h,
      Nat.choose_eq_zero_of_lt hji]

/-- The symmetry identity $\binom{i + j}{i} = \binom{i + j}{j}$. -/
theorem mvChoose_symm_add (i j : σ →₀ ℕ) :
    mvChoose (i + j) i = mvChoose (i + j) j := by
  classical
  rw [mvChoose_of_le (Finsupp.le_def.2 fun x => Nat.le_add_right _ _),
    mvChoose_of_le (Finsupp.le_def.2 fun x => Nat.le_add_left _ _)]
  simp only [Finsupp.prod, Finsupp.add_apply]
  refine Finset.prod_congr rfl (fun x _hx ↦ ?_)
  simpa using (Nat.choose_symm_add (a := i x) (b := j x))

lemma mvChoose_symm_add_cast (i j : σ →₀ ℕ) :
    (mvChoose (i + j) i : R) = (mvChoose (i + j) j : R) :=
  congrArg (fun n : ℕ => (n : R)) (mvChoose_symm_add (σ := σ) i j)

/-- The identity $\binom{k}{i} \binom{k - i}{j} = \binom{k}{i + j} \binom{i + j}{i}$. -/
theorem mvChoose_mul (k i j : σ →₀ ℕ) :
    mvChoose k i * mvChoose (k - i) j =
      mvChoose k (i + j) * mvChoose (i + j) i := by
  classical
  by_cases hi : i ≤ k
  · by_cases hj : j ≤ k - i
    · have hij : i + j ≤ k := by
        rw [Finsupp.le_def] at hi hj ⊢
        intro x
        have hx : i x + j x ≤ i x + (k x - i x) := Nat.add_le_add_left (hj x) _
        simpa [Finsupp.add_apply, Finsupp.tsub_apply, Nat.add_sub_of_le (hi x)] using hx
      rw [mvChoose_of_le hi, mvChoose_of_le hj, mvChoose_of_le hij,
        mvChoose_of_le (Finsupp.le_def.2 fun x => Nat.le_add_right _ _)]
      have hprod_ki :
          (k - i).prod (fun x n ↦ n.choose (j x)) =
            ∏ x ∈ k.support, (k x - i x).choose (j x) := by
        have h :=
          Finset.prod_subset (Finsupp.support_tsub (f1 := k) (f2 := i))
            (f := fun x ↦ (k x - i x).choose (j x)) ?_
        · simpa [Finsupp.prod, Finsupp.tsub_apply] using h
        · intro x _hxk hxki
          have hx0 : (k - i) x = 0 := Finsupp.notMem_support_iff.mp hxki
          have hx0' : k x - i x = 0 := by simpa [Finsupp.tsub_apply] using hx0
          have hjx : j x = 0 := by
            have : j x ≤ (k - i) x := (Finsupp.le_def.mp hj) x
            exact Nat.eq_zero_of_le_zero (by simpa [hx0] using this)
          simp [hx0', hjx]
      have hprod_ij :
          (i + j).prod (fun x n ↦ n.choose (i x)) =
            ∏ x ∈ k.support, (i x + j x).choose (i x) := by
        have hsupp : (i + j).support ⊆ k.support := by
          intro x hxij
          have hx_ne0 : (i + j) x ≠ 0 := Finsupp.mem_support_iff.mp hxij
          have hx_pos : 0 < (i + j) x := Nat.pos_of_ne_zero hx_ne0
          have hx_le : (i + j) x ≤ k x := (Finsupp.le_def.mp hij) x
          exact Finsupp.mem_support_iff.mpr (Nat.ne_of_gt (lt_of_lt_of_le hx_pos hx_le))
        have h :=
          Finset.prod_subset hsupp (f := fun x ↦ (i x + j x).choose (i x)) ?_
        · simpa [Finsupp.prod, Finsupp.add_apply] using h
        · intro x _hxk hxij
          have hx0 : (i + j) x = 0 := Finsupp.notMem_support_iff.mp hxij
          obtain ⟨hix, hjx⟩ := Nat.add_eq_zero_iff.mp (by simpa [Finsupp.add_apply] using hx0)
          simp [hix, hjx]
      rw [hprod_ki, hprod_ij]
      simp only [Finsupp.prod, Finsupp.add_apply]
      rw [(Finset.prod_mul_distrib (s := k.support)
            (f := fun x ↦ (k x).choose (i x))
            (g := fun x ↦ (k x - i x).choose (j x))).symm]
      rw [(Finset.prod_mul_distrib (s := k.support)
            (f := fun x ↦ (k x).choose (i x + j x))
            (g := fun x ↦ (i x + j x).choose (i x))).symm]
      refine Finset.prod_congr rfl (fun x hx ↦ ?_)
      simpa [Nat.add_sub_cancel_left] using
        (Nat.choose_mul (n := k x) (k := i x + j x) (s := i x) (Nat.le_add_right _ _)).symm
    · have hij : ¬ i + j ≤ k := by
        intro hij
        apply hj
        rw [Finsupp.le_def] at hij ⊢
        intro x
        have hijx : i x + j x ≤ k x := by simpa [Finsupp.add_apply] using hij x
        have : j x + i x ≤ k x := by simpa [Nat.add_comm] using hijx
        have : j x ≤ k x - i x := Nat.le_sub_of_add_le this
        simpa [Finsupp.tsub_apply] using this
      simp [mvChoose_of_not_le hj, mvChoose_of_not_le hij]
  · have hij : ¬ i + j ≤ k := fun hij =>
      hi ((Finsupp.le_def.2 fun x => Nat.le_add_right _ _).trans hij)
    simp [mvChoose_of_not_le hi, mvChoose_of_not_le hij]

/-- Over a finite index type, $\binom{k}{i} = \prod_{j : \sigma} \binom{k_j}{i_j}$. -/
lemma mvChoose_eq_prod_choose [Fintype σ] (k i : σ →₀ ℕ) :
    mvChoose k i = ∏ j : σ, (k j).choose (i j) := by
  classical
  by_cases hle : i ≤ k
  · rw [mvChoose_of_le (k := k) (i := i) hle]
    have houtside :
        ∀ x ∈ (Finset.univ : Finset σ), x ∉ k.support → Nat.choose (k x) (i x) = 1 := by
      intro x _hx hxnot
      have hk0 : k x = 0 := Finsupp.notMem_support_iff.mp hxnot
      have hix : i x = 0 := by
        have : i x ≤ k x := (Finsupp.le_def.mp hle) x
        exact Nat.eq_zero_of_le_zero (by simpa [hk0] using this)
      simp [hk0, hix]
    simpa [Finsupp.prod] using
      (Finset.prod_subset (Finset.subset_univ _) houtside :
        ∏ x ∈ k.support, Nat.choose (k x) (i x) =
          ∏ x ∈ (Finset.univ : Finset σ), Nat.choose (k x) (i x))
  · rw [mvChoose_of_not_le (k := k) (i := i) hle]
    have hnot : ¬ ∀ x, i x ≤ k x := by
      simpa [Finsupp.le_def] using hle
    rcases not_forall.mp hnot with ⟨x, hx⟩
    have hxlt : k x < i x := lt_of_not_ge hx
    have hx0 : Nat.choose (k x) (i x) = 0 := Nat.choose_eq_zero_of_lt hxlt
    have hprod : (∏ y : σ, Nat.choose (k y) (i y)) = 0 := by
      simpa using (Finset.prod_eq_zero (i := x) (by simp) hx0)
    simp [hprod]

lemma mvChoose_mapDomain_equiv (e : σ ≃ τ) (k i : σ →₀ ℕ) :
    mvChoose (k.mapDomain e) (i.mapDomain e) = mvChoose k i := by
  by_cases h : i ≤ k
  · have hmap : i.mapDomain e ≤ k.mapDomain e := by
      rw [Finsupp.le_def] at h ⊢
      intro a
      simpa [Finsupp.mapDomain_equiv_apply] using h (e.symm a)
    rw [mvChoose_of_le hmap, mvChoose_of_le h]
    simpa [Finsupp.mapDomain_equiv_apply] using
      (Finsupp.prod_mapDomain_index_inj
        (f := e) (s := k) (h := fun a n ↦ n.choose ((i.mapDomain e) a)) e.injective)
  · have hmap : ¬ i.mapDomain e ≤ k.mapDomain e := by
      intro hmap
      apply h
      rw [Finsupp.le_def] at hmap ⊢
      intro a
      simpa [Finsupp.mapDomain_equiv_apply] using hmap (e a)
    simp [mvChoose_of_not_le h, mvChoose_of_not_le hmap]

private lemma mvChoose_eq_prod_choose_of_support_subset
    (k i : σ →₀ ℕ) (s : Finset σ) (hi : i.support ⊆ s) :
    mvChoose k i = ∏ a : s, (k a).choose (i a) := by
  classical
  by_cases hki : i ≤ k
  · rw [mvChoose_of_le hki]
    have hsupp : i.support ⊆ k.support := by
      intro a ha
      refine Finsupp.mem_support_iff.mpr fun hk0 ↦ ?_
      have : i a ≤ k a := (Finsupp.le_def.mp hki) a
      have hi0 : i a = 0 := Nat.eq_zero_of_le_zero (by simpa [hk0] using this)
      exact (Finsupp.mem_support_iff.mp ha) hi0
    calc
      k.prod (fun a n ↦ n.choose (i a)) = ∏ a ∈ k.support, (k a).choose (i a) := by
        simp [Finsupp.prod]
      _ = ∏ a ∈ k.support ∪ s, (k a).choose (i a) := by
        refine Finset.prod_subset (by
          intro a ha
          exact Finset.mem_union.mpr (Or.inl ha)) ?_
        intro a ha hnotk
        have has : a ∈ s := (Finset.mem_union.mp ha).resolve_left hnotk
        have hnoti : a ∉ i.support := fun h ↦ hnotk (hsupp h)
        have hi0 : i a = 0 := Finsupp.notMem_support_iff.mp hnoti
        simp [hi0]
      _ = ∏ a ∈ s, (k a).choose (i a) := by
        symm
        refine Finset.prod_subset (by
          intro a ha
          exact Finset.mem_union.mpr (Or.inr ha)) ?_
        intro a ha hnots
        have hak : a ∈ k.support := (Finset.mem_union.mp ha).resolve_right hnots
        have hnoti : a ∉ i.support := fun h ↦ hnots (hi h)
        have hi0 : i a = 0 := Finsupp.notMem_support_iff.mp hnoti
        simp [hi0]
      _ = ∏ a : s, (k a).choose (i a) := by
        calc
          ∏ a ∈ s, (k a).choose (i a) = ∏ a ∈ s.attach, (k a).choose (i a) := by
            simpa using (Finset.prod_attach s (fun a ↦ (k a).choose (i a))).symm
          _ = ∏ a : s, (k a).choose (i a) := by
            rw [Finset.univ_eq_attach]
  · rw [mvChoose_of_not_le (k := k) (i := i) hki]
    have hnot : ¬ ∀ a, i a ≤ k a := by
      simpa [Finsupp.le_def] using hki
    rcases not_forall.mp hnot with ⟨a, ha⟩
    have hlt : k a < i a := lt_of_not_ge ha
    have hai : a ∈ i.support := Finsupp.mem_support_iff.mpr
      (Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le _) hlt))
    have has : a ∈ s := hi hai
    refine (Finset.prod_eq_zero (i := ⟨a, has⟩) (by simp) ?_).symm
    simpa using Nat.choose_eq_zero_of_lt hlt

theorem mvChoose_add (a b i : σ →₀ ℕ) [DecidableEq σ] :
    mvChoose (a + b) i = ∑ p ∈ Finset.antidiagonal i, mvChoose a p.1 * mvChoose b p.2 := by
  classical
  let τ := {x // x ∈ i.support}
  let ψ : (∀ x : τ, ℕ × ℕ) → (σ →₀ ℕ) × (σ →₀ ℕ) := fun f ↦
    ((Finsupp.equivFunOnFinite.symm fun x : τ ↦ (f x).1).extendDomain,
      (Finsupp.equivFunOnFinite.symm fun x : τ ↦ (f x).2).extendDomain)
  have hψ_mem :
      ∀ f, f ∈ Fintype.piFinset (fun x : τ ↦ Finset.antidiagonal (i x)) →
        ψ f ∈ Finset.antidiagonal i := by
    intro f hf
    rw [Finset.mem_antidiagonal]
    ext a
    by_cases ha : a ∈ i.support
    · have hfa : f ⟨a, ha⟩ ∈ Finset.antidiagonal (i a) :=
        (Fintype.mem_piFinset.mp hf) ⟨a, ha⟩
      simpa [ψ, Finsupp.extendDomain_apply, ha, Finsupp.coe_equivFunOnFinite_symm] using
        (Finset.mem_antidiagonal.mp hfa)
    · have hi0 : i a = 0 := Finsupp.notMem_support_iff.mp ha
      simp [ψ, Finsupp.extendDomain_apply, ha, hi0]
  have hψ_val :
      ∀ f, f ∈ Fintype.piFinset (fun x : τ ↦ Finset.antidiagonal (i x)) →
        (∏ x : τ, (a x).choose (f x).1 * (b x).choose (f x).2) =
          mvChoose a (ψ f).1 * mvChoose b (ψ f).2 := by
    intro f hf
    have hsubset₁ :
        (ψ f).1.support ⊆ i.support := by
      intro x hx
      exact (Finsupp.support_extendDomain_subset
        (f := Finsupp.equivFunOnFinite.symm fun y : τ ↦ (f y).1)) hx
    have hsubset₂ :
        (ψ f).2.support ⊆ i.support := by
      intro x hx
      exact (Finsupp.support_extendDomain_subset
        (f := Finsupp.equivFunOnFinite.symm fun y : τ ↦ (f y).2)) hx
    have hprod₁ : (∏ x : τ, (a x).choose (f x).1) = mvChoose a (ψ f).1 := by
      rw [mvChoose_eq_prod_choose_of_support_subset (s := i.support) (hi := hsubset₁)]
      symm
      refine Fintype.prod_congr _ _ fun x ↦ ?_
      have hcoe :
          (ψ f).1 ↑x = (f x).1 := by
        change ((Finsupp.equivFunOnFinite.symm fun y : τ ↦ (f y).1).extendDomain) ↑x = (f x).1
        rw [Finsupp.extendDomain_eq_embDomain_subtype]
        simpa using
          (Finsupp.embDomain_apply_self
            (.subtype fun a : σ ↦ a ∈ i.support)
            (Finsupp.equivFunOnFinite.symm fun y : τ ↦ (f y).1) x)
      exact congrArg (fun n ↦ (a x).choose n) hcoe
    have hprod₂ : (∏ x : τ, (b x).choose (f x).2) = mvChoose b (ψ f).2 := by
      rw [mvChoose_eq_prod_choose_of_support_subset (s := i.support) (hi := hsubset₂)]
      symm
      refine Fintype.prod_congr _ _ fun x ↦ ?_
      have hcoe :
          (ψ f).2 ↑x = (f x).2 := by
        change ((Finsupp.equivFunOnFinite.symm fun y : τ ↦ (f y).2).extendDomain) ↑x = (f x).2
        rw [Finsupp.extendDomain_eq_embDomain_subtype]
        simpa using
          (Finsupp.embDomain_apply_self
            (.subtype fun a : σ ↦ a ∈ i.support)
            (Finsupp.equivFunOnFinite.symm fun y : τ ↦ (f y).2) x)
      exact congrArg (fun n ↦ (b x).choose n) hcoe
    calc
      (∏ x : τ, (a x).choose (f x).1 * (b x).choose (f x).2) =
          (∏ x : τ, (a x).choose (f x).1) * ∏ x : τ, (b x).choose (f x).2 := by
            simpa using
              (Finset.prod_mul_distrib (s := (Finset.univ : Finset τ))
                (f := fun x : τ ↦ (a x).choose (f x).1)
                (g := fun x : τ ↦ (b x).choose (f x).2))
      _ = mvChoose a (ψ f).1 * mvChoose b (ψ f).2 := by rw [hprod₁, hprod₂]
  have hψ_inj :
      ∀ f g,
        f ∈ Fintype.piFinset (fun x : τ ↦ Finset.antidiagonal (i x)) →
        g ∈ Fintype.piFinset (fun x : τ ↦ Finset.antidiagonal (i x)) →
        ψ f = ψ g → f = g := by
    intro f g hf hg hfg
    funext x
    apply Prod.ext
    · have h := congrArg (fun p ↦ p.1 x) hfg
      simpa [ψ, Finsupp.extendDomain_apply, x.prop, Finsupp.coe_equivFunOnFinite_symm] using h
    · have h := congrArg (fun p ↦ p.2 x) hfg
      simpa [ψ, Finsupp.extendDomain_apply, x.prop, Finsupp.coe_equivFunOnFinite_symm] using h
  have hψ_surj :
      ∀ p, p ∈ Finset.antidiagonal i →
        ∃ f ∈ Fintype.piFinset (fun x : τ ↦ Finset.antidiagonal (i x)), ψ f = p := by
    intro p hp
    let f : ∀ x : τ, ℕ × ℕ := fun x ↦ (p.1 x, p.2 x)
    have hf : f ∈ Fintype.piFinset (fun x : τ ↦ Finset.antidiagonal (i x)) := by
      rw [Fintype.mem_piFinset]
      intro x
      have hx : p.1 x + p.2 x = i x := by
        simpa only [Finsupp.add_apply] using
          congrArg (fun q : σ →₀ ℕ => q x) (Finset.mem_antidiagonal.mp hp)
      exact Finset.mem_antidiagonal.mpr (by simpa [f] using hx)
    refine ⟨f, hf, ?_⟩
    apply Prod.ext <;> ext a
    · by_cases ha : a ∈ i.support
      · have hcoe :
            (Finsupp.equivFunOnFinite.symm fun x : τ ↦ p.1 x) ⟨a, ha⟩ = p.1 a := by
          exact congrFun (Finsupp.coe_equivFunOnFinite_symm (f := fun x : τ ↦ p.1 x)) ⟨a, ha⟩
        simp [ψ, f, Finsupp.extendDomain_apply, ha, hcoe]
      · have hi0 : i a = 0 := Finsupp.notMem_support_iff.mp ha
        have hp0 : p.1 a + p.2 a = 0 := by
          simpa [hi0] using congrArg (fun q : σ →₀ ℕ => q a) (Finset.mem_antidiagonal.mp hp)
        have hp10 : p.1 a = 0 := (Nat.add_eq_zero_iff.mp hp0).1
        simp [ψ, f, Finsupp.extendDomain_apply, ha, hp10]
    · by_cases ha : a ∈ i.support
      · have hcoe :
            (Finsupp.equivFunOnFinite.symm fun x : τ ↦ p.2 x) ⟨a, ha⟩ = p.2 a := by
          exact congrFun (Finsupp.coe_equivFunOnFinite_symm (f := fun x : τ ↦ p.2 x)) ⟨a, ha⟩
        simp [ψ, f, Finsupp.extendDomain_apply, ha, hcoe]
      · have hi0 : i a = 0 := Finsupp.notMem_support_iff.mp ha
        have hp0 : p.1 a + p.2 a = 0 := by
          simpa [hi0] using congrArg (fun q : σ →₀ ℕ => q a) (Finset.mem_antidiagonal.mp hp)
        have hp20 : p.2 a = 0 := (Nat.add_eq_zero_iff.mp hp0).2
        simp [ψ, f, Finsupp.extendDomain_apply, ha, hp20]
  calc
    mvChoose (a + b) i = ∏ x : τ, ((a + b) x).choose (i x) := by
      exact mvChoose_eq_prod_choose_of_support_subset (k := a + b) (i := i)
        (s := i.support) (hi := fun x hx ↦ hx)
    _ = ∏ x : τ, ∑ p ∈ Finset.antidiagonal (i x), (a x).choose p.1 * (b x).choose p.2 := by
      refine Finset.prod_congr rfl fun x _ ↦ ?_
      simpa [Finsupp.add_apply] using (Nat.add_choose_eq (a x) (b x) (i x))
    _ = ∑ f ∈ Fintype.piFinset (fun x : τ ↦ Finset.antidiagonal (i x)),
          ∏ x : τ, (a x).choose (f x).1 * (b x).choose (f x).2 := by
      simpa using
        (Finset.prod_univ_sum
          (t := fun x : τ ↦ Finset.antidiagonal (i x))
          (f := fun x p ↦ (a x).choose p.1 * (b x).choose p.2))
    _ = ∑ p ∈ Finset.antidiagonal i, mvChoose a p.1 * mvChoose b p.2 := by
      refine Finset.sum_bij (fun f _ ↦ ψ f) hψ_mem
        (fun f hf g hg hfg ↦ hψ_inj f g hf hg hfg)
        (fun p hp ↦ by
          rcases hψ_surj p hp with ⟨f, hf, hfp⟩
          exact ⟨f, hf, hfp⟩)
        hψ_val

end MvPolynomial
