/-
Copyright (c) 2024 Alessandro Iraci. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nirvana Coppola, Alessandro Iraci
-/
import Mathlib.RingTheory.MvPowerSeries.Basic

/-!
# Degree on MvPowerSeries

This file defines a degree on MvPowerSeries, with values in WithTop WithBot ℕ.

## Main declarations

* `MvPowerSeries.degree`

-/

open Classical

section Degree

namespace MvPowerSeries


variable {σ R S : Type*} [CommSemiring R] [DecidableEq (MvPowerSeries σ R)]
variable {φ ψ : MvPowerSeries σ R}

/-- A `MvPowerSeries φ` has bounded degree if its monomials are uniformly bounded -/
def HasDegreeBound (n : WithBot (WithTop ℕ)) : MvPowerSeries σ R → Prop :=
  fun φ ↦ (∀ s : σ →₀ ℕ, coeff R s φ ≠ 0 → s.sum (fun _ ↦ id) ≤ n)

/-- A `MvPowerSeries φ` has bounded degree if its monomials are uniformly bounded -/
def HasBoundedDegree (φ : MvPowerSeries σ R) : Prop :=
  ∃ n, HasDegreeBound n φ

noncomputable def degree (φ : MvPowerSeries σ R) : WithBot (WithTop ℕ) :=
  sInf { n | HasDegreeBound n φ }


theorem le_degree {s : σ →₀ ℕ} (h : φ s ≠ 0) : (s.sum fun _ ↦ id) ≤ degree φ := by
  simp only [Nat.cast_finsupp_sum, id_eq, degree, le_sInf_iff, Set.mem_setOf_eq]
  intro b hb
  simp only [HasDegreeBound, ne_eq, Nat.cast_finsupp_sum, id_eq] at hb
  apply hb
  exact h

theorem totalDegree_le_of_support_subset (h : ∀ s, φ s ≠ 0 → ψ s ≠ 0) :
    degree φ ≤ degree ψ :=
  sorry

@[simp]
theorem degree_zero : (0 : MvPowerSeries σ R).degree = ⊥ := by
  simp only [degree, HasDegreeBound, map_zero, ne_eq, not_true_eq_false, Nat.cast_finsupp_sum,
    id_eq, IsEmpty.forall_iff, forall_const, Set.setOf_true, sInf_univ]

@[simp]
theorem degree_eq_bot_iff_zero : φ.degree = ⊥ ↔ φ = 0 := by
  constructor
  · intro hbot
    simp [degree] at hbot
    have : HasDegreeBound ⊥ φ := by
      sorry

    sorry
  · sorry

@[simp]
theorem degree_lt_zero_iff_zero : φ.degree < 0 ↔ φ = 0 := sorry

@[simp]
theorem degree_C (r : R) (hr : r ≠ 0) : (C σ R r : MvPowerSeries σ R).degree = 0 := by
  rw [le_antisymm_iff]
  constructor
  · apply sInf_le
    simp only [HasDegreeBound, ne_eq, Nat.cast_finsupp_sum, id_eq, Set.mem_setOf_eq]
    intro s hs
    simp only [coeff_C, ite_eq_right_iff, not_forall, exists_prop] at hs
    rw [hs.1]
    simp only [Finsupp.sum_zero_index, le_refl]
  · have (s : R) : 0 ≤ degree ((C σ R) s) ↔ s ≠ 0 := by
      constructor
      · intro hC
        intro hs
        have : (C σ R) s = (0 : MvPowerSeries σ R) := by
          rw [hs]
          simp only [map_zero]
        rw [← degree_lt_zero_iff_zero] at this
        have := lt_of_lt_of_le' this hC
        contradiction
      · intro hs
        by_contra hC
        simp only [not_le, degree_lt_zero_iff_zero] at hC
        have : coeff R 0 (C σ R s) = s := by simp only [coeff_C, ↓reduceIte]
        rw [hC] at this
        simp at this
        symm at this
        contradiction
    rw [this]
    exact hr

@[simp]
theorem degree_one : (1 : MvPowerSeries σ R).degree = 0 :=
  degree_C (1 : R)

@[simp]
theorem degree_X [Nontrivial R] (s : σ) : (X s : MvPowerSeries σ R).degree = 1 := by
  -- rw [degree, support_X]
  -- simp only [Finset.sup, Finsupp.sum_single_index, Finset.fold_singleton, sup_bot_eq]
  sorry

theorem degree_add : (φ + ψ).degree ≤ max φ.degree ψ.degree := by
  sorry

theorem degree_add_eq_left_of_degree_lt (h : ψ.degree < φ.degree) :
    (φ + ψ).degree = φ.degree := by
  -- classical
  --   apply le_antisymm
  --   · rw [← max_eq_left_of_lt h]
  --     exact totalDegree_add p q
  --   by_cases hp : p = 0
  --   · simp [hp]
  --   obtain ⟨b, hb₁, hb₂⟩ :=
  --     p.support.exists_mem_eq_sup (Finsupp.support_nonempty_iff.mpr hp) fun m : σ →₀ ℕ =>
  --       Multiset.card (toMultiset m)
  --   have hb : ¬b ∈ q.support := by
  --     contrapose! h
  --     rw [totalDegree_eq p, hb₂, totalDegree_eq]
  --     apply Finset.le_sup h
  --   have hbb : b ∈ (p + q).support := by
  --     apply support_sdiff_support_subset_support_add
  --     rw [Finset.mem_sdiff]
  --     exact ⟨hb₁, hb⟩
  --   rw [totalDegree_eq, hb₂, totalDegree_eq]
  --   exact Finset.le_sup (f := fun m => Multiset.card (Finsupp.toMultiset m)) hbb
  sorry

theorem degree_add_eq_right_of_degree_lt (h : ψ.degree < φ.degree) :
    (ψ + φ).degree = φ.degree := by
  rw [add_comm, degree_add_eq_left_of_degree_lt h]

theorem degree_mul : (φ * ψ).degree ≤ φ.degree + ψ.degree := by
  sorry


theorem degree_smul_le [CommSemiring S] [DistribMulAction R S] (r : R) :
    (r • φ).degree ≤ φ.degree := sorry

theorem degree_pow (n : ℕ) : (φ ^ n).degree ≤ n * φ.degree := by
  -- rw [Finset.pow_eq_prod_const, ← Nat.nsmul_eq_mul, Finset.nsmul_eq_sum_const]
  -- refine supDegree_prod_le rfl (fun _ _ => ?_)
  -- exact Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)
  sorry

@[simp]
theorem degree_monomial (s : σ →₀ ℕ) {r : R} (hr : r ≠ 0) :
    (monomial _ s r : MvPowerSeries σ R).degree = s.sum fun _ ↦ id := by
  --simp [degree, support_monomial, if_neg hr]
  sorry

-- theorem totalDegree_monomial_le (s : σ →₀ ℕ) (c : R) :
--     (monomial s c).totalDegree ≤ s.sum fun _ ↦ id := by
--   if hc : c = 0 then
--     simp only [hc, map_zero, totalDegree_zero, zero_le]
--   else
--     rw [totalDegree_monomial _ hc]
--     exact le_rfl

-- @[simp]
-- theorem totalDegree_X_pow [Nontrivial R] (s : σ) (n : ℕ) :
--     (X s ^ n : MvPolynomial σ R).totalDegree = n := by simp [X_pow_eq_monomial, one_ne_zero]
-- set_option linter.uppercaseLean3 false in
-- #align mv_polynomial.total_degree_X_pow MvPolynomial.totalDegree_X_pow

-- /- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
-- theorem totalDegree_list_prod :
--     ∀ s : List (MvPolynomial σ R), s.prod.totalDegree ≤ (s.map MvPolynomial.totalDegree).sum
--   | [] => by rw [@List.prod_nil (MvPolynomial σ R) _, totalDegree_one]; rfl
--   | p::ps => by
--     rw [@List.prod_cons (MvPolynomial σ R) _, List.map, List.sum_cons]
--     exact le_trans (totalDegree_mul _ _) (add_le_add_left (totalDegree_list_prod ps) _)
-- #align mv_polynomial.total_degree_list_prod MvPolynomial.totalDegree_list_prod

-- theorem totalDegree_multiset_prod (s : Multiset (MvPolynomial σ R)) :
--     s.prod.totalDegree ≤ (s.map MvPolynomial.totalDegree).sum := by
--   refine' Quotient.inductionOn s fun l => _
--   rw [Multiset.quot_mk_to_coe, Multiset.prod_coe, Multiset.map_coe, Multiset.sum_coe]
--   exact totalDegree_list_prod l
-- #align mv_polynomial.total_degree_multiset_prod MvPolynomial.totalDegree_multiset_prod

-- theorem totalDegree_finset_prod {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ R) :
--     (s.prod f).totalDegree ≤ ∑ i in s, (f i).totalDegree := by
--   refine' le_trans (totalDegree_multiset_prod _) _
--   rw [Multiset.map_map]
--   rfl
-- #align mv_polynomial.total_degree_finset_prod MvPolynomial.totalDegree_finset_prod

-- theorem totalDegree_finset_sum {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ R) :
--     (s.sum f).totalDegree ≤ Finset.sup s fun i => (f i).totalDegree := by
--   induction' s using Finset.cons_induction with a s has hind
--   · exact zero_le _
--   · rw [Finset.sum_cons, Finset.sup_cons, sup_eq_max]
--     exact (MvPolynomial.totalDegree_add _ _).trans (max_le_max le_rfl hind)
-- #align mv_polynomial.total_degree_finset_sum MvPolynomial.totalDegree_finset_sum

-- lemma degreeOf_le_totalDegree (f : MvPolynomial σ R) (i : σ) : f.degreeOf i ≤ f.totalDegree :=
--   degreeOf_le_iff.mpr fun d hd ↦ (eq_or_ne (d i) 0).elim (·.trans_le zero_le') fun h ↦
--     (Finset.single_le_sum (fun _ _ ↦ zero_le') <| Finsupp.mem_support_iff.mpr h).trans
--     (le_totalDegree hd)

-- theorem exists_degree_lt [Fintype σ] (f : MvPolynomial σ R) (n : ℕ)
--     (h : f.totalDegree < n * Fintype.card σ) {d : σ →₀ ℕ} (hd : d ∈ f.support) : ∃ i, d i < n := by
--   contrapose! h
--   calc
--     n * Fintype.card σ = ∑ _s : σ, n := by
--       rw [Finset.sum_const, Nat.nsmul_eq_mul, mul_comm, Finset.card_univ]
--     _ ≤ ∑ s, d s := Finset.sum_le_sum fun s _ => h s
--     _ ≤ d.sum fun _ e => e := by
--       rw [Finsupp.sum_fintype]
--       intros
--       rfl
--     _ ≤ f.totalDegree := le_totalDegree hd
-- #align mv_polynomial.exists_degree_lt MvPolynomial.exists_degree_lt

-- theorem coeff_eq_zero_of_totalDegree_lt {f : MvPolynomial σ R} {d : σ →₀ ℕ}
--     (h : f.totalDegree < ∑ i in d.support, d i) : coeff d f = 0 := by
--   classical
--     rw [totalDegree, Finset.sup_lt_iff] at h
--     · specialize h d
--       rw [mem_support_iff] at h
--       refine' not_not.mp (mt h _)
--       exact lt_irrefl _
--     · exact lt_of_le_of_lt (Nat.zero_le _) h
-- #align mv_polynomial.coeff_eq_zero_of_total_degree_lt MvPolynomial.coeff_eq_zero_of_totalDegree_lt

-- theorem totalDegree_rename_le (f : σ → τ) (p : MvPolynomial σ R) :
--     (rename f p).totalDegree ≤ p.totalDegree :=
--   Finset.sup_le fun b => by
--     classical
--     intro h
--     rw [rename_eq] at h
--     have h' := Finsupp.mapDomain_support h
--     rw [Finset.mem_image] at h'
--     rcases h' with ⟨s, hs, rfl⟩
--     exact (sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)).trans_le (le_totalDegree hs)
-- #align mv_polynomial.total_degree_rename_le MvPolynomial.totalDegree_rename_le


end MvPowerSeries

end Degree
