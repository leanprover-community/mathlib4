/-
Copyright (c) 2023 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.Polynomial.Roots

/-!
# The Schwartz-Zippel lemma

This file contains a proof of the
[Schwartz-Zippel](https://en.wikipedia.org/wiki/Schwartz%E2%80%93Zippel_lemma) lemma.

This lemma tells us that the probability that a nonzero multivariable polynomial over an integral
domain evaluates to zero at a random point is bounded by the degree of the polynomial over the size
of the field, or more generally, that a nonzero multivariable polynomial over any integral domain
has a low probability of being zero when evaluated at points drawn at random from some finite subset
of the field. This lemma is useful as a probabilistic polynomial identity test.

## TODO

* Generalize to noncommutative rings? Is that even possible?
* Generalize to subset of the ring being different for each variable.
  * What does the theorem say in thic case?
  * Note that the Schwartz paper covers this case
* Reexpress in terms of probabilities.
* Then generalize to polynomials over arbitrary variable types
* Write a tactic to apply this lemma to a given polynomial

## References

* [demillo_lipton_1978]
* [schwartz_1980]
* [zippel_1979]

-/

open BigOperators

section find_home

-- REVIEWERS: Not sure what to do here.
-- Presumably we don't want these lemmas, but the proof below is more complicated without them
lemma and_or_and_not_iff (p q : Prop) : ((p ∧ q) ∨ (p ∧ ¬ q)) ↔ p := by
  tauto

lemma and_and_and_not_iff (p q r : Prop) : ((p ∧ q) ∧ (r ∧ ¬ q)) ↔ false := by
  tauto

-- https://github.com/leanprover-community/mathlib4/pull/7898
lemma Finset.card_filter_piFinset_eq' {n : ℕ} {α : Fin (n + 1) → Type*}
    (p : ((i : Fin n) → α i.succ) → Prop) [DecidablePred p]
    (S : (i : Fin (n + 1)) → Finset (α i)) :
    Finset.card (Finset.filter (fun r ↦ p (fun x ↦ r $ Fin.succ x)) (Fintype.piFinset S))
      = Finset.card ((S 0) ×ˢ Finset.filter p (Fintype.piFinset (fun x ↦ S $ Fin.succ x))) := by
  rw [← Finset.card_map ((Equiv.piFinSuccAbove α 0).toEmbedding)]
  congr
  ext ⟨x, f⟩
  simp only [Fin.zero_succAbove, Fintype.mem_piFinset,
      Fin.forall_fin_succ, and_imp, mem_map_equiv, mem_filter, mem_product]
  tauto

-- https://github.com/leanprover-community/mathlib4/pull/7898
@[simp]
lemma Finset.card_filter_succ_piFinset_eq {n : ℕ} {α : Fin (n + 1) → Type*}
    (p : ((i : Fin n) → α i.succ) → Prop) [DecidablePred p]
    (S : (i : Fin (n + 1)) → Finset (α i)) :
    Finset.card (Finset.filter (fun r ↦ p (fun x ↦ r $ Fin.succ x)) (Fintype.piFinset S))
     = (S 0).card * Finset.card (Finset.filter p (Fintype.piFinset (fun x ↦ S $ Fin.succ x))) := by
  rw [card_filter_piFinset_eq']
  exact Finset.card_product (S 0) (Finset.filter p (Fintype.piFinset (fun x ↦ S $ Fin.succ x)))

end find_home

-- Following the wikipedia proof (induction starting at n = 0)

-- -- TODO remove p from context now by reexpressing everthing in terms of p'?
-- have p_eq : p = (MvPolynomial.finSuccEquiv F n).symm p' := by
--   apply AlgEquiv_invFun_apply

-- TODO remove tsub from proof

/--
The **Schwartz-Zippel lemma**: For a nonzero multivariable polynomial `p` over an integral domain,
the probability that `p` evaluates to zero at points drawn at random from some finite subset `S` of
the integral domain is bounded by the degree of `p` over `|S|`. This version presents this lemma in
terms of `Finset`s
-/
lemma schwartz_zippel (F : Type) [CommRing F] [IsDomain F] [DecidableEq F] (n : ℕ)
    (p : MvPolynomial (Fin n) F) (hp : p ≠ 0) (S : Finset F) :
    (Finset.filter
      (fun f => MvPolynomial.eval f p = 0)
      (Fintype.piFinset fun _ => S)).card * S.card
      ≤ (p.totalDegree) * S.card ^ n := by
  revert p hp S
  induction n with
  | zero =>
    intros p hp S
    -- Because p is a polynomial over the (empty) type Fin 0 of variables, it is constant
    rw [p.eq_C_of_isEmpty] at *
    simp only [Nat.zero_eq, MvPolynomial.eval_C, Fin.forall_fin_zero_pi, Finset.filter_const,
      MvPolynomial.totalDegree_C, pow_zero, mul_one, nonpos_iff_eq_zero, mul_eq_zero,
      Finset.card_eq_zero, ite_eq_right_iff]
    left
    intro h
    simp [h] at hp
    -- Now, assume that the theorem holds for all polynomials in n variables.
  | succ n ih =>
    intros p p_nonzero S
    -- We can then consider p to be a polynomial over MvPolynomials in one fewer variables
    set p' : Polynomial (MvPolynomial (Fin n) F) := MvPolynomial.finSuccEquiv F n p with hp'
    -- since p is not identically zero, there is some i such that p_i' is not identically zero
    -- take the largest such i
    set i := p'.natDegree with hi
    set p_i' := Polynomial.coeff p' i with hp_i'
    have h0 : p_i'.totalDegree + i ≤ (p.totalDegree) := by
      apply MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le
      rw [← Polynomial.leadingCoeff, Polynomial.leadingCoeff_ne_zero]
      exact Iff.mpr (AddEquivClass.map_ne_zero_iff (MvPolynomial.finSuccEquiv F n)) p_nonzero
    have h1 : p_i' ≠ 0 := by
      rw [hp_i', hi, ← Polynomial.leadingCoeff, Polynomial.leadingCoeff_ne_zero]
      exact Iff.mpr (AddEquivClass.map_ne_zero_iff (MvPolynomial.finSuccEquiv F n)) p_nonzero
    -- We use the inductive hypothesis on p_i'
    replace ih := ih p_i' h1 S

    -- We then split the set of possible zeros into a union of two cases:
    -- In the first case, p_i' evaluates to 0.
    have h_first_half :
      Finset.card
        (Finset.filter
          (fun r ↦ MvPolynomial.eval (r ∘ Fin.succ) p_i' = 0)
          (Fintype.piFinset fun _ => S))
      ≤
      (MvPolynomial.totalDegree p - i) * S.card ^ n := by
      -- In this case, we bound the size of the set via the inductive hypothesis
      calc
        _ ≤ (MvPolynomial.totalDegree p_i') * S.card ^ n := by
          convert ih
          rw [mul_comm]
          convert Finset.card_filter_succ_piFinset_eq
                    (fun f ↦ (MvPolynomial.eval f) p_i' = 0) (fun _ => S)
        _ ≤ _ := by
          exact Nat.mul_le_mul_right (S.card ^ n) (Nat.le_sub_of_add_le h0)
    -- In the second case p_i' does not evaluate to zero.
    have h_second_half :
      Finset.card
          (Finset.filter
            (fun r ↦ MvPolynomial.eval r p = 0 ∧ MvPolynomial.eval (r ∘ Fin.succ) p_i' ≠ 0)
            ((Fintype.piFinset fun _ => S)))
      ≤
      i * S.card ^ n := by
      clear h_first_half
      -- In this case, given r on which p_i' does not evaluate to zero,
      -- p' mapped over the evaluation on r of p_i' is a nonzero univariate polynomial of degree i.
      -- There can therefore only be at most i zeros per r value.
      rw [← Finset.card_map (Equiv.toEmbedding (Equiv.piFinSucc n F)), Finset.map_filter,
        Finset.card_eq_sum_ones, Finset.sum_finset_product_right _
            (s := (Finset.filter (fun r ↦ MvPolynomial.eval r p_i' ≠ 0)
              (Fintype.piFinset fun _ => S)))
            -- Note that ((Equiv.piFinSucc n F).invFun (f, r))
            -- can be more simply written with Fin.cons
            (t := fun r => Finset.filter
                    (fun f => (MvPolynomial.eval ((Equiv.piFinSucc n F).invFun (f, r))) p = 0) S)]
      · simp_rw [← Finset.card_eq_sum_ones]
        apply le_trans (Finset.sum_le_sum (g := fun _ => i) _)
        · rw [Finset.sum_const, smul_eq_mul, mul_comm]
          apply Nat.mul_le_mul_left
          apply le_trans (Finset.card_filter_le _ _)
          apply le_of_eq
          rw [Fintype.card_piFinset]
          simp only [Finset.prod_const, Finset.card_fin]
        · intros r hr
          simp_rw [Equiv.invFun_as_coe, Equiv.piFinSucc_symm_apply,
            MvPolynomial.eval_eq_eval_mv_eval']
          rw [← hp']
          simp only [← hp', Fintype.mem_piFinset, Finset.mem_filter] at hr
          -- hr2 is in wikipedia P_i(r_2, ... , r_n) ≠ 0
          rcases hr with ⟨_, hr2⟩
          -- This proof is wikis P(x_1, r_2, ... r_n) = ∑ x_1^i P_i(r_2, ... r_n)
          set p_r := (Polynomial.map (MvPolynomial.eval r) p') with hp_r
          have : p_r.natDegree = i := by
            rw [hp_r, hi, Polynomial.natDegree_map_of_leadingCoeff_ne_zero (MvPolynomial.eval r) hr2]
          rw [← this]
          apply le_trans _ (Polynomial.card_roots' p_r)
          apply le_trans _ (Multiset.toFinset_card_le p_r.roots)
          apply Finset.card_le_card _
          rw [Finset.subset_iff]
          intro x
          rw [Finset.mem_filter,
            Multiset.mem_toFinset, Polynomial.mem_roots', and_imp, Polynomial.IsRoot.def]
          intros _ hxr
          simp_rw [ hxr, and_true]
          intro hpr_zero
          rw [hp_i', ← this, hpr_zero, Polynomial.natDegree_zero, ← Polynomial.coeff_map, ← hp_r,
            hpr_zero, Polynomial.coeff_zero] at hr2
          exact hr2 rfl
      · simp only [ne_eq, Equiv.piFinSucc_symm_apply, Finset.mem_filter, Finset.mem_map_equiv,
        Fintype.mem_piFinset, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ,
        Function.comp_apply, Equiv.invFun_as_coe, Prod.forall]
        tauto


    -- Putting these results together,
    -- we take a union bound over these two cases to finish the proof
    calc
      -- Pr[A]
      Finset.card
        (Finset.filter
          (fun r ↦ MvPolynomial.eval r p = 0)
          (Fintype.piFinset fun _ => S))
      * S.card
      =
      -- Pr [A ∩ B] + Pr [A ∩ Bᶜ]
      (Finset.card
        (Finset.filter
          (fun r ↦ MvPolynomial.eval r p = 0 ∧ MvPolynomial.eval (r ∘ Fin.succ) p_i' = 0)
          (Fintype.piFinset fun _ => S))
      +
      Finset.card
        (Finset.filter
          (fun r ↦ MvPolynomial.eval r p = 0 ∧ MvPolynomial.eval (r ∘ Fin.succ) p_i' ≠ 0)
          (Fintype.piFinset fun _ => S))
      )
      * S.card := by
        congr
        rw [← Finset.card_union_add_card_inter, Finset.filter_union_right, ← Finset.filter_and]
        simp only [ne_eq, and_or_and_not_iff, and_and_and_not_iff, Finset.filter_False,
          Finset.card_empty, add_zero]
      -- Pr [B] + Pr [A ∩ Bᶜ]
      _ ≤ (Finset.card
        (Finset.filter
          (fun r ↦ MvPolynomial.eval (r ∘ Fin.succ) p_i' = 0)
          (Fintype.piFinset fun _ => S))
      +
      Finset.card
        (Finset.filter
          (fun r ↦ MvPolynomial.eval r p = 0 ∧ MvPolynomial.eval (r ∘ Fin.succ) p_i' ≠ 0)
          (Fintype.piFinset fun _ => S))
      )
      * S.card := by
        apply Nat.mul_le_mul_right
        rw [add_le_add_iff_right]
        apply Finset.card_le_card
        apply Finset.monotone_filter_right
        rw [Pi.le_def]
        intro i
        simp_all only [ne_eq, MvPolynomial.finSuccEquiv_apply, MvPolynomial.coe_eval₂Hom,
          Polynomial.coeff_natDegree, Polynomial.leadingCoeff_eq_zero, ge_iff_le, not_and, not_not,
          le_Prop_eq, and_imp, implies_true]
      -- Bound the two terms by the casework done previously
      _ ≤ ((MvPolynomial.totalDegree p - i) * S.card ^ n
          +
          i * S.card ^ n
          )
      * S.card := Nat.mul_le_mul_right S.card (add_le_add h_first_half h_second_half)
      -- Simplify
      _ =
      MvPolynomial.totalDegree p * S.card ^ Nat.succ n := by
        rw [Nat.pow_succ, ← mul_assoc, ← add_mul, mul_eq_mul_right_iff,
          Nat.sub_add_cancel (le_of_add_le_right h0)]
        tauto
