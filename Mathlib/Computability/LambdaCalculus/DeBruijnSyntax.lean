/-
Copyright (c) 2026 zayn7lie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Wang, Maksym Radziwill
-/
module

public import Mathlib.Data.Nat.Basic

/-!
# Untyped lambda calculus with de Bruijn indices

This file defines the syntax of untyped lambda terms using de Bruijn indices, together
with the basic operations on terms needed for β-reduction.  Using de Bruijn indices avoids
explicit reasoning about α-conversion and variable names.

## Main definitions

* `Lambda.Term`: the type of lambda terms.
* `Term.incre`: lifting (shifting) of free variables above a cutoff.
* `Term.subst`: raw substitution at a de Bruijn index.
* `Term.decre`: lowering of free variables above a cutoff.
* `Term.sub`: the substitution operation implementing β-contraction.

## Main lemmas

* `Term.incre_rfl`: shifting by `0` is the identity.
* `Term.decre_incre_elim`: lowering cancels a corresponding shift.
* `Term.var_sub_elim`, `Term.var_lt_sub`, `Term.var_gt_sub`: basic computations for
  substitution on variables.

## Notes

The definitions in this file are tailored to the later development of one-step β-reduction,
parallel reduction, and the Church–Rosser theorem.

## References

* <https://en.wikipedia.org/wiki/De_Bruijn_index>
-/


namespace Lambda

/-- using de Bruijn syntax avoiding α-conversion -/
public inductive Term : Type where
  | var : Nat → Term
  | abs : Term → Term
  | app : Term → Term → Term
deriving DecidableEq, Repr

open Term
namespace Term

notation:max "𝕧" str => Term.var str
notation:max "λ." t => Term.abs t
infixl:77 "·" => Term.app

/-- `incre i l t` increments `i` for all free vars `≥ l`. -/
@[simp, expose] public def incre (i : Nat) (l : Nat) : Term → Term
  | var k   => if l ≤ k then var (k + i) else var k
  | abs t   => abs (incre i (l + 1) t)
  | app t u => app (incre i l t) (incre i l u)

/-- `subst j s t` substitutes `j` with term `s` in `t`. -/
@[simp, expose] public def subst (j : Nat) (s : Term) : Term → Term
  | var k   => if k = j then s else var k
  | abs t   => abs (subst (j + 1) (incre 1 0 s) t)
  | app t u => app (subst j s t) (subst j s u)

/-- `decre c t` decrements free vars `> c` by 1. -/
@[simp, expose] public def decre (l : Nat) : Term → Term
  | var k   => if l < k then var (k - 1) else var k
  | abs t   => abs (decre (l + 1) t)
  | app t u => app (decre l t) (decre l u)

/-- Substitute into the body of a lambda: `(λ.t) s` -/
@[simp, expose] public def sub (t : Term) (n : Nat) (s : Term) := decre n (subst n (incre 1 n s) t)

/-- Increment of 0 is identity -/
@[simp] public theorem incre_rfl {l t} : incre 0 l t = t := by
  induction t generalizing l with
  | var k => simp_all
  | abs t ih => simp_all
  | app t u iht ihu => simp_all

/-- Decrement of increment with same bound is the same.
Lemma for `var_sub` -/
@[simp] public theorem decre_incre_elim {l t} : decre l (incre 1 l t) = t := by
  induction t generalizing l with
  | var k =>
      unfold decre incre
      cases em (l ≤ k) with
      | inl h => simp_all [Nat.lt_succ_of_le h]
      | inr h =>
          have : ¬(l < k) := by omega
          simp only [if_neg h, if_neg this]
  | abs t ih => simp_all
  | app t u iht ihu => simp_all

/-- Substitution of var n. -/
@[simp] public theorem var_sub_elim {n s} : ((𝕧 n).sub) n s = s := by
  simp_all only [sub, subst, ↓reduceIte, decre_incre_elim]

/-- Vacuously Substitution of var k to var k. -/
@[simp] public theorem var_lt_sub {k n s} (hk : k < n) :
    ((𝕧 k).sub) n s = 𝕧 k := by
  simp_all only [sub, subst, Nat.ne_of_lt hk, ↓reduceIte, decre, Nat.not_lt_of_gt hk]

/-- Vacuously Substitution of var k to var k - 1. -/
@[simp] public theorem var_gt_sub {k n s} (hk : k > n) :
    ((𝕧 k).sub) n s = 𝕧 (k - 1) := by
  simp_all [Nat.ne_of_gt hk]

/-- Increments elimination for same lower bound.
Special thanks to professor Radziwill @maksym-radziwill about
his idea of generalizing proper variable. -/
@[simp] public theorem incre_same_bound_elim {i j n t} :
    (incre i n (incre j n t)) = (incre (i + j) n t) := by
  induction t generalizing i n with
  | var k =>
      cases em (n ≤ k) with
      | inl h =>
          simp_all [le_trans h (Nat.le_add_right k j)]
          simp_all [Nat.add_comm, Nat.add_left_comm]
      | inr h => simp_all [if_neg h]
  | abs t' ih => simp_all
  | app t₁ t₂ ih₁ ih₂ => simp_all

/-- Communitivity of incre. -/
public theorem incre_comm {i j k l t} :
    (incre j (k + l + i) (incre i l t))=
      (incre i l (incre j (k + l) t)) := by
  induction t generalizing l with
  | var n =>
      cases em (k + l ≤ n) with
      | inl h =>
          have : l ≤ n := le_trans (Nat.le_add_left _ _) h
          simp_all [le_trans this (Nat.le_add_right _ _)]
          simp [Nat.add_comm, Nat.add_left_comm]
      | inr h =>
          simp only [incre, if_neg h]
          cases em (l ≤ n) with
          | inl h' =>
              simp_all only [not_le, ↓reduceIte, incre,
                Nat.add_le_add_iff_right, ite_eq_right_iff]
              intro hk
              have : n < n := Nat.lt_of_lt_of_le h hk
              exact (Nat.lt_irrefl n this).elim
          | inr h' =>
              simp_all only [not_le, if_neg h', incre,
                ite_eq_right_iff, var.injEq, Nat.add_eq_left]
              intro hk
              have hl : l ≤ n := by omega
              exact (Nat.lt_irrefl n
                (Nat.lt_of_lt_of_le h' hl)).elim
  | abs t' ih => simp_all [Nat.add_assoc, Nat.add_comm]
  | app t₁ t₂ ih₁ ih₂ => simp_all

public theorem incre_comm_zero {n s} :
    incre 1 (n + 1) (incre 1 0 s) =
      incre 1 0 (incre 1 n s) := by
  simpa using
      (incre_comm (i := 1) (l := 0) (j := 1) (k := n) (t := s))

@[simp] public theorem abs_sub_zero {t n s} :
    ((λ.t).sub n s) = λ.(t.sub (n + 1) (incre 1 0 s)) := by
  simp_all [incre_comm_zero]

private lemma incre_sub_var {i l n k s} :
    (incre i (l + n + 1) 𝕧 k).sub n (incre i (l + n) s) =
    incre i (l + n) ((𝕧 k).sub n s) := by
  cases em (k = n) with
  | inl h =>
      have : ¬ (l + n + 1 ≤ n) := by omega
      simp_all [if_neg this]
  | inr h =>
      cases em (l + n + 1 ≤ k) with
      | inl h' =>
          have : k + i ≠ n := by omega
          have : n < k := by omega
          have : l + n ≤ k - 1 := by omega
          have : n < k + i := by omega
          have : k + i - 1 = k - 1 + i := by omega
          simp_all only [ne_eq, sub, incre,
            ↓reduceIte, subst, decre]
      | inr h' =>
          simp_all only [not_le, sub, incre, if_neg h',
            subst, ↓reduceIte, decre]
          cases em (n < k) with
          | inl h'' =>
              simp_all only [↓reduceIte, incre,
                right_eq_ite_iff, var.injEq, Nat.left_eq_add]
              intro; omega
          | inr h'' =>
              simp_all only [not_lt, if_neg h'', incre,
                right_eq_ite_iff, var.injEq, Nat.left_eq_add]
              intro; omega

/-- The communitivity between sub and incre for free var. -/
@[simp] public theorem incre_sub {i l n t s} :
    ((incre i (l + n + 1) t).sub n (incre i (l + n) s)) =
    (incre i (l + n) (t.sub n s)) := by
  induction t generalizing l n s with
  | var k => exact incre_sub_var
  | abs t' ih =>
      simpa [← incre_comm_zero, ← incre_comm] using ih
  | app t₁ t₂ ih₁ ih₂ => simp_all

private lemma subst_zero_incre {n t u} :
    subst n t (incre 1 n u) = incre 1 n u := by
  induction u generalizing n t with
  | var k =>
      cases em (n ≤ k) with
      | inl h =>
          simp_all only [incre, ↓reduceIte, subst, ite_eq_right_iff]
          intro; omega
      | inr h =>
          simp_all only [not_le, incre, if_neg h,
            subst, ite_eq_right_iff]
          intro; omega
  | abs t ih => simp_all
  | app t v iht ihv => simp_all

private lemma sub_incre_same {u r m} :
    ((incre 1 m u).sub m r) = u := by
  simp_all [subst_zero_incre]

@[simp] public theorem sub_lift_zero {i t n u} :
    ((incre 1 i t).sub (n + i + 1) (incre 1 i u)) =
      incre 1 i (t.sub (n + i) u) := by
  induction t generalizing n u i with
  | var k =>
      cases em (k = n + i) with
      | inl hk => simp_all
      | inr hk =>
        cases em (k < n + i) with
          | inl hlt =>
              have hlt' : k + 1 < n + i + 1 := by omega
              have hnlt : ¬(n + i < k) := by omega
              simp only [sub, incre, subst]
              cases em (i ≤ k) with
              | inl hlt' => simp_all [if_neg hnlt]
              | inr hlt' =>
                  have h' : ¬(k = n + i + 1) := by omega
                  have : ¬(n + i + 1 < k) := by omega
                  simp_all [if_neg hlt', if_neg this, if_neg hnlt]
          | inr hlt =>
              have hle : i ≤ k := by omega
              have hgt : n + i < k := by omega
              have hlt : i ≤ k - 1 := by omega
              simp_all
              omega
  | abs t ih =>
      simpa [← incre_comm_zero] using
        (ih (i := i + 1) (n := n) (u := incre 1 0 u))
  | app t₁ t₂ ih₁ ih₂ => simp_all

private lemma sub_comm_var {k n m u s} :
    (((𝕧 k).sub ((n + m) + 1) (incre 1 m u)).sub m (s.sub (n + m) u))
    = (((𝕧 k).sub m s).sub (n + m) u) := by
  cases em (k = n + m + 1) with
  | inl hk =>
      have : ¬(n + m + 1 = m) := by omega
      have : m < n + m + 1 := by omega
      simp_all [subst_zero_incre]
  | inr hk =>
      cases em (k = m) with
      | inl hkm =>
          have : ¬(n + m + 1 < m) := by omega
          simp_all [if_neg this]
      | inr hkm =>
          have : ¬(k - 1 = n + m) := by omega
          cases em (n + m + 1 < k) with
          | inl hlt =>
              have : ¬(k - 1 = m) := by omega
              have : m < k := by omega
              have : m < k - 1 := by omega
              simp_all only [sub, subst, ↓reduceIte, decre,
                left_eq_ite_iff, not_lt, Nat.sub_le_iff_le_add, var.injEq]
              intro h
              exact (Nat.not_lt_of_ge h hlt).elim
          | inr hlt =>
              simp_all only [not_lt, sub, subst,
                ↓reduceIte, decre, if_neg hlt]
              cases em (m < k) with
              | inl hlt =>
                  simp_all only [↓reduceIte, subst, decre,
                    right_eq_ite_iff, var.injEq]
                  intro h
                  have nh : ¬(n + m < k - 1) := by omega
                  exact (nh h).elim
              | inr hlt =>
                  have hneq : ¬(k = n + m) := by omega
                  have hnlt : ¬(m < k) := by omega
                  simp_all only [not_false_eq_true, not_lt, if_neg hnlt, subst,
                    ↓reduceIte, decre, right_eq_ite_iff, var.injEq]
                  intro h
                  have nh : ¬(n + m < k) := by omega
                  exact (nh h).elim

public theorem sub_comm {t : Term} {n m s u} :
    ((t.sub ((n + m) + 1) (incre 1 m u)).sub m (s.sub (n + m) u))
    = ((t.sub m s).sub (n + m) u) := by
  induction t generalizing n m s u with
  | var k => exact sub_comm_var
  | abs t' ih =>
      have : ∀ k, (incre 1 0 (decre k (subst k (incre 1 k u) s))) =
          (decre (k + 1) (subst (k + 1) (incre 1 (k + 1)
          (incre 1 0 u)) (incre 1 0 s))) := by
        intro k
        simpa using
        (sub_lift_zero (t := s) (n := k) (u := u) (i := 0)).symm
      simpa [← incre_comm_zero, this] using
        (ih (n := n) (m := m + 1) (u := incre 1 0 u) (s := incre 1 0 s))
  | app t₁ t₂ ih₁ ih₂ => simp_all

public theorem sub_sub_incre {t : Term} {n k u s} :
    ((t.sub (n + 1) (incre (1 + k) 0 u)).sub 0 (s.sub n (incre k 0 u)))
    = ((t.sub 0 s).sub n (incre k 0 u)) := by
  have h' :
      ((t.sub (n + 1) (incre 1 0 (incre k 0 u))).sub 0
          ((s.sub n (incre k 0 u)))) =
        ((t.sub 0 s).sub n (incre k 0 u)) := by
    simpa using (sub_comm (t := t) (u := incre k 0 u) (s := s) (n := n) (m := 0))
  simpa using h'


end Term
end Lambda
