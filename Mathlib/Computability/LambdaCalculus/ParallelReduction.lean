/-
Copyright (c) 2026 zayn7lie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Wang
-/
import Mathlib.Computability.LambdaCalculus.BetaReduction

/-!
# Parallel β-reduction and complete developments

This file defines parallel β-reduction on de Bruijn lambda terms.  Parallel reduction
contracts β-redexes across a term in a syntax-directed way, and it is the key technical
device used later to prove the Church–Rosser theorem.

The file also defines the complete development `Term.dev` of a term and proves that every
parallel reduct further reduces in parallel to this complete development.

## Main definitions

* `Lambda.Par`: parallel β-reduction.
* `Lambda.ParStar`: the reflexive-transitive closure of `Par`.
* `Term.dev`: the complete development of a term.

## Main lemmas

* `par_refl`: reflexivity of parallel reduction.
* `beta_subset_par`: every β-step is a parallel step.
* `par_subset_betaStar`: every parallel step induces a β-reduction sequence.
* `incre_par`: parallel reduction is preserved by shifting.
* `par_subst`: parallel reduction is preserved by substitution.
* `par_dev`: every term parallel-reduces to its complete development.
* `par_to_dev`: every parallel reduct of a term further parallel-reduces to the complete
  development of the original term.

These results provide the diamond argument used in the final Church–Rosser proof.
-/

namespace Lambda
open Term

/-- Parallel β-reduction (syntax-directed). -/
inductive Par : Term → Term → Prop
  | var (n) : Par (𝕧 n) (𝕧 n)
  | abs {t t'} : Par t t' → Par (λ.t) (λ.t')
  | app {t t' u u'} : Par t t' → Par u u' → Par (t·u) (t'·u')
  | red {t t' s s'} : Par t t' → Par s s' →
      Par ((λ.t)·s) (t'.sub 0 s')
abbrev ParStar := Relation.ReflTransGen Par

/-- reflexivity of Par. -/
@[simp] theorem par_refl {t} : Par t t := by
  induction t with
  | var n => exact Par.var n
  | app t u iht ihu => exact Par.app iht ihu
  | abs t iht => exact Par.abs iht

/-- `Beta ⊆ Par`. -/
theorem beta_subset_par {a b} (h : Beta a b) : Par a b := by
  induction h with
  | appL h ih => exact Par.app ih par_refl
  | appR h ih => exact Par.app par_refl ih
  | abs h ih  => exact Par.abs ih
  | red t s  => exact Par.red par_refl par_refl

/-- Simulation lemma: `Par ⊆ BetaStar`. -/
theorem par_subset_betaStar {a b} (h : Par a b) :
    BetaStar a b := by
  induction h with
  | var n => exact BetaStar.refl (𝕧 n)
  | app hpt hpu hbt hbu =>
      exact BetaStar.trans
              (BetaStar.appL hbt) (BetaStar.appR hbu)
  | abs h ht => exact BetaStar.abs ht
  | red ht hs iht ihs =>
      exact BetaStar.trans (BetaStar.appL (BetaStar.abs iht))
        (BetaStar.tail (BetaStar.appR ihs) (Beta.red _ _))

@[simp] theorem incre_par {a b i l} (h : Par a b) :
    Par (incre i l a) (incre i l b) := by
  induction h generalizing l with
  | var n => exact par_refl
  | abs ht ih => exact Par.abs ih
  | app ht hu iht ihu => exact Par.app iht ihu
  | red ht hs iht ihs =>
      have hsub {t s : Term} :
          (incre i (l + 1) t).sub 0 (incre i l s) =
          incre i l (t.sub 0 s) := by
        simpa using
          (incre_sub (i := i) (l := l) (n := 0) (t := t) (s := s))
      rw [← hsub]
      exact Par.red iht ihs

/-- Substitution lemma for `par_to_dev`. -/
lemma par_subst {t t' u u'} (ht : Par t t') (hu : Par u u')
  (k : Nat) (n : Nat) :
    Par (t.sub n (incre k 0 u)) (t'.sub n (incre k 0 u')) := by
  match t, t' with
  | var t, var t' => match ht with
      | Par.var t => cases em (t = n) with
          | inl h => simp_all
          | inr h => cases em (t < n) with
              | inl h' => simp_all
              | inr h' =>
                  simp_all [ (Nat.lt_of_le_of_ne
                      (Nat.le_of_not_gt h') (Ne.symm h))]
  | abs t, abs t' => match ht with
      | Par.abs ht' =>
          have hp := Par.abs
            (par_subst ht' hu (1 + k) (n + 1))
          simp_all [← incre_comm_zero]
  | app t₁ t₂, t' => match t₁ with
      | abs t₁ => match ht with
          | Par.app ht₁ ht₂ =>
              exact Par.app
                (par_subst ht₁ hu k n) (par_subst ht₂ hu k n)
          | Par.red ht₁ ht₂ =>
              have hp := Par.red
                (par_subst ht₁ hu (1 + k) (n + 1))
                (par_subst ht₂ hu k n)
              rw [sub_sub_incre] at hp
              simp_all [← incre_comm_zero]
      | var t₁ => match ht with
          | Par.app ht₁ ht₂ =>
              exact Par.app
                (par_subst ht₁ hu k n) (par_subst ht₂ hu k n)
      | app t₁ t₁' => match ht with
          | Par.app ht₁ ht₂ =>
              exact Par.app
                (par_subst ht₁ hu k n) (par_subst ht₂ hu k n)

/-- Complete development (maximal Par) for a term. -/
def Term.dev : Term → Term
  | 𝕧 n     => 𝕧 n
  | λ.t     => λ.(t.dev)
  | (λ.t)·s => t.dev.sub 0 s.dev
  | t·u     => t.dev·u.dev

/-- t.dev is a par reduction for t. -/
theorem par_dev (t : Term) : Par t t.dev :=
  match t with
  | 𝕧 n     => Par.var n
  | λ.t     => Par.abs (par_dev t)
  | (λ.t)·u => Par.red (par_dev t) (par_dev u)
  | t·u => match t with
      | var n     => Par.app (Par.var n) (par_dev u)
      | abs t'    => Par.red (par_dev t') (par_dev u)
      | app t₁ t₂ => Par.app (par_dev (t₁·t₂)) (par_dev u)

/-- t.dev is max par reduction for t. -/
theorem par_to_dev {t u} (h : Par t u) : Par u (t.dev) := by
  match t, u with
  | var t', var u' =>
      match h with | Par.var t' => exact Par.var t'
  | abs t', abs u' =>
      match h with
      | Par.abs h' => exact Par.abs (par_to_dev h')
  | app t t', _ => match h with
      | Par.app ht hu =>
          rename_i u u'
          match t, u with
          | abs t, abs u => match ht with
              | Par.abs ht' =>
                exact Par.red
                  (par_to_dev ht') (par_to_dev hu)
          | var _, _ =>
              exact Par.app (par_to_dev ht) (par_to_dev hu)
          | app _ _, _ =>
              exact Par.app (par_to_dev ht) (par_to_dev hu)
      | Par.red hu ht =>
          have hp := par_subst
            (par_to_dev hu) (par_to_dev ht) 0 0
          repeat rw [incre_rfl] at hp
          exact hp

end Lambda
