/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Dynamics.PeriodicPts.Lemmas

/-!
# IMO 2006 Q5

Let $P(x)$ be a polynomial of degree $n>1$ with integer coefficients, and let $k$ be a positive
integer. Consider the polynomial $Q(x) = P(P(\ldots P(P(x))\ldots))$, where $P$ occurs $k$ times.
Prove that there are at most $n$ integers $t$ such that $Q(t)=t$.

## Sketch of solution

The following solution is adapted from
https://artofproblemsolving.com/wiki/index.php/2006_IMO_Problems/Problem_5.

Let $P^k$ denote the polynomial $P$ composed with itself $k$ times. We rely on a key observation: if
$P^k(t)=t$, then $P(P(t))=t$. We prove this by building the cyclic list
$(P(t)-t,P^2(t)-P(t),\ldots)$, and showing that each entry divides the next, which by transitivity
implies they all divide each other, and thus have the same absolute value.

If the entries in this list are all pairwise equal, then we can show inductively that for positive
$n$, $P^n(t)-t$ must always have the same sign as $P(t)-t$. Substituting $n=k$ gives us $P(t)=t$ and
in particular $P(P(t))=t$.

Otherwise, there must be two consecutive entries that are opposites of one another. This means
$P^{n+2}(t)-P^{n+1}(t)=P^n(t)-P^{n+1}(t)$, which implies $P^{n+2}(t)=P^n(t)$ and $P(P(t))=t$.

With this lemma, we can reduce the problem to the case $k=2$. If every root of $P(P(t))-t$ is also a
root of $P(t)-t$, then we're done. Otherwise, there exist $a$ and $b$ with $a\ne b$ and $P(a)=b$,
$P(b)=a$. For any root $t$ of $P(P(t))-t$, defining $u=P(t)$, we easily verify $a-t\mid b-u$,
$b-u\mid a-t$, $a-u\mid b-t$, $b-t\mid a-u$, which imply $|a-t|=|b-u|$ and $|a-u|=|b-t|$. By casing
on these equalities, we deduce $a+b=t+u$. This means that every root of $P(P(t))-t$ is a root of
$P(t)+t-a-b$, and we're again done.
-/


open Function Polynomial

namespace Imo2006Q5

/-- If every entry in a cyclic list of integers divides the next, then they all have the same
absolute value. -/
theorem Int.natAbs_eq_of_chain_dvd {l : Cycle ℤ} {x y : ℤ} (hl : l.Chain (· ∣ ·)) (hx : x ∈ l)
    (hy : y ∈ l) : x.natAbs = y.natAbs := by
  rw [Cycle.chain_iff_pairwise] at hl
  exact Int.natAbs_eq_of_dvd_dvd (hl x hx y hy) (hl y hy x hx)

theorem Int.add_eq_add_of_natAbs_eq_of_natAbs_eq {a b c d : ℤ} (hne : a ≠ b)
    (h₁ : (c - a).natAbs = (d - b).natAbs) (h₂ : (c - b).natAbs = (d - a).natAbs) :
    a + b = c + d := by
  rcases Int.natAbs_eq_natAbs_iff.1 h₁ with h₁ | h₁
  · rcases Int.natAbs_eq_natAbs_iff.1 h₂ with h₂ | h₂
    · exact (hne <| by linarith).elim
    · linarith
  · linarith

/-- The main lemma in the proof: if $P^k(t)=t$, then $P(P(t))=t$. -/
theorem Polynomial.isPeriodicPt_eval_two {P : Polynomial ℤ} {t : ℤ}
    (ht : t ∈ periodicPts fun x => P.eval x) : IsPeriodicPt (fun x => P.eval x) 2 t := by
  -- The cycle [P(t) - t, P(P(t)) - P(t), ...]
  let C : Cycle ℤ := (periodicOrbit (fun x => P.eval x) t).map fun x => P.eval x - x
  have HC : ∀ {n : ℕ}, (fun x => P.eval x)^[n + 1] t - (fun x => P.eval x)^[n] t ∈ C := by
    intro n
    rw [Cycle.mem_map, Function.iterate_succ_apply']
    exact ⟨_, iterate_mem_periodicOrbit ht n, rfl⟩
  -- Elements in C are all divisible by one another.
  have Hdvd : C.Chain (· ∣ ·) := by
    rw [Cycle.chain_map, periodicOrbit_chain' _ ht]
    intro n
    convert sub_dvd_eval_sub ((fun x => P.eval x)^[n + 1] t) ((fun x => P.eval x)^[n] t) P <;>
      rw [Function.iterate_succ_apply']
  -- Any two entries in C have the same absolute value.
  have Habs :
    ∀ m n : ℕ,
      ((fun x => P.eval x)^[m + 1] t - (fun x => P.eval x)^[m] t).natAbs =
        ((fun x => P.eval x)^[n + 1] t - (fun x => P.eval x)^[n] t).natAbs :=
    fun m n => Int.natAbs_eq_of_chain_dvd Hdvd HC HC
  -- We case on whether the elements on C are pairwise equal.
  by_cases HC' : C.Chain (· = ·)
  · -- Any two entries in C are equal.
    have Heq :
      ∀ m n : ℕ,
        (fun x => P.eval x)^[m + 1] t - (fun x => P.eval x)^[m] t =
          (fun x => P.eval x)^[n + 1] t - (fun x => P.eval x)^[n] t :=
      fun m n => Cycle.chain_iff_pairwise.1 HC' _ HC _ HC
    -- The sign of P^n(t) - t is the same as P(t) - t for positive n. Proven by induction on n.
    have IH (n : ℕ) : ((fun x => P.eval x)^[n + 1] t - t).sign = (P.eval t - t).sign := by
      induction n with
      | zero => rfl
      | succ n IH =>
        apply Eq.trans _ (Int.sign_add_eq_of_sign_eq IH)
        have H := Heq n.succ 0
        dsimp at H ⊢
        rw [← H, sub_add_sub_cancel']
    -- This implies that the sign of P(t) - t is the same as the sign of P^k(t) - t, which is 0.
    -- Hence P(t) = t and P(P(t)) = P(t).
    rcases ht with ⟨_ | k, hk, hk'⟩
    · exact (irrefl 0 hk).elim
    · have H := IH k
      rw [hk'.isFixedPt.eq, sub_self, Int.sign_zero, eq_comm, Int.sign_eq_zero_iff_zero,
        sub_eq_zero] at H
      simp [IsPeriodicPt, IsFixedPt, H]
  · -- We take two nonequal consecutive entries.
    rw [Cycle.chain_map, periodicOrbit_chain' _ ht] at HC'
    push_neg at HC'
    obtain ⟨n, hn⟩ := HC'
    -- They must have opposite sign, so that P^{k + 1}(t) - P^k(t) = P^{k + 2}(t) - P^{k + 1}(t).
    rcases Int.natAbs_eq_natAbs_iff.1 (Habs n n.succ) with hn' | hn'
    · apply (hn _).elim
      convert hn' <;> simp only [Function.iterate_succ_apply']
    -- We deduce P^{k + 2}(t) = P^k(t) and hence P(P(t)) = t.
    · rw [neg_sub, sub_right_inj] at hn'
      simp only [Function.iterate_succ_apply'] at hn'
      exact isPeriodicPt_of_mem_periodicPts_of_isPeriodicPt_iterate ht hn'.symm

theorem Polynomial.iterate_comp_sub_X_ne {P : Polynomial ℤ} (hP : 1 < P.natDegree) {k : ℕ}
    (hk : 0 < k) : P.comp^[k] X - X ≠ 0 := by
  rw [sub_ne_zero]
  apply_fun natDegree
  simpa using (one_lt_pow₀ hP hk.ne').ne'

/-- We solve the problem for the specific case k = 2 first. -/
theorem imo2006_q5' {P : Polynomial ℤ} (hP : 1 < P.natDegree) :
    (P.comp P - X).roots.toFinset.card ≤ P.natDegree := by
  -- Auxiliary lemmas on degrees.
  have hPX : (P - X).natDegree = P.natDegree := by
    rw [natDegree_sub_eq_left_of_natDegree_lt]
    simpa using hP
  have hPX' : P - X ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hPX
    rw [← hPX] at hP
    exact (zero_le_one.not_gt hP).elim
  -- If every root of P(P(t)) - t is also a root of P(t) - t, then we're done.
  by_cases H : (P.comp P - X).roots.toFinset ⊆ (P - X).roots.toFinset
  · exact (Finset.card_le_card H).trans
      ((Multiset.toFinset_card_le _).trans ((card_roots' _).trans_eq hPX))
  -- Otherwise, take a, b with P(a) = b, P(b) = a, a ≠ b.
  · rcases Finset.not_subset.1 H with ⟨a, ha, hab⟩
    replace ha := isRoot_of_mem_roots (Multiset.mem_toFinset.1 ha)
    rw [IsRoot.def, eval_sub, eval_comp, eval_X, sub_eq_zero] at ha
    rw [Multiset.mem_toFinset, mem_roots hPX', IsRoot.def, eval_sub, eval_X, sub_eq_zero]
      at hab
    set b := P.eval a
    -- More auxiliary lemmas on degrees.
    have hPab : (P + (X : ℤ[X]) - a - b).natDegree = P.natDegree := by
      rw [sub_sub, ← Int.cast_add]
      have h₁ : (P + X).natDegree = P.natDegree := by
        rw [natDegree_add_eq_left_of_natDegree_lt]
        simpa using hP
      rwa [natDegree_sub_eq_left_of_natDegree_lt]
      rw [h₁, natDegree_intCast]
      exact zero_lt_one.trans hP
    have hPab' : P + (X : ℤ[X]) - a - b ≠ 0 := by
      intro h
      rw [h, natDegree_zero] at hPab
      rw [← hPab] at hP
      exact (zero_le_one.not_gt hP).elim
    -- We claim that every root of P(P(t)) - t is a root of P(t) + t - a - b. This allows us to
    -- conclude the problem.
    suffices H' : (P.comp P - X).roots.toFinset ⊆ (P + (X : ℤ[X]) - a - b).roots.toFinset from
      (Finset.card_le_card H').trans
        ((Multiset.toFinset_card_le _).trans <| (card_roots' _).trans_eq hPab)
    -- Let t be a root of P(P(t)) - t, define u = P(t).
    intro t ht
    replace ht := isRoot_of_mem_roots (Multiset.mem_toFinset.1 ht)
    rw [IsRoot.def, eval_sub, eval_comp, eval_X, sub_eq_zero] at ht
    simp only [mem_roots hPab', sub_eq_iff_eq_add, Multiset.mem_toFinset, IsRoot.def,
      eval_sub, eval_add, eval_X, eval_intCast, Int.cast_id, zero_add]
    -- An auxiliary lemma proved earlier implies we only need to show |t - a| = |u - b| and
    -- |t - b| = |u - a|. We prove this by establishing that each side of either equation divides
    -- the other.
    apply (Int.add_eq_add_of_natAbs_eq_of_natAbs_eq hab _ _).symm <;>
        apply Int.natAbs_eq_of_dvd_dvd <;> set u := P.eval t
    · rw [← ha, ← ht]; apply sub_dvd_eval_sub
    · apply sub_dvd_eval_sub
    · rw [← ht]; apply sub_dvd_eval_sub
    · rw [← ha]; apply sub_dvd_eval_sub

end Imo2006Q5

open Imo2006Q5

/-- The general problem follows easily from the k = 2 case. -/
theorem imo2006_q5 {P : Polynomial ℤ} (hP : 1 < P.natDegree) {k : ℕ} (hk : 0 < k) :
    (P.comp^[k] X - X).roots.toFinset.card ≤ P.natDegree := by
  refine (Finset.card_le_card fun t ht => ?_).trans (imo2006_q5' hP)
  have hP' : P.comp P - X ≠ 0 := by
    simpa [Nat.iterate] using Polynomial.iterate_comp_sub_X_ne hP zero_lt_two
  replace ht := isRoot_of_mem_roots (Multiset.mem_toFinset.1 ht)
  rw [IsRoot.def, eval_sub, iterate_comp_eval, eval_X, sub_eq_zero] at ht
  rw [Multiset.mem_toFinset, mem_roots hP', IsRoot.def, eval_sub, eval_comp, eval_X,
    sub_eq_zero]
  exact Polynomial.isPeriodicPt_eval_two ⟨k, hk, ht⟩
