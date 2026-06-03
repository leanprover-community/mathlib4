/-
Copyright (c) 2026 metakunt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: metakunt
-/
module

public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
/-!
# Introspective relation

This defines the main relation for the proof as defined in their original paper.

## References


<https://www.cse.iitk.ac.in/users/manindra/algebra/primality_v6.pdf>.

## Main Theorems

- `Introspective.of_multiset`

## Tags

prime number, polynomial prime number test, AKS, Agrawal-Kayal-Saxena, Introspective
-/



variable {K : Type*} [CommRing K] [IsDomain K]

@[expose] public section Introspective

open Polynomial Nat

/-- The introspective relation, currently only useful for the proof of the AKS primality theorem. -/
def Introspective (f : K[X]) (n : ℕ) (r : ℕ) : Prop :=
  ∀ μ ∈ (primitiveRoots r K), f.eval (μ ^ n) = f.eval μ ^ n
namespace Introspective

variable {r : ℕ}

protected theorem one {f : K[X]} : Introspective f 1 r := by
  grind [Introspective]

protected theorem X_sub_C {p a : ℕ} [ExpChar K p] : Introspective (X - C (a : K)) p r := by
  intro μ hμ
  simp only [eval_sub, eval_X, eval_C]
  change (frobenius K p) μ - _ = (frobenius K p) (μ - a)
  simp

/-- The product of two polynomials is introspective. -/
protected theorem mul {n : ℕ} {f g : K[X]} (hf : Introspective f n r)
    (hg : Introspective g n r) : Introspective (f * g) n r := by
  intro μ hm
  simp only [eval_mul, hf μ hm, hg μ hm]
  ring

variable [NeZero r]

protected theorem eval_pow {μ : K} {f : K[X]} {n : ℕ} (h : IsPrimitiveRoot μ r)
    (hi : Introspective f n r) : f.eval (μ ^ n) = f.eval μ ^ n := by
  haveI : r ≠ 0 := NeZero.out
  exact hi μ ((mem_primitiveRoots (by lia)).mpr h)

protected theorem div {p a n : ℕ} [ExpChar K p] (h : Introspective (X - C (a : K)) n r) (hd : p ∣ n)
    (hc : p.Coprime r) : Introspective (X - C (a : K)) (n / p) r := by
  simp only [map_natCast, Introspective] at ⊢ h
  intro μ hμ
  have h2 : p * (n / p) = n := Nat.mul_div_cancel' hd
  simp only [eval_sub, eval_X, eval_natCast] at h ⊢
  let π := IsPrimitiveRoot.primitiveRootsPowEquivOfCoprime (R := K) hc
  replace h := h (π.symm ⟨μ, hμ⟩) (by grind)
  have _ : π (π.symm ⟨μ, hμ⟩) = μ := by simp
  revert h
  refine (Eq.congr ?_ ?_).mp
  · nth_rw 1 [sub_left_inj, ← h2, pow_mul]
    congr
  · nth_rw 1 [← h2, pow_mul]
    congr
    change (frobenius K p) _ = _
    simp only [map_sub]
    congr
    simp

/-- The product of coprime exponents is Introspective. -/
theorem mul_of_coprime {d e : ℕ} {f : K[X]} (hf : Introspective f e r)
    (hg : Introspective f d r) (h : e.Coprime r) : Introspective f (e * d) r := by
  intro μ hm
  have mu : μ ^ e ∈ primitiveRoots r K := by
    have hl : 0 < r := pos_of_neZero r
    simp only [mem_primitiveRoots hl] at ⊢ hm
    exact IsPrimitiveRoot.pow_of_coprime hm e h
  rw [pow_mul, hg (μ ^ e) mu, hf μ hm]
  ring

/-- Necessary condition for the auxilliary proof. -/
theorem of_multiset {p n b : ℕ} [ExpChar K p] (d e : ℕ) (s : Multiset (Fin b)) (hcprm : n.Coprime r)
    (hs : ∀ x : Fin b, Introspective (ofMultiset {(x.val : K)}) n r) (hdiv : p ∣ n) :
    Introspective (ofMultiset (s.map fun x ↦ (x.val : K))) (p ^ d * (n / p) ^ e) r := by
  simp only [ofMultiset_apply]
  have hcprm2 := Coprime.coprime_mul_right (Eq.symm (Nat.mul_div_cancel' hdiv) ▸ hcprm)
  induction s using Multiset.induction_on with
  | empty => simp [Introspective]
  | cons x l h1 =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    refine Introspective.mul ?_ h1
    clear h1
    refine mul_of_coprime ?_ ?_ ?_
    · induction d with
      | zero => simp [Introspective.one]
      | succ i hi =>
        simp only [map_natCast, pow_succ, mul_comm]
        exact mul_of_coprime Introspective.X_sub_C hi hcprm2
    · induction e with
      | zero => simp [Introspective.one]
      | succ i hi =>
        simp only [pow_succ, mul_comm]
        refine mul_of_coprime ?_ hi ?_
        · have hsx := hs x
          simp only [ofMultiset_apply, Multiset.map_singleton, Multiset.prod_singleton] at hsx
          exact Introspective.div hsx hdiv hcprm2
        · exact Coprime.coprime_div_left hcprm hdiv
    · exact Coprime.pow_left d hcprm2

end Introspective
