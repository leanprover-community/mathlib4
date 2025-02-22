/-
Copyright (c) 2024 Julian Berman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Berman
-/
import Mathlib.Algebra.ModEq
import Mathlib.Algebra.MonoidAlgebra.Ideal
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.DedekindDomain.Ideal
import Mathlib.RingTheory.Multiplicity
import Mathlib.RingTheory.Polynomial.Content
/-!
# The generalized factorial function over subsets of a Dedekind Domain

## References

 * https://www.jstor.org/stable/2695734
 * https://pdf.sciencedirectassets.com/272482/1-s2.0-S0022314X00X00534/1-s2.0-S0022314X9892220X/main.pdf?X-Amz-Security-Token=IQoJb3JpZ2luX2VjEHkaCXVzLWVhc3QtMSJIMEYCIQCi4U%2BQq8XXsNyCFxOOB1z3779RcF1x5SgA3cEo0TChjwIhAOIeVRwHVjJLumM8vZQHR1y3zWmWiFoCWmiRXgNCgNksKrMFCDIQBRoMMDU5MDAzNTQ2ODY1IgzCehXHeTR%2FbAkQ1vUqkAXZQZ1uzW2ORh%2BxjPJSYFGOBvOaKRfNOH0fEfAKDO915O5jhejV1NpDCxsJ%2FVenTzqNQolhp3W1Ud3YwxfmJE9%2BHmOK81cXfDG2%2FiCCP3RLUGBo5NYG6UulB1hC2HuqF3db4hO1F3AU1qdap%2FigWk0kI567w9Zx3Fg1jDONDuSwvFnfrbq%2FzAWYFUXVNNgWq3RFbL4moZkvd2Oi92uI00mgNjO2q2gNoxQ5cpEJgzstAjGZ0t1GVDL0%2FinHDW1QOVoutv%2FnX1s%2BguKrJ%2F1KWtXyi2PSBYruBtPNm2jG%2BWSe2cH4GS%2FnKOmgZQds7If0Djn5IdiwXtLv%2BiznazuSKQsCVdb6rIWu0NSY5IieqxYqqf1jlhpSNWxONbtyUDxtSVh1WVE%2FbJNAyrkipq1mKHoDuyEuutIQQvm2EZxP%2F%2BLuuzo%2BE5in70q6UM%2Fyxvx0zDgQivRmhLCbRCd2eZLtpufKE5TSNVeF3MW1iLRi74GeJIo%2FkoeJBSVMdEKUO%2BsLu0lM3iO06tk2mHAz7F8hxthYuqNGausolbRjjacQD2NWL%2BLXzSj1kklmXbqGrB%2BNdCH3Xj7omcs3qDm3ofdJwvsT3rRCKPHKn2UWw%2FB1voNR6ug7H5t8EbEmfgpLlHcXUp6JtkuspWovHg98Kq5gnx%2BdXADm58qi73oJjRDYZdBEYy5S0SNjxBAZkhA4baZNnp2fhpN%2FcGP68AWpEU9lZvt8mxzjHL%2FxGtzsIjHqDj9OB%2FoPcJt3GDCBsz8bW6%2F7zMvdPQPbqYoG7y84%2Br1VBdEhFsGtzlIz7Hjum8a7khtvM1JoTma%2BbCOmW%2BbnsyG%2F6dgVSWUZsk8AlYuMz6fB8ib7L9laJvUVYE833mD06wmwUTCX1My6BjqwAQvbAglYdP7vv8fDLWJ6M5V1WTCHj2SZ5yVhrlx8kTbGO28MGihwVK1xXOZ2L%2BH462Dfyh0SdjCfbDriFbTlCAbtRMvfA8bKCdNdR88s21GwKvtGvhOoaREnpiwyIUqvZ4lWClEF%2FC0lxUXC92zUAc%2F0Gmu0LXtv63Ef8lZyxiVeeGTEAotj1Ot93DCuLKku58C8aDIz2iBdh83wAZKeub5%2B3DLqKEzUa5TY0sfaglxo&X-Amz-Algorithm=AWS4-HMAC-SHA256&X-Amz-Date=20241206T174540Z&X-Amz-SignedHeaders=host&X-Amz-Expires=300&X-Amz-Credential=ASIAQ3PHCVTYTSABWTT7%2F20241206%2Fus-east-1%2Fs3%2Faws4_request&X-Amz-Signature=a8c185e03d8f01e9c8cda0181dea98082cfdfc647a729536d5e4483417e2a8af&hash=6d39e45f4a1d3b9f09e6ee51ebb0768816354b07db3b3047ebf4402a5d3d2afb&host=68042c943591013ac2b2430a89b270f6af2c76d8dfd086a07176afe7c76c2c61&pii=S0022314X9892220X&tid=spdf-d9c90067-67e5-47f5-b707-b0ed31f3c86d&sid=b54c02540a819-44f4-85bd-e2390804978cgxrqa&type=client&tsoh=d3d3LnNjaWVuY2VkaXJlY3QuY29t&ua=13115606040b52595100&rr=8ede174ad9b2903f&cc=us
 * https://en.wikipedia.org/wiki/Bhargava_factorial

 * https://www.youtube.com/watch?v=1YB-5occzSk
 * https://www.cip.ifi.lmu.de/~grinberg/algebra/fps20gfv.pdf
 * https://arxiv.org/pdf/2310.12949

## TODO

* Add to bibliography

## Tags
dedekind domain, factorial ideal, factorial, ideal
-/

open BigOperators
open Finset (range)
open Ideal (span)
open Set (mem_univ univ)
open scoped Nat Polynomial

variable {R : Type*} (S : Set R)

namespace Polynomial

variable [Semiring R]

def fixedDivisor (𝒻 : R[X]) : Ideal R := span <| 𝒻.eval '' S

lemma fixedDivisor_eq_span (𝒻 : R[X]) : 𝒻.fixedDivisor S = (span <| 𝒻.eval '' S) := rfl

example : (X ^ 5 + X : ℤ[X]).fixedDivisor univ = span {2} := by
  refine eq_of_le_of_le ?_ ?_
  · intro x hx
    apply Ideal.mem_span_singleton.mpr
    simp only [fixedDivisor_eq_span, eval_add, eval_pow, eval_X, Set.image_univ,
               Finsupp.mem_ideal_span_range_iff_exists_finsupp] at hx
    obtain ⟨c, hc⟩ := hx
    rw [← hc]
    apply Finset.dvd_sum
    intro i _
    have two_div : 2 ∣ i^5 + i := even_iff_two_dvd.mp <| by simp [parity_simps]
    exact two_div.mul_left <| c i
  · refine span ((X^5 + X : ℤ[X]).eval '' univ) |>.span_singleton_le_iff_mem.mpr ?_
    exact Ideal.mem_span 2 |>.mpr fun _ h ↦ h ⟨1, by norm_num⟩

end Polynomial

variable [CommRing R] [IsDomain R] [IsDedekindDomain R]

variable (p : ℕ) [Fact p.Prime]

structure Set.pOrdering where
  elems : ℕ → S
  emultiplicity_le (k : ℕ) (s : S) :
    0 < k →  -- TODO: Maybe this isn't necessary?
      emultiplicity ↑p (∏ i ∈ Finset.range k, ((elems k).val - (elems i).val)) ≤
        emultiplicity ↑p (∏ i ∈ Finset.range k, (s.val - (elems i).val))

instance : CoeFun (S.pOrdering p) (fun _ ↦ ℕ → R) := ⟨fun ν k ↦ ν.elems k |>.val⟩

/-- The generalized descending factorial given a p-ordering. -/
def Set.pOrdering.descFactorial (ν : S.pOrdering p) (n : ℕ) (x : R) :=
  ∏ i ∈ Finset.range n, (x - (ν i))

/-- The associated p-sequence for a p-ordering.

  Technically in the paper, this sequence is defined to be the powers, rather than the exponents
  themselves, but it seems like this perhaps shouldn't make much difference?
-/
noncomputable def Set.pOrdering.pSequence {ν : S.pOrdering p} (k : ℕ) :=
  emultiplicity ↑p <| ∏ i : Fin k, (ν k - ν i)


def pSequence.eq (ν₁ ν₂ : S.pOrdering p) : ν₁.pSequence = ν₂.pSequence := by
  sorry

open Polynomial (X C)

-- c_0 + (c_1 * (x - a_0)) + (c_2 * (x - a_0) * (x - a_1))
noncomputable def lemma_12_prod (pOrder : Set.pOrdering S p) (k : ℕ) (c : Fin (k + 1) → R): R[X]
   := ∑ i : Fin (k + 1), (c i) • ∏ j ∈ Finset.range i, (X - Polynomial.C (pOrder.elems j).val)

lemma lemma_12 (pOrder : Set.pOrdering S p) (k e : ℕ) (c : Fin (k + 1) → R) (s : R) (hs : s ∈ S):
  (lemma_12_prod S p pOrder k c).eval s ≡ 0 [PMOD (p^e : R)] := by sorry

/-- ℕ is a p-ordering of ℤ for any prime `p`. -/
def natPOrdering : (univ : Set ℤ).pOrdering p where
  elems := (⟨·, mem_univ _⟩)
  emultiplicity_le := fun k ⟨s, hs⟩ kpos ↦ emultiplicity_le_emultiplicity_of_dvd_right <| by
    have hdivk := k.factorial_dvd_descFactorial k
    rw [k.descFactorial_eq_prod_range k] at hdivk

    have prod_cast : (∏ j ∈ range k, (s - ↑(k - 1 - j))) = (∏ j ∈ range k, (s - ↑(k - 1) + j)) := by
      apply Finset.prod_congr (rfl)
      intro
      simp
      omega
    conv_rhs => rw [← Finset.prod_range_reflect, prod_cast]
    obtain ⟨a, ha⟩ := k.factorial_coe_dvd_prod (s - ↑(k - 1))
    have sub_cast : ∏ i ∈ range k, ↑(k - i) = ∏ i ∈ range k, ((k : ℤ) - (i : ℤ)) := by
      apply Finset.prod_congr rfl
      intro
      simp
      omega
    have fac_range := k.descFactorial_eq_prod_range k
    zify at fac_range
    rw [sub_cast] at fac_range
    simp [sub_cast, ← fac_range, Nat.descFactorial_self, ha]


namespace Polynomial

/-- A special case originally proved by Pòlya. -/
theorem polya_dvd {𝒻 : ℤ[X]} {k : ℕ} (hP : 𝒻.IsPrimitive) (hD : 𝒻.natDegree = k) :
    𝒻.fixedDivisor ∣ k ! :=
  sorry

/-- A special case originally proved by Pòlya. -/
theorem polya_exists (k : ℕ) : ∃ 𝒻 : ℤ[X], 𝒻.IsPrimitive ∧ 𝒻.natDegree = k ∧ 𝒻.fixedDivisor = k ! :=
  sorry

end Polynomial
