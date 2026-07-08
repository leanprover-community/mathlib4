import Mathlib.AlgebraicGeometry.AlgebraicCycle.ResidueFieldModule
import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic

/-!
# Degrees of divisors

In this file we define the degree of a divisor on a curve. This is really a special case of the
degree of a zero-cycle as in Fulton. This better definition is currently in a mathlib PR, but
for backwards compatibility reasons I am keeping these definitions here for this repo, as everything
in this branch needs to be refactored not to use Scheme.Over.

-/

universe u

namespace AlgebraicGeometry.AlgebraicCycle

variable {X : Scheme.{u}} (k : Type u) [Field k]
    (D : AlgebraicCycle X ℤ) [X.Over (Spec (CommRingCat.of k))]

noncomputable def degree : ℤ := ∑ᶠ (x : X), (D x) * (Module.finrank k (X.residueField x))

variable {D} in
/-- On a compact space, the summand defining `degree` has finite support. -/
lemma finite_support_degree_summand [CompactSpace X] :
    (Function.support fun x => D x * (Module.finrank k (X.residueField x) : ℤ)).Finite := by
  have := LocallyFiniteSupport.finite_inter_support_of_isCompact D.locallyFiniteSupport
    CompactSpace.isCompact_univ
  simp only [Function.locallyFinsuppWithin.toFun_eq_coe, Set.univ_inter,
    Function.support_mul] at this ⊢
  exact Set.Finite.inter_of_left this _

@[simp]
lemma degree_sum (D D' : AlgebraicCycle X ℤ) [CompactSpace X]
    : degree k (D + D') = degree k D + degree k D' := by
  simp only [degree, Function.locallyFinsuppWithin.coe_add, Pi.add_apply, add_mul]
  exact finsum_add_distrib (finite_support_degree_summand k) (finite_support_degree_summand k)

@[simp]
lemma degree_neg (D : AlgebraicCycle X ℤ)
    : degree k (-D) = - degree k D := by simp [degree, finsum_neg_distrib]

@[simp]
lemma degree_minus (D D' : AlgebraicCycle X ℤ) [CompactSpace X]
    : degree k (D - D') = degree k D - degree k D' := by
  rw [sub_eq_add_neg, degree_sum, degree_neg, sub_eq_add_neg]

open Function.locallyFinsuppWithin Classical in
@[simp]
lemma degree_single (p : X) {n : ℤ} : degree k (single p n) =
    n * (Module.finrank k (X.residueField p)):= by
  rw [degree, finsum_eq_finsetSum_of_support_subset _ (s := {p}) (by simp)]
  simp

end AlgebraicGeometry.AlgebraicCycle
