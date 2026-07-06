import Mathlib.AlgebraicGeometry.AlgebraicCycle.SkyscraperEulerChar
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

@[simp]
lemma degree_sum (D D' : AlgebraicCycle X ℤ) [CompactSpace X]
    : degree k (D + D') = degree k D + degree k D' := by
  simp [degree]
  ring_nf
  rw [finsum_add_distrib]
  · have :=
      LocallyFiniteSupport.finite_inter_support_of_isCompact D.locallyFiniteSupport
      CompactSpace.isCompact_univ
    simp only [Function.locallyFinsuppWithin.toFun_eq_coe, Set.univ_inter,
      Function.HasFiniteSupport, Function.support_mul] at this ⊢
    exact Set.Finite.inter_of_left this _
  · have :=
      LocallyFiniteSupport.finite_inter_support_of_isCompact D'.locallyFiniteSupport
      CompactSpace.isCompact_univ
    simp only [Function.locallyFinsuppWithin.toFun_eq_coe, Set.univ_inter,
      Function.HasFiniteSupport, Function.support_mul] at this ⊢
    exact Set.Finite.inter_of_left this _

@[simp]
lemma degree_neg (D : AlgebraicCycle X ℤ)
    : degree k (-D) = - degree k D := by simp [degree, finsum_neg_distrib]

@[simp]
lemma degree_minus (D D' : AlgebraicCycle X ℤ) [CompactSpace X]
    : degree k (D - D') = degree k D - degree k D' := by
  have := degree_sum k D (-D')
  simp [-degree_sum] at this
  ring_nf at this
  rw [← this]
  congr

open Function.locallyFinsuppWithin Classical in
@[simp]
lemma degree_single (p : X) {n : ℤ} : degree k (single p n) =
    n * (Module.finrank k (X.residueField p)):= by
  simp only [degree]
  rw [finsum_eq_finsetSum_of_support_subset (s := {p})]
  · simp
  · simp

end AlgebraicGeometry.AlgebraicCycle
