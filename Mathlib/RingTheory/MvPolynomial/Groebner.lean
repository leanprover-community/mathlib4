import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Data.Finsupp.Lex

/-! # Groebner bases -/


namespace Finsupp


structure MonomialOrder (σ : Type*) where 
  syn : Type*
  clacm : CanonicallyLinearOrderedAddCommMonoid syn
  toSyn : (σ →₀ ℕ) ≃+ syn

instance (σ : Type*) (m : MonomialOrder σ) : CanonicallyLinearOrderedAddCommMonoid m.syn := m.clacm

theorem MonomialOrder.wf (σ : Type*) (m : MonomialOrder σ) : 
--    haveI : CanonicallyLinearOrderedAddCommMonoid m.syn := m.clacm
    WellFounded (fun d e ↦ m.toSyn d < m.toSyn e) := 
  sorry

end Finsupp
