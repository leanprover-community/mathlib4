/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.Hom.TypeTags
public import Mathlib.Algebra.Order.Monoid.AssociatedEquiv
public import Mathlib.Algebra.Order.Monoid.Multiset
public import Mathlib.Order.Hom.WithTopBot
public import Mathlib.RingTheory.UniqueFactorizationDomain.FactorSet

/-!
# Structure of a unique factorization monoid

A (nontrivial) unique factorization monoid `α` is isomorphic to
`WithZero (αˣ × Multiplicative (Multiset ι))`, where `ι` is the type of irreducible associates.
This isomorphism is not canonical, as it depends on a choice of representative of each irreducible
associate.

Consequently, `Associates α` is order isomorphic to `WithTop (Multiset ι)`.

## Main declarations

* `UniqueFactorizationMonoid.mulEquivWithZero`: `α ≃* WithZero (αˣ × Multiplicative (Multiset ι))`.
* `UniqueFactorizationMonoid.associatesOrderIso`: `Associates α ≃o WithTop (Multiset ι)`.
-/

@[expose] public section

namespace UniqueFactorizationMonoid
open Associates

instance {ι : Type*} : Subsingleton (AddUnits (Multiset ι)) :=
  subsingleton_of_forall_eq 0 fun u ↦ AddUnits.ext (add_eq_zero.1 u.val_neg).1

variable {α : Type*} [CommMonoidWithZero α]

/-- The type of irreducible associates, which indexes the factors of an element of a unique
factorization monoid. -/
abbrev IrreducibleAssociates (α : Type*) [CommMonoidWithZero α] :=
  {p : Associates α // Irreducible p}

variable (α) in
/-- The monoid homomorphism sending a unit and a multiset of irreducible associates to the unit
times the product of chosen representatives of the irreducible associates. -/
noncomputable def ofFactors : αˣ × Multiplicative (Multiset (IrreducibleAssociates α)) →* α where
  toFun x := x.1 * (x.2.toAdd.map fun p ↦ p.1.out).prod
  map_one' := by simp
  map_mul' x y := by simp [Multiset.prod_add, mul_mul_mul_comm]

lemma mk_ofFactors (x : αˣ × Multiplicative (Multiset (IrreducibleAssociates α))) :
    Associates.mk (ofFactors α x) = FactorSet.prod (x.2.toAdd : Multiset _) := by
  rw [ofFactors, MonoidHom.coe_mk, OneHom.coe_mk, ← Associates.mkMonoidHom_apply, map_mul,
    map_multiset_prod, Multiset.map_map]
  simp only [Associates.mkMonoidHom_apply, mk_eq_one.2 x.1.isUnit, one_mul]
  simp [Function.comp_def]

variable [UniqueFactorizationMonoid α] [Nontrivial α]

lemma ofFactors_ne_zero (x : αˣ × Multiplicative (Multiset (IrreducibleAssociates α))) :
    ofFactors α x ≠ 0 := by
  rw [← Associates.mk_ne_zero, mk_ofFactors]
  exact (FactorSet.prod_eq_zero_iff _).not.2 (WithTop.coe_ne_top)

lemma ofFactors_injective : Function.Injective (ofFactors α) := by
  rintro ⟨u, m⟩ ⟨v, n⟩ h
  obtain rfl : m = n := by
    have := congrArg Associates.mk h
    rw [mk_ofFactors, mk_ofFactors] at this
    exact Multiplicative.toAdd.injective (WithTop.coe_injective (FactorSet.unique this))
  have hP : (m.toAdd.map fun p ↦ p.1.out).prod ≠ 0 := by
    simpa [ofFactors] using ofFactors_ne_zero (α := α) (1, m)
  have : (u : α) = v := mul_right_cancel₀ hP (by simpa [ofFactors] using h)
  rw [Units.ext this]

omit [Nontrivial α] in
lemma ofFactors_surjective {a : α} (ha : a ≠ 0) : ∃ x, ofFactors α x = a := by
  obtain ⟨s, hs⟩ := factors_eq_some_iff_ne_zero.2 (mk_ne_zero.2 ha)
  have h : Associates.mk (ofFactors α (1, Multiplicative.ofAdd s)) = Associates.mk a := by
    rw [mk_ofFactors, ← Associates.factors_prod (Associates.mk a), hs]
    rfl
  obtain ⟨u, hu⟩ := mk_eq_mk_iff_associated.1 h
  refine ⟨(u, Multiplicative.ofAdd s), ?_⟩
  rw [← hu]
  simp [ofFactors, mul_comm]

/-- A nontrivial unique factorization monoid is isomorphic to `WithZero` of its units times the
free commutative monoid on the irreducible associates.

This isomorphism is not canonical: it depends on a choice of representative of each irreducible
associate. -/
noncomputable def mulEquivWithZero :
    α ≃* WithZero (αˣ × Multiplicative (Multiset (IrreducibleAssociates α))) := by
  refine .symm <| .ofBijective (WithZero.lift' (ofFactors α)) ⟨fun x y h ↦ ?_, fun a ↦ ?_⟩
  · induction x using WithZero.recZeroCoe <;> induction y using WithZero.recZeroCoe
    · rfl
    · exact absurd h.symm (ofFactors_ne_zero _)
    · exact absurd h (ofFactors_ne_zero _)
    · simpa using ofFactors_injective (by simpa using h)
  · obtain rfl | ha := eq_or_ne a 0
    · exact ⟨0, rfl⟩
    · obtain ⟨x, hx⟩ := ofFactors_surjective ha
      exact ⟨x, hx⟩

/-- The associates of a nontrivial unique factorization monoid are order isomorphic to `WithTop` of
the multisets of irreducible associates. -/
noncomputable def associatesOrderIso :
    Associates α ≃o WithTop (Multiset (IrreducibleAssociates α)) :=
  (congrOrderMonoidIso mulEquivWithZero).toOrderIso.trans <| withZeroOrderIso.trans <|
    .withTopCongr <| prodOrderIso.trans <| (OrderIso.uniqueProd _ _).trans <|
      canonicalOrderMonoidIso.toOrderIso.trans (OrderIso.multiplicative _).symm

end UniqueFactorizationMonoid
