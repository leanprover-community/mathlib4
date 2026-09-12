/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Fiberwise bijections

A *fibered set* is a finite set `S` equipped with a map `f : S → I`; the *fiber* of `i` is
the preimage of `i`.  Two fibered sets whose fibers all have the same cardinality are in
bijection *fiberwise*, that is by a bijection commuting with the two maps.

This file ports `theories/Combi/fibered_set.v` of
[Coq-Combi](https://github.com/math-comp/Coq-Combi).

## Main results

* `Fintype.exists_equiv_of_card_fiber_eq` : two finite types equipped with maps to a common
  type having fibers of equal cardinality are in bijection by a map commuting with the two
  maps.
* `Fintype.exists_bijOn_of_card_fiber_eq` : the same statement for two finite subsets of two
  types, in the form of a `Set.BijOn` (Coq `fbbijP`).
-/

@[expose] public section

namespace Fintype

variable {α β I : Type*}

/-- **Fiberwise bijection between fibered sets**: if two finite types `α` and `β` are
equipped with maps `f` and `g` to a common type whose fibers have the same cardinality,
then there is a bijection from `α` to `β` commuting with `f` and `g`. -/
theorem exists_equiv_of_card_fiber_eq [Finite α] [Finite β] (f : α → I) (g : β → I)
    (h : ∀ i, Nat.card {x // f x = i} = Nat.card {y // g y = i}) :
    ∃ e : α ≃ β, ∀ x, g (e x) = f x := by
  have efib : ∀ i : I, {x // f x = i} ≃ {y // g y = i} := fun i => (Finite.card_eq.mp (h i)).some
  exact ⟨(Equiv.sigmaFiberEquiv f).symm.trans
    ((Equiv.sigmaCongrRight efib).trans (Equiv.sigmaFiberEquiv g)), fun x =>
    (efib (f x) ⟨x, rfl⟩).2⟩

/-- The fiber of `i` in a finite subset `s`, as a subtype of the subtype attached to `s`,
is in bijection with the corresponding filtered finset. -/
def fiberSubtypeEquiv [DecidableEq I] (s : Finset α) (f : α → I) (i : I) :
    {x : {x // x ∈ s} // f x.1 = i} ≃ {x // x ∈ s.filter fun x => f x = i} where
  toFun x := ⟨x.1.1, Finset.mem_filter.2 ⟨x.1.2, x.2⟩⟩
  invFun y := ⟨⟨y.1, (Finset.mem_filter.1 y.2).1⟩, (Finset.mem_filter.1 y.2).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Fiberwise bijection between fibered sets** (Coq `fbbijP`): if two finite subsets `s`
and `t` of two types are equipped with maps `f` and `g` to a common type whose fibers have
the same cardinality, then there is a map from the first type to the second which is a
bijection from `s` onto `t` and which commutes with `f` and `g`. -/
theorem exists_bijOn_of_card_fiber_eq [Nonempty β] [DecidableEq I] (s : Finset α) (t : Finset β)
    (f : α → I) (g : β → I)
    (h : ∀ i, (s.filter fun x => f x = i).card = (t.filter fun y => g y = i).card) :
    ∃ e : α → β, Set.BijOn e ↑s ↑t ∧ ∀ x ∈ s, g (e x) = f x := by
  classical
  obtain ⟨E, hE⟩ := exists_equiv_of_card_fiber_eq (α := {x // x ∈ s}) (β := {y // y ∈ t})
    (fun x => f x.1) (fun y => g y.1) fun i => by
      rw [Nat.card_congr (fiberSubtypeEquiv s f i), Nat.card_congr (fiberSubtypeEquiv t g i),
        Nat.card_eq_finsetCard, Nat.card_eq_finsetCard, h i]
  set e : α → β := fun x => if hx : x ∈ s then (E ⟨x, hx⟩).1 else Classical.arbitrary β with he
  have hes : ∀ (x : α) (hx : x ∈ s), e x = (E ⟨x, hx⟩).1 := fun x hx => by
    simp [he, dite_eq_left hx]
  refine ⟨e, ⟨fun x hx ↦ ?_, fun x hx y hy hxy ↦ ?_, fun y hy ↦ ?_⟩, fun x hx ↦ ?_⟩
  · simp only [Finset.mem_coe] at hx ⊢
    rw [hes x hx]
    exact (E ⟨x, hx⟩).2
  · simp only [Finset.mem_coe] at hx hy
    rw [hes x hx, hes y hy] at hxy
    exact congrArg Subtype.val (E.injective (Subtype.ext hxy))
  · simp only [Finset.mem_coe] at hy
    refine ⟨(E.symm ⟨y, hy⟩).1, (E.symm ⟨y, hy⟩).2, ?_⟩
    simp [hes _ (E.symm ⟨y, hy⟩).2]
  · simp [hes x hx, hE]

end Fintype
