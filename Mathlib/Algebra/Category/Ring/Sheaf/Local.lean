/-
Copyright (c) 2026 Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Nugent
-/
module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Local sheaves of rings

A sheaf of commutative rings is locally ringed if every section `a` has a covering on which
either `a` or `1 - a` is invertible. We use the weak version of this condition, which allows
the zero ring: no internal nontriviality condition is imposed.

For a nonempty finite family of sections whose sum is invertible, there is then a covering
on which one of the sections is invertible.
-/

@[expose] public section

universe u v w

open CategoryTheory Opposite

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{w})

/-- The sieve on which a section of a sheaf of rings is invertible. -/
@[simps -isSimp]
def isUnitSieve {X : C} (a : R.obj.obj (op X)) : Sieve X where
  arrows Y f := IsUnit (R.obj.map f.op a)
  downward_closed := by
    intro Y Z f hf g
    simpa only [op_comp, Functor.map_comp, CommRingCat.comp_apply] using
      hf.map (R.obj.map g.op).hom

@[simp]
lemma isUnitSieve_eq_top {X : C} {a : R.obj.obj (op X)} (ha : IsUnit a) :
    R.isUnitSieve a = ⊤ := by
  ext Y f
  exact iff_of_true (ha.map (R.obj.map f.op).hom) trivial

@[simp]
lemma isUnitSieve_pullback {X Y : C} (a : R.obj.obj (op X)) (f : Y ⟶ X) :
    (R.isUnitSieve a).pullback f = R.isUnitSieve (R.obj.map f.op a) := by
  ext Z g
  simp [isUnitSieve]

@[simp]
lemma finset_sup_isUnitSieve_apply {ι : Type*} (s : Finset ι) {X Y : C}
    (a : ι → R.obj.obj (op X)) (f : Y ⟶ X) :
    (s.sup fun i ↦ R.isUnitSieve (a i)) f ↔ ∃ i ∈ s, IsUnit (R.obj.map f.op (a i)) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s hi ih => simp [Finset.sup_cons, ih, isUnitSieve_apply]

@[simp]
lemma finset_sup_isUnitSieve_pullback {ι : Type*} (s : Finset ι) {X Y : C}
    (a : ι → R.obj.obj (op X)) (f : Y ⟶ X) :
    (s.sup fun i ↦ R.isUnitSieve (a i)).pullback f =
      s.sup fun i ↦ R.isUnitSieve (R.obj.map f.op (a i)) := by
  ext Z g
  simp [Sieve.pullback_apply]

/-- The weak local-ring condition for a sheaf of commutative rings on a site.

This is the usual local-ring condition internally, except that we do not require internal
nontriviality. In particular, the zero sheaf of rings satisfies this condition. This follows
the convention of SGA 4, Exposé IV, Exercise 13.9; the Stacks Project's definition of a locally
ringed site additionally requires internal nontriviality. -/
@[stacks 04ES "(1)"]
class IsLocallyRinged : Prop where
  isUnitSieve_mem {X : C} (a : R.obj.obj (op X)) :
    (R.isUnitSieve a ⊔ R.isUnitSieve (1 - a)) ∈ J X

variable [R.IsLocallyRinged]

/-- If two sections sum to one, locally one of them is invertible. -/
lemma isUnitSieve_sup_mem_of_add_eq_one {X : C} {a b : R.obj.obj (op X)}
    (h : a + b = 1) : (R.isUnitSieve a ⊔ R.isUnitSieve b) ∈ J X := by
  have hb : b = 1 - a := eq_sub_iff_add_eq.mpr (by simpa [add_comm] using h)
  rw [hb]
  exact IsLocallyRinged.isUnitSieve_mem a

/-- If the sum of two sections is invertible, locally one of them is invertible. -/
lemma isUnitSieve_sup_mem_of_isUnit_add {X : C} {a b : R.obj.obj (op X)}
    (h : IsUnit (a + b)) : (R.isUnitSieve a ⊔ R.isUnitSieve b) ∈ J X := by
  obtain ⟨c, hc⟩ := h.exists_left_inv
  have h' : c * a + c * b = 1 := by simpa only [← mul_add] using hc
  refine J.superset_covering ?_ (R.isUnitSieve_sup_mem_of_add_eq_one h')
  intro Y f hf
  rcases hf with hf | hf
  · left
    exact isUnit_of_mul_isUnit_right (by simpa only [isUnitSieve_apply, map_mul] using hf)
  · right
    exact isUnit_of_mul_isUnit_right (by simpa only [isUnitSieve_apply, map_mul] using hf)

/-- If a nonempty finite sum of sections is invertible, locally one summand is invertible.
Nonemptiness is needed since `IsLocallyRinged` allows the zero ring. -/
lemma finset_sup_isUnitSieve_mem_of_isUnit_sum {ι : Type*} {s : Finset ι}
    (hs : s.Nonempty) {X : C} (a : ι → R.obj.obj (op X))
    (h : IsUnit (∑ i ∈ s, a i)) : (s.sup fun i ↦ R.isUnitSieve (a i)) ∈ J X := by
  induction hs using Finset.Nonempty.cons_induction generalizing X with
  | singleton i =>
    simp only [Finset.sum_singleton] at h
    simpa only [Finset.sup_singleton, R.isUnitSieve_eq_top h] using J.top_mem X
  | cons i s hi hs ih =>
    simp only [Finset.sum_cons] at h
    refine J.transitive (R.isUnitSieve_sup_mem_of_isUnit_add h) _ ?_
    intro Y f hf
    rcases hf with hf | hf
    · apply J.covering_of_eq_top
      apply top_unique
      intro Z g _
      rw [Sieve.pullback_apply, finset_sup_isUnitSieve_apply]
      exact ⟨i, Finset.mem_cons_self i s, (R.isUnitSieve (a i)).downward_closed hf g⟩
    · rw [finset_sup_isUnitSieve_pullback]
      refine J.superset_covering (Finset.sup_mono (Finset.subset_cons _)) ?_
      apply ih
      simpa only [isUnitSieve_apply, map_sum] using hf

end CategoryTheory.Sheaf
