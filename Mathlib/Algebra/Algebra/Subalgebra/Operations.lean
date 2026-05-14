/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Antoine Chambert-Loir
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.Algebra.Ring.Action.Submonoid
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Sub.Unbundled.Basic
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Rat.Cast.Order
import Mathlib.RingTheory.Ideal.Lattice
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

/-!
# More operations on subalgebras

In this file we relate the definitions in `Mathlib/RingTheory/Ideal/Operations.lean` to subalgebras.
The contents of this file are somewhat random since both
`Mathlib/Algebra/Algebra/Subalgebra/Basic.lean` and `Mathlib/RingTheory/Ideal/Operations.lean` are
somewhat of a grab-bag of definitions, and this is whatever ends up in the intersection.
-/

@[expose] public section

assert_not_exists Cardinal

namespace AlgHom

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem ker_rangeRestrict (f : A →ₐ[R] B) : RingHom.ker f.rangeRestrict = RingHom.ker f :=
  Ideal.ext fun _ ↦ Subtype.ext_iff

end AlgHom

namespace Subalgebra

open Algebra

variable {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
variable (S' : Subalgebra R S)

/-- Suppose we are given `∑ i, lᵢ * sᵢ = 1` ∈ `S`, and `S'` a subalgebra of `S` that contains
`lᵢ` and `sᵢ`. To check that an `x : S` falls in `S'`, we only need to show that
`sᵢ ^ n • x ∈ S'` for some `n` for each `sᵢ`. -/
theorem mem_of_finsetSum_eq_one_of_pow_smul_mem
    {ι : Type*} (ι' : Finset ι) (s : ι → S) (l : ι → S)
    (e : ∑ i ∈ ι', l i * s i = 1) (hs : ∀ i, s i ∈ S') (hl : ∀ i, l i ∈ S') (x : S)
    (H : ∀ i, ∃ n : ℕ, (s i ^ n : S) • x ∈ S') : x ∈ S' := by
  suffices x ∈ Subalgebra.toSubmodule (Algebra.ofId S' S).range by
    obtain ⟨x, rfl⟩ := this
    exact x.2
  choose n hn using H
  let s' : ι → S' := fun x => ⟨s x, hs x⟩
  let l' : ι → S' := fun x => ⟨l x, hl x⟩
  have e' : ∑ i ∈ ι', l' i * s' i = 1 := by
    ext
    change S'.subtype (∑ i ∈ ι', l' i * s' i) = 1
    simpa only [map_sum, map_mul] using e
  have : Ideal.span (s' '' ι') = ⊤ := by
    rw [Ideal.eq_top_iff_one, ← e']
    apply sum_mem
    intro i hi
    exact Ideal.mul_mem_left _ _ <| Ideal.subset_span <| Set.mem_image_of_mem s' hi
  let N := ι'.sup n
  have hN := Ideal.span_pow_eq_top _ this N
  apply (Algebra.ofId S' S).range.toSubmodule.mem_of_span_top_of_smul_mem _ hN
  rintro ⟨_, _, ⟨i, hi, rfl⟩, rfl⟩
  change s' i ^ N • x ∈ _
  rw [← tsub_add_cancel_of_le (show n i ≤ N from Finset.le_sup hi), pow_add, mul_smul]
  refine Submodule.smul_mem _ (⟨_, pow_mem (hs i) _⟩ : S') ?_
  exact ⟨⟨_, hn i⟩, rfl⟩

@[deprecated (since := "2026-04-08")]
alias mem_of_finset_sum_eq_one_of_pow_smul_mem := mem_of_finsetSum_eq_one_of_pow_smul_mem

theorem mem_of_span_eq_top_of_smul_pow_mem
    (s : Set S) (l : s →₀ S) (hs : Finsupp.linearCombination S ((↑) : s → S) l = 1)
    (hs' : s ⊆ S') (hl : ∀ i, l i ∈ S') (x : S) (H : ∀ r : s, ∃ n : ℕ, (r : S) ^ n • x ∈ S') :
    x ∈ S' :=
  mem_of_finsetSum_eq_one_of_pow_smul_mem S' l.support (↑) l hs (fun x => hs' x.2) hl x H

end Subalgebra

section MulSemiringAction

variable (A B B' : Type*) [CommSemiring A] [Ring B] [Semiring B'] [Algebra A B] [Algebra A B']
variable (G : Type*) [Monoid G] [MulSemiringAction G B] [SMulCommClass G A B]
  [MulSemiringAction G B'] [SMulCommClass G A B']

/-- The set of fixed points under a group action, as a subring. -/
def FixedPoints.subsemiring : Subsemiring B' where
  __ := FixedPoints.addSubmonoid G B'
  __ := FixedPoints.submonoid G B'

/-- The set of fixed points under a group action, as a subring. -/
def FixedPoints.subring : Subring B where
  __ := FixedPoints.addSubgroup G B
  __ := FixedPoints.submonoid G B

/-- The set of fixed points under a group action, as a subalgebra. -/
def FixedPoints.subalgebra : Subalgebra A B' where
  __ := FixedPoints.subsemiring B' G
  algebraMap_mem' r g := smul_algebraMap g r

end MulSemiringAction
