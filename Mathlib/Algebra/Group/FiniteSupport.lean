/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
public import Mathlib.Algebra.Order.Group.Indicator
public import Mathlib.Data.Set.Finite.Lattice

import Mathlib.Algebra.Group.Support

/-!
# Make fun_prop work for finite (mulitplicative) support

We define a new predicate `HasFiniteMulSupport` (and its additivized version) on functions
and provide the infrastructure so that `fun_prop` can prove it for functions that are
built from other functions with finite multiplicative support.
-/

@[expose] public section

namespace Function

variable {α M : Type*} [One M]

/-- The function `f` has finite multiplicative support. -/
@[to_additive (attr := fun_prop) /-- The function `f` has finite support. -/]
def HasFiniteMulSupport (f : α → M) : Prop := f.mulSupport.Finite

@[to_additive (attr := fun_prop)]
lemma hasFiniteMulSupport_one : HasFiniteMulSupport fun _ : α ↦ (1 : M) := by
  simp [HasFiniteMulSupport]

-- why do we need both versions?
@[to_additive (attr := fun_prop)]
lemma hasFiniteMulSupport_one' : HasFiniteMulSupport (1 : α → M) := by
  simp [HasFiniteMulSupport]

example : HasFiniteMulSupport (1 : ℕ → ℕ) := by fun_prop

example : HasFiniteMulSupport fun _ : ℕ ↦ (1 : ℤ) := by fun_prop

@[to_additive (attr := fun_prop)]
lemma hasFiniteMulSupport_fst {M' : Type*} [One M'] (f : α → M × M') (hf : HasFiniteMulSupport f) :
    HasFiniteMulSupport fun a ↦ (f a).fst := by
  simp only [HasFiniteMulSupport] at hf ⊢
  refine hf.subset fun a ha ↦ ?_
  simp only [mem_mulSupport] at ha ⊢
  contrapose! ha
  exact ha ▸ Prod.fst_one

@[to_additive (attr := fun_prop)]
lemma hasFiniteMulSupport_snd {M' : Type*} [One M'] (f : α → M × M') (hf : HasFiniteMulSupport f) :
    HasFiniteMulSupport fun a ↦ (f a).snd := by
  simp only [HasFiniteMulSupport] at hf ⊢
  refine hf.subset fun a ha ↦ ?_
  simp only [mem_mulSupport] at ha ⊢
  contrapose! ha
  exact ha ▸ Prod.snd_one

@[to_additive (attr := fun_prop)]
lemma hasFiniteMulSupport_prod_mk {M' : Type*} [One M'] (f : α → M) (g : α → M')
    (hf : HasFiniteMulSupport f) (hg : HasFiniteMulSupport g) :
    HasFiniteMulSupport fun a ↦ (f a, g a) := by
  simp only [HasFiniteMulSupport] at hf hg ⊢
  rw [mulSupport_prodMk f g]
  exact hf.union hg

@[to_additive (attr := fun_prop)]
lemma hasFiniteMulSupport_mul {M : Type*} [MulOneClass M] (f g : α → M)
    (hf : HasFiniteMulSupport f) (hg : HasFiniteMulSupport g) :
    HasFiniteMulSupport fun a ↦ f a * g a :=
  (hf.union hg).subset <| mulSupport_mul ..

@[to_additive (attr := fun_prop)]
lemma hasFiniteMulSupport_inv {M : Type*} [DivisionMonoid M] (f : α → M)
    (hf : HasFiniteMulSupport f) :
    HasFiniteMulSupport fun a ↦ (f a)⁻¹ := by
  simp only [HasFiniteMulSupport] at hf ⊢
  exact f.mulSupport_fun_inv ▸ hf

@[to_additive (attr := fun_prop)]
lemma hasFiniteMulSupport_prod {M : Type*} [CommMonoid M] {ι : Type*} (f : ι → α → M)
    (hf : ∀ i, HasFiniteMulSupport (f i)) (s : Finset ι) :
    HasFiniteMulSupport fun a ↦ ∏ i ∈ s, f i a :=
  (s.finite_toSet.biUnion fun i _ ↦ hf i).subset <| s.mulSupport_prod f

@[to_additive (attr := fun_prop)]
lemma hasFiniteMulSupport_div {M : Type*} [DivisionMonoid M] (f g : α → M)
    (hf : HasFiniteMulSupport f) (hg : HasFiniteMulSupport g) :
    HasFiniteMulSupport fun a ↦ f a / g a :=
  (hf.union hg).subset <| mulSupport_div ..

@[to_additive (attr := fun_prop)]
lemma hasFiniteMulSupport_pow {M : Type*} [Monoid M] (f : α → M) (hf : HasFiniteMulSupport f)
    (n : ℕ) :
    HasFiniteMulSupport fun a ↦ f a ^ n :=
  hf.subset <| f.mulSupport_pow n

@[to_additive (attr := fun_prop)]
lemma hasFiniteMulSupport_max [LinearOrder M] (f g : α → M) (hf : HasFiniteMulSupport f)
    (hg : HasFiniteMulSupport g) :
    HasFiniteMulSupport fun a ↦ max (f a) (g a) :=
    (hf.union hg).subset <| mulSupport_max ..

@[to_additive (attr := fun_prop)]
lemma hasFiniteMulSupport_min [LinearOrder M] (f g : α → M) (hf : HasFiniteMulSupport f)
    (hg : HasFiniteMulSupport g) :
    HasFiniteMulSupport fun a ↦ min (f a) (g a) :=
    (hf.union hg).subset <| mulSupport_min ..

@[to_additive (attr := fun_prop)]
lemma hasFiniteMulSupport_sup [SemilatticeSup M] (f g : α → M) (hf : HasFiniteMulSupport f)
    (hg : HasFiniteMulSupport g) :
    HasFiniteMulSupport fun a ↦ f a ⊔ g a :=
    (hf.union hg).subset <| mulSupport_sup ..

@[to_additive (attr := fun_prop)]
lemma hasFiniteMulSupport_inf [SemilatticeInf M] (f g : α → M) (hf : HasFiniteMulSupport f)
    (hg : HasFiniteMulSupport g) :
    HasFiniteMulSupport fun a ↦ f a ⊓ g a :=
    (hf.union hg).subset <| mulSupport_inf ..

@[to_additive (attr := fun_prop)]
lemma hasFiniteMulSupport_iSup [ConditionallyCompleteLattice M] {ι : Sort*} [Nonempty ι]
    [Finite ι] (f : ι → α → M) (hf : ∀ i, HasFiniteMulSupport (f i)) :
    HasFiniteMulSupport fun a ↦ ⨆ i, f i a :=
  (Set.finite_iUnion hf).subset <| mulSupport_iSup f

@[to_additive (attr := fun_prop)]
lemma hasFiniteMulSupport_iInf [ConditionallyCompleteLattice M] {ι : Sort*} [Nonempty ι]
    [Finite ι] (f : ι → α → M) (hf : ∀ i, HasFiniteMulSupport (f i)) :
    HasFiniteMulSupport fun a ↦ ⨅ i, f i a :=
  (Set.finite_iUnion hf).subset <| mulSupport_iInf f

@[to_additive (attr := fun_prop)]
lemma hasFiniteMulSupport_comp {N : Type*} [One N] (g : M → N) (f : α → M)
    (hf : HasFiniteMulSupport f) (hg : g 1 = 1) :
    HasFiniteMulSupport fun a ↦ g (f a) :=
  hf.subset <| mulSupport_comp_subset hg f

@[to_additive (attr := fun_prop)]
lemma hasFiniteMulSupport_pi {ι : Type*} [Finite α] (f : ι → α → M)
    (hf : ∀ a, HasFiniteMulSupport (f · a)) :
    HasFiniteMulSupport f := by
  simp only [HasFiniteMulSupport] at hf ⊢
  refine (Set.finite_iUnion hf).subset fun i hi ↦ ?_
  simp only [mem_mulSupport, Set.mem_iUnion] at hi ⊢
  exact ne_iff.mp hi

@[to_additive (attr := fun_prop)]
lemma hasFiniteMulSupport_sup' [SemilatticeSup M] {ι : Type*} (f : ι → α → M)
    (s : Finset ι) (hf : ∀ i ∈ s, HasFiniteMulSupport (f i)) (hs : s.Nonempty) :
    HasFiniteMulSupport fun a ↦ s.sup' hs (f · a) := by
  simp only [HasFiniteMulSupport] at hf ⊢
  refine (s.finite_toSet.biUnion hf).subset fun a ha ↦ ?_
  simp only [mem_mulSupport, SetLike.mem_coe, Set.mem_iUnion, exists_prop] at ha ⊢
  contrapose! ha
  exact Finset.sup'_eq_of_forall hs (fun x ↦ f x a) ha

@[to_additive (attr := fun_prop)]
lemma hasFiniteMulSupport_inf' [SemilatticeInf M] {ι : Type*} (f : ι → α → M)
    (s : Finset ι) (hf : ∀ i ∈ s, HasFiniteMulSupport (f i)) (hs : s.Nonempty) :
    HasFiniteMulSupport fun a ↦ s.inf' hs (f · a) := by
  simp only [HasFiniteMulSupport] at hf ⊢
  refine (s.finite_toSet.biUnion hf).subset fun a ha ↦ ?_
  simp only [mem_mulSupport, SetLike.mem_coe, Set.mem_iUnion, exists_prop] at ha ⊢
  contrapose! ha
  exact Finset.inf'_eq_of_forall hs (fun x ↦ f x a) ha

example {K ι : Type*} {v : ι → K → ℤ} (hv : ∀ x, HasFiniteMulSupport fun i ↦ v i x) (x y : K) :
    HasFiniteMulSupport fun i ↦ max (v i x * v i y) 1 := by
  fun_prop

end Function

end
