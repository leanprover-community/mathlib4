/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
public import Mathlib.Algebra.FiniteSupport.Defs
public import Mathlib.Algebra.Order.Group.Indicator
public import Mathlib.Data.Set.Finite.Lattice

import Mathlib.Algebra.Group.Support

/-!
# Make fun_prop work for finite (mulitplicative) support

We provide API lemmas for the predicate `HasFiniteMulSupport` (and its additivized version
`HasFiniteSupport`) on functions so that `fun_prop` can prove it for functions that are
built from other functions with finite multiplicative support.
-/

@[expose] public section

namespace Function

variable {α M : Type*} [One M]

@[to_additive (attr := fun_prop)]
lemma hasFiniteMulSupport_fun_one : HasFiniteMulSupport (1 : α → M) := by
  simp [HasFiniteMulSupport]

@[to_additive (attr := fun_prop)]
lemma HasFiniteMulSupport.fun_comp {N : Type*} [One N] {g : M → N} {f : α → M}
    (hf : HasFiniteMulSupport f) (hg : g 1 = 1) :
    HasFiniteMulSupport fun a ↦ g (f a) :=
  hf.subset <| mulSupport_comp_subset hg f

@[to_additive (attr := fun_prop)]
lemma HasFiniteMulSupport.comp {N : Type*} [One N] {g : M → N} {f : α → M}
    (hf : HasFiniteMulSupport f) (hg : g 1 = 1) :
    HasFiniteMulSupport (g ∘ f) :=
  hf.subset <| mulSupport_comp_subset hg f

@[to_additive (attr := fun_prop)]
lemma HasFiniteMulSupport.fst {M' : Type*} [One M'] {f : α → M × M'} (hf : HasFiniteMulSupport f) :
    HasFiniteMulSupport fun a ↦ (f a).fst :=
  hf.comp rfl

@[to_additive (attr := fun_prop)]
lemma HasFiniteMulSupport.snd {M' : Type*} [One M'] {f : α → M × M'} (hf : HasFiniteMulSupport f) :
    HasFiniteMulSupport fun a ↦ (f a).snd :=
  hf.comp rfl

@[to_additive (attr := fun_prop)]
lemma HasFiniteMulSupport.prodMk {M' : Type*} [One M'] {f : α → M} {g : α → M'}
    (hf : HasFiniteMulSupport f) (hg : HasFiniteMulSupport g) :
    HasFiniteMulSupport fun a ↦ (f a, g a) := by
  simp only [HasFiniteMulSupport] at hf hg ⊢
  rw [mulSupport_prodMk f g]
  exact hf.union hg

@[to_additive (attr := to_fun (attr := fun_prop))]
lemma HasFiniteMulSupport.mul {M : Type*} [MulOneClass M] {f g : α → M}
    (hf : HasFiniteMulSupport f) (hg : HasFiniteMulSupport g) :
    HasFiniteMulSupport (f * g) :=
  (hf.union hg).subset <| mulSupport_mul ..

attribute [to_additive existing] HasFiniteMulSupport.fun_mul

@[to_additive (attr := to_fun (attr := fun_prop))]
lemma HasFiniteMulSupport.inv {M : Type*} [DivisionMonoid M] {f : α → M}
    (hf : HasFiniteMulSupport f) :
    HasFiniteMulSupport f⁻¹ :=
  hf.comp inv_one

attribute [to_additive existing] HasFiniteMulSupport.fun_inv

@[to_additive (attr := fun_prop)]
lemma HasFiniteMulSupport.prod {M : Type*} [CommMonoid M] {ι : Type*} {f : ι → α → M}
    (hf : ∀ i, HasFiniteMulSupport (f i)) (s : Finset ι) :
    HasFiniteMulSupport fun a ↦ ∏ i ∈ s, f i a :=
  (s.finite_toSet.biUnion fun i _ ↦ hf i).subset <| s.mulSupport_prod f

@[to_additive (attr := to_fun (attr := fun_prop))]
lemma HasFiniteMulSupport.div {M : Type*} [DivisionMonoid M] {f g : α → M}
    (hf : HasFiniteMulSupport f) (hg : HasFiniteMulSupport g) :
    HasFiniteMulSupport (f / g) :=
  (hf.union hg).subset <| mulSupport_div ..

attribute [to_additive existing] HasFiniteMulSupport.fun_div

@[to_additive (attr := to_fun (attr := fun_prop))]
lemma HasFiniteMulSupport.pow {M : Type*} [Monoid M] {f : α → M} (hf : HasFiniteMulSupport f)
    (n : ℕ) :
    HasFiniteMulSupport (f ^ n) :=
  hf.comp (one_pow n)

attribute [to_additive existing] HasFiniteMulSupport.fun_pow

@[to_additive (attr := to_fun (attr := fun_prop))]
lemma HasFiniteMulSupport.zpow {M : Type*} [DivisionMonoid M] {f : α → M}
    (hf : HasFiniteMulSupport f) (n : ℤ) :
    HasFiniteMulSupport (f ^ n) :=
  hf.comp (one_zpow n)

attribute [to_additive existing] HasFiniteMulSupport.fun_zpow

@[to_additive (attr := fun_prop)]
lemma HasFiniteMulSupport.max [LinearOrder M] {f g : α → M} (hf : HasFiniteMulSupport f)
    (hg : HasFiniteMulSupport g) :
    HasFiniteMulSupport fun a ↦ max (f a) (g a) :=
  (hf.union hg).subset <| mulSupport_max ..

@[to_additive (attr := fun_prop)]
lemma HasFiniteMulSupport.min [LinearOrder M] {f g : α → M} (hf : HasFiniteMulSupport f)
    (hg : HasFiniteMulSupport g) :
    HasFiniteMulSupport fun a ↦ min (f a) (g a) :=
  (hf.union hg).subset <| mulSupport_min ..

@[to_additive (attr := fun_prop)]
lemma HasFiniteMulSupport.sup [SemilatticeSup M] {f g : α → M} (hf : HasFiniteMulSupport f)
    (hg : HasFiniteMulSupport g) :
    HasFiniteMulSupport fun a ↦ f a ⊔ g a :=
  (hf.union hg).subset <| mulSupport_sup ..

@[to_additive (attr := fun_prop)]
lemma HasFiniteMulSupport.inf [SemilatticeInf M] {f g : α → M} (hf : HasFiniteMulSupport f)
    (hg : HasFiniteMulSupport g) :
    HasFiniteMulSupport fun a ↦ f a ⊓ g a :=
  (hf.union hg).subset <| mulSupport_inf ..

@[to_additive (attr := fun_prop)]
lemma HasFiniteMulSupport.iSup [ConditionallyCompleteLattice M] {ι : Sort*} [Nonempty ι]
    [Finite ι] {f : ι → α → M} (hf : ∀ i, HasFiniteMulSupport (f i)) :
    HasFiniteMulSupport fun a ↦ ⨆ i, f i a :=
  (Set.finite_iUnion hf).subset <| mulSupport_iSup f

@[to_additive (attr := fun_prop)]
lemma HasFiniteMulSupport.iInf [ConditionallyCompleteLattice M] {ι : Sort*} [Nonempty ι]
    [Finite ι] {f : ι → α → M} (hf : ∀ i, HasFiniteMulSupport (f i)) :
    HasFiniteMulSupport fun a ↦ ⨅ i, f i a :=
  (Set.finite_iUnion hf).subset <| mulSupport_iInf f

@[to_additive (attr := fun_prop)]
lemma HasFiniteMulSupport.pi {ι : Type*} [Finite α] {f : ι → α → M}
    (hf : ∀ a, HasFiniteMulSupport (f · a)) :
    HasFiniteMulSupport f := by
  simp only [HasFiniteMulSupport] at hf ⊢
  refine (Set.finite_iUnion hf).subset fun i hi ↦ ?_
  simp only [mem_mulSupport, Set.mem_iUnion] at hi ⊢
  exact ne_iff.mp hi

@[to_additive (attr := fun_prop)]
lemma HasFiniteMulSupport.sup' [SemilatticeSup M] {ι : Type*} {f : ι → α → M}
    (s : Finset ι) (hf : ∀ i ∈ s, HasFiniteMulSupport (f i)) (hs : s.Nonempty) :
    HasFiniteMulSupport fun a ↦ s.sup' hs (f · a) := by
  simp only [HasFiniteMulSupport] at hf ⊢
  refine (s.finite_toSet.biUnion hf).subset fun a ha ↦ ?_
  simp only [mem_mulSupport, SetLike.mem_coe, Set.mem_iUnion, exists_prop] at ha ⊢
  contrapose! ha
  exact Finset.sup'_eq_of_forall hs (fun x ↦ f x a) ha

@[to_additive (attr := fun_prop)]
lemma HasFiniteMulSupport.inf' [SemilatticeInf M] {ι : Type*} {f : ι → α → M}
    (s : Finset ι) (hf : ∀ i ∈ s, HasFiniteMulSupport (f i)) (hs : s.Nonempty) :
    HasFiniteMulSupport fun a ↦ s.inf' hs (f · a) := by
  simp only [HasFiniteMulSupport] at hf ⊢
  refine (s.finite_toSet.biUnion hf).subset fun a ha ↦ ?_
  simp only [mem_mulSupport, SetLike.mem_coe, Set.mem_iUnion, exists_prop] at ha ⊢
  contrapose! ha
  exact Finset.inf'_eq_of_forall hs (fun x ↦ f x a) ha

variable {β : Type*} {f : β → M} {g : α → β}

@[to_additive (attr := fun_prop)]
lemma HasFiniteMulSupport.comp_of_injective (hg : Injective g) (hf : f.HasFiniteMulSupport) :
    (f ∘ g).HasFiniteMulSupport := by
  refine Set.Finite.of_injOn ?_ (Set.injOn_of_injective hg) hf
  grind [Set.mapsTo_iff_subset_preimage]

@[to_additive (attr := fun_prop)]
lemma HasFiniteMulSupport.fun_comp_of_injective (hg : Injective g) (hf : f.HasFiniteMulSupport) :
    (fun a ↦ f (g a)).HasFiniteMulSupport :=
  hf.comp_of_injective hg

@[to_additive]
lemma HasFiniteMulSupport.of_comp [One β] (hfg : (f ∘ g).HasFiniteMulSupport) (h : f 1 = 1)
    (hf : Injective f) :
    g.HasFiniteMulSupport := by
  refine Set.Finite.subset hfg fun _ ha ↦ Set.mem_setOf.mpr fun H ↦ Set.mem_setOf.mp ha ?_
  grind

end Function

end
