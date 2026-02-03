/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Support
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Order.ConditionallyCompleteLattice.Defs

import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
import Mathlib.Algebra.Order.Group.Indicator

/-!
# API for finite (mulitplicative) support

We provide a bunch of API lemmas allowing to deduce that the (multiplicative) support
of a given function is finite.
-/

@[expose] public section

namespace Function

variable {α M : Type*} [One M]

@[to_additive]
lemma finite_mulSupport_one : (fun _ : α ↦ (1 : M)).mulSupport.Finite :=
  mulSupport_fun_one (M := M) ▸ Set.finite_empty

@[to_additive]
lemma finite_mulSupport_fst {M' : Type*} [One M'] {f : α → M × M'} (hf : f.mulSupport.Finite) :
    (fun a ↦ (f a).fst).mulSupport.Finite := by
  refine hf.subset fun a ha ↦ ?_
  simp only [mem_mulSupport] at ha ⊢
  contrapose! ha
  exact ha ▸ Prod.fst_one

@[to_additive]
lemma finite_mulSupport_snd {M' : Type*} [One M'] {f : α → M × M'} (hf : f.mulSupport.Finite) :
    (fun a ↦ (f a).snd).mulSupport.Finite := by
  refine hf.subset fun a ha ↦ ?_
  simp only [mem_mulSupport] at ha ⊢
  contrapose! ha
  exact ha ▸ Prod.snd_one

@[to_additive]
lemma finite_mulSupport_prod_mk {M' : Type*} [One M'] {f : α → M} {g : α → M'}
    (hf : f.mulSupport.Finite) (hg : g.mulSupport.Finite) :
    (fun a ↦ (f a, g a)).mulSupport.Finite :=
  mulSupport_prodMk f g ▸ hf.union hg

@[to_additive]
lemma finite_mulSupport_binop {M N P : Type*} [One M] [One N] [One P] (op : M → N → P)
    (op1 : op 1 1 = 1) {f : α → M} {g : α → N} (hf : f.mulSupport.Finite)
    (hg : g.mulSupport.Finite) :
    (fun a ↦ op (f a) (g a)).mulSupport.Finite :=
  (hf.union hg).subset <| mulSupport_binop_subset _ op1 ..

@[to_additive]
lemma finite_mulSupport_mul {M : Type*} [MulOneClass M] {f g : α → M}
    (hf : f.mulSupport.Finite) (hg : g.mulSupport.Finite) :
    (fun a ↦ f a * g a).mulSupport.Finite :=
  (hf.union hg).subset <| mulSupport_mul ..

@[to_additive]
lemma finite_mulSupport_inv {M : Type*} [DivisionMonoid M] {f : α → M} (hf : f.mulSupport.Finite) :
    (fun a ↦ (f a)⁻¹).mulSupport.Finite :=
  f.mulSupport_fun_inv ▸ hf

@[to_additive]
lemma finite_mulSupport_prod {M : Type*} [CommMonoid M] {ι : Type*} {f : ι → α → M}
    (hf : ∀ i, (f i).mulSupport.Finite) (s : Finset ι) :
    (fun a ↦ ∏ i ∈ s, f i a).mulSupport.Finite :=
  (s.finite_toSet.biUnion fun i _ ↦ hf i).subset <| s.mulSupport_prod f

@[to_additive]
lemma finite_mulSupport_div {M : Type*} [DivisionMonoid M] {f g : α → M}
    (hf : f.mulSupport.Finite) (hg : g.mulSupport.Finite) :
    (fun a ↦ f a / g a).mulSupport.Finite :=
  (hf.union hg).subset <| mulSupport_div ..

@[to_additive]
lemma finite_mulSupport_pow {M : Type*} [Monoid M] {f : α → M} (hf : f.mulSupport.Finite)
    (n : ℕ) :
    (fun a ↦ f a ^ n).mulSupport.Finite :=
  hf.subset <| f.mulSupport_pow n

@[to_additive]
lemma finite_mulSupport_max [LinearOrder M] {f g : α → M} (hf : f.mulSupport.Finite)
    (hg : g.mulSupport.Finite) :
    (fun a ↦ max (f a) (g a)).mulSupport.Finite :=
    (hf.union hg).subset <| mulSupport_max ..

@[to_additive]
lemma finite_mulSupport_min [LinearOrder M] {f g : α → M} (hf : f.mulSupport.Finite)
    (hg : g.mulSupport.Finite) :
    (fun a ↦ min (f a) (g a)).mulSupport.Finite :=
    (hf.union hg).subset <| mulSupport_min ..

@[to_additive]
lemma finite_mulSupport_sup [SemilatticeSup M] {f g : α → M} (hf : f.mulSupport.Finite)
    (hg : g.mulSupport.Finite) :
    (fun a ↦ f a ⊔ g a).mulSupport.Finite :=
    (hf.union hg).subset <| mulSupport_sup ..

@[to_additive]
lemma finite_mulSupport_inf [SemilatticeInf M] {f g : α → M} (hf : f.mulSupport.Finite)
    (hg : g.mulSupport.Finite) :
    (fun a ↦ f a ⊓ g a).mulSupport.Finite :=
    (hf.union hg).subset <| mulSupport_inf ..

@[to_additive]
lemma finite_mulSupport_iSup [ConditionallyCompleteLattice M] {ι : Sort*} [Nonempty ι]
    [Finite ι] {f : ι → α → M} (hf : ∀ i, (f i).mulSupport.Finite) :
    (fun a ↦ ⨆ i, f i a).mulSupport.Finite :=
  (Set.finite_iUnion hf).subset <| mulSupport_iSup f

@[to_additive]
lemma finite_mulSupport_iInf [ConditionallyCompleteLattice M] {ι : Sort*} [Nonempty ι]
    [Finite ι] {f : ι → α → M} (hf : ∀ i, (f i).mulSupport.Finite) :
    (fun a ↦ ⨅ i, f i a).mulSupport.Finite :=
  (Set.finite_iUnion hf).subset <| mulSupport_iInf f

@[to_additive]
lemma finite_mulSupport_comp {N : Type*} [One N] {g : M → N} {f : α → M}
    (hf : f.mulSupport.Finite) (hg : g 1 = 1) :
    (fun a ↦ g (f a)).mulSupport.Finite :=
  hf.subset <| mulSupport_comp_subset hg f

@[to_additive]
lemma finite_mulSupport_pi {ι : Type*} [Finite α] {f : ι → α → M}
    (hf : ∀ a, (f · a).mulSupport.Finite) :
    f.mulSupport.Finite := by
  refine (Set.finite_iUnion hf).subset fun i hi ↦ ?_
  simp only [mem_mulSupport, Set.mem_iUnion] at hi ⊢
  exact ne_iff.mp hi

@[to_additive]
lemma finite_mulSupport_sup' [SemilatticeSup M] {ι : Type*} {f : ι → α → M}
    (s : Finset ι) (hf : ∀ i ∈ s, (f i).mulSupport.Finite) (hs : s.Nonempty) :
    (fun a ↦ s.sup' hs (f · a)).mulSupport.Finite := by
  refine (s.finite_toSet.biUnion hf).subset fun a ha ↦ ?_
  simp only [mem_mulSupport, SetLike.mem_coe, Set.mem_iUnion, exists_prop] at ha ⊢
  contrapose! ha
  exact Finset.sup'_eq_of_forall hs (f · a) ha

@[to_additive]
lemma finite_mulSupport_inf' [SemilatticeInf M] {ι : Type*} {f : ι → α → M}
    (s : Finset ι) (hf : ∀ i ∈ s, (f i).mulSupport.Finite) (hs : s.Nonempty) :
    (fun a ↦ s.inf' hs (f · a)).mulSupport.Finite := by
  refine (s.finite_toSet.biUnion hf).subset fun a ha ↦ ?_
  simp only [mem_mulSupport, SetLike.mem_coe, Set.mem_iUnion, exists_prop] at ha ⊢
  contrapose! ha
  exact Finset.inf'_eq_of_forall hs (f · a) ha

end Function

end
