/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Aaron Anderson, Yakov Pechersky
-/
module

public import Mathlib.Data.Fintype.Basic
public import Mathlib.GroupTheory.Perm.Support.Disjoint

/-!
# The support of a permutation as a `Finset`

The main theory of the support of a permutation is developed for the `Set`-valued
`Equiv.Perm.support`.

This file provides the `Finset`-valued version for a `Fintype` with decidable equality, and
transfers the `Set` API to it along `Equiv.Perm.coe_supportFinset_eq_support`.

## Main definitions

In the following, `f g : Equiv.Perm α`, where `α` is a `Fintype` with decidable equality.

* `Equiv.Perm.supportFinset`: the `Finset` of elements `x : α` that are not fixed by `f`.
  Two permutations `f` and `g` are `Disjoint` iff their `supportFinset`s are disjoint.

## Main statements

* `Equiv.Perm.coe_supportFinset_eq_support`: `(f.supportFinset : Set α) = f.support`.
-/

public section

open Equiv Finset Function

namespace Equiv.Perm

variable {α : Type*}

section supportFinset

variable [DecidableEq α] [Fintype α] {f g : Perm α}

/-- The `Finset` of nonfixed points of a permutation. -/
@[expose] def supportFinset (f : Perm α) : Finset α := {x | f x ≠ x}

@[simp]
theorem mem_supportFinset {x : α} : x ∈ f.supportFinset ↔ f x ≠ x := by
  rw [supportFinset, mem_filter, and_iff_right (mem_univ x)]

theorem notMem_supportFinset {x : α} : x ∉ f.supportFinset ↔ f x = x := by simp

@[norm_cast]
theorem coe_supportFinset_eq_support (f : Perm α) :
    (f.supportFinset : Set α) = f.support := by ext; simp

attribute [local simp] coe_supportFinset_eq_support

@[deprecated (since := "2026-11-16")] alias coe_support_eq_set_support :=
  coe_supportFinset_eq_support

@[simp]
theorem supportFinset_one : (1 : Perm α).supportFinset = ∅ := by simp [← coe_inj]

@[simp]
theorem supportFinset_refl : supportFinset (Equiv.refl α) = ∅ := supportFinset_one

@[simp]
theorem supportFinset_inv (σ : Perm α) : supportFinset σ⁻¹ = σ.supportFinset := by simp [← coe_inj]

theorem apply_mem_supportFinset {x : α} : f x ∈ f.supportFinset ↔ x ∈ f.supportFinset := by simp

theorem apply_inv_mem_supportFinset {x : α} :
    f⁻¹ x ∈ f.supportFinset ↔ x ∈ f.supportFinset := by
  simpa using f.apply_inv_mem_support

@[simp]
theorem supportFinset_eq_empty_iff : f.supportFinset = ∅ ↔ f = 1 := coe_inj.symm.trans <| by simp

@[simp]
theorem supportFinset_nonempty_iff : f.supportFinset.Nonempty ↔ f ≠ 1 := by
  simp [← coe_nonempty, support_nonempty_iff]

theorem supportFinset_ne_singleton {x} : f.supportFinset ≠ {x} := by
  simpa [← coe_inj] using support_ne_singleton

theorem supportFinset_eq_pair_iff {x y : α} : f.supportFinset = {x, y} ↔ x ≠ y ∧ f x = y ∧
    f y = x ∧ (∀ {z}, z ≠ x → z ≠ y → f z = z) := by simp [← coe_inj, support_eq_pair_iff]

theorem exists_pair_mem_supportFinset_ne (hf : f ≠ 1) :
    ∃ x ∈ f.supportFinset, ∃ y ∈ f.supportFinset, x ≠ y := by
  simpa using exists_pair_mem_support_ne hf

theorem exists_mem_supportFinset_ne (hf : f ≠ 1) (a : α) : ∃ b ∈ f.supportFinset, a ≠ b := by
  simpa using exists_mem_support_ne hf a

theorem mem_supportFinset_iff_of_commute {g c : Perm α} (hgc : Commute g c) (x : α) :
    g x ∈ c.supportFinset ↔ x ∈ c.supportFinset := by
  simpa using mem_support_iff_of_commute hgc x

theorem supportFinset_congr (h : f.supportFinset ⊆ g.supportFinset)
    (h' : ∀ x ∈ g.supportFinset, f x = g x) : f = g :=
  support_congr (by simpa using coe_subset.2 h) fun x hx => h' x (by simpa using hx)

theorem supportFinset_pow_subset (σ : Perm α) (n : ℕ) :
    (σ ^ n).supportFinset ⊆ σ.supportFinset := by simpa [← coe_subset] using support_pow_subset n

@[deprecated (since := "2026-11-16")] alias support_pow_le := supportFinset_pow_subset

theorem supportFinset_mul_subset (f g : Perm α) :
    (f * g).supportFinset ⊆ f.supportFinset ∪ g.supportFinset := by
  simpa [← coe_subset] using support_mul_subset f g

@[deprecated (since := "2026-11-16")] alias support_mul_le := supportFinset_mul_subset

theorem exists_mem_supportFinset_of_mem_supportFinset_prod {l : List (Perm α)} {x : α}
    (hx : x ∈ l.prod.supportFinset) : ∃ f : Perm α, f ∈ l ∧ x ∈ f.supportFinset := by
  simpa using exists_mem_support_of_mem_support_prod (by simpa using hx)

theorem isInvariant_of_supportFinset_subset {c : Perm α} {s : Finset α} (hcs : c.supportFinset ⊆ s)
    (x : α) : c x ∈ s ↔ x ∈ s :=
  isInvariant_of_support_subset (by simpa using coe_subset.2 hcs) x

@[deprecated (since := "2026-11-16")] alias isInvariant_of_support_le :=
    isInvariant_of_supportFinset_subset

/-- A permutation c is the extension of a restriction of g to s
  iff its support is contained in s and its restriction is that of g -/
lemma ofSubtype_eq_iff_mem_finset {g c : Equiv.Perm α} {s : Finset α}
    (hg : ∀ x, g x ∈ s ↔ x ∈ s) :
    ofSubtype (g.subtypePerm hg) = c ↔ c.supportFinset ⊆ s ∧
      ∀ (hc' : ∀ x, c x ∈ s ↔ x ∈ s), c.subtypePerm hc' = g.subtypePerm hg := by
  simp [← coe_subset, ofSubtype_eq_iff hg]

theorem supportFinset_ofSubtype {p : α → Prop} [DecidablePred p] (u : Perm (Subtype p)) :
    (ofSubtype u).supportFinset = u.supportFinset.map (Function.Embedding.subtype p) := by
  simpa [← coe_inj] using support_ofSubtype u

theorem mem_supportFinset_ofSubtype {p : α → Prop} [DecidablePred p] (x : α)
    (u : Perm (Subtype p)) :
    x ∈ (ofSubtype u).supportFinset ↔ ∃ (hx : p x), ⟨x, hx⟩ ∈ u.supportFinset := by
  simpa using mem_support_ofSubtype x u

theorem pow_apply_mem_supportFinset {n : ℕ} {x : α} :
    (f ^ n) x ∈ f.supportFinset ↔ x ∈ f.supportFinset := by simp

theorem zpow_apply_mem_supportFinset {n : ℤ} {x : α} :
    (f ^ n) x ∈ f.supportFinset ↔ x ∈ f.supportFinset := by simp

theorem pow_eq_on_of_mem_supportFinset (h : ∀ x ∈ f.supportFinset ∩ g.supportFinset, f x = g x)
    (k : ℕ) :
    ∀ x ∈ f.supportFinset ∩ g.supportFinset, (f ^ k) x = (g ^ k) x := by
  simpa using pow_eq_on_of_mem_support (by simpa using h) k

theorem disjoint_iff_disjoint_supportFinset : f.Disjoint g ↔
    _root_.Disjoint f.supportFinset g.supportFinset := by
  simp [← disjoint_coe, disjoint_iff_disjoint_support]

theorem Disjoint.disjoint_supportFinset
    (h : f.Disjoint g) : _root_.Disjoint f.supportFinset g.supportFinset :=
  disjoint_iff_disjoint_supportFinset.1 h

theorem Disjoint.supportFinset_mul (h : f.Disjoint g) :
    (f * g).supportFinset = f.supportFinset ∪ g.supportFinset := by
  simpa [← coe_inj] using h.support_mul

theorem supportFinset_prod_of_pairwise_disjoint (l : List (Perm α)) (h : l.Pairwise Perm.Disjoint) :
    l.prod.supportFinset = (l.map supportFinset).foldr (· ∪ ·) ⊥ := by
  simpa [← coe_inj, coe_foldr_union_map] using support_prod_of_pairwise_disjoint l h

theorem supportFinset_prod_subset (l : List (Perm α)) : l.prod.supportFinset ⊆
    (l.map supportFinset).foldr (· ∪ ·) ⊥ := by
  simpa [← l.prod.supportFinset.coe_subset, coe_foldr_union_map] using support_prod_subset l

@[deprecated (since := "2026-11-16")] alias support_prod_le := supportFinset_prod_subset

theorem supportFinset_zpow_subset (σ : Perm α) (n : ℤ) :
    (σ ^ n).supportFinset ⊆ σ.supportFinset := by
  simpa [← coe_subset] using support_zpow_subset n

@[deprecated (since := "2026-11-16")] alias support_zpow_le := supportFinset_zpow_subset

@[simp]
theorem supportFinset_swap {x y : α} (h : x ≠ y) : supportFinset (swap x y) = {x, y} := by
  simp [h, ← coe_inj]

theorem supportFinset_swap_iff (x y : α) : supportFinset (swap x y) = {x, y} ↔ x ≠ y := by
  simp [← coe_inj, support_swap_iff]

theorem supportFinset_swap_mul_swap {x y z : α} (h : List.Nodup [x, y, z]) :
    supportFinset (swap x y * swap y z) = {x, y, z} := by
  simpa [← coe_inj] using support_swap_mul_swap h

theorem supportFinset_sdiff_subset_supportFinset_swap_mul (f : Perm α) (x y : α) :
    f.supportFinset \ {x, y} ⊆ (swap x y * f).supportFinset := by
  simpa [← coe_subset] using support_sdiff_subset_support_swap_mul f x y

@[deprecated (since := "2026-11-16")] alias support_swap_mul_ge_support_sdiff :=
    supportFinset_sdiff_subset_supportFinset_swap_mul

@[deprecated (since := "2026-06-03")]
alias support_swap_mul_ge_support_diff := supportFinset_sdiff_subset_supportFinset_swap_mul

theorem supportFinset_swap_mul_eq (f : Perm α) (x : α) (h : f (f x) ≠ x) :
    (swap x (f x) * f).supportFinset = f.supportFinset \ {x} := by
  simpa [← coe_inj] using support_swap_mul_eq f x h

theorem mem_supportFinset_swap_mul_imp_mem_supportFinset_ne {x y : α}
    (hy : y ∈ supportFinset (swap x (f x) * f)) :
    y ∈ supportFinset f ∧ y ≠ x := by
  simpa using mem_support_swap_mul_imp_mem_support_ne (by simpa using hy)

theorem eq_on_supportFinset_mem_disjoint {l : List (Perm α)} (h : f ∈ l)
    (hl : l.Pairwise Perm.Disjoint) :
    ∀ x ∈ f.supportFinset, f x = l.prod x := by
  simpa using eq_on_support_mem_disjoint h hl

theorem Disjoint.mono_supportFinset {x y : Perm α} (h : f.Disjoint g)
    (hf : x.supportFinset ⊆ f.supportFinset)
    (hg : y.supportFinset ⊆ g.supportFinset) : x.Disjoint y :=
  h.mono (by simpa using coe_subset.2 hf) (by simpa using coe_subset.2 hg)

theorem supportFinset_subset_prod_of_mem {l : List (Perm α)} (h : f ∈ l)
    (hl : l.Pairwise Perm.Disjoint) :
    f.supportFinset ⊆ l.prod.supportFinset := by
  simpa [← coe_subset] using support_subset_prod_of_mem h hl

@[deprecated (since := "2026-11-16")] alias support_le_prod_of_mem :=
    supportFinset_subset_prod_of_mem

section ExtendDomain

variable {β : Type*} [DecidableEq β] [Fintype β] {p : β → Prop} [DecidablePred p]

@[simp]
theorem supportFinset_extend_domain (f : α ≃ Subtype p) {g : Perm α} :
    supportFinset (g.extendDomain f) = g.supportFinset.map f.asEmbedding := by
  simp [← coe_inj]

end ExtendDomain

section Conjugation

@[simp]
theorem supportFinset_conj : (f * g * f⁻¹).supportFinset = g.supportFinset.map f.toEmbedding := by
  simp [← coe_inj]

@[simp]
theorem supportFinset_conj_inv :
    (f⁻¹ * g * f).supportFinset = g.supportFinset.map f⁻¹.toEmbedding := by
  simp [← coe_inj]

end Conjugation

end supportFinset

@[simp]
theorem supportFinset_subtypePerm [DecidableEq α] {s : Finset α} (f : Perm α) (h) :
    (f.subtypePerm h : Perm s).supportFinset = ({x | f x ≠ x} : Finset s) := by
  ext; simp [Subtype.ext_iff]

end Equiv.Perm
