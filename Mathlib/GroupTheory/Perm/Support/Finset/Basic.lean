/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Aaron Anderson, Yakov Pechersky
-/
module

public import Mathlib.Data.Fintype.Card
public import Mathlib.GroupTheory.Perm.Support.Disjoint

/-!
# The support of a permutation as a `Finset`

## Main definitions

In the following, `f g : Equiv.Perm α`, where `α` is a `Fintype` with decidable equality.

* `Equiv.Perm.support`: the `Finset` of elements `x : α` that are not fixed by `f`.
  Two permutations `f` and `g` are `Disjoint` iff their `support`s are disjoint.
-/

public section

open Equiv Finset Function

namespace Equiv.Perm

variable {α : Type*}

section support

variable [DecidableEq α] [Fintype α] {f g : Perm α}

/-- The `Finset` of nonfixed points of a permutation. -/
@[expose] def support (f : Perm α) : Finset α := {x | f x ≠ x}

@[simp]
theorem mem_support {x : α} : x ∈ f.support ↔ f x ≠ x := by
  rw [support, mem_filter, and_iff_right (mem_univ x)]

theorem notMem_support {x : α} : x ∉ f.support ↔ f x = x := by simp

theorem coe_support_eq_set_support (f : Perm α) : (f.support : Set α) = { x | f x ≠ x } := by
  ext
  simp

@[simp]
theorem support_eq_empty_iff {σ : Perm α} : σ.support = ∅ ↔ σ = 1 := by
  simp_rw [Finset.ext_iff, mem_support, Finset.notMem_empty, iff_false, not_not,
    Equiv.Perm.ext_iff, one_apply]

@[simp]
theorem support_one : (1 : Perm α).support = ∅ := by rw [support_eq_empty_iff]

@[simp]
theorem support_refl : support (Equiv.refl α) = ∅ :=
  support_one

theorem support_congr (h : f.support ⊆ g.support) (h' : ∀ x ∈ g.support, f x = g x) : f = g := by
  grind [notMem_support]

/-- If g and c commute, then g stabilizes the support of c -/
theorem mem_support_iff_of_commute {g c : Perm α} (hgc : Commute g c) (x : α) :
    g x ∈ c.support ↔ x ∈ c.support := by
  simp only [mem_support, not_iff_not, ← mul_apply]
  rw [← hgc, mul_apply, Equiv.apply_eq_iff_eq]

theorem support_mul_le (f g : Perm α) : (f * g).support ≤ f.support ∪ g.support := fun x => by
  rw [mem_union, mem_support, mem_support, mem_support, mul_apply, ← not_and_or, not_imp_not]
  rintro ⟨hf, hg⟩
  rw [hg, hf]

theorem exists_mem_support_of_mem_support_prod {l : List (Perm α)} {x : α}
    (hx : x ∈ l.prod.support) : ∃ f : Perm α, f ∈ l ∧ x ∈ f.support := by
  contrapose! hx
  simp_rw [mem_support, not_not] at hx ⊢
  induction l with
  | nil => rfl
  | cons f l ih =>
    rw [List.prod_cons, mul_apply, ih, hx]
    · simp only [List.mem_cons, true_or]
    grind

theorem support_pow_le (σ : Perm α) (n : ℕ) : (σ ^ n).support ≤ σ.support := fun _ h1 =>
  mem_support.mpr fun h2 => mem_support.mp h1 (pow_apply_eq_self_of_apply_eq_self h2 n)

@[simp]
theorem support_inv (σ : Perm α) : support σ⁻¹ = σ.support := by
  simp_rw [Finset.ext_iff, mem_support, not_iff_not, inv_eq_iff_eq.trans eq_comm, imp_true_iff]

theorem apply_mem_support {x : α} : f x ∈ f.support ↔ x ∈ f.support := by
  rw [mem_support, mem_support, Ne, Ne, apply_eq_iff_eq]

/-- The support of a permutation is invariant -/
theorem isInvariant_of_support_le {c : Perm α} {s : Finset α} (hcs : c.support ≤ s) (x : α) :
    c x ∈ s ↔ x ∈ s := by
  by_cases hx' : x ∈ c.support
  · simp only [hcs hx', hcs (apply_mem_support.mpr hx')]
  · rw [notMem_support.mp hx']

/-- A permutation c is the extension of a restriction of g to s
  iff its support is contained in s and its restriction is that of g -/
lemma ofSubtype_eq_iff {g c : Equiv.Perm α} {s : Finset α}
    (hg : ∀ x, g x ∈ s ↔ x ∈ s) :
    ofSubtype (g.subtypePerm hg) = c ↔
      c.support ≤ s ∧
      ∀ (hc' : ∀ x, c x ∈ s ↔ x ∈ s), c.subtypePerm hc' = g.subtypePerm hg := by
  simp only [Equiv.ext_iff, subtypePerm_apply, Subtype.mk.injEq, Subtype.forall]
  constructor
  · intro h
    constructor
    · intro a ha
      by_contra ha'
      rw [mem_support, ← h a, ofSubtype_apply_of_not_mem (p := (· ∈ s)) _ ha'] at ha
      exact ha rfl
    · intro _ a ha
      rw [← h a, ofSubtype_apply_of_mem (p := (· ∈ s)) _ ha, subtypePerm_apply]
  · rintro ⟨hc, h⟩ a
    specialize h (isInvariant_of_support_le hc)
    by_cases ha : a ∈ s
    · rw [h a ha, ofSubtype_apply_of_mem (p := (· ∈ s)) _ ha, subtypePerm_apply]
    · rw [ofSubtype_apply_of_not_mem (p := (· ∈ s)) _ ha, eq_comm, ← notMem_support]
      exact Finset.notMem_mono hc ha

theorem support_ofSubtype {p : α → Prop} [DecidablePred p] (u : Perm (Subtype p)) :
    (ofSubtype u).support = u.support.map (Function.Embedding.subtype p) := by
  ext x
  simp only [mem_support, ne_eq, Finset.mem_map, Function.Embedding.coe_subtype, Subtype.exists,
    exists_and_right, exists_eq_right, not_iff_comm, not_exists, not_not]
  by_cases hx : p x
  · simp only [forall_prop_of_true hx, ofSubtype_apply_of_mem u hx, ← Subtype.coe_inj]
  · simp only [forall_prop_of_false hx, ofSubtype_apply_of_not_mem u hx]

theorem mem_support_ofSubtype {p : α → Prop} [DecidablePred p] (x : α) (u : Perm (Subtype p)) :
    x ∈ (ofSubtype u).support ↔ ∃ (hx : p x), ⟨x, hx⟩ ∈ u.support := by
  simp [support_ofSubtype]

theorem pow_apply_mem_support {n : ℕ} {x : α} : (f ^ n) x ∈ f.support ↔ x ∈ f.support := by
  simp only [mem_support, ne_eq, apply_pow_apply_eq_iff]

theorem zpow_apply_mem_support {n : ℤ} {x : α} : (f ^ n) x ∈ f.support ↔ x ∈ f.support := by
  simp only [mem_support, ne_eq, apply_zpow_apply_eq_iff]

theorem pow_eq_on_of_mem_support (h : ∀ x ∈ f.support ∩ g.support, f x = g x) (k : ℕ) :
    ∀ x ∈ f.support ∩ g.support, (f ^ k) x = (g ^ k) x := by
  induction k with
  | zero => simp
  | succ k hk =>
    intro x hx
    rw [pow_succ, mul_apply, pow_succ, mul_apply, h _ hx, hk]
    rwa [mem_inter, apply_mem_support, ← h _ hx, apply_mem_support, ← mem_inter]

theorem disjoint_iff_disjoint_support : Disjoint f g ↔ _root_.Disjoint f.support g.support := by
  simp [disjoint_iff_eq_or_eq, disjoint_iff, disjoint_iff, Finset.ext_iff,
    imp_iff_not_or]

theorem Disjoint.disjoint_support (h : Disjoint f g) : _root_.Disjoint f.support g.support :=
  disjoint_iff_disjoint_support.1 h

theorem Disjoint.support_mul (h : Disjoint f g) : (f * g).support = f.support ∪ g.support := by
  refine le_antisymm (support_mul_le _ _) fun a => ?_
  rw [mem_union, mem_support, mem_support, mem_support, mul_apply, ← not_and_or, not_imp_not]
  exact
    (h a).elim (fun hf h => ⟨hf, f.apply_eq_iff_eq.mp (h.trans hf.symm)⟩) fun hg h =>
      ⟨congr(f $hg).symm.trans h, hg⟩

theorem support_prod_of_pairwise_disjoint (l : List (Perm α)) (h : l.Pairwise Disjoint) :
    l.prod.support = (l.map support).foldr (· ∪ ·) ⊥ := by
  induction l with
  | nil => simp
  | cons hd tl hl =>
    rw [List.pairwise_cons] at h
    have : Disjoint hd tl.prod := disjoint_prod_right _ h.left
    simp [this.support_mul, hl h.right]

theorem support_prod_le (l : List (Perm α)) : l.prod.support ≤ (l.map support).foldr (· ∪ ·) ⊥ := by
  induction l with
  | nil => simp
  | cons hd tl hl =>
    rw [List.prod_cons, List.map_cons, List.foldr_cons]
    refine (support_mul_le hd tl.prod).trans ?_
    exact sup_le_sup le_rfl hl

theorem support_zpow_le (σ : Perm α) (n : ℤ) : (σ ^ n).support ≤ σ.support := fun _ h1 =>
  mem_support.mpr fun h2 => mem_support.mp h1 (zpow_apply_eq_self_of_apply_eq_self h2 n)

@[simp]
theorem support_swap {x y : α} (h : x ≠ y) : support (swap x y) = {x, y} := by
  grind [support]

theorem support_swap_iff (x y : α) : support (swap x y) = {x, y} ↔ x ≠ y := by
  refine ⟨fun h => ?_, fun h => support_swap h⟩
  rintro rfl
  simp [Finset.ext_iff] at h

theorem support_swap_mul_swap {x y z : α} (h : List.Nodup [x, y, z]) :
    support (swap x y * swap y z) = {x, y, z} := by
  simp only [List.not_mem_nil, and_true, List.mem_cons, not_false_iff, List.nodup_cons,
    and_self_iff, List.nodup_nil] at h
  push Not at h
  apply le_antisymm
  · convert support_mul_le (swap x y) (swap y z) using 1
    rw [support_swap h.left.left, support_swap h.right.left]
    simp [-Finset.union_singleton]
  · intro
    simp only [mem_insert, mem_singleton]
    rintro (rfl | rfl | rfl | _) <;>
      simp [swap_apply_of_ne_of_ne, h.left.left, h.left.left.symm, h.left.right.symm,
        h.left.right.left.symm, h.right.left.symm]

theorem support_swap_mul_ge_support_sdiff (f : Perm α) (x y : α) :
    f.support \ {x, y} ≤ (swap x y * f).support := by
  intro
  simp only [and_imp, Perm.coe_mul, Function.comp_apply, Ne, mem_support, mem_insert, mem_sdiff,
    mem_singleton]
  push Not
  rintro ha ⟨hx, hy⟩ H
  rw [swap_apply_eq_iff, swap_apply_of_ne_of_ne hx hy] at H
  exact ha H

@[deprecated (since := "2026-06-03")]
alias support_swap_mul_ge_support_diff := support_swap_mul_ge_support_sdiff

theorem support_swap_mul_eq (f : Perm α) (x : α) (h : f (f x) ≠ x) :
    (swap x (f x) * f).support = f.support \ {x} := by
  by_cases hx : f x = x
  · simp [hx, sdiff_singleton_eq_erase, notMem_support.mpr hx, erase_eq_of_notMem, pull_end]
  ext z
  by_cases hzx : z = x
  · simp [hzx]
  by_cases hzf : z = f x
  · simp [hzf, hx, h, swap_apply_of_ne_of_ne]
  by_cases hzfx : f z = x
  · simp [Ne.symm hzx, hzx, Ne.symm hzf, hzfx]
  · simp [hzx, hzfx, f.injective.ne hzx, swap_apply_of_ne_of_ne]

theorem mem_support_swap_mul_imp_mem_support_ne {x y : α} (hy : y ∈ support (swap x (f x) * f)) :
    y ∈ support f ∧ y ≠ x := by
  simp only [mem_support, swap_apply_def, mul_apply, f.injective.eq_iff] at *
  grind

omit [Fintype α] in
theorem disjoint_swap_swap {x y z t : α} (h : [x, y, z, t].Nodup) :
    Disjoint (swap x y) (swap z t) := by
  intro; grind

theorem Disjoint.mem_imp (h : Disjoint f g) {x : α} (hx : x ∈ f.support) : x ∉ g.support :=
  disjoint_left.mp h.disjoint_support hx

theorem eq_on_support_mem_disjoint {l : List (Perm α)} (h : f ∈ l) (hl : l.Pairwise Disjoint) :
    ∀ x ∈ f.support, f x = l.prod x := by
  induction l with
  | nil => simp at h
  | cons hd tl IH =>
    intro x hx
    rw [List.pairwise_cons] at hl
    rw [List.mem_cons] at h
    rcases h with (rfl | h)
    · rw [List.prod_cons, mul_apply,
        notMem_support.mp ((disjoint_prod_right tl hl.left).mem_imp hx)]
    · rw [List.prod_cons, mul_apply, ← IH h hl.right _ hx, eq_comm, ← notMem_support]
      refine (hl.left _ h).symm.mem_imp ?_
      simpa using hx

theorem Disjoint.mono {x y : Perm α} (h : Disjoint f g) (hf : x.support ≤ f.support)
    (hg : y.support ≤ g.support) : Disjoint x y := by
  rw [disjoint_iff_disjoint_support] at h ⊢
  exact h.mono hf hg

theorem support_le_prod_of_mem {l : List (Perm α)} (h : f ∈ l) (hl : l.Pairwise Disjoint) :
    f.support ≤ l.prod.support := by
  intro x hx
  rwa [mem_support, ← eq_on_support_mem_disjoint h hl _ hx, ← mem_support]

section ExtendDomain

variable {β : Type*} [DecidableEq β] [Fintype β] {p : β → Prop} [DecidablePred p]

@[simp]
theorem support_extend_domain (f : α ≃ Subtype p) {g : Perm α} :
    support (g.extendDomain f) = g.support.map f.asEmbedding := by
  ext b
  simp only [mem_map, Ne,
    mem_support]
  by_cases pb : p b
  · rw [extendDomain_apply_subtype _ _ pb]
    grind [asEmbedding_apply]
  · rw [extendDomain_apply_not_subtype _ _ pb]
    simp only [not_exists, false_iff, not_and, not_true]
    rintro a _ rfl
    exact pb (Subtype.prop _)

end ExtendDomain

end support

@[simp]
theorem support_subtypePerm [DecidableEq α] {s : Finset α} (f : Perm α) (h) :
    (f.subtypePerm h : Perm s).support = ({x | f x ≠ x} : Finset s) := by
  ext; simp [Subtype.ext_iff]

section Conjugation

variable [Fintype α] [DecidableEq α] {σ τ : Perm α}

@[simp]
theorem support_conj : (σ * τ * σ⁻¹).support = τ.support.map σ.toEmbedding := by
  ext
  simp only [mem_map_equiv, Perm.coe_mul, Function.comp_apply, Ne, Perm.mem_support,
    Equiv.eq_symm_apply, inv_def]

end Conjugation

end Equiv.Perm
