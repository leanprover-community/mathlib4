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

* `Equiv.Perm.supportFinset`: the `Finset` of elements `x : α` that are not fixed by `f`.
  Two permutations `f` and `g` are `Disjoint` iff their `supportFinset`s are disjoint.
-/

public section

open Equiv Finset Function

namespace Equiv.Perm

variable {α : Type*}

section supportFinset

variable [DecidableEq α] [Fintype α] {f g : Perm α}

/-- The `Finset` of nonfixed points of a permutation. -/
@[expose] def supportFinset (f : Perm α) : Finset α := {x | f x ≠ x}

@[deprecated (since := "2026-11-16")] alias support := supportFinset

@[simp]
theorem mem_supportFinset {x : α} : x ∈ f.supportFinset ↔ f x ≠ x := by
  rw [supportFinset, mem_filter, and_iff_right (mem_univ x)]

@[deprecated (since := "2026-11-16")] alias mem_support := mem_supportFinset

theorem notMem_supportFinset {x : α} : x ∉ f.supportFinset ↔ f x = x := by simp

@[deprecated (since := "2026-11-16")] alias notMem_support := notMem_supportFinset

theorem coe_supportFinset_eq_support (f : Perm α) :
    (f.supportFinset : Set α) = { x | f x ≠ x } := by
  ext
  simp

@[deprecated (since := "2026-11-16")] alias coe_support_eq_set_support :=
    coe_supportFinset_eq_support

@[simp]
theorem supportFinset_eq_empty_iff {σ : Perm α} : σ.supportFinset = ∅ ↔ σ = 1 := by
  simp_rw [Finset.ext_iff, mem_supportFinset, Finset.notMem_empty, iff_false, not_not,
    Equiv.Perm.ext_iff, one_apply]

@[deprecated (since := "2026-11-16")] alias support_eq_empty_iff := supportFinset_eq_empty_iff

@[simp]
theorem supportFinset_one : (1 : Perm α).supportFinset = ∅ := by rw [supportFinset_eq_empty_iff]

@[deprecated (since := "2026-11-16")] alias support_one := supportFinset_one

@[simp]
theorem supportFinset_refl : supportFinset (Equiv.refl α) = ∅ :=
  supportFinset_one

@[deprecated (since := "2026-11-16")] alias support_refl := supportFinset_refl

theorem supportFinset_congr (h : f.supportFinset ⊆ g.supportFinset)
    (h' : ∀ x ∈ g.supportFinset, f x = g x) : f = g := by
  grind [notMem_supportFinset]

@[deprecated (since := "2026-11-16")] alias support_congr := supportFinset_congr

/-- If g and c commute, then g stabilizes the support of c -/
theorem mem_supportFinset_iff_of_commute {g c : Perm α} (hgc : Commute g c) (x : α) :
    g x ∈ c.supportFinset ↔ x ∈ c.supportFinset := by
  simp only [mem_supportFinset, not_iff_not, ← mul_apply]
  rw [← hgc, mul_apply, Equiv.apply_eq_iff_eq]

@[deprecated (since := "2026-11-16")] alias mem_support_iff_of_commute :=
    mem_supportFinset_iff_of_commute

theorem supportFinset_mul_subset (f g : Perm α) :
    (f * g).supportFinset ⊆ f.supportFinset ∪ g.supportFinset := fun x => by
  rw [mem_union, mem_supportFinset, mem_supportFinset, mem_supportFinset, mul_apply, ← not_and_or,
    not_imp_not]
  rintro ⟨hf, hg⟩
  rw [hg, hf]

@[deprecated (since := "2026-11-16")] alias support_mul_le := supportFinset_mul_subset

theorem exists_mem_supportFinset_of_mem_supportFinset_prod {l : List (Perm α)} {x : α}
    (hx : x ∈ l.prod.supportFinset) : ∃ f : Perm α, f ∈ l ∧ x ∈ f.supportFinset := by
  contrapose! hx
  simp_rw [mem_supportFinset, not_not] at hx ⊢
  induction l with
  | nil => rfl
  | cons f l ih =>
    rw [List.prod_cons, mul_apply, ih, hx]
    · simp only [List.mem_cons, true_or]
    grind

@[deprecated (since := "2026-11-16")] alias exists_mem_support_of_mem_support_prod :=
    exists_mem_supportFinset_of_mem_supportFinset_prod

theorem supportFinset_pow_subset (σ : Perm α) (n : ℕ) :
    (σ ^ n).supportFinset ⊆ σ.supportFinset := fun _ h1 =>
  mem_supportFinset.mpr fun h2 => mem_supportFinset.mp h1 (pow_apply_eq_self_of_apply_eq_self h2 n)

@[deprecated (since := "2026-11-16")] alias support_pow_le := supportFinset_pow_subset

@[simp]
theorem supportFinset_inv (σ : Perm α) : supportFinset σ⁻¹ = σ.supportFinset := by
  simp_rw [Finset.ext_iff, mem_supportFinset, not_iff_not, inv_eq_iff_eq.trans eq_comm,
    imp_true_iff]

@[deprecated (since := "2026-11-16")] alias support_inv := supportFinset_inv

theorem apply_mem_supportFinset {x : α} : f x ∈ f.supportFinset ↔ x ∈ f.supportFinset := by
  rw [mem_supportFinset, mem_supportFinset, Ne, Ne, apply_eq_iff_eq]

@[deprecated (since := "2026-11-16")] alias apply_mem_support := apply_mem_supportFinset

/-- The support of a permutation is invariant -/
theorem isInvariant_of_supportFinset_subset {c : Perm α} {s : Finset α} (hcs : c.supportFinset ⊆ s)
    (x : α) :
    c x ∈ s ↔ x ∈ s := by
  by_cases hx' : x ∈ c.supportFinset
  · simp only [hcs hx', hcs (apply_mem_supportFinset.mpr hx')]
  · rw [notMem_supportFinset.mp hx']

@[deprecated (since := "2026-11-16")] alias isInvariant_of_support_le :=
    isInvariant_of_supportFinset_subset

/-- A permutation c is the extension of a restriction of g to s
  iff its support is contained in s and its restriction is that of g -/
lemma ofSubtype_subtypePerm_eq_iff_supportFinset_subset {g c : Equiv.Perm α} {s : Finset α}
    (hg : ∀ x, g x ∈ s ↔ x ∈ s) :
    ofSubtype (g.subtypePerm hg) = c ↔
      c.supportFinset ⊆ s ∧
      ∀ (hc' : ∀ x, c x ∈ s ↔ x ∈ s), c.subtypePerm hc' = g.subtypePerm hg := by
  simp only [Equiv.ext_iff, subtypePerm_apply, Subtype.mk.injEq, Subtype.forall]
  constructor
  · intro h
    constructor
    · intro a ha
      by_contra ha'
      rw [mem_supportFinset, ← h a, ofSubtype_apply_of_not_mem (p := (· ∈ s)) _ ha'] at ha
      exact ha rfl
    · intro _ a ha
      rw [← h a, ofSubtype_apply_of_mem (p := (· ∈ s)) _ ha, subtypePerm_apply]
  · rintro ⟨hc, h⟩ a
    specialize h (isInvariant_of_supportFinset_subset hc)
    by_cases ha : a ∈ s
    · rw [h a ha, ofSubtype_apply_of_mem (p := (· ∈ s)) _ ha, subtypePerm_apply]
    · rw [ofSubtype_apply_of_not_mem (p := (· ∈ s)) _ ha, eq_comm, ← notMem_supportFinset]
      exact Finset.notMem_mono hc ha

@[deprecated (since := "2026-11-16")] alias ofSubtype_eq_iff :=
    ofSubtype_subtypePerm_eq_iff_supportFinset_subset

theorem supportFinset_ofSubtype {p : α → Prop} [DecidablePred p] (u : Perm (Subtype p)) :
    (ofSubtype u).supportFinset = u.supportFinset.map (Function.Embedding.subtype p) := by
  ext x
  simp only [mem_supportFinset, ne_eq, Finset.mem_map, Function.Embedding.coe_subtype,
    Subtype.exists, exists_and_right, exists_eq_right, not_iff_comm, not_exists, not_not]
  by_cases hx : p x
  · simp only [forall_prop_of_true hx, ofSubtype_apply_of_mem u hx, ← Subtype.coe_inj]
  · simp only [forall_prop_of_false hx, ofSubtype_apply_of_not_mem u hx]

@[deprecated (since := "2026-11-16")] alias support_ofSubtype := supportFinset_ofSubtype

theorem mem_supportFinset_ofSubtype {p : α → Prop} [DecidablePred p] (x : α)
    (u : Perm (Subtype p)) :
    x ∈ (ofSubtype u).supportFinset ↔ ∃ (hx : p x), ⟨x, hx⟩ ∈ u.supportFinset := by
  simp [supportFinset_ofSubtype]

@[deprecated (since := "2026-11-16")] alias mem_support_ofSubtype := mem_supportFinset_ofSubtype

theorem pow_apply_mem_supportFinset {n : ℕ} {x : α} :
    (f ^ n) x ∈ f.supportFinset ↔ x ∈ f.supportFinset := by
  simp only [mem_supportFinset, ne_eq, apply_pow_apply_eq_iff]

@[deprecated (since := "2026-11-16")] alias pow_apply_mem_support := pow_apply_mem_supportFinset

theorem zpow_apply_mem_supportFinset {n : ℤ} {x : α} :
    (f ^ n) x ∈ f.supportFinset ↔ x ∈ f.supportFinset := by
  simp only [mem_supportFinset, ne_eq, apply_zpow_apply_eq_iff]

@[deprecated (since := "2026-11-16")] alias zpow_apply_mem_support := zpow_apply_mem_supportFinset

theorem pow_eq_on_of_mem_supportFinset (h : ∀ x ∈ f.supportFinset ∩ g.supportFinset, f x = g x)
    (k : ℕ) :
    ∀ x ∈ f.supportFinset ∩ g.supportFinset, (f ^ k) x = (g ^ k) x := by
  induction k with
  | zero => simp
  | succ k hk =>
    intro x hx
    rw [pow_succ, mul_apply, pow_succ, mul_apply, h _ hx, hk]
    rwa [mem_inter, apply_mem_supportFinset, ← h _ hx, apply_mem_supportFinset, ← mem_inter]

@[deprecated (since := "2026-11-16")] alias pow_eq_on_of_mem_support :=
    pow_eq_on_of_mem_supportFinset

theorem disjoint_iff_disjoint_supportFinset : Disjoint f g ↔
    _root_.Disjoint f.supportFinset g.supportFinset := by
  simp [disjoint_iff_eq_or_eq, disjoint_iff, disjoint_iff, Finset.ext_iff,
    imp_iff_not_or]

@[deprecated (since := "2026-11-16")] alias disjoint_iff_disjoint_support :=
    disjoint_iff_disjoint_supportFinset

theorem Disjoint.disjoint_supportFinset
    (h : Disjoint f g) : _root_.Disjoint f.supportFinset g.supportFinset :=
  disjoint_iff_disjoint_supportFinset.1 h

@[deprecated (since := "2026-11-16")] alias Disjoint.disjoint_support :=
    Disjoint.disjoint_supportFinset

theorem Disjoint.supportFinset_mul (h : Disjoint f g) :
    (f * g).supportFinset = f.supportFinset ∪ g.supportFinset := by
  refine le_antisymm (supportFinset_mul_subset _ _) fun a => ?_
  rw [mem_union, mem_supportFinset, mem_supportFinset, mem_supportFinset, mul_apply, ← not_and_or,
    not_imp_not]
  exact
    (h a).elim (fun hf h => ⟨hf, f.apply_eq_iff_eq.mp (h.trans hf.symm)⟩) fun hg h =>
      ⟨congr(f $hg).symm.trans h, hg⟩

@[deprecated (since := "2026-11-16")] alias Disjoint.support_mul := Disjoint.supportFinset_mul

theorem supportFinset_prod_of_pairwise_disjoint (l : List (Perm α)) (h : l.Pairwise Disjoint) :
    l.prod.supportFinset = (l.map supportFinset).foldr (· ∪ ·) ⊥ := by
  induction l with
  | nil => simp
  | cons hd tl hl =>
    rw [List.pairwise_cons] at h
    have : Disjoint hd tl.prod := disjoint_prod_right _ h.left
    simp [this.supportFinset_mul, hl h.right]

@[deprecated (since := "2026-11-16")] alias support_prod_of_pairwise_disjoint :=
    supportFinset_prod_of_pairwise_disjoint

theorem supportFinset_prod_subset (l : List (Perm α)) : l.prod.supportFinset ⊆
    (l.map supportFinset).foldr (· ∪ ·) ⊥ := by
  induction l with
  | nil => simp
  | cons hd tl hl =>
    rw [List.prod_cons, List.map_cons, List.foldr_cons]
    refine (supportFinset_mul_subset hd tl.prod).trans ?_
    exact sup_le_sup le_rfl hl

@[deprecated (since := "2026-11-16")] alias support_prod_le := supportFinset_prod_subset

theorem supportFinset_zpow_subset (σ : Perm α) (n : ℤ) :
    (σ ^ n).supportFinset ⊆ σ.supportFinset := fun _ h1 =>
  mem_supportFinset.mpr fun h2 => mem_supportFinset.mp h1 (zpow_apply_eq_self_of_apply_eq_self h2 n)

@[deprecated (since := "2026-11-16")] alias support_zpow_le := supportFinset_zpow_subset

@[simp]
theorem supportFinset_swap {x y : α} (h : x ≠ y) : supportFinset (swap x y) = {x, y} := by
  grind [supportFinset]

@[deprecated (since := "2026-11-16")] alias support_swap := supportFinset_swap

theorem supportFinset_swap_iff (x y : α) : supportFinset (swap x y) = {x, y} ↔ x ≠ y := by
  refine ⟨fun h => ?_, fun h => supportFinset_swap h⟩
  rintro rfl
  simp [Finset.ext_iff] at h

@[deprecated (since := "2026-11-16")] alias support_swap_iff := supportFinset_swap_iff

theorem supportFinset_swap_mul_swap {x y z : α} (h : List.Nodup [x, y, z]) :
    supportFinset (swap x y * swap y z) = {x, y, z} := by
  simp only [List.not_mem_nil, and_true, List.mem_cons, not_false_iff, List.nodup_cons,
    and_self_iff, List.nodup_nil] at h
  push Not at h
  apply le_antisymm
  · convert supportFinset_mul_subset (swap x y) (swap y z) using 1
    rw [supportFinset_swap h.left.left, supportFinset_swap h.right.left]
    simp [-Finset.union_singleton]
  · intro
    simp only [mem_insert, mem_singleton]
    rintro (rfl | rfl | rfl | _) <;>
      simp [swap_apply_of_ne_of_ne, h.left.left, h.left.left.symm, h.left.right.symm,
        h.left.right.left.symm, h.right.left.symm]

@[deprecated (since := "2026-11-16")] alias support_swap_mul_swap := supportFinset_swap_mul_swap

theorem supportFinset_sdiff_subset_supportFinset_swap_mul (f : Perm α) (x y : α) :
    f.supportFinset \ {x, y} ⊆ (swap x y * f).supportFinset := by
  intro
  simp only [and_imp, Perm.coe_mul, Function.comp_apply, Ne, mem_supportFinset, mem_insert,
    mem_sdiff, mem_singleton]
  push Not
  rintro ha ⟨hx, hy⟩ H
  rw [swap_apply_eq_iff, swap_apply_of_ne_of_ne hx hy] at H
  exact ha H

@[deprecated (since := "2026-11-16")] alias support_swap_mul_ge_support_sdiff :=
    supportFinset_sdiff_subset_supportFinset_swap_mul

@[deprecated (since := "2026-06-03")]
alias support_swap_mul_ge_support_diff := supportFinset_sdiff_subset_supportFinset_swap_mul

theorem supportFinset_swap_mul_eq (f : Perm α) (x : α) (h : f (f x) ≠ x) :
    (swap x (f x) * f).supportFinset = f.supportFinset \ {x} := by
  by_cases hx : f x = x
  · simp [hx, sdiff_singleton_eq_erase, notMem_supportFinset.mpr hx, erase_eq_of_notMem, pull_end]
  ext z
  by_cases hzx : z = x
  · simp [hzx]
  by_cases hzf : z = f x
  · simp [hzf, hx, h, swap_apply_of_ne_of_ne]
  by_cases hzfx : f z = x
  · simp [Ne.symm hzx, hzx, Ne.symm hzf, hzfx]
  · simp [hzx, hzfx, f.injective.ne hzx, swap_apply_of_ne_of_ne]

@[deprecated (since := "2026-11-16")] alias support_swap_mul_eq := supportFinset_swap_mul_eq

theorem mem_supportFinset_swap_mul_imp_mem_supportFinset_ne {x y : α}
    (hy : y ∈ supportFinset (swap x (f x) * f)) :
    y ∈ supportFinset f ∧ y ≠ x := by
  simp only [mem_supportFinset, swap_apply_def, mul_apply, f.injective.eq_iff] at *
  grind

@[deprecated (since := "2026-11-16")] alias mem_support_swap_mul_imp_mem_support_ne :=
    mem_supportFinset_swap_mul_imp_mem_supportFinset_ne

omit [Fintype α] in
theorem disjoint_swap_swap {x y z t : α} (h : [x, y, z, t].Nodup) :
    Disjoint (swap x y) (swap z t) := by
  intro; grind

theorem Disjoint.mem_imp (h : Disjoint f g) {x : α}
    (hx : x ∈ f.supportFinset) : x ∉ g.supportFinset :=
  disjoint_left.mp h.disjoint_supportFinset hx

theorem eq_on_supportFinset_mem_disjoint {l : List (Perm α)} (h : f ∈ l)
    (hl : l.Pairwise Disjoint) :
    ∀ x ∈ f.supportFinset, f x = l.prod x := by
  induction l with
  | nil => simp at h
  | cons hd tl IH =>
    intro x hx
    rw [List.pairwise_cons] at hl
    rw [List.mem_cons] at h
    rcases h with (rfl | h)
    · rw [List.prod_cons, mul_apply,
        notMem_supportFinset.mp ((disjoint_prod_right tl hl.left).mem_imp hx)]
    · rw [List.prod_cons, mul_apply, ← IH h hl.right _ hx, eq_comm, ← notMem_supportFinset]
      refine (hl.left _ h).symm.mem_imp ?_
      simpa using hx

@[deprecated (since := "2026-11-16")] alias eq_on_support_mem_disjoint :=
    eq_on_supportFinset_mem_disjoint

theorem Disjoint.mono_supportFinset {x y : Perm α} (h : Disjoint f g)
    (hf : x.supportFinset ⊆ f.supportFinset)
    (hg : y.supportFinset ⊆ g.supportFinset) : Disjoint x y := by
  rw [disjoint_iff_disjoint_supportFinset] at h ⊢
  exact h.mono hf hg

@[deprecated (since := "2026-11-16")] alias Disjoint.mono := Disjoint.mono_supportFinset

theorem supportFinset_subset_prod_of_mem {l : List (Perm α)} (h : f ∈ l)
    (hl : l.Pairwise Disjoint) :
    f.supportFinset ⊆ l.prod.supportFinset := by
  intro x hx
  rwa [mem_supportFinset, ← eq_on_supportFinset_mem_disjoint h hl _ hx, ← mem_supportFinset]

@[deprecated (since := "2026-11-16")] alias support_le_prod_of_mem :=
    supportFinset_subset_prod_of_mem

section ExtendDomain

variable {β : Type*} [DecidableEq β] [Fintype β] {p : β → Prop} [DecidablePred p]

@[simp]
theorem supportFinset_extend_domain (f : α ≃ Subtype p) {g : Perm α} :
    supportFinset (g.extendDomain f) = g.supportFinset.map f.asEmbedding := by
  ext b
  simp only [mem_map, Ne,
    mem_supportFinset]
  by_cases pb : p b
  · rw [extendDomain_apply_subtype _ _ pb]
    grind [asEmbedding_apply]
  · rw [extendDomain_apply_not_subtype _ _ pb]
    simp only [not_exists, false_iff, not_and, not_true]
    rintro a _ rfl
    exact pb (Subtype.prop _)

@[deprecated (since := "2026-11-16")] alias support_extend_domain := supportFinset_extend_domain

end ExtendDomain

end supportFinset

@[simp]
theorem supportFinset_subtypePerm [DecidableEq α] {s : Finset α} (f : Perm α) (h) :
    (f.subtypePerm h : Perm s).supportFinset = ({x | f x ≠ x} : Finset s) := by
  ext; simp [Subtype.ext_iff]

@[deprecated (since := "2026-11-16")] alias support_subtypePerm := supportFinset_subtypePerm

section Conjugation

variable [Fintype α] [DecidableEq α] {σ τ : Perm α}

@[simp]
theorem supportFinset_conj : (σ * τ * σ⁻¹).supportFinset = τ.supportFinset.map σ.toEmbedding := by
  ext
  simp only [mem_map_equiv, Perm.coe_mul, Function.comp_apply, Ne, Perm.mem_supportFinset,
    Equiv.eq_symm_apply, inv_def]

@[deprecated (since := "2026-11-16")] alias support_conj := supportFinset_conj

end Conjugation

end Equiv.Perm
