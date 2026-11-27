/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Aaron Anderson, Yakov Pechersky
-/
module

public import Mathlib.Algebra.Group.End

import Mathlib.Data.Set.Insert

/-!
# Support of a permutation: basic definitions

This file contains material about the points moved by a permutation that does not need any
finiteness assumptions.

## Main definitions

In the following, `f : Equiv.Perm α`.

* `Equiv.Perm.support` is the set `{x | f x ≠ x}`, the set of all elements that are not fixed
  by the permutation.

See `Mathlib/GroupTheory/Perm/Support/Finset/Basic.lean` for `Equiv.Perm.supportFinset`, the
`Finset` of points moved by a permutation of a `Fintype`.
-/

assert_not_exists Finset

public section

namespace Equiv.Perm

variable {α : Type*}

/-- The `Set` of nonfixed points of a permutation. -/
@[irreducible] def support (f : Perm α) : Set α := {x | f x ≠ x}

section Support

variable {f g : Perm α}

unseal support in @[grind =, simp]
theorem mem_support {x : α} : x ∈ f.support ↔ f x ≠ x := Set.mem_ofPred

theorem apply_ne_of_mem_support {x} (h : x ∈ f.support) : f x ≠ x := by grind
theorem mem_support_of_apply_ne {x} (h : f x ≠ x) : x ∈ f.support := by grind

theorem mem_support_iff_not_isFixedPt {x : α} : x ∈ f.support ↔ ¬ (⇑f).IsFixedPt x :=
  mem_support.trans Iff.rfl

theorem support_def : f.support = {x | f x ≠ x} := by grind

theorem support_compl_def : f.supportᶜ = {x | f x = x} := by grind

instance [DecidableEq α] : DecidablePred (· ∈ f.support) := fun _ =>
  decidable_of_decidable_of_iff mem_support.symm

theorem notMem_support {x : α} : x ∉ f.support ↔ f x = x := mem_support.not_left

theorem apply_eq_of_notMem_support {x} (h : x ∉ f.support) : f x = x := by grind
theorem notMem_support_of_apply_eq {x} (h : f x = x) : x ∉ f.support := by grind

@[simp] theorem support_one : (1 : Perm α).support = ∅ := by ext; simp

@[simp] theorem support_refl : support (Equiv.refl α) = ∅ := by simp [push_end]

@[simp]
theorem support_inv (f : Perm α) : f⁻¹.support = f.support := by
  grind [f.inv_eq_iff_eq]

@[simp] theorem support_symm : support f.symm = f.support := by grind

@[deprecated (since := "2026-11-17")] alias set_support_symm_eq := support_symm

theorem apply_mem_support {x : α} : f x ∈ f.support ↔ x ∈ f.support := by simp

@[deprecated (since := "2026-11-17")] alias set_support_apply_mem := apply_mem_support

theorem apply_inv_mem_support {x : α} : f⁻¹ x ∈ f.support ↔ x ∈ f.support := by
  rw [← apply_mem_support, ← mul_apply, mul_inv_cancel, one_apply]

theorem pow_apply_mem_support {n : ℕ} {x : α} : (f ^ n) x ∈ f.support ↔ x ∈ f.support := by simp

theorem zpow_apply_mem_support {n : ℤ} {x : α} : (f ^ n) x ∈ f.support ↔ x ∈ f.support := by simp

@[simp] theorem support_eq_empty_iff : f.support = ∅ ↔ f = 1 := by
  simp [Set.ext_iff, Equiv.ext_iff]

@[simp] theorem support_nonempty_iff : f.support.Nonempty ↔ f ≠ 1 := iff_not_comm.mpr <| by
  simp [Set.not_nonempty_iff_eq_empty]

theorem support_ne_singleton {x} : f.support ≠ {x} := fun h => by simpa using Set.ext_iff.1 h (f x)

theorem exists_pair_mem_support_ne (hf : f ≠ 1) : ∃ x ∈ f.support, ∃ y ∈ f.support, x ≠ y := by
  obtain ⟨x, hx⟩ := support_nonempty_iff.mpr hf
  exact ⟨x, hx, f x, apply_mem_support.mpr hx, (apply_ne_of_mem_support hx).symm⟩

theorem exists_mem_support_ne (hf : f ≠ 1) (a : α) : ∃ b ∈ f.support, a ≠ b := by
  obtain ⟨x, hx, y, hy, hxy⟩ := exists_pair_mem_support_ne hf
  exact Classical.by_cases (p := a = x) (fun h => h ▸ ⟨y, hy, hxy⟩) (fun hax => ⟨x, hx, hax⟩)

theorem support_eq_pair_iff {x y} : f.support = {x, y} ↔ x ≠ y ∧ f x = y ∧ f y = x ∧
    (∀ {z}, z ≠ x → z ≠ y → f z = z) := Set.ext_iff.trans <|
    ⟨(by have := · ∘' f; grind [f.injective]), by grind⟩

theorem support_eq_pair_iff_eq_swap {x y} [DecidableEq α] : f.support = {x, y} ↔
    x ≠ y ∧ f = swap x y := support_eq_pair_iff.trans <| and_congr_right <| by grind

/-- If `g` and `c` commute, then `g` stabilizes the support of `c`. -/
theorem mem_support_iff_of_commute {g c : Perm α} (hgc : Commute g c) (x : α) :
    g x ∈ c.support ↔ x ∈ c.support := by
  simp only [mem_support, ne_eq, hgc.symm.apply_apply, g.apply_eq_iff_eq]

theorem support_congr (h : f.support ⊆ g.support) (h' : ∀ x ∈ g.support, f x = g x) : f = g := by
  grind

theorem support_swap_iff [DecidableEq α] {x y : α} :
    (swap x y).support = {x, y} ↔ x ≠ y :=
  support_eq_pair_iff_eq_swap.trans <| and_iff_left_of_imp (congrFun rfl)

@[simp]
theorem support_swap_of_ne [DecidableEq α] {x y : α} (h : x ≠ y) : (swap x y).support = {x, y} :=
  support_swap_iff.mpr h

theorem support_swap [DecidableEq α] {x y : α} : (swap x y).support =
    if x = y then ∅ else {x, y} := if h : x = y then
    Eq.trans (h ▸ swap_self x ▸ support_refl) ((ite_eq_left h).symm) else
    Eq.trans (support_swap_of_ne h) (ite_eq_right h).symm

theorem support_pow_subset (n : ℕ) : (f ^ n).support ⊆ f.support := by
  grind [pow_apply_eq_self_of_apply_eq_self]

theorem support_zpow_subset (n : ℤ) : (f ^ n).support ⊆ f.support := by
  grind [zpow_apply_eq_self_of_apply_eq_self]

@[deprecated (since := "2026-11-17")] alias set_support_zpow_subset := support_zpow_subset

theorem support_mul_subset (f g : Perm α) : (f * g).support ⊆ f.support ∪ g.support := by
  grind [mul_apply]

@[deprecated (since := "2026-11-17")] alias set_support_mul_subset := support_mul_subset

@[simp]
theorem support_conj : (f * g * f⁻¹).support = f '' g.support := by
  grind [mul_apply, Set.mem_image_perm, f.eq_inv_iff_eq]

@[simp]
theorem support_conj_inv : (f⁻¹ * g * f).support = ⇑f⁻¹ '' g.support := by
  simpa using f⁻¹.support_conj

theorem support_permCongr : (f.permCongr g).support = f '' g.support := by simp

theorem _root_.MulAut.support_conj_apply : (MulAut.conj f g).support = f '' g.support := by simp

theorem exists_mem_support_of_mem_support_prod {l : List (Perm α)} {x : α}
    (hx : x ∈ l.prod.support) : ∃ f : Perm α, f ∈ l ∧ x ∈ f.support := by
  induction l <;> grind [support_mul_subset, support_one]

theorem isInvariant_of_support_subset {c : Perm α} {s : Set α} (hcs : c.support ⊆ s)
    (x : α) : c x ∈ s ↔ x ∈ s := by
  by_cases hx' : x ∈ c.support
  · simp only [hcs hx', hcs (apply_mem_support.mpr hx')]
  · rw [apply_eq_of_notMem_support hx']

theorem ofSubtype_subtypePerm_eq_iff_support_subset {g c : Equiv.Perm α} {s : Set α}
    [DecidablePred (· ∈ s)] (hg : ∀ x, g x ∈ s ↔ x ∈ s) :
    ofSubtype (g.subtypePerm hg) = c ↔ c.support ⊆ s ∧
      ∀ (hc' : ∀ x, c x ∈ s ↔ x ∈ s), c.subtypePerm hc' = g.subtypePerm hg := by
  simp only [Equiv.ext_iff, subtypePerm_apply, Subtype.mk.injEq, Subtype.forall, Set.subset_def]
  refine ⟨fun h => ⟨fun a ha => ?_, fun _ a ha => ?_⟩, fun ⟨hc, h⟩ a => ?_⟩
  · by_contra ha'; simp [← h a, ofSubtype_apply_of_not_mem _ ha'] at ha
  · simp [← h a, ofSubtype_apply_of_mem _ ha]
  · by_cases ha : a ∈ s
    · simp [h (isInvariant_of_support_subset hc) a ha, ofSubtype_apply_of_mem _ ha]
    · grind [ofSubtype_apply_of_not_mem]

theorem support_ofSubtype {p : α → Prop} [DecidablePred p] (u : Perm (Subtype p)) :
    (ofSubtype u).support = Subtype.val '' u.support := by
  ext x
  simp only [mem_support, ne_eq, Set.mem_image,
    Subtype.exists, exists_and_right, exists_eq_right, not_iff_comm, not_exists, not_not]
  by_cases hx : p x
  · simp only [forall_prop_of_true hx, ofSubtype_apply_of_mem u hx, ← Subtype.coe_inj]
  · simp only [forall_prop_of_false hx, ofSubtype_apply_of_not_mem u hx]

theorem mem_support_ofSubtype {p : α → Prop} [DecidablePred p] (x : α)
    (u : Perm (Subtype p)) :
    x ∈ (ofSubtype u).support ↔ ∃ (hx : p x), ⟨x, hx⟩ ∈ u.support := by simp [support_ofSubtype]

theorem pow_eq_on_of_mem_support (h : ∀ x ∈ f.support ∩ g.support, f x = g x)
    (k : ℕ) : ∀ x ∈ f.support ∩ g.support, (f ^ k) x = (g ^ k) x := by
  induction k with
  | zero => simp
  | succ k hk =>
    intro x hx
    rw [pow_succ, mul_apply, pow_succ, mul_apply, h _ hx, hk]
    rwa [Set.mem_inter_iff, apply_mem_support, ← h _ hx, apply_mem_support, ← Set.mem_inter_iff]

theorem support_prod_subset (l : List (Perm α)) : l.prod.support ⊆
    (l.map support).foldr (· ∪ ·) ⊥ := by
  induction l with
  | nil => simp
  | cons hd tl hl =>
    rw [List.prod_cons, List.map_cons, List.foldr_cons]
    exact (support_mul_subset hd tl.prod).trans <| sup_le_sup le_rfl hl

theorem support_swap_mul_swap [DecidableEq α] {x y z : α} (h : List.Nodup [x, y, z]) :
    support (swap x y * swap y z) = {x, y, z} := by grind [mul_apply]

theorem support_sdiff_subset_support_swap_mul [DecidableEq α] (f : Perm α) (x y : α) :
    f.support \ {x, y} ⊆ (swap x y * f).support := by grind [mul_apply]

theorem support_swap_mul_subset [DecidableEq α] (f : Perm α) (x : α) :
    (swap x (f x) * f).support ⊆ f.support \ {x} := fun y => by
  simp only [mem_support, swap_apply_def, mul_apply, f.injective.eq_iff]
  grind

theorem support_swap_mul_eq [DecidableEq α] (f : Perm α) (x : α) (h : f (f x) ≠ x) :
    (swap x (f x) * f).support = f.support \ {x} := by
  refine (support_swap_mul_subset f x).antisymm fun z hz => ?_
  simp only [mem_support, swap_apply_def, mul_apply, f.injective.eq_iff]
  grind

theorem mem_support_swap_mul_imp_mem_support_ne [DecidableEq α] {x y : α}
    (hy : y ∈ support (swap x (f x) * f)) :
    y ∈ support f ∧ y ≠ x := support_swap_mul_subset f x hy

end Support

section ExtendDomain

variable {β} {p : β → Prop} [DecidablePred p]

@[simp]
theorem support_extend_domain (f : α ≃ Subtype p) {g : Perm α} :
    support (g.extendDomain f) = Subtype.val ∘ f '' g.support := Set.ext fun b => by
  by_cases pb : p b
  · simp only [mem_support, extendDomain_apply_subtype _ _ pb, ne_eq, Set.mem_image,
    Function.comp_apply]; grind
  · simp only [mem_support, extendDomain_apply_not_subtype _ _ pb, ne_eq, not_true_eq_false,
    Set.mem_image, Function.comp_apply, false_iff, not_exists, not_and]; grind

end ExtendDomain

section SubtypePerm

@[simp]
theorem support_subtypePerm {s : Set α} (f : Perm α) (h) :
    (f.subtypePerm h : Perm s).support = Subtype.val ⁻¹' f.support := by
  simp [Set.ext_iff, Subtype.ext_iff]

theorem image_val_support_subtypePerm {s : Set α} (f : Perm α) (h : ∀ x, f x ∈ s ↔ x ∈ s) :
    Subtype.val '' (f.subtypePerm h : Perm s).support = s ∩ f.support := by
  simp [Set.ext_iff, and_comm]

end SubtypePerm

end Equiv.Perm
