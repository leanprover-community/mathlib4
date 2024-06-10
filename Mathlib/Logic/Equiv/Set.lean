/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
import Mathlib.Data.Set.Function
import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic.Says

#align_import logic.equiv.set from "leanprover-community/mathlib"@"aba57d4d3dae35460225919dcd82fe91355162f9"

/-!
# Equivalences and sets

In this file we provide lemmas linking equivalences to sets.

Some notable definitions are:

* `Equiv.ofInjective`: an injective function is (noncomputably) equivalent to its range.
* `Equiv.setCongr`: two equal sets are equivalent as types.
* `Equiv.Set.union`: a disjoint union of sets is equivalent to their `Sum`.

This file is separate from `Equiv/Basic` such that we do not require the full lattice structure
on sets before defining what an equivalence is.
-/


open Function Set

universe u v w z

variable {α : Sort u} {β : Sort v} {γ : Sort w}

namespace Equiv

@[simp]
theorem range_eq_univ {α : Type*} {β : Type*} (e : α ≃ β) : range e = univ :=
  eq_univ_of_forall e.surjective
#align equiv.range_eq_univ Equiv.range_eq_univ

protected theorem image_eq_preimage {α β} (e : α ≃ β) (s : Set α) : e '' s = e.symm ⁻¹' s :=
  Set.ext fun _ => mem_image_iff_of_inverse e.left_inv e.right_inv
#align equiv.image_eq_preimage Equiv.image_eq_preimage

@[simp 1001]
theorem _root_.Set.mem_image_equiv {α β} {S : Set α} {f : α ≃ β} {x : β} :
    x ∈ f '' S ↔ f.symm x ∈ S :=
  Set.ext_iff.mp (f.image_eq_preimage S) x
#align set.mem_image_equiv Set.mem_image_equiv

/-- Alias for `Equiv.image_eq_preimage` -/
theorem _root_.Set.image_equiv_eq_preimage_symm {α β} (S : Set α) (f : α ≃ β) :
    f '' S = f.symm ⁻¹' S :=
  f.image_eq_preimage S
#align set.image_equiv_eq_preimage_symm Set.image_equiv_eq_preimage_symm

/-- Alias for `Equiv.image_eq_preimage` -/
theorem _root_.Set.preimage_equiv_eq_image_symm {α β} (S : Set α) (f : β ≃ α) :
    f ⁻¹' S = f.symm '' S :=
  (f.symm.image_eq_preimage S).symm
#align set.preimage_equiv_eq_image_symm Set.preimage_equiv_eq_image_symm

-- Porting note: increased priority so this fires before `image_subset_iff`
@[simp high]
protected theorem symm_image_subset {α β} (e : α ≃ β) (s : Set α) (t : Set β) :
    e.symm '' t ⊆ s ↔ t ⊆ e '' s := by rw [image_subset_iff, e.image_eq_preimage]
#align equiv.subset_image Equiv.symm_image_subset

@[deprecated] alias subset_image := Equiv.symm_image_subset -- deprecated since 2024-01-19

-- Porting note: increased priority so this fires before `image_subset_iff`
@[simp high]
protected theorem subset_symm_image {α β} (e : α ≃ β) (s : Set α) (t : Set β) :
    s ⊆ e.symm '' t ↔ e '' s ⊆ t :=
  calc
    s ⊆ e.symm '' t ↔ e.symm.symm '' s ⊆ t := by rw [e.symm.symm_image_subset]
    _ ↔ e '' s ⊆ t := by rw [e.symm_symm]
#align equiv.subset_image' Equiv.subset_symm_image

@[deprecated] alias subset_image' := Equiv.subset_symm_image -- deprecated since 2024-01-19

@[simp]
theorem symm_image_image {α β} (e : α ≃ β) (s : Set α) : e.symm '' (e '' s) = s :=
  e.leftInverse_symm.image_image s
#align equiv.symm_image_image Equiv.symm_image_image

theorem eq_image_iff_symm_image_eq {α β} (e : α ≃ β) (s : Set α) (t : Set β) :
    t = e '' s ↔ e.symm '' t = s :=
  (e.symm.injective.image_injective.eq_iff' (e.symm_image_image s)).symm
#align equiv.eq_image_iff_symm_image_eq Equiv.eq_image_iff_symm_image_eq

@[simp]
theorem image_symm_image {α β} (e : α ≃ β) (s : Set β) : e '' (e.symm '' s) = s :=
  e.symm.symm_image_image s
#align equiv.image_symm_image Equiv.image_symm_image

@[simp]
theorem image_preimage {α β} (e : α ≃ β) (s : Set β) : e '' (e ⁻¹' s) = s :=
  e.surjective.image_preimage s
#align equiv.image_preimage Equiv.image_preimage

@[simp]
theorem preimage_image {α β} (e : α ≃ β) (s : Set α) : e ⁻¹' (e '' s) = s :=
  e.injective.preimage_image s
#align equiv.preimage_image Equiv.preimage_image

protected theorem image_compl {α β} (f : Equiv α β) (s : Set α) : f '' sᶜ = (f '' s)ᶜ :=
  image_compl_eq f.bijective
#align equiv.image_compl Equiv.image_compl

@[simp]
theorem symm_preimage_preimage {α β} (e : α ≃ β) (s : Set β) : e.symm ⁻¹' (e ⁻¹' s) = s :=
  e.rightInverse_symm.preimage_preimage s
#align equiv.symm_preimage_preimage Equiv.symm_preimage_preimage

@[simp]
theorem preimage_symm_preimage {α β} (e : α ≃ β) (s : Set α) : e ⁻¹' (e.symm ⁻¹' s) = s :=
  e.leftInverse_symm.preimage_preimage s
#align equiv.preimage_symm_preimage Equiv.preimage_symm_preimage

theorem preimage_subset {α β} (e : α ≃ β) (s t : Set β) : e ⁻¹' s ⊆ e ⁻¹' t ↔ s ⊆ t :=
  e.surjective.preimage_subset_preimage_iff
#align equiv.preimage_subset Equiv.preimage_subset

-- Porting note (#10618): removed `simp` attribute. `simp` can prove it.
theorem image_subset {α β} (e : α ≃ β) (s t : Set α) : e '' s ⊆ e '' t ↔ s ⊆ t :=
  image_subset_image_iff e.injective
#align equiv.image_subset Equiv.image_subset

@[simp]
theorem image_eq_iff_eq {α β} (e : α ≃ β) (s t : Set α) : e '' s = e '' t ↔ s = t :=
  image_eq_image e.injective
#align equiv.image_eq_iff_eq Equiv.image_eq_iff_eq

theorem preimage_eq_iff_eq_image {α β} (e : α ≃ β) (s t) : e ⁻¹' s = t ↔ s = e '' t :=
  Set.preimage_eq_iff_eq_image e.bijective
#align equiv.preimage_eq_iff_eq_image Equiv.preimage_eq_iff_eq_image

theorem eq_preimage_iff_image_eq {α β} (e : α ≃ β) (s t) : s = e ⁻¹' t ↔ e '' s = t :=
  Set.eq_preimage_iff_image_eq e.bijective
#align equiv.eq_preimage_iff_image_eq Equiv.eq_preimage_iff_image_eq

lemma setOf_apply_symm_eq_image_setOf {α β} (e : α ≃ β) (p : α → Prop) :
    {b | p (e.symm b)} = e '' {a | p a} := by
  rw [Equiv.image_eq_preimage, preimage_setOf_eq]

@[simp]
theorem prod_assoc_preimage {α β γ} {s : Set α} {t : Set β} {u : Set γ} :
    Equiv.prodAssoc α β γ ⁻¹' s ×ˢ t ×ˢ u = (s ×ˢ t) ×ˢ u := by
  ext
  simp [and_assoc]
#align equiv.prod_assoc_preimage Equiv.prod_assoc_preimage

@[simp]
theorem prod_assoc_symm_preimage {α β γ} {s : Set α} {t : Set β} {u : Set γ} :
    (Equiv.prodAssoc α β γ).symm ⁻¹' (s ×ˢ t) ×ˢ u = s ×ˢ t ×ˢ u := by
  ext
  simp [and_assoc]
#align equiv.prod_assoc_symm_preimage Equiv.prod_assoc_symm_preimage

-- `@[simp]` doesn't like these lemmas, as it uses `Set.image_congr'` to turn `Equiv.prodAssoc`
-- into a lambda expression and then unfold it.
theorem prod_assoc_image {α β γ} {s : Set α} {t : Set β} {u : Set γ} :
    Equiv.prodAssoc α β γ '' (s ×ˢ t) ×ˢ u = s ×ˢ t ×ˢ u := by
  simpa only [Equiv.image_eq_preimage] using prod_assoc_symm_preimage
#align equiv.prod_assoc_image Equiv.prod_assoc_image

theorem prod_assoc_symm_image {α β γ} {s : Set α} {t : Set β} {u : Set γ} :
    (Equiv.prodAssoc α β γ).symm '' s ×ˢ t ×ˢ u = (s ×ˢ t) ×ˢ u := by
  simpa only [Equiv.image_eq_preimage] using prod_assoc_preimage
#align equiv.prod_assoc_symm_image Equiv.prod_assoc_symm_image

/-- A set `s` in `α × β` is equivalent to the sigma-type `Σ x, {y | (x, y) ∈ s}`. -/
def setProdEquivSigma {α β : Type*} (s : Set (α × β)) :
    s ≃ Σx : α, { y : β | (x, y) ∈ s } where
  toFun x := ⟨x.1.1, x.1.2, by simp⟩
  invFun x := ⟨(x.1, x.2.1), x.2.2⟩
  left_inv := fun ⟨⟨x, y⟩, h⟩ => rfl
  right_inv := fun ⟨x, y, h⟩ => rfl
#align equiv.set_prod_equiv_sigma Equiv.setProdEquivSigma

/-- The subtypes corresponding to equal sets are equivalent. -/
@[simps! apply]
def setCongr {α : Type*} {s t : Set α} (h : s = t) : s ≃ t :=
  subtypeEquivProp h
#align equiv.set_congr Equiv.setCongr
#align equiv.set_congr_apply Equiv.setCongr_apply

-- We could construct this using `Equiv.Set.image e s e.injective`,
-- but this definition provides an explicit inverse.
/-- A set is equivalent to its image under an equivalence.
-/
@[simps]
def image {α β : Type*} (e : α ≃ β) (s : Set α) :
    s ≃ e '' s where
  toFun x := ⟨e x.1, by simp⟩
  invFun y :=
    ⟨e.symm y.1, by
      rcases y with ⟨-, ⟨a, ⟨m, rfl⟩⟩⟩
      simpa using m⟩
  left_inv x := by simp
  right_inv y := by simp
#align equiv.image Equiv.image
#align equiv.image_symm_apply_coe Equiv.image_symm_apply_coe
#align equiv.image_apply_coe Equiv.image_apply_coe

namespace Set

-- Porting note: Removed attribute @[simps apply symm_apply]
/-- `univ α` is equivalent to `α`. -/
protected def univ (α) : @univ α ≃ α :=
  ⟨Subtype.val, fun a => ⟨a, trivial⟩, fun ⟨_, _⟩ => rfl, fun _ => rfl⟩
#align equiv.set.univ Equiv.Set.univ

/-- An empty set is equivalent to the `Empty` type. -/
protected def empty (α) : (∅ : Set α) ≃ Empty :=
  equivEmpty _
#align equiv.set.empty Equiv.Set.empty

/-- An empty set is equivalent to a `PEmpty` type. -/
protected def pempty (α) : (∅ : Set α) ≃ PEmpty :=
  equivPEmpty _
#align equiv.set.pempty Equiv.Set.pempty

/-- If sets `s` and `t` are separated by a decidable predicate, then `s ∪ t` is equivalent to
`s ⊕ t`. -/
protected def union' {α} {s t : Set α} (p : α → Prop) [DecidablePred p] (hs : ∀ x ∈ s, p x)
    (ht : ∀ x ∈ t, ¬p x) : (s ∪ t : Set α) ≃ s ⊕ t where
  toFun x :=
    if hp : p x then Sum.inl ⟨_, x.2.resolve_right fun xt => ht _ xt hp⟩
    else Sum.inr ⟨_, x.2.resolve_left fun xs => hp (hs _ xs)⟩
  invFun o :=
    match o with
    | Sum.inl x => ⟨x, Or.inl x.2⟩
    | Sum.inr x => ⟨x, Or.inr x.2⟩
  left_inv := fun ⟨x, h'⟩ => by by_cases h : p x <;> simp [h]
  right_inv o := by
    rcases o with (⟨x, h⟩ | ⟨x, h⟩) <;> [simp [hs _ h]; simp [ht _ h]]
#align equiv.set.union' Equiv.Set.union'

/-- If sets `s` and `t` are disjoint, then `s ∪ t` is equivalent to `s ⊕ t`. -/
protected def union {α} {s t : Set α} [DecidablePred fun x => x ∈ s] (H : s ∩ t ⊆ ∅) :
    (s ∪ t : Set α) ≃ s ⊕ t :=
  Set.union' (fun x => x ∈ s) (fun _ => id) fun _ xt xs => H ⟨xs, xt⟩
#align equiv.set.union Equiv.Set.union

theorem union_apply_left {α} {s t : Set α} [DecidablePred fun x => x ∈ s] (H : s ∩ t ⊆ ∅)
    {a : (s ∪ t : Set α)} (ha : ↑a ∈ s) : Equiv.Set.union H a = Sum.inl ⟨a, ha⟩ :=
  dif_pos ha
#align equiv.set.union_apply_left Equiv.Set.union_apply_left

theorem union_apply_right {α} {s t : Set α} [DecidablePred fun x => x ∈ s] (H : s ∩ t ⊆ ∅)
    {a : (s ∪ t : Set α)} (ha : ↑a ∈ t) : Equiv.Set.union H a = Sum.inr ⟨a, ha⟩ :=
  dif_neg fun h => H ⟨h, ha⟩
#align equiv.set.union_apply_right Equiv.Set.union_apply_right

@[simp]
theorem union_symm_apply_left {α} {s t : Set α} [DecidablePred fun x => x ∈ s] (H : s ∩ t ⊆ ∅)
    (a : s) : (Equiv.Set.union H).symm (Sum.inl a) = ⟨a, by simp⟩ :=
  rfl
#align equiv.set.union_symm_apply_left Equiv.Set.union_symm_apply_left

@[simp]
theorem union_symm_apply_right {α} {s t : Set α} [DecidablePred fun x => x ∈ s] (H : s ∩ t ⊆ ∅)
    (a : t) : (Equiv.Set.union H).symm (Sum.inr a) = ⟨a, by simp⟩ :=
  rfl
#align equiv.set.union_symm_apply_right Equiv.Set.union_symm_apply_right

/-- A singleton set is equivalent to a `PUnit` type. -/
protected def singleton {α} (a : α) : ({a} : Set α) ≃ PUnit.{u} :=
  ⟨fun _ => PUnit.unit, fun _ => ⟨a, mem_singleton _⟩, fun ⟨x, h⟩ => by
    simp? at h says simp only [mem_singleton_iff] at h
    subst x
    rfl, fun ⟨⟩ => rfl⟩
#align equiv.set.singleton Equiv.Set.singleton

/-- Equal sets are equivalent.

TODO: this is the same as `Equiv.setCongr`! -/
@[simps! apply symm_apply]
protected def ofEq {α : Type u} {s t : Set α} (h : s = t) : s ≃ t :=
  Equiv.setCongr h
#align equiv.set.of_eq Equiv.Set.ofEq

/-- If `a ∉ s`, then `insert a s` is equivalent to `s ⊕ PUnit`. -/
protected def insert {α} {s : Set.{u} α} [DecidablePred (· ∈ s)] {a : α} (H : a ∉ s) :
    (insert a s : Set α) ≃ Sum s PUnit.{u + 1} :=
  calc
    (insert a s : Set α) ≃ ↥(s ∪ {a}) := Equiv.Set.ofEq (by simp)
    _ ≃ Sum s ({a} : Set α) := Equiv.Set.union fun x ⟨hx, _⟩ => by simp_all
    _ ≃ Sum s PUnit.{u + 1} := sumCongr (Equiv.refl _) (Equiv.Set.singleton _)
#align equiv.set.insert Equiv.Set.insert

@[simp]
theorem insert_symm_apply_inl {α} {s : Set.{u} α} [DecidablePred (· ∈ s)] {a : α} (H : a ∉ s)
    (b : s) : (Equiv.Set.insert H).symm (Sum.inl b) = ⟨b, Or.inr b.2⟩ :=
  rfl
#align equiv.set.insert_symm_apply_inl Equiv.Set.insert_symm_apply_inl

@[simp]
theorem insert_symm_apply_inr {α} {s : Set.{u} α} [DecidablePred (· ∈ s)] {a : α} (H : a ∉ s)
    (b : PUnit.{u + 1}) : (Equiv.Set.insert H).symm (Sum.inr b) = ⟨a, Or.inl rfl⟩ :=
  rfl
#align equiv.set.insert_symm_apply_inr Equiv.Set.insert_symm_apply_inr

@[simp]
theorem insert_apply_left {α} {s : Set.{u} α} [DecidablePred (· ∈ s)] {a : α} (H : a ∉ s) :
    Equiv.Set.insert H ⟨a, Or.inl rfl⟩ = Sum.inr PUnit.unit :=
  (Equiv.Set.insert H).apply_eq_iff_eq_symm_apply.2 rfl
#align equiv.set.insert_apply_left Equiv.Set.insert_apply_left

@[simp]
theorem insert_apply_right {α} {s : Set.{u} α} [DecidablePred (· ∈ s)] {a : α} (H : a ∉ s) (b : s) :
    Equiv.Set.insert H ⟨b, Or.inr b.2⟩ = Sum.inl b :=
  (Equiv.Set.insert H).apply_eq_iff_eq_symm_apply.2 rfl
#align equiv.set.insert_apply_right Equiv.Set.insert_apply_right

/-- If `s : Set α` is a set with decidable membership, then `s ⊕ sᶜ` is equivalent to `α`. -/
protected def sumCompl {α} (s : Set α) [DecidablePred (· ∈ s)] : Sum s (sᶜ : Set α) ≃ α :=
  calc
    Sum s (sᶜ : Set α) ≃ ↥(s ∪ sᶜ) := (Equiv.Set.union (by simp [Set.ext_iff])).symm
    _ ≃ @univ α := Equiv.Set.ofEq (by simp)
    _ ≃ α := Equiv.Set.univ _
#align equiv.set.sum_compl Equiv.Set.sumCompl

@[simp]
theorem sumCompl_apply_inl {α : Type u} (s : Set α) [DecidablePred (· ∈ s)] (x : s) :
    Equiv.Set.sumCompl s (Sum.inl x) = x :=
  rfl
#align equiv.set.sum_compl_apply_inl Equiv.Set.sumCompl_apply_inl

@[simp]
theorem sumCompl_apply_inr {α : Type u} (s : Set α) [DecidablePred (· ∈ s)] (x : (sᶜ : Set α)) :
    Equiv.Set.sumCompl s (Sum.inr x) = x :=
  rfl
#align equiv.set.sum_compl_apply_inr Equiv.Set.sumCompl_apply_inr

theorem sumCompl_symm_apply_of_mem {α : Type u} {s : Set α} [DecidablePred (· ∈ s)] {x : α}
    (hx : x ∈ s) : (Equiv.Set.sumCompl s).symm x = Sum.inl ⟨x, hx⟩ := by
  have : ((⟨x, Or.inl hx⟩ : (s ∪ sᶜ : Set α)) : α) ∈ s := hx
  rw [Equiv.Set.sumCompl]
  simpa using Set.union_apply_left (by simp) this
#align equiv.set.sum_compl_symm_apply_of_mem Equiv.Set.sumCompl_symm_apply_of_mem

theorem sumCompl_symm_apply_of_not_mem {α : Type u} {s : Set α} [DecidablePred (· ∈ s)] {x : α}
    (hx : x ∉ s) : (Equiv.Set.sumCompl s).symm x = Sum.inr ⟨x, hx⟩ := by
  have : ((⟨x, Or.inr hx⟩ : (s ∪ sᶜ : Set α)) : α) ∈ sᶜ := hx
  rw [Equiv.Set.sumCompl]
  simpa using Set.union_apply_right (by simp) this
#align equiv.set.sum_compl_symm_apply_of_not_mem Equiv.Set.sumCompl_symm_apply_of_not_mem

@[simp]
theorem sumCompl_symm_apply {α : Type*} {s : Set α} [DecidablePred (· ∈ s)] {x : s} :
    (Equiv.Set.sumCompl s).symm x = Sum.inl x := by
  cases' x with x hx; exact Set.sumCompl_symm_apply_of_mem hx
#align equiv.set.sum_compl_symm_apply Equiv.Set.sumCompl_symm_apply

@[simp]
theorem sumCompl_symm_apply_compl {α : Type*} {s : Set α} [DecidablePred (· ∈ s)]
    {x : (sᶜ : Set α)} : (Equiv.Set.sumCompl s).symm x = Sum.inr x := by
  cases' x with x hx; exact Set.sumCompl_symm_apply_of_not_mem hx
#align equiv.set.sum_compl_symm_apply_compl Equiv.Set.sumCompl_symm_apply_compl

/-- `sumDiffSubset s t` is the natural equivalence between
`s ⊕ (t \ s)` and `t`, where `s` and `t` are two sets. -/
protected def sumDiffSubset {α} {s t : Set α} (h : s ⊆ t) [DecidablePred (· ∈ s)] :
    Sum s (t \ s : Set α) ≃ t :=
  calc
    Sum s (t \ s : Set α) ≃ (s ∪ t \ s : Set α) :=
      (Equiv.Set.union (by simp [inter_diff_self])).symm
    _ ≃ t := Equiv.Set.ofEq (by simp [union_diff_self, union_eq_self_of_subset_left h])
#align equiv.set.sum_diff_subset Equiv.Set.sumDiffSubset

@[simp]
theorem sumDiffSubset_apply_inl {α} {s t : Set α} (h : s ⊆ t) [DecidablePred (· ∈ s)] (x : s) :
    Equiv.Set.sumDiffSubset h (Sum.inl x) = inclusion h x :=
  rfl
#align equiv.set.sum_diff_subset_apply_inl Equiv.Set.sumDiffSubset_apply_inl

@[simp]
theorem sumDiffSubset_apply_inr {α} {s t : Set α} (h : s ⊆ t) [DecidablePred (· ∈ s)]
    (x : (t \ s : Set α)) : Equiv.Set.sumDiffSubset h (Sum.inr x) = inclusion diff_subset x :=
  rfl
#align equiv.set.sum_diff_subset_apply_inr Equiv.Set.sumDiffSubset_apply_inr

theorem sumDiffSubset_symm_apply_of_mem {α} {s t : Set α} (h : s ⊆ t) [DecidablePred (· ∈ s)]
    {x : t} (hx : x.1 ∈ s) : (Equiv.Set.sumDiffSubset h).symm x = Sum.inl ⟨x, hx⟩ := by
  apply (Equiv.Set.sumDiffSubset h).injective
  simp only [apply_symm_apply, sumDiffSubset_apply_inl]
  exact Subtype.eq rfl
#align equiv.set.sum_diff_subset_symm_apply_of_mem Equiv.Set.sumDiffSubset_symm_apply_of_mem

theorem sumDiffSubset_symm_apply_of_not_mem {α} {s t : Set α} (h : s ⊆ t) [DecidablePred (· ∈ s)]
    {x : t} (hx : x.1 ∉ s) : (Equiv.Set.sumDiffSubset h).symm x = Sum.inr ⟨x, ⟨x.2, hx⟩⟩ := by
  apply (Equiv.Set.sumDiffSubset h).injective
  simp only [apply_symm_apply, sumDiffSubset_apply_inr]
  exact Subtype.eq rfl
#align equiv.set.sum_diff_subset_symm_apply_of_not_mem Equiv.Set.sumDiffSubset_symm_apply_of_not_mem

/-- If `s` is a set with decidable membership, then the sum of `s ∪ t` and `s ∩ t` is equivalent
to `s ⊕ t`. -/
protected def unionSumInter {α : Type u} (s t : Set α) [DecidablePred (· ∈ s)] :
    Sum (s ∪ t : Set α) (s ∩ t : Set α) ≃ Sum s t :=
  calc
    Sum (s ∪ t : Set α) (s ∩ t : Set α)
      ≃ Sum (s ∪ t \ s : Set α) (s ∩ t : Set α) := by rw [union_diff_self]
    _ ≃ Sum (Sum s (t \ s : Set α)) (s ∩ t : Set α) :=
      sumCongr (Set.union <| subset_empty_iff.2 (inter_diff_self _ _)) (Equiv.refl _)
    _ ≃ Sum s (Sum (t \ s : Set α) (s ∩ t : Set α)) := sumAssoc _ _ _
    _ ≃ Sum s (t \ s ∪ s ∩ t : Set α) :=
      sumCongr (Equiv.refl _)
        (by
          refine (Set.union' (· ∉ s) ?_ ?_).symm
          exacts [fun x hx => hx.2, fun x hx => not_not_intro hx.1])
    _ ≃ Sum s t := by
      { rw [(_ : t \ s ∪ s ∩ t = t)]
        rw [union_comm, inter_comm, inter_union_diff] }
#align equiv.set.union_sum_inter Equiv.Set.unionSumInter

/-- Given an equivalence `e₀` between sets `s : Set α` and `t : Set β`, the set of equivalences
`e : α ≃ β` such that `e ↑x = ↑(e₀ x)` for each `x : s` is equivalent to the set of equivalences
between `sᶜ` and `tᶜ`. -/
protected def compl {α : Type u} {β : Type v} {s : Set α} {t : Set β} [DecidablePred (· ∈ s)]
    [DecidablePred (· ∈ t)] (e₀ : s ≃ t) :
    { e : α ≃ β // ∀ x : s, e x = e₀ x } ≃ ((sᶜ : Set α) ≃ (tᶜ : Set β)) where
  toFun e :=
    subtypeEquiv e fun a =>
      not_congr <|
        Iff.symm <|
          MapsTo.mem_iff (mapsTo_iff_exists_map_subtype.2 ⟨e₀, e.2⟩)
            (SurjOn.mapsTo_compl
              (surjOn_iff_exists_map_subtype.2 ⟨t, e₀, Subset.refl t, e₀.surjective, e.2⟩)
              e.1.injective)
  invFun e₁ :=
    Subtype.mk
      (calc
        α ≃ Sum s (sᶜ : Set α) := (Set.sumCompl s).symm
        _ ≃ Sum t (tᶜ : Set β) := e₀.sumCongr e₁
        _ ≃ β := Set.sumCompl t
        )
      fun x => by
      simp only [Sum.map_inl, trans_apply, sumCongr_apply, Set.sumCompl_apply_inl,
        Set.sumCompl_symm_apply, Trans.trans]
  left_inv e := by
    ext x
    by_cases hx : x ∈ s
    · simp only [Set.sumCompl_symm_apply_of_mem hx, ← e.prop ⟨x, hx⟩, Sum.map_inl, sumCongr_apply,
        trans_apply, Subtype.coe_mk, Set.sumCompl_apply_inl, Trans.trans]
    · simp only [Set.sumCompl_symm_apply_of_not_mem hx, Sum.map_inr, subtypeEquiv_apply,
        Set.sumCompl_apply_inr, trans_apply, sumCongr_apply, Subtype.coe_mk, Trans.trans]
  right_inv e :=
    Equiv.ext fun x => by
      simp only [Sum.map_inr, subtypeEquiv_apply, Set.sumCompl_apply_inr, Function.comp_apply,
        sumCongr_apply, Equiv.coe_trans, Subtype.coe_eta, Subtype.coe_mk, Trans.trans,
        Set.sumCompl_symm_apply_compl]
#align equiv.set.compl Equiv.Set.compl

/-- The set product of two sets is equivalent to the type product of their coercions to types. -/
protected def prod {α β} (s : Set α) (t : Set β) : ↥(s ×ˢ t) ≃ s × t :=
  @subtypeProdEquivProd α β s t
#align equiv.set.prod Equiv.Set.prod

/-- The set `Set.pi Set.univ s` is equivalent to `Π a, s a`. -/
@[simps]
protected def univPi {α : Type*} {β : α → Type*} (s : ∀ a, Set (β a)) :
    pi univ s ≃ ∀ a, s a where
  toFun f a := ⟨(f : ∀ a, β a) a, f.2 a (mem_univ a)⟩
  invFun f := ⟨fun a => f a, fun a _ => (f a).2⟩
  left_inv := fun ⟨f, hf⟩ => by
    ext a
    rfl
  right_inv f := by
    ext a
    rfl
#align equiv.set.univ_pi Equiv.Set.univPi
#align equiv.set.univ_pi_symm_apply_coe Equiv.Set.univPi_symm_apply_coe
#align equiv.set.univ_pi_apply_coe Equiv.Set.univPi_apply_coe

/-- If a function `f` is injective on a set `s`, then `s` is equivalent to `f '' s`. -/
protected noncomputable def imageOfInjOn {α β} (f : α → β) (s : Set α) (H : InjOn f s) :
    s ≃ f '' s :=
  ⟨fun p => ⟨f p, mem_image_of_mem f p.2⟩, fun p =>
    ⟨Classical.choose p.2, (Classical.choose_spec p.2).1⟩, fun ⟨_, h⟩ =>
    Subtype.eq
      (H (Classical.choose_spec (mem_image_of_mem f h)).1 h
        (Classical.choose_spec (mem_image_of_mem f h)).2),
    fun ⟨_, h⟩ => Subtype.eq (Classical.choose_spec h).2⟩
#align equiv.set.image_of_inj_on Equiv.Set.imageOfInjOn

/-- If `f` is an injective function, then `s` is equivalent to `f '' s`. -/
@[simps! apply]
protected noncomputable def image {α β} (f : α → β) (s : Set α) (H : Injective f) : s ≃ f '' s :=
  Equiv.Set.imageOfInjOn f s H.injOn
#align equiv.set.image Equiv.Set.image
#align equiv.set.image_apply Equiv.Set.image_apply

@[simp]
protected theorem image_symm_apply {α β} (f : α → β) (s : Set α) (H : Injective f) (x : α)
    (h : f x ∈ f '' s) : (Set.image f s H).symm ⟨f x, h⟩ = ⟨x, H.mem_set_image.1 h⟩ :=
  (Equiv.symm_apply_eq _).2 rfl
#align equiv.set.image_symm_apply Equiv.Set.image_symm_apply

theorem image_symm_preimage {α β} {f : α → β} (hf : Injective f) (u s : Set α) :
    (fun x => (Set.image f s hf).symm x : f '' s → α) ⁻¹' u = Subtype.val ⁻¹' (f '' u) := by
  ext ⟨b, a, has, rfl⟩
  simp [hf.eq_iff]
#align equiv.set.image_symm_preimage Equiv.Set.image_symm_preimage

/-- If `α` is equivalent to `β`, then `Set α` is equivalent to `Set β`. -/
@[simps]
protected def congr {α β : Type*} (e : α ≃ β) : Set α ≃ Set β :=
  ⟨fun s => e '' s, fun t => e.symm '' t, symm_image_image e, symm_image_image e.symm⟩
#align equiv.set.congr Equiv.Set.congr
#align equiv.set.congr_apply Equiv.Set.congr_apply
#align equiv.set.congr_symm_apply Equiv.Set.congr_symm_apply

/-- The set `{x ∈ s | t x}` is equivalent to the set of `x : s` such that `t x`. -/
protected def sep {α : Type u} (s : Set α) (t : α → Prop) :
    ({ x ∈ s | t x } : Set α) ≃ { x : s | t x } :=
  (Equiv.subtypeSubtypeEquivSubtypeInter s t).symm
#align equiv.set.sep Equiv.Set.sep

/-- The set `𝒫 S := {x | x ⊆ S}` is equivalent to the type `Set S`. -/
protected def powerset {α} (S : Set α) :
    𝒫 S ≃ Set S where
  toFun := fun x : 𝒫 S => Subtype.val ⁻¹' (x : Set α)
  invFun := fun x : Set S => ⟨Subtype.val '' x, by rintro _ ⟨a : S, _, rfl⟩; exact a.2⟩
  left_inv x := by ext y;exact ⟨fun ⟨⟨_, _⟩, h, rfl⟩ => h, fun h => ⟨⟨_, x.2 h⟩, h, rfl⟩⟩
  right_inv x := by ext; simp
#align equiv.set.powerset Equiv.Set.powerset

/-- If `s` is a set in `range f`,
then its image under `rangeSplitting f` is in bijection (via `f`) with `s`.
-/
@[simps]
noncomputable def rangeSplittingImageEquiv {α β : Type*} (f : α → β) (s : Set (range f)) :
    rangeSplitting f '' s ≃ s where
  toFun x :=
    ⟨⟨f x, by simp⟩, by
      rcases x with ⟨x, ⟨y, ⟨m, rfl⟩⟩⟩
      simpa [apply_rangeSplitting f] using m⟩
  invFun x := ⟨rangeSplitting f x, ⟨x, ⟨x.2, rfl⟩⟩⟩
  left_inv x := by
    rcases x with ⟨x, ⟨y, ⟨m, rfl⟩⟩⟩
    simp [apply_rangeSplitting f]
  right_inv x := by simp [apply_rangeSplitting f]
#align equiv.set.range_splitting_image_equiv Equiv.Set.rangeSplittingImageEquiv
#align equiv.set.range_splitting_image_equiv_symm_apply_coe Equiv.Set.rangeSplittingImageEquiv_symm_apply_coe
#align equiv.set.range_splitting_image_equiv_apply_coe_coe Equiv.Set.rangeSplittingImageEquiv_apply_coe_coe

/-- Equivalence between the range of `Sum.inl : α → α ⊕ β` and `α`. -/
@[simps symm_apply_coe]
def rangeInl (α β : Type*) : Set.range (Sum.inl : α → α ⊕ β) ≃ α where
  toFun
  | ⟨.inl x, _⟩ => x
  | ⟨.inr _, h⟩ => False.elim <| by rcases h with ⟨x, h'⟩; cases h'
  invFun x := ⟨.inl x, mem_range_self _⟩
  left_inv := fun ⟨_, _, rfl⟩ => rfl
  right_inv x := rfl

@[simp] lemma rangeInl_apply_inl {α : Type*} (β : Type*) (x : α) :
    (rangeInl α β) ⟨.inl x, mem_range_self _⟩ = x :=
  rfl

/-- Equivalence between the range of `Sum.inr : β → α ⊕ β` and `β`. -/
@[simps symm_apply_coe]
def rangeInr (α β : Type*) : Set.range (Sum.inr : β → α ⊕ β) ≃ β where
  toFun
  | ⟨.inl _, h⟩ => False.elim <| by rcases h with ⟨x, h'⟩; cases h'
  | ⟨.inr x, _⟩ => x
  invFun x := ⟨.inr x, mem_range_self _⟩
  left_inv := fun ⟨_, _, rfl⟩ => rfl
  right_inv x := rfl

@[simp] lemma rangeInr_apply_inr (α : Type*) {β : Type*} (x : β) :
    (rangeInr α β) ⟨.inr x, mem_range_self _⟩ = x :=
  rfl

end Set

/-- If `f : α → β` has a left-inverse when `α` is nonempty, then `α` is computably equivalent to the
range of `f`.

While awkward, the `Nonempty α` hypothesis on `f_inv` and `hf` allows this to be used when `α` is
empty too. This hypothesis is absent on analogous definitions on stronger `Equiv`s like
`LinearEquiv.ofLeftInverse` and `RingEquiv.ofLeftInverse` as their typeclass assumptions
are already sufficient to ensure non-emptiness. -/
@[simps]
def ofLeftInverse {α β : Sort _} (f : α → β) (f_inv : Nonempty α → β → α)
    (hf : ∀ h : Nonempty α, LeftInverse (f_inv h) f) :
    α ≃ range f where
  toFun a := ⟨f a, a, rfl⟩
  invFun b := f_inv (nonempty_of_exists b.2) b
  left_inv a := hf ⟨a⟩ a
  right_inv := fun ⟨b, a, ha⟩ =>
    Subtype.eq <| show f (f_inv ⟨a⟩ b) = b from Eq.trans (congr_arg f <| ha ▸ hf _ a) ha
#align equiv.of_left_inverse Equiv.ofLeftInverse
#align equiv.of_left_inverse_apply_coe Equiv.ofLeftInverse_apply_coe
#align equiv.of_left_inverse_symm_apply Equiv.ofLeftInverse_symm_apply

/-- If `f : α → β` has a left-inverse, then `α` is computably equivalent to the range of `f`.

Note that if `α` is empty, no such `f_inv` exists and so this definition can't be used, unlike
the stronger but less convenient `ofLeftInverse`. -/
abbrev ofLeftInverse' {α β : Sort _} (f : α → β) (f_inv : β → α) (hf : LeftInverse f_inv f) :
    α ≃ range f :=
  ofLeftInverse f (fun _ => f_inv) fun _ => hf
#align equiv.of_left_inverse' Equiv.ofLeftInverse'

/-- If `f : α → β` is an injective function, then domain `α` is equivalent to the range of `f`. -/
@[simps! apply]
noncomputable def ofInjective {α β} (f : α → β) (hf : Injective f) : α ≃ range f :=
  Equiv.ofLeftInverse f (fun _ => Function.invFun f) fun _ => Function.leftInverse_invFun hf
#align equiv.of_injective Equiv.ofInjective
#align equiv.of_injective_apply Equiv.ofInjective_apply

theorem apply_ofInjective_symm {α β} {f : α → β} (hf : Injective f) (b : range f) :
    f ((ofInjective f hf).symm b) = b :=
  Subtype.ext_iff.1 <| (ofInjective f hf).apply_symm_apply b
#align equiv.apply_of_injective_symm Equiv.apply_ofInjective_symm

@[simp]
theorem ofInjective_symm_apply {α β} {f : α → β} (hf : Injective f) (a : α) :
    (ofInjective f hf).symm ⟨f a, ⟨a, rfl⟩⟩ = a := by
  apply (ofInjective f hf).injective
  simp [apply_ofInjective_symm hf]
#align equiv.of_injective_symm_apply Equiv.ofInjective_symm_apply

theorem coe_ofInjective_symm {α β} {f : α → β} (hf : Injective f) :
    ((ofInjective f hf).symm : range f → α) = rangeSplitting f := by
  ext ⟨y, x, rfl⟩
  apply hf
  simp [apply_rangeSplitting f]
#align equiv.coe_of_injective_symm Equiv.coe_ofInjective_symm

@[simp]
theorem self_comp_ofInjective_symm {α β} {f : α → β} (hf : Injective f) :
    f ∘ (ofInjective f hf).symm = Subtype.val :=
  funext fun x => apply_ofInjective_symm hf x
#align equiv.self_comp_of_injective_symm Equiv.self_comp_ofInjective_symm

theorem ofLeftInverse_eq_ofInjective {α β : Type*} (f : α → β) (f_inv : Nonempty α → β → α)
    (hf : ∀ h : Nonempty α, LeftInverse (f_inv h) f) :
    ofLeftInverse f f_inv hf =
      ofInjective f ((isEmpty_or_nonempty α).elim (fun h _ _ _ => Subsingleton.elim _ _)
        (fun h => (hf h).injective)) := by
  ext
  simp
#align equiv.of_left_inverse_eq_of_injective Equiv.ofLeftInverse_eq_ofInjective

theorem ofLeftInverse'_eq_ofInjective {α β : Type*} (f : α → β) (f_inv : β → α)
    (hf : LeftInverse f_inv f) : ofLeftInverse' f f_inv hf = ofInjective f hf.injective := by
  ext
  simp
#align equiv.of_left_inverse'_eq_of_injective Equiv.ofLeftInverse'_eq_ofInjective

protected theorem set_forall_iff {α β} (e : α ≃ β) {p : Set α → Prop} :
    (∀ a, p a) ↔ ∀ a, p (e ⁻¹' a) :=
  e.injective.preimage_surjective.forall
#align equiv.set_forall_iff Equiv.set_forall_iff

theorem preimage_piEquivPiSubtypeProd_symm_pi {α : Type*} {β : α → Type*} (p : α → Prop)
    [DecidablePred p] (s : ∀ i, Set (β i)) :
    (piEquivPiSubtypeProd p β).symm ⁻¹' pi univ s =
      (pi univ fun i : { i // p i } => s i) ×ˢ pi univ fun i : { i // ¬p i } => s i := by
  ext ⟨f, g⟩
  simp only [mem_preimage, mem_univ_pi, prod_mk_mem_set_prod_eq, Subtype.forall, ← forall_and]
  refine forall_congr' fun i => ?_
  dsimp only [Subtype.coe_mk]
  by_cases hi : p i <;> simp [hi]
#align equiv.preimage_pi_equiv_pi_subtype_prod_symm_pi Equiv.preimage_piEquivPiSubtypeProd_symm_pi

-- See also `Equiv.sigmaFiberEquiv`.
/-- `sigmaPreimageEquiv f` for `f : α → β` is the natural equivalence between
the type of all preimages of points under `f` and the total space `α`. -/
@[simps!]
def sigmaPreimageEquiv {α β} (f : α → β) : (Σb, f ⁻¹' {b}) ≃ α :=
  sigmaFiberEquiv f
#align equiv.sigma_preimage_equiv Equiv.sigmaPreimageEquiv
#align equiv.sigma_preimage_equiv_symm_apply_snd_coe Equiv.sigmaPreimageEquiv_symm_apply_snd_coe
#align equiv.sigma_preimage_equiv_apply Equiv.sigmaPreimageEquiv_apply
#align equiv.sigma_preimage_equiv_symm_apply_fst Equiv.sigmaPreimageEquiv_symm_apply_fst

-- See also `Equiv.ofFiberEquiv`.
/-- A family of equivalences between preimages of points gives an equivalence between domains. -/
@[simps!]
def ofPreimageEquiv {α β γ} {f : α → γ} {g : β → γ} (e : ∀ c, f ⁻¹' {c} ≃ g ⁻¹' {c}) : α ≃ β :=
  Equiv.ofFiberEquiv e
#align equiv.of_preimage_equiv Equiv.ofPreimageEquiv
#align equiv.of_preimage_equiv_apply Equiv.ofPreimageEquiv_apply
#align equiv.of_preimage_equiv_symm_apply Equiv.ofPreimageEquiv_symm_apply

theorem ofPreimageEquiv_map {α β γ} {f : α → γ} {g : β → γ} (e : ∀ c, f ⁻¹' {c} ≃ g ⁻¹' {c})
    (a : α) : g (ofPreimageEquiv e a) = f a :=
  Equiv.ofFiberEquiv_map e a
#align equiv.of_preimage_equiv_map Equiv.ofPreimageEquiv_map

end Equiv

/-- If a function is a bijection between two sets `s` and `t`, then it induces an
equivalence between the types `↥s` and `↥t`. -/
noncomputable def Set.BijOn.equiv {α : Type*} {β : Type*} {s : Set α} {t : Set β} (f : α → β)
    (h : BijOn f s t) : s ≃ t :=
  Equiv.ofBijective _ h.bijective
#align set.bij_on.equiv Set.BijOn.equiv

/-- The composition of an updated function with an equiv on a subtype can be expressed as an
updated function. -/
-- Porting note: replace `s : Set α` and `: s` with `p : α → Prop` and `: Subtype p`, since the
-- former now unfolds syntactically to a less general case of the latter.
theorem dite_comp_equiv_update {α : Type*} {β : Sort*} {γ : Sort*} {p : α → Prop}
    (e : β ≃ Subtype p)
    (v : β → γ) (w : α → γ) (j : β) (x : γ) [DecidableEq β] [DecidableEq α]
    [∀ j, Decidable (p j)] :
    (fun i : α => if h : p i then (Function.update v j x) (e.symm ⟨i, h⟩) else w i) =
      Function.update (fun i : α => if h : p i then v (e.symm ⟨i, h⟩) else w i) (e j) x := by
  ext i
  by_cases h : p i
  · rw [dif_pos h, Function.update_apply_equiv_apply, Equiv.symm_symm,
      Function.update_apply, Function.update_apply, dif_pos h]
    have h_coe : (⟨i, h⟩ : Subtype p) = e j ↔ i = e j :=
      Subtype.ext_iff.trans (by rw [Subtype.coe_mk])
    simp [h_coe]
  · have : i ≠ e j := by
      contrapose! h
      have : p (e j : α) := (e j).2
      rwa [← h] at this
    simp [h, this]
#align dite_comp_equiv_update dite_comp_equiv_updateₓ

section Swap

variable {α : Type*} [DecidableEq α] {a b : α} {s : Set α}

theorem Equiv.swap_bijOn_self (hs : a ∈ s ↔ b ∈ s) : BijOn (Equiv.swap a b) s s := by
  refine ⟨fun x hx ↦ ?_, (Equiv.injective _).injOn, fun x hx ↦ ?_⟩
  · obtain (rfl | hxa) := eq_or_ne x a; rwa [swap_apply_left, ← hs]
    obtain (rfl | hxb) := eq_or_ne x b; rwa [swap_apply_right, hs]
    rwa [swap_apply_of_ne_of_ne hxa hxb]
  obtain (rfl | hxa) := eq_or_ne x a; simp [hs.1 hx]
  obtain (rfl | hxb) := eq_or_ne x b; simp [hs.2 hx]
  exact ⟨x, hx, swap_apply_of_ne_of_ne hxa hxb⟩

theorem Equiv.swap_bijOn_exchange (ha : a ∈ s) (hb : b ∉ s) :
    BijOn (Equiv.swap a b) s (insert b (s \ {a})) := by
  refine ⟨fun x hx ↦ ?_, (Equiv.injective _).injOn, fun x hx ↦ ?_⟩
  · obtain (rfl | hxa) := eq_or_ne x a; simp [swap_apply_left]
    rw [swap_apply_of_ne_of_ne hxa (by rintro rfl; contradiction)]
    exact .inr ⟨hx, hxa⟩
  obtain (rfl | hxb) := eq_or_ne x b; exact ⟨a, ha, by simp⟩
  simp only [mem_insert_iff, mem_diff, mem_singleton_iff, or_iff_right hxb] at hx
  exact ⟨x, hx.1, swap_apply_of_ne_of_ne hx.2 hxb⟩

end Swap
