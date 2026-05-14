/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Data.Set.Basic
public import Mathlib.Order.BooleanAlgebra.Basic
public import Mathlib.Order.Hom.Basic
public import Mathlib.Tactic.ToAdditive
import Batteries.Tactic.Congr
import Mathlib.Data.Set.NAry
import Mathlib.Data.Set.Prod
import Mathlib.Data.ULift
import Mathlib.Init
import Mathlib.Order.BoundedOrder.Lattice
import Mathlib.Order.Bounds.Basic
import Mathlib.Order.Bounds.Image
import Mathlib.Order.Hom.Set
import Mathlib.Tactic.Coe
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.GCongr.Core
import Mathlib.Tactic.SimpRw
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Translate.ToDual
import Mathlib.Util.CompileInductive

/-!
# Theory of complete lattices

This file contains basic results on complete lattices.

## Naming conventions

In lemma names,
* `sSup` is called `sSup`
* `sInf` is called `sInf`
* `⨆ i, s i` is called `iSup`
* `⨅ i, s i` is called `iInf`
* `⨆ i j, s i j` is called `iSup₂`. This is an `iSup` inside an `iSup`.
* `⨅ i j, s i j` is called `iInf₂`. This is an `iInf` inside an `iInf`.
* `⨆ i ∈ s, t i` is called `biSup` for "bounded `iSup`". This is the special case of `iSup₂`
  where `j : i ∈ s`.
* `⨅ i ∈ s, t i` is called `biInf` for "bounded `iInf`". This is the special case of `iInf₂`
  where `j : i ∈ s`.

## Notation

* `⨆ i, f i` : `iSup f`, the supremum of the range of `f`;
* `⨅ i, f i` : `iInf f`, the infimum of the range of `f`.
-/

public section

open Function OrderDual Set

variable {α β γ : Type*} {ι ι' : Sort*} {κ : ι → Sort*} {κ' : ι' → Sort*}

@[to_dual (attr := simp)] lemma iSup_ulift {ι : Type*} [SupSet α] (f : ULift ι → α) :
    ⨆ i : ULift ι, f i = ⨆ i, f (.up i) := by simp only [iSup]; congr with x; simp

section

variable [CompleteSemilatticeSup α] {s t : Set α} {a b : α}

@[to_dual]
theorem sSup_le_sSup_of_isCofinalFor (h : IsCofinalFor s t) : sSup s ≤ sSup t :=
  IsLeast.mono (isLUB_sSup t) (isLUB_sSup s) <| upperBounds_mono_of_isCofinalFor h

-- We will generalize this to conditionally complete lattices in `csSup_singleton`.
@[to_dual (attr := simp)]
theorem sSup_singleton {a : α} : sSup {a} = a :=
  isLUB_singleton.sSup_eq

end

open OrderDual

section

variable [CompleteLattice α] {s t : Set α} {b : α}

theorem sInf_le_sSup (hs : s.Nonempty) : sInf s ≤ sSup s :=
  isGLB_le_isLUB (isGLB_sInf s) (isLUB_sSup s) hs

theorem sInf_le_sSup_of_nonempty_inter (h : (s ∩ t).Nonempty) : sInf s ≤ sSup t :=
  isGLB_le_isLUB_of_nonempty_inter h (isGLB_sInf s) (isLUB_sSup t)

@[to_dual]
theorem sSup_union {s t : Set α} : sSup (s ∪ t) = sSup s ⊔ sSup t :=
  ((isLUB_sSup s).union (isLUB_sSup t)).sSup_eq

@[to_dual le_sInf_inter]
theorem sSup_inter_le {s t : Set α} : sSup (s ∩ t) ≤ sSup s ⊓ sSup t :=
  sSup_le fun _ hb => le_inf (le_sSup hb.1) (le_sSup hb.2)

@[to_dual (attr := simp)]
theorem sSup_empty : sSup ∅ = (⊥ : α) :=
  (@isLUB_empty α _ _).sSup_eq

@[to_dual (attr := simp)]
theorem sSup_univ : sSup univ = (⊤ : α) :=
  (@isLUB_univ α _ _).sSup_eq

-- TODO(Jeremy): get this automatically
@[to_dual (attr := simp)]
theorem sSup_insert {a : α} {s : Set α} : sSup (insert a s) = a ⊔ sSup s :=
  ((isLUB_sSup s).insert a).sSup_eq

@[to_dual]
theorem sSup_le_sSup_of_subset_insert_bot (h : s ⊆ insert ⊥ t) : sSup s ≤ sSup t :=
  (sSup_le_sSup h).trans_eq (sSup_insert.trans (bot_sup_eq _))

@[to_dual (attr := simp)]
theorem sSup_diff_singleton_bot (s : Set α) : sSup (s \ {⊥}) = sSup s :=
  (sSup_le_sSup diff_subset).antisymm <|
    sSup_le_sSup_of_subset_insert_bot <| subset_insert_diff_singleton _ _

@[to_dual]
theorem sSup_pair {a b : α} : sSup {a, b} = a ⊔ b :=
  (@isLUB_pair α _ a b).sSup_eq

@[to_dual (attr := simp)]
theorem sSup_eq_bot : sSup s = ⊥ ↔ ∀ a ∈ s, a = ⊥ :=
  ⟨fun h _ ha => bot_unique <| h ▸ le_sSup ha, fun h =>
    bot_unique <| sSup_le fun a ha => le_bot_iff.2 <| h a ha⟩

@[to_dual]
lemma sSup_eq_bot' {s : Set α} : sSup s = ⊥ ↔ s = ∅ ∨ s = {⊥} := by
  rw [sSup_eq_bot, ← subset_singleton_iff_eq, subset_singleton_iff]

@[to_dual]
theorem eq_singleton_bot_of_sSup_eq_bot_of_nonempty {s : Set α} (h_sup : sSup s = ⊥)
    (hne : s.Nonempty) : s = {⊥} := by
  rw [Set.eq_singleton_iff_nonempty_unique_mem]
  rw [sSup_eq_bot] at h_sup
  exact ⟨hne, h_sup⟩

/-- Introduction rule to prove that `b` is the supremum of `s`: it suffices to check that `b`
is larger than all elements of `s`, and that this is not the case of any `w < b`.
See `csSup_eq_of_forall_le_of_forall_lt_exists_gt` for a version in conditionally complete
lattices. -/
@[to_dual sInf_eq_of_forall_ge_of_forall_gt_exists_lt
/-- Introduction rule to prove that `b` is the infimum of `s`: it suffices to check that `b`
is smaller than all elements of `s`, and that this is not the case of any `w > b`.
See `csInf_eq_of_forall_ge_of_forall_gt_exists_lt` for a version in conditionally complete
lattices. -/]
theorem sSup_eq_of_forall_le_of_forall_lt_exists_gt (h₁ : ∀ a ∈ s, a ≤ b)
    (h₂ : ∀ w, w < b → ∃ a ∈ s, w < a) : sSup s = b :=
  (sSup_le h₁).eq_of_not_lt fun h =>
    let ⟨_, ha, ha'⟩ := h₂ _ h
    ((le_sSup ha).trans_lt ha').false

end

/-
### iSup & iInf
-/
section SupSet

variable [SupSet α] {f g : ι → α}

@[to_dual]
theorem sSup_range : sSup (range f) = iSup f :=
  rfl

@[to_dual]
theorem sSup_eq_iSup' (s : Set α) : sSup s = ⨆ a : s, (a : α) := by rw [iSup, Subtype.range_coe]

@[to_dual]
theorem iSup_congr (h : ∀ i, f i = g i) : ⨆ i, f i = ⨆ i, g i :=
  congr_arg _ <| funext h

@[to_dual]
theorem biSup_congr {p : ι → Prop} (h : ∀ i, p i → f i = g i) :
    ⨆ (i) (_ : p i), f i = ⨆ (i) (_ : p i), g i :=
  iSup_congr fun i ↦ iSup_congr (h i)

@[to_dual]
theorem biSup_congr' {p : ι → Prop} {f g : (i : ι) → p i → α}
    (h : ∀ i (hi : p i), f i hi = g i hi) :
    ⨆ i, ⨆ (hi : p i), f i hi = ⨆ i, ⨆ (hi : p i), g i hi := by
  #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
  (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal.
  It is not yet clear whether this is due to defeq abuse in Mathlib or a problem in the new
  canonicalizer; a minimization would help. The original proof was: `grind` -/
  simp_all

@[to_dual]
theorem Function.Surjective.iSup_comp {f : ι → ι'} (hf : Surjective f) (g : ι' → α) :
    ⨆ x, g (f x) = ⨆ y, g y := by
  simp only [iSup.eq_1]
  congr
  exact hf.range_comp g

@[to_dual]
theorem Equiv.iSup_comp {g : ι' → α} (e : ι ≃ ι') : ⨆ x, g (e x) = ⨆ y, g y :=
  e.surjective.iSup_comp _

@[to_dual]
protected theorem Function.Surjective.iSup_congr {g : ι' → α} (h : ι → ι') (h1 : Surjective h)
    (h2 : ∀ x, g (h x) = f x) : ⨆ x, f x = ⨆ y, g y := by
  convert h1.iSup_comp g
  exact (h2 _).symm

@[to_dual]
protected theorem Equiv.iSup_congr {g : ι' → α} (e : ι ≃ ι') (h : ∀ x, g (e x) = f x) :
    ⨆ x, f x = ⨆ y, g y :=
  e.surjective.iSup_congr _ h

@[to_dual (attr := congr)]
theorem iSup_congr_Prop {p q : Prop} {f₁ : p → α} {f₂ : q → α} (pq : p ↔ q)
    (f : ∀ x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂ := by
  obtain rfl := propext pq
  congr with x
  apply f

@[to_dual]
theorem iSup_plift_up (f : PLift ι → α) : ⨆ i, f (PLift.up i) = ⨆ i, f i :=
  (PLift.up_surjective.iSup_congr _) fun _ => rfl

@[to_dual]
theorem iSup_plift_down (f : ι → α) : ⨆ i, f (PLift.down i) = ⨆ i, f i :=
  (PLift.down_surjective.iSup_congr _) fun _ => rfl

@[to_dual]
theorem iSup_range' (g : β → α) (f : ι → β) : ⨆ b : range f, g b = ⨆ i, g (f i) := by
  rw [iSup, iSup, ← image_eq_range, ← range_comp']

@[to_dual]
theorem sSup_image' {s : Set β} {f : β → α} : sSup (f '' s) = ⨆ a : s, f a := by
  rw [iSup, image_eq_range]

end SupSet

section

variable [CompleteLattice α] {f g s : ι → α} {a b : α}

@[to_dual iInf_le]
theorem le_iSup (f : ι → α) (i : ι) : f i ≤ iSup f :=
  le_sSup ⟨i, rfl⟩

lemma iInf_le_iSup [Nonempty ι] : ⨅ i, f i ≤ ⨆ i, f i :=
  (iInf_le _ (Classical.arbitrary _)).trans <| le_iSup _ (Classical.arbitrary _)

@[to_dual]
theorem isLUB_iSup : IsLUB (range f) (⨆ j, f j) :=
  isLUB_sSup _

@[to_dual]
theorem IsLUB.iSup_eq (h : IsLUB (range f) a) : ⨆ j, f j = a :=
  h.sSup_eq

@[to_dual iInf_le_of_le]
theorem le_iSup_of_le (i : ι) (h : a ≤ f i) : a ≤ iSup f :=
  h.trans <| le_iSup _ i

@[to_dual iInf₂_le]
theorem le_iSup₂ {f : ∀ i, κ i → α} (i : ι) (j : κ i) : f i j ≤ ⨆ (i) (j), f i j :=
  le_iSup_of_le i <| le_iSup (f i) j

@[to_dual iInf₂_le_of_le]
theorem le_iSup₂_of_le {f : ∀ i, κ i → α} (i : ι) (j : κ i) (h : a ≤ f i j) :
    a ≤ ⨆ (i) (j), f i j :=
  h.trans <| le_iSup₂ i j

@[to_dual le_iInf]
theorem iSup_le (h : ∀ i, f i ≤ a) : iSup f ≤ a :=
  sSup_le fun _ ⟨i, Eq⟩ => Eq ▸ h i

@[to_dual le_iInf₂]
theorem iSup₂_le {f : ∀ i, κ i → α} (h : ∀ i j, f i j ≤ a) : ⨆ (i) (j), f i j ≤ a :=
  iSup_le fun i => iSup_le <| h i

@[to_dual iInf_le_iInf₂]
theorem iSup₂_le_iSup (κ : ι → Sort*) (f : ι → α) : ⨆ (i) (_ : κ i), f i ≤ ⨆ i, f i :=
  iSup₂_le fun i _ => le_iSup f i

@[to_dual (attr := gcongr)]
theorem iSup_mono (h : ∀ i, f i ≤ g i) : iSup f ≤ iSup g :=
  iSup_le fun i => le_iSup_of_le i <| h i

@[to_dual]
theorem iSup₂_mono {f g : ∀ i, κ i → α} (h : ∀ i j, f i j ≤ g i j) :
    ⨆ (i) (j), f i j ≤ ⨆ (i) (j), g i j :=
  iSup_mono fun i => iSup_mono <| h i

@[to_dual]
theorem iSup_mono' {g : ι' → α} (h : ∀ i, ∃ i', f i ≤ g i') : iSup f ≤ iSup g :=
  iSup_le fun i => Exists.elim (h i) le_iSup_of_le

@[to_dual]
theorem iSup₂_mono' {f : ∀ i, κ i → α} {g : ∀ i', κ' i' → α} (h : ∀ i j, ∃ i' j', f i j ≤ g i' j') :
    ⨆ (i) (j), f i j ≤ ⨆ (i) (j), g i j :=
  iSup₂_le fun i j =>
    let ⟨i', j', h⟩ := h i j
    le_iSup₂_of_le i' j' h

@[to_dual]
theorem iSup_const_mono (h : ι → ι') : ⨆ _ : ι, a ≤ ⨆ _ : ι', a :=
  iSup_le <| le_iSup _ ∘ h

@[to_dual none]
theorem iSup_iInf_le_iInf_iSup (f : ι → ι' → α) : ⨆ i, ⨅ j, f i j ≤ ⨅ j, ⨆ i, f i j :=
  iSup_le fun i => iInf_mono fun j => le_iSup (fun i => f i j) i

@[to_dual]
theorem biSup_mono {p q : ι → Prop} (hpq : ∀ i, p i → q i) :
    ⨆ (i) (_ : p i), f i ≤ ⨆ (i) (_ : q i), f i :=
  iSup_mono fun i => iSup_const_mono (hpq i)

@[to_dual (attr := simp) le_iInf_iff]
theorem iSup_le_iff : iSup f ≤ a ↔ ∀ i, f i ≤ a :=
  (isLUB_le_iff isLUB_iSup).trans forall_mem_range

@[to_dual le_iInf₂_iff]
theorem iSup₂_le_iff {f : ∀ i, κ i → α} : ⨆ (i) (j), f i j ≤ a ↔ ∀ i j, f i j ≤ a := by
  simp_rw [iSup_le_iff]

@[to_dual]
theorem sSup_eq_iSup {s : Set α} : sSup s = ⨆ a ∈ s, a :=
  le_antisymm (sSup_le le_iSup₂) (iSup₂_le fun _ => le_sSup)

@[to_dual]
lemma sSup_lowerBounds_eq_sInf (s : Set α) : sSup (lowerBounds s) = sInf s :=
  (isLUB_sSup _).unique (isGLB_sInf _).isLUB

@[deprecated (since := "2026-02-01")] alias sInf_upperBounds_eq_csSup := sInf_upperBounds_eq_sSup

@[to_dual map_iInf_le]
theorem Monotone.le_map_iSup [CompleteLattice β] {f : α → β} (hf : Monotone f) :
    ⨆ i, f (s i) ≤ f (iSup s) :=
  iSup_le fun _ => hf <| le_iSup _ _

@[to_dual map_iSup_le]
theorem Antitone.le_map_iInf [CompleteLattice β] {f : α → β} (hf : Antitone f) :
    ⨆ i, f (s i) ≤ f (iInf s) :=
  hf.dual_left.le_map_iSup

@[to_dual map_iInf₂_le]
theorem Monotone.le_map_iSup₂ [CompleteLattice β] {f : α → β} (hf : Monotone f) (s : ∀ i, κ i → α) :
    ⨆ (i) (j), f (s i j) ≤ f (⨆ (i) (j), s i j) :=
  iSup₂_le fun _ _ => hf <| le_iSup₂ _ _

@[to_dual map_iSup₂_le]
theorem Antitone.le_map_iInf₂ [CompleteLattice β] {f : α → β} (hf : Antitone f) (s : ∀ i, κ i → α) :
    ⨆ (i) (j), f (s i j) ≤ f (⨅ (i) (j), s i j) :=
  hf.dual_left.le_map_iSup₂ _

@[to_dual map_sInf_le]
theorem Monotone.le_map_sSup [CompleteLattice β] {s : Set α} {f : α → β} (hf : Monotone f) :
    ⨆ a ∈ s, f a ≤ f (sSup s) := by rw [sSup_eq_iSup]; exact hf.le_map_iSup₂ _

@[to_dual map_sSup_le]
theorem Antitone.le_map_sInf [CompleteLattice β] {s : Set α} {f : α → β} (hf : Antitone f) :
    ⨆ a ∈ s, f a ≤ f (sInf s) :=
  hf.dual_left.le_map_sSup

@[to_dual]
theorem OrderIso.map_iSup [CompleteLattice β] (f : α ≃o β) (x : ι → α) :
    f (⨆ i, x i) = ⨆ i, f (x i) :=
  eq_of_forall_ge_iff <| f.surjective.forall.2
  fun x => by simp only [f.le_iff_le, iSup_le_iff]

@[to_dual]
lemma OrderIso.map_iSup₂ [CompleteLattice β] (f : α ≃o β) (x : ∀ i, κ i → α) :
    f (⨆ i, ⨆ j, x i j) = ⨆ i, ⨆ j, f (x i j) :=
  eq_of_forall_ge_iff <| f.surjective.forall.2
  fun x => by simp only [f.le_iff_le, iSup_le_iff]

@[to_dual]
theorem OrderIso.map_sSup [CompleteLattice β] (f : α ≃o β) (s : Set α) :
    f (sSup s) = ⨆ a ∈ s, f a := by
  simp only [sSup_eq_iSup, OrderIso.map_iSup]

@[to_dual le_iInf_comp]
theorem iSup_comp_le {ι' : Sort*} (f : ι' → α) (g : ι → ι') : ⨆ x, f (g x) ≤ ⨆ y, f y :=
  iSup_mono' fun _ => ⟨_, le_rfl⟩

@[to_dual]
theorem Monotone.iSup_comp_eq [Preorder β] {f : β → α} (hf : Monotone f) {s : ι → β}
    (hs : ∀ x, ∃ i, x ≤ s i) : ⨆ x, f (s x) = ⨆ y, f y :=
  le_antisymm (iSup_comp_le _ _) (iSup_mono' fun x => (hs x).imp fun _ hi => hf hi)

@[to_dual le_iInf_const]
theorem iSup_const_le : ⨆ _ : ι, a ≤ a :=
  iSup_le fun _ => le_rfl

-- We generalize this to conditionally complete lattices in `ciSup_const` and `ciInf_const`.
@[to_dual]
theorem iSup_const [Nonempty ι] : ⨆ _ : ι, a = a := by rw [iSup, range_const, sSup_singleton]

@[to_dual]
lemma iSup_unique [Unique ι] (f : ι → α) : ⨆ i, f i = f default := by
  simp only [congr_arg f (Unique.eq_default _), iSup_const]

@[to_dual (attr := simp)]
theorem iSup_bot : (⨆ _ : ι, ⊥ : α) = ⊥ :=
  bot_unique iSup_const_le

@[to_dual (attr := simp)]
theorem iSup_eq_bot : iSup s = ⊥ ↔ ∀ i, s i = ⊥ :=
  sSup_eq_bot.trans forall_mem_range

@[to_dual (attr := simp) iInf_lt_top]
lemma bot_lt_iSup : ⊥ < ⨆ i, s i ↔ ∃ i, ⊥ < s i := by simp [bot_lt_iff_ne_bot]

@[to_dual]
theorem iSup₂_eq_bot {f : ∀ i, κ i → α} : ⨆ (i) (j), f i j = ⊥ ↔ ∀ i j, f i j = ⊥ := by
  simp

@[to_dual (attr := simp)]
theorem iSup_pos {p : Prop} {f : p → α} (hp : p) : ⨆ h : p, f h = f hp :=
  le_antisymm (iSup_le fun _ => le_rfl) (le_iSup _ _)

@[to_dual (attr := simp)]
theorem iSup_neg {p : Prop} {f : p → α} (hp : ¬p) : ⨆ h : p, f h = ⊥ :=
  le_antisymm (iSup_le fun h => (hp h).elim) bot_le

/-- Introduction rule to prove that `b` is the supremum of `f`: it suffices to check that `b`
is larger than `f i` for all `i`, and that this is not the case of any `w<b`.
See `ciSup_eq_of_forall_le_of_forall_lt_exists_gt` for a version in conditionally complete
lattices. -/
@[to_dual iInf_eq_of_forall_ge_of_forall_gt_exists_lt
/-- Introduction rule to prove that `b` is the infimum of `f`: it suffices to check that `b`
is smaller than `f i` for all `i`, and that this is not the case of any `w>b`.
See `ciInf_eq_of_forall_ge_of_forall_gt_exists_lt` for a version in conditionally complete
lattices. -/]
theorem iSup_eq_of_forall_le_of_forall_lt_exists_gt {f : ι → α} (h₁ : ∀ i, f i ≤ b)
    (h₂ : ∀ w, w < b → ∃ i, w < f i) : ⨆ i : ι, f i = b :=
  sSup_eq_of_forall_le_of_forall_lt_exists_gt (forall_mem_range.mpr h₁) fun w hw =>
    exists_range_iff.mpr <| h₂ w hw

@[to_dual]
theorem iSup_eq_dif {p : Prop} [Decidable p] (a : p → α) :
    ⨆ h : p, a h = if h : p then a h else ⊥ := by by_cases h : p <;> simp [h]

@[to_dual]
theorem iSup_eq_if {p : Prop} [Decidable p] (a : α) : ⨆ _ : p, a = if p then a else ⊥ :=
  iSup_eq_dif fun _ => a

@[to_dual]
theorem iSup_comm {f : ι → ι' → α} : ⨆ (i) (j), f i j = ⨆ (j) (i), f i j :=
  le_antisymm (iSup_le fun i => iSup_mono fun j => le_iSup (fun i => f i j) i)
    (iSup_le fun _ => iSup_mono fun _ => le_iSup _ _)

@[to_dual]
theorem iSup₂_comm {ι₁ ι₂ : Sort*} {κ₁ : ι₁ → Sort*} {κ₂ : ι₂ → Sort*}
    (f : ∀ i₁, κ₁ i₁ → ∀ i₂, κ₂ i₂ → α) :
    ⨆ (i₁) (j₁) (i₂) (j₂), f i₁ j₁ i₂ j₂ = ⨆ (i₂) (j₂) (i₁) (j₁), f i₁ j₁ i₂ j₂ := by
  simp only [@iSup_comm _ (κ₁ _), @iSup_comm _ ι₁]

/- TODO: this is strange. In the proof below, we get exactly the desired among the equalities,
but close does not get it.
begin
  apply @le_antisymm,
    simp, intros,
    begin [smt]
      ematch, ematch, ematch, trace_state, have := le_refl (f i_1 i),
      trace_state, close
    end
end
-/
@[to_dual (attr := simp)]
theorem iSup_iSup_eq_left {b : β} {f : ∀ x : β, x = b → α} : ⨆ x, ⨆ h : x = b, f x h = f b rfl :=
  (@le_iSup₂ _ _ _ _ f b rfl).antisymm'
    (iSup_le fun c =>
      iSup_le <| by
        rintro rfl
        rfl)

@[to_dual (attr := simp)]
theorem iSup_iSup_eq_right {b : β} {f : ∀ x : β, b = x → α} : ⨆ x, ⨆ h : b = x, f x h = f b rfl :=
  (le_iSup₂ b rfl).antisymm'
    (iSup₂_le fun c => by
      rintro rfl
      rfl)

@[to_dual]
theorem iSup_subtype {p : ι → Prop} {f : Subtype p → α} : iSup f = ⨆ (i) (h : p i), f ⟨i, h⟩ :=
  le_antisymm (iSup_le fun ⟨i, h⟩ => @le_iSup₂ _ _ p _ (fun i h => f ⟨i, h⟩) i h)
    (iSup₂_le fun _ _ => le_iSup _ _)

@[to_dual]
theorem iSup_subtype' {p : ι → Prop} {f : ∀ i, p i → α} :
    ⨆ (i) (h), f i h = ⨆ x : Subtype p, f x x.property :=
  (@iSup_subtype _ _ _ p fun x => f x.val x.property).symm

@[to_dual]
theorem iSup_subtype'' {ι} (s : Set ι) (f : ι → α) : ⨆ i : s, f i = ⨆ (t : ι) (_ : t ∈ s), f t :=
  iSup_subtype

@[to_dual]
theorem biSup_const {a : α} {s : Set β} (hs : s.Nonempty) : ⨆ i ∈ s, a = a := by
  haveI : Nonempty s := Set.nonempty_coe_sort.mpr hs
  rw [← iSup_subtype'', iSup_const]

@[to_dual]
theorem iSup_sup_eq : ⨆ x, f x ⊔ g x = (⨆ x, f x) ⊔ ⨆ x, g x :=
  le_antisymm (iSup_le fun _ => sup_le_sup (le_iSup _ _) <| le_iSup _ _)
    (sup_le (iSup_mono fun _ => le_sup_left) <| iSup_mono fun _ => le_sup_right)

@[to_dual]
lemma Equiv.biSup_comp {ι ι' : Type*} {g : ι' → α} (e : ι ≃ ι') (s : Set ι') :
    ⨆ i ∈ e.symm '' s, g (e i) = ⨆ i ∈ s, g i := by
  simpa only [iSup_subtype'] using (image e.symm s).symm.iSup_comp (g := g ∘ (↑))

@[to_dual biInf_le]
lemma le_biSup {ι : Type*} {s : Set ι} (f : ι → α) {i : ι} (hi : i ∈ s) : f i ≤ ⨆ i ∈ s, f i :=
  le_iSup₂_of_le i hi le_rfl

lemma biInf_le_biSup {ι : Type*} {s : Set ι} (hs : s.Nonempty) {f : ι → α} :
    ⨅ i ∈ s, f i ≤ ⨆ i ∈ s, f i :=
  (biInf_le _ hs.choose_spec).trans <| le_biSup _ hs.choose_spec

/- TODO: here is another example where more flexible pattern matching might help.

begin
  apply @le_antisymm,
  safe, pose h := f a ⊓ g a, begin [smt] ematch, ematch end
end
-/
@[to_dual]
theorem iSup_sup [Nonempty ι] {f : ι → α} {a : α} : (⨆ x, f x) ⊔ a = ⨆ x, f x ⊔ a := by
  rw [iSup_sup_eq, iSup_const]

@[to_dual]
theorem sup_iSup [Nonempty ι] {f : ι → α} {a : α} : (a ⊔ ⨆ x, f x) = ⨆ x, a ⊔ f x := by
  rw [iSup_sup_eq, iSup_const]

@[to_dual]
theorem biSup_sup {p : ι → Prop} {f : ∀ i, p i → α} {a : α} (h : ∃ i, p i) :
    (⨆ (i) (h : p i), f i h) ⊔ a = ⨆ (i) (h : p i), f i h ⊔ a := by
  haveI : Nonempty { i // p i } :=
    let ⟨i, hi⟩ := h
    ⟨⟨i, hi⟩⟩
  rw [iSup_subtype', iSup_subtype', iSup_sup]

@[to_dual]
theorem sup_biSup {p : ι → Prop} {f : ∀ i, p i → α} {a : α} (h : ∃ i, p i) :
    (a ⊔ ⨆ (i) (h : p i), f i h) = ⨆ (i) (h : p i), a ⊔ f i h := by
  simpa only [sup_comm] using @biSup_sup α _ _ p _ _ h

@[to_dual (dont_translate := ι)]
lemma biSup_lt_eq_iSup {ι : Type*} [LT ι] [NoMaxOrder ι] {f : ι → α} :
    ⨆ (i) (j < i), f j = ⨆ i, f i := by
  apply le_antisymm
  · exact iSup_le fun _ ↦ iSup₂_le fun _ _ ↦ le_iSup _ _
  · refine iSup_le fun j ↦ ?_
    obtain ⟨i, jlt⟩ := exists_gt j
    exact le_iSup_of_le i (le_iSup₂_of_le j jlt le_rfl)

@[to_dual (dont_translate := ι)]
lemma biSup_le_eq_iSup {ι : Type*} [Preorder ι] {f : ι → α} :
    ⨆ (i) (j ≤ i), f j = ⨆ i, f i := by
  apply le_antisymm
  · exact iSup_le fun _ ↦ iSup₂_le fun _ _ ↦ le_iSup _ _
  · exact iSup_le fun j ↦ le_iSup_of_le j (le_iSup₂_of_le j le_rfl le_rfl)

@[to_dual (dont_translate := ι)]
lemma biSup_gt_eq_iSup {ι : Type*} [LT ι] [NoMinOrder ι] {f : ι → α} :
    ⨆ (i) (j > i), f j = ⨆ i, f i := by
  apply le_antisymm
  · exact iSup_le fun _ ↦ iSup₂_le fun _ _ ↦ le_iSup _ _
  · refine iSup_le fun j ↦ ?_
    obtain ⟨i, jlt⟩ := exists_lt j
    exact le_iSup_of_le i (le_iSup₂_of_le j jlt le_rfl)

@[to_dual (dont_translate := ι)]
lemma biSup_ge_eq_iSup {ι : Type*} [Preorder ι] {f : ι → α} : ⨆ (i) (j ≥ i), f j = ⨆ i, f i := by
  apply le_antisymm
  · exact iSup_le fun _ ↦ iSup₂_le fun _ _ ↦ le_iSup _ _
  · exact iSup_le fun j ↦ le_iSup_of_le j (le_iSup₂_of_le j le_rfl le_rfl)

@[to_dual biInf_ge_eq_of_monotone]
lemma biSup_le_eq_of_monotone [Preorder β] {f : β → α} (hf : Monotone f) (b : β) :
    ⨆ (b' ≤ b), f b' = f b :=
  le_antisymm (iSup₂_le_iff.2 (fun _ hji ↦ hf hji))
    (le_iSup_of_le b (ge_of_eq (iSup_pos le_rfl)))

@[to_dual biSup_ge_eq_of_antitone]
lemma biInf_le_eq_of_antitone [Preorder β] {f : β → α} (hf : Antitone f) (b : β) :
    ⨅ (b' ≤ b), f b' = f b :=
  le_antisymm (iInf₂_le_of_le b le_rfl le_rfl)
    (le_iInf₂ fun _ hji ↦ hf hji)

/-! ### `iSup` and `iInf` under `Prop` -/

@[to_dual]
theorem iSup_false {s : False → α} : iSup s = ⊥ := by simp

@[to_dual]
theorem iSup_true {s : True → α} : iSup s = s trivial :=
  iSup_pos trivial

@[to_dual (attr := simp)]
theorem iSup_exists {p : ι → Prop} {f : Exists p → α} : ⨆ x, f x = ⨆ (i) (h), f ⟨i, h⟩ :=
  le_antisymm (iSup_le fun ⟨i, h⟩ => @le_iSup₂ _ _ _ _ (fun _ _ => _) i h)
    (iSup₂_le fun _ _ => le_iSup _ _)

@[to_dual]
theorem iSup_and {p q : Prop} {s : p ∧ q → α} : iSup s = ⨆ (h₁) (h₂), s ⟨h₁, h₂⟩ :=
  le_antisymm (iSup_le fun ⟨i, h⟩ => @le_iSup₂ _ _ _ _ (fun _ _ => _) i h)
    (iSup₂_le fun _ _ => le_iSup _ _)

/-- The symmetric case of `iSup_and`, useful for rewriting into a supremum over a conjunction -/
@[to_dual /-- The symmetric case of `iInf_and`,
useful for rewriting into an infimum over a conjunction. -/]
theorem iSup_and' {p q : Prop} {s : p → q → α} :
    ⨆ (h₁ : p) (h₂ : q), s h₁ h₂ = ⨆ h : p ∧ q, s h.1 h.2 :=
  Eq.symm iSup_and

@[to_dual]
theorem iSup_or {p q : Prop} {s : p ∨ q → α} :
    ⨆ x, s x = (⨆ i, s (Or.inl i)) ⊔ ⨆ j, s (Or.inr j) :=
  le_antisymm
    (iSup_le fun i =>
      match i with
      | Or.inl _ => le_sup_of_le_left <| le_iSup (fun _ => s _) _
      | Or.inr _ => le_sup_of_le_right <| le_iSup (fun _ => s _) _)
    (sup_le (iSup_comp_le _ _) (iSup_comp_le _ _))

section

variable (p : ι → Prop) [DecidablePred p]

@[to_dual]
theorem iSup_dite (f : ∀ i, p i → α) (g : ∀ i, ¬p i → α) :
    ⨆ i, (if h : p i then f i h else g i h) = (⨆ (i) (h : p i), f i h) ⊔ ⨆ (i) (h : ¬p i),
    g i h := by
  rw [← iSup_sup_eq]
  congr 1 with i
  split_ifs with h <;> simp [h]

@[to_dual]
theorem iSup_ite (f g : ι → α) :
    ⨆ i, (if p i then f i else g i) = (⨆ (i) (_ : p i), f i) ⊔ ⨆ (i) (_ : ¬p i), g i :=
  iSup_dite _ _ _

end

@[to_dual]
theorem iSup_range {g : β → α} {f : ι → β} : ⨆ b ∈ range f, g b = ⨆ i, g (f i) := by
  rw [← iSup_subtype'', iSup_range']

@[to_dual]
theorem sSup_image {s : Set β} {f : β → α} : sSup (f '' s) = ⨆ a ∈ s, f a := by
  rw [← iSup_subtype'', sSup_image']

@[to_dual]
theorem OrderIso.map_sSup_eq_sSup_symm_preimage [CompleteLattice β] (f : α ≃o β) (s : Set α) :
    f (sSup s) = sSup (f.symm ⁻¹' s) := by
  rw [map_sSup, ← sSup_image, f.image_eq_preimage_symm]

/-
### iSup and iInf under set constructions
-/

@[to_dual]
theorem iSup_emptyset {f : β → α} : ⨆ x ∈ (∅ : Set β), f x = ⊥ := by simp

@[to_dual]
theorem iSup_univ {f : β → α} : ⨆ x ∈ (univ : Set β), f x = ⨆ x, f x := by simp

@[to_dual]
theorem iSup_union {f : β → α} {s t : Set β} :
    ⨆ x ∈ s ∪ t, f x = (⨆ x ∈ s, f x) ⊔ ⨆ x ∈ t, f x := by
  simp_rw [mem_union, iSup_or, iSup_sup_eq]

@[to_dual]
theorem iSup_split (f : β → α) (p : β → Prop) :
    ⨆ i, f i = (⨆ (i) (_ : p i), f i) ⊔ ⨆ (i) (_ : ¬p i), f i := by
  simpa [Classical.em] using @iSup_union _ _ _ f { i | p i } { i | ¬p i }

@[to_dual]
theorem iSup_split_single (f : β → α) (i₀ : β) : ⨆ i, f i = f i₀ ⊔ ⨆ (i) (_ : i ≠ i₀), f i := by
  convert iSup_split f (fun i => i = i₀)
  simp

@[to_dual]
theorem iSup_le_iSup_of_subset {f : β → α} {s t : Set β} : s ⊆ t → ⨆ x ∈ s, f x ≤ ⨆ x ∈ t, f x :=
  biSup_mono

@[to_dual]
theorem iSup_insert {f : β → α} {s : Set β} {b : β} :
    ⨆ x ∈ insert b s, f x = f b ⊔ ⨆ x ∈ s, f x := by
  simp [iSup_or, iSup_sup_eq]

@[to_dual]
theorem iSup_singleton {f : β → α} {b : β} : ⨆ x ∈ (singleton b : Set β), f x = f b := by simp

@[to_dual]
theorem iSup_pair {f : β → α} {a b : β} : ⨆ x ∈ ({a, b} : Set β), f x = f a ⊔ f b := by
  rw [iSup_insert, iSup_singleton]

@[to_dual]
theorem iSup_image {γ} {f : β → γ} {g : γ → α} {t : Set β} :
    ⨆ c ∈ f '' t, g c = ⨆ b ∈ t, g (f b) := by
  rw [← sSup_image, ← sSup_image, ← image_comp, comp_def]

@[to_dual]
theorem iSup_extend_bot {e : ι → β} (he : Injective e) (f : ι → α) :
    ⨆ j, extend e f ⊥ j = ⨆ i, f i := by
  rw [iSup_split _ fun j => ∃ i, e i = j]
  simp +contextual [he.extend_apply, extend_apply', @iSup_comm _ β ι]

@[to_dual]
theorem Set.BijOn.iSup_comp {s : Set β} {t : Set γ} {f : β → γ} (g : γ → α)
    (hf : Set.BijOn f s t) : ⨆ x ∈ s, g (f x) = ⨆ y ∈ t, g y := by
  rw [← hf.image_eq, iSup_image]

@[to_dual]
theorem Set.BijOn.iSup_congr {s : Set β} {t : Set γ} (f : β → α) (g : γ → α) {h : β → γ}
    (h1 : Set.BijOn h s t) (h2 : ∀ x, g (h x) = f x) : ⨆ x ∈ s, f x = ⨆ y ∈ t, g y := by
  simpa only [h2] using h1.iSup_comp g

section le

variable {ι : Type*} [PartialOrder ι] (f : ι → α) (i : ι)

@[to_dual (dont_translate := ι)]
theorem biSup_le_eq_sup : (⨆ j ≤ i, f j) = (⨆ j < i, f j) ⊔ f i := by
  rw [iSup_split_single _ i]
  -- Squeezed for a ~10x speedup, though it's still reasonably fast unsqueezed.
  simp only [le_refl, iSup_pos, iSup_and', lt_iff_le_and_ne, and_comm, sup_comm]

@[to_dual (dont_translate := ι)]
theorem biSup_ge_eq_sup : (⨆ j ≥ i, f j) = f i ⊔ (⨆ j > i, f j) := by
  rw [iSup_split_single _ i]
  -- Squeezed for a ~10x speedup, though it's still reasonably fast unsqueezed.
  simp only [ge_iff_le, le_refl, iSup_pos, ne_comm, iSup_and', gt_iff_lt, lt_iff_le_and_ne,
    and_comm]

end le

/-!
### `iSup` and `iInf` under `Type`
-/

@[to_dual iInf_of_isEmpty]
theorem iSup_of_empty' {α ι} [SupSet α] [IsEmpty ι] (f : ι → α) : iSup f = sSup (∅ : Set α) :=
  congr_arg sSup (range_eq_empty f)

@[to_dual]
theorem iSup_of_empty [IsEmpty ι] (f : ι → α) : iSup f = ⊥ :=
  (iSup_of_empty' f).trans sSup_empty

@[to_dual]
theorem isLUB_biSup {s : Set β} {f : β → α} : IsLUB (f '' s) (⨆ x ∈ s, f x) := by
  simpa only [range_comp, Subtype.range_coe, iSup_subtype'] using
    @isLUB_iSup α s _ (f ∘ fun x => (x : β))

@[to_dual]
theorem iSup_sigma {p : β → Type*} {f : Sigma p → α} : ⨆ x, f x = ⨆ (i) (j), f ⟨i, j⟩ :=
  eq_of_forall_ge_iff fun c => by simp only [iSup_le_iff, Sigma.forall]

@[to_dual]
lemma iSup_sigma' {κ : β → Type*} (f : ∀ i, κ i → α) :
    (⨆ i, ⨆ j, f i j) = ⨆ x : Σ i, κ i, f x.1 x.2 := (iSup_sigma (f := fun x ↦ f x.1 x.2)).symm

@[to_dual]
lemma iSup_psigma {ι : Sort*} {κ : ι → Sort*} (f : (Σ' i, κ i) → α) :
    ⨆ ij, f ij = ⨆ i, ⨆ j, f ⟨i, j⟩ :=
  eq_of_forall_ge_iff fun c ↦ by simp only [iSup_le_iff, PSigma.forall]

@[to_dual]
lemma iSup_psigma' {ι : Sort*} {κ : ι → Sort*} (f : ∀ i, κ i → α) :
    (⨆ i, ⨆ j, f i j) = ⨆ ij : Σ' i, κ i, f ij.1 ij.2 := (iSup_psigma fun x ↦ f x.1 x.2).symm

@[to_dual]
theorem iSup_prod {f : β × γ → α} : ⨆ x, f x = ⨆ (i) (j), f (i, j) :=
  eq_of_forall_ge_iff fun c => by simp only [iSup_le_iff, Prod.forall]

@[to_dual]
lemma iSup_prod' (f : β → γ → α) : (⨆ i, ⨆ j, f i j) = ⨆ x : β × γ, f x.1 x.2 :=
(iSup_prod (f := fun x ↦ f x.1 x.2)).symm

@[to_dual]
theorem biSup_prod {f : β × γ → α} {s : Set β} {t : Set γ} :
    ⨆ x ∈ s ×ˢ t, f x = ⨆ (a ∈ s) (b ∈ t), f (a, b) := by
  simp_rw [iSup_prod, mem_prod, iSup_and]
  exact iSup_congr fun _ => iSup_comm

@[to_dual]
theorem biSup_prod' {f : β → γ → α} {s : Set β} {t : Set γ} :
    ⨆ x ∈ s ×ˢ t, f x.1 x.2 = ⨆ (a ∈ s) (b ∈ t), f a b :=
  biSup_prod

@[to_dual]
theorem iSup_image2 {γ δ} (f : β → γ → δ) (s : Set β) (t : Set γ) (g : δ → α) :
    ⨆ d ∈ image2 f s t, g d = ⨆ b ∈ s, ⨆ c ∈ t, g (f b c) := by
  rw [← image_prod, iSup_image, biSup_prod]

@[to_dual]
theorem iSup_sum {f : β ⊕ γ → α} : ⨆ x, f x = (⨆ i, f (Sum.inl i)) ⊔ ⨆ j, f (Sum.inr j) :=
  eq_of_forall_ge_iff fun c => by simp only [sup_le_iff, iSup_le_iff, Sum.forall]

@[to_dual]
theorem iSup_option (f : Option β → α) : ⨆ o, f o = f none ⊔ ⨆ b, f (Option.some b) :=
  eq_of_forall_ge_iff fun c => by simp only [iSup_le_iff, sup_le_iff, Option.forall]

/-- A version of `iSup_option` useful for rewriting right-to-left. -/
@[to_dual /-- A version of `iInf_option` useful for rewriting right-to-left. -/]
theorem iSup_option_elim (a : α) (f : β → α) : ⨆ o : Option β, o.elim a f = a ⊔ ⨆ b, f b := by
  simp [iSup_option]

/-- When taking the supremum of `f : ι → α`, the elements of `ι` on which `f` gives `⊥` can be
dropped, without changing the result. -/
@[to_dual /-- When taking the infimum of `f : ι → α`, the elements of `ι` on which `f` gives `⊤`
can be dropped, without changing the result. -/, simp]
theorem iSup_ne_bot_subtype (f : ι → α) : ⨆ i : { i // f i ≠ ⊥ }, f i = ⨆ i, f i := by
  by_cases! htriv : ∀ i, f i = ⊥
  · simp only [iSup_bot, (funext htriv : f = _)]
  refine (iSup_comp_le f _).antisymm (iSup_mono' fun i => ?_)
  by_cases hi : f i = ⊥
  · rw [hi]
    obtain ⟨i₀, hi₀⟩ := htriv
    exact ⟨⟨i₀, hi₀⟩, bot_le⟩
  · exact ⟨⟨i, hi⟩, rfl.le⟩

@[to_dual]
theorem sSup_image2 {f : β → γ → α} {s : Set β} {t : Set γ} :
    sSup (image2 f s t) = ⨆ (a ∈ s) (b ∈ t), f a b := by rw [← image_prod, sSup_image, biSup_prod]

end

section CompleteLinearOrder

variable [CompleteLinearOrder α]

@[to_dual]
lemma iSup₂_eq_top (f : ∀ i, κ i → α) : ⨆ i, ⨆ j, f i j = ⊤ ↔ ∀ b < ⊤, ∃ i j, b < f i j := by
  simp_rw [iSup_psigma', iSup_eq_top, PSigma.exists]

end CompleteLinearOrder

/-!
### Instances
-/


instance Prop.instCompleteLattice : CompleteLattice Prop where
  __ := Prop.instBoundedOrder
  __ := Prop.instDistribLattice
  sSup s := ∃ a ∈ s, a
  isLUB_sSup _ := ⟨fun a h p ↦ ⟨a, h, p⟩, fun _ h ⟨_, h', p⟩ => h h' p⟩
  sInf s := ∀ a ∈ s, a
  isGLB_sInf _ := ⟨fun a h p ↦ p a h, fun _ h p _ hb ↦ h hb p⟩

noncomputable instance Prop.instCompleteLinearOrder : CompleteLinearOrder Prop where
  __ := Prop.instCompleteLattice
  __ := Prop.linearOrder
  __ := BooleanAlgebra.toBiheytingAlgebra

@[simp]
theorem sSup_Prop_eq {s : Set Prop} : sSup s = ∃ p ∈ s, p :=
  rfl

@[simp]
theorem sInf_Prop_eq {s : Set Prop} : sInf s = ∀ p ∈ s, p :=
  rfl

@[simp]
theorem iSup_Prop_eq {p : ι → Prop} : ⨆ i, p i = ∃ i, p i :=
  le_antisymm (fun ⟨_, ⟨i, (eq : p i = _)⟩, hq⟩ => ⟨i, eq.symm ▸ hq⟩) fun ⟨i, hi⟩ =>
    ⟨p i, ⟨i, rfl⟩, hi⟩

@[simp]
theorem iInf_Prop_eq {p : ι → Prop} : ⨅ i, p i = ∀ i, p i :=
  le_antisymm (fun h i => h _ ⟨i, rfl⟩) fun h _ ⟨i, Eq⟩ => Eq ▸ h i

@[to_dual]
instance Pi.supSet {α : Type*} {β : α → Type*} [∀ i, SupSet (β i)] : SupSet (∀ i, β i) :=
  ⟨fun s i => ⨆ f : s, (f : ∀ i, β i) i⟩

@[to_dual (attr := simp)]
theorem sSup_apply {α : Type*} {β : α → Type*} [∀ i, SupSet (β i)] {s : Set (∀ a, β a)} {a : α} :
    (sSup s) a = ⨆ f : s, (f : ∀ a, β a) a :=
  rfl

@[to_dual]
theorem sSup_apply_eq_sSup_image {α : Type*} {β : α → Type*} [∀ i, SupSet (β i)]
    {s : Set (∀ a, β a)} {a : α} :
    sSup s a = sSup (eval a '' s) := by
  simp [sSup_apply, iSup, image_eq_range]

instance Pi.instCompleteLattice {α : Type*} {β : α → Type*} [∀ i, CompleteLattice (β i)] :
    CompleteLattice (∀ i, β i) where
  __ := instBoundedOrder
  isLUB_sSup _ := isLUB_pi.mpr fun _ ↦ by rw [sSup_apply_eq_sSup_image]; exact isLUB_sSup _
  isGLB_sInf _ := isGLB_pi.mpr fun _ ↦ by rw [sInf_apply_eq_sInf_image]; exact isGLB_sInf _

@[to_dual (attr := simp)]
theorem iSup_apply {α : Type*} {β : α → Type*} {ι : Sort*} [∀ i, SupSet (β i)] {f : ι → ∀ a, β a}
    {a : α} : (⨆ i, f i) a = ⨆ i, f i a := by
  rw [iSup, sSup_apply, iSup, iSup, ← image_eq_range (fun f : ∀ i, β i => f a) (range f), ←
    range_comp]; rfl

theorem unary_relation_sSup_iff {α : Type*} (s : Set (α → Prop)) {a : α} :
    sSup s a ↔ ∃ r ∈ s, r a := by
  simp

theorem unary_relation_sInf_iff {α : Type*} (s : Set (α → Prop)) {a : α} :
    sInf s a ↔ ∀ r ∈ s, r a := by
  simp

theorem binary_relation_sSup_iff {α β : Type*} (s : Set (α → β → Prop)) {a : α} {b : β} :
    sSup s a b ↔ ∃ r ∈ s, r a b := by
  simp

theorem binary_relation_sInf_iff {α β : Type*} (s : Set (α → β → Prop)) {a : α} {b : β} :
    sInf s a b ↔ ∀ r ∈ s, r a b := by
  simp

section CompleteLattice

variable [Preorder α] [CompleteLattice β] {s : Set (α → β)} {f : ι → α → β}

@[to_dual]
protected lemma Monotone.sSup (hs : ∀ f ∈ s, Monotone f) : Monotone (sSup s) :=
  fun _ _ h ↦ iSup_mono fun f ↦ hs f f.2 h

@[to_dual]
protected lemma Antitone.sSup (hs : ∀ f ∈ s, Antitone f) : Antitone (sSup s) :=
  fun _ _ h ↦ iSup_mono fun f ↦ hs f f.2 h

@[to_dual]
protected lemma Monotone.iSup (hf : ∀ i, Monotone (f i)) : Monotone (⨆ i, f i) :=
  Monotone.sSup (by simpa)

@[to_dual]
protected lemma Antitone.iSup (hf : ∀ i, Antitone (f i)) : Antitone (⨆ i, f i) :=
  Antitone.sSup (by simpa)

end CompleteLattice

namespace Prod

variable (α β)

@[to_dual]
instance supSet [SupSet α] [SupSet β] : SupSet (α × β) :=
  ⟨fun s => (sSup (Prod.fst '' s), sSup (Prod.snd '' s))⟩

variable {α β}

@[to_dual]
theorem fst_sSup [SupSet α] [SupSet β] (s : Set (α × β)) : (sSup s).fst = sSup (Prod.fst '' s) :=
  rfl

@[to_dual]
theorem snd_sSup [SupSet α] [SupSet β] (s : Set (α × β)) : (sSup s).snd = sSup (Prod.snd '' s) :=
  rfl

@[to_dual]
theorem swap_sSup [SupSet α] [SupSet β] (s : Set (α × β)) : (sSup s).swap = sSup (Prod.swap '' s) :=
  Prod.ext (congr_arg sSup <| image_comp Prod.fst swap s)
    (congr_arg sSup <| image_comp Prod.snd swap s)

@[to_dual]
theorem fst_iSup [SupSet α] [SupSet β] (f : ι → α × β) : (iSup f).fst = ⨆ i, (f i).fst :=
  congr_arg sSup (range_comp _ _).symm

@[to_dual]
theorem snd_iSup [SupSet α] [SupSet β] (f : ι → α × β) : (iSup f).snd = ⨆ i, (f i).snd :=
  congr_arg sSup (range_comp _ _).symm

@[to_dual]
theorem swap_iSup [SupSet α] [SupSet β] (f : ι → α × β) : (iSup f).swap = ⨆ i, (f i).swap := by
  simp_rw [iSup, swap_sSup, ← range_comp, comp_def]

@[to_dual]
theorem iSup_mk [SupSet α] [SupSet β] (f : ι → α) (g : ι → β) :
    ⨆ i, (f i, g i) = (⨆ i, f i, ⨆ i, g i) :=
  congr_arg₂ Prod.mk (fst_iSup _) (snd_iSup _)

instance instCompleteLattice [CompleteLattice α] [CompleteLattice β] : CompleteLattice (α × β) where
  __ := instBoundedOrder α β
  isLUB_sSup _ := isLUB_prod.mpr ⟨isLUB_sSup _, isLUB_sSup _⟩
  isGLB_sInf _ := isGLB_prod.mpr ⟨isGLB_sInf _, isGLB_sInf _⟩

end Prod

@[to_dual]
lemma sSup_prod [SupSet α] [SupSet β] {s : Set α} {t : Set β} (hs : s.Nonempty) (ht : t.Nonempty) :
    sSup (s ×ˢ t) = (sSup s, sSup t) :=
congr_arg₂ Prod.mk (congr_arg sSup <| fst_image_prod _ ht) (congr_arg sSup <| snd_image_prod hs _)

-- See note [reducible non-instances]
/-- Pullback a `CompleteLattice` along an injection. -/
protected abbrev Function.Injective.completeLattice [Max α] [Min α] [LE α] [LT α]
    [SupSet α] [InfSet α] [Top α] [Bot α] [CompleteLattice β]
    (f : α → β) (hf : Function.Injective f)
    (le : ∀ {x y}, f x ≤ f y ↔ x ≤ y) (lt : ∀ {x y}, f x < f y ↔ x < y)
    (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b)
    (map_sSup : ∀ s, f (sSup s) = ⨆ a ∈ s, f a) (map_sInf : ∀ s, f (sInf s) = ⨅ a ∈ s, f a)
    (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥) : CompleteLattice α where
  __ := hf.lattice f le lt map_sup map_inf
  __ := BoundedOrder.lift f (fun _ _ ↦ le.1) map_top map_bot
  isLUB_sSup _ := .of_image le (by rw [map_sSup]; exact isLUB_biSup)
  isGLB_sInf _ := .of_image le (by rw [map_sInf]; exact isGLB_biInf)

namespace Equiv

variable (e : α ≃ β)

/-- Transfer `CompleteLattice` across an `Equiv`. -/
protected abbrev completeLattice [CompleteLattice β] : CompleteLattice α := by
  let top := e.top
  let bot := e.bot
  let supSet := e.supSet
  let infSet := e.infSet
  let lattice := e.lattice
  apply e.injective.completeLattice <;> intros <;> first | rfl | exact e.apply_symm_apply _

end Equiv
