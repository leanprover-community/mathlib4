/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Data.Set.Pairwise.Basic
import Mathlib.Data.SetLike.Basic
import Mathlib.Order.Directed
import Mathlib.Order.Hom.Set

/-!
# Chains and flags

This file defines chains for an arbitrary relation and flags for an order.

## Main declarations

* `IsChain s`: A chain `s` is a set of comparable elements.
* `Flag`: The type of flags, aka maximal chains, of an order.

## Notes

Originally ported from Isabelle/HOL. The
[original file](https://isabelle.in.tum.de/dist/library/HOL/HOL/Zorn.html) was written by Jacques D.
Fleuriot, Tobias Nipkow, Christian Sternagel.
-/

assert_not_exists CompleteLattice

open Set

variable {α β : Type*}

/-! ### Chains -/


section Chain

variable (r : α → α → Prop)

/-- In this file, we use `≺` as a local notation for any relation `r`. -/
local infixl:50 " ≺ " => r

/-- A chain is a set `s` satisfying `x ≺ y ∨ x = y ∨ y ≺ x` for all `x y ∈ s`. -/
def IsChain (s : Set α) : Prop :=
  s.Pairwise fun x y => x ≺ y ∨ y ≺ x

/-- `SuperChain s t` means that `t` is a chain that strictly includes `s`. -/
def SuperChain (s t : Set α) : Prop :=
  IsChain r t ∧ s ⊂ t

/-- A chain `s` is a maximal chain if there does not exists a chain strictly including `s`. -/
def IsMaxChain (s : Set α) : Prop :=
  IsChain r s ∧ ∀ ⦃t⦄, IsChain r t → s ⊆ t → s = t

variable {r} {c c₁ c₂ s t : Set α} {a b x y : α}

@[simp] lemma IsChain.empty : IsChain r ∅ := pairwise_empty _
@[simp] lemma IsChain.singleton : IsChain r {a} := pairwise_singleton ..

@[deprecated (since := "2024-11-25")] alias isChain_empty := IsChain.empty

theorem Set.Subsingleton.isChain (hs : s.Subsingleton) : IsChain r s :=
  hs.pairwise _

theorem IsChain.mono : s ⊆ t → IsChain r t → IsChain r s :=
  Set.Pairwise.mono

theorem IsChain.mono_rel {r' : α → α → Prop} (h : IsChain r s) (h_imp : ∀ x y, r x y → r' x y) :
    IsChain r' s :=
  h.mono' fun x y => Or.imp (h_imp x y) (h_imp y x)

/-- This can be used to turn `IsChain (≥)` into `IsChain (≤)` and vice-versa. -/
theorem IsChain.symm (h : IsChain r s) : IsChain (flip r) s :=
  h.mono' fun _ _ => Or.symm

theorem isChain_of_trichotomous [IsTrichotomous α r] (s : Set α) : IsChain r s :=
  fun a _ b _ hab => (trichotomous_of r a b).imp_right fun h => h.resolve_left hab

protected theorem IsChain.insert (hs : IsChain r s) (ha : ∀ b ∈ s, a ≠ b → a ≺ b ∨ b ≺ a) :
    IsChain r (insert a s) :=
  hs.insert_of_symmetric (fun _ _ => Or.symm) ha

lemma IsChain.pair (h : r a b) : IsChain r {a, b} :=
  IsChain.singleton.insert fun _ hb _ ↦ .inl <| (eq_of_mem_singleton hb).symm.recOn ‹_›

theorem isChain_univ_iff : IsChain r (univ : Set α) ↔ IsTrichotomous α r := by
  refine ⟨fun h => ⟨fun a b => ?_⟩, fun h => @isChain_of_trichotomous _ _ h univ⟩
  rw [or_left_comm, or_iff_not_imp_left]
  exact h trivial trivial

theorem IsChain.image (r : α → α → Prop) (s : β → β → Prop) (f : α → β)
    (h : ∀ x y, r x y → s (f x) (f y)) {c : Set α} (hrc : IsChain r c) : IsChain s (f '' c) :=
  fun _ ⟨_, ha₁, ha₂⟩ _ ⟨_, hb₁, hb₂⟩ =>
  ha₂ ▸ hb₂ ▸ fun hxy => (hrc ha₁ hb₁ <| ne_of_apply_ne f hxy).imp (h _ _) (h _ _)

lemma isChain_union {s t : Set α} :
    IsChain r (s ∪ t) ↔ IsChain r s ∧ IsChain r t ∧ ∀ a ∈ s, ∀ b ∈ t, a ≠ b → r a b ∨ r b a := by
  rw [IsChain, IsChain, IsChain, pairwise_union_of_symmetric fun _ _ ↦ Or.symm]

lemma Monotone.isChain_image [Preorder α] [Preorder β] {s : Set α} {f : α → β}
    (hf : Monotone f) (hs : IsChain (· ≤ ·) s) : IsChain (· ≤ ·) (f '' s) :=
  hs.image _ _ _ (fun _ _ a ↦ hf a)

theorem Monotone.isChain_range [LinearOrder α] [Preorder β] {f : α → β} (hf : Monotone f) :
    IsChain (· ≤ ·) (range f) := by
  rw [← image_univ]
  exact hf.isChain_image (isChain_of_trichotomous _)

theorem IsChain.lt_of_le [PartialOrder α] {s : Set α} (h : IsChain (· ≤ ·) s) :
    IsChain (· < ·) s := fun _a ha _b hb hne ↦
  (h ha hb hne).imp hne.lt_of_le hne.lt_of_le'

section Total

variable [IsRefl α r]

theorem IsChain.total (h : IsChain r s) (hx : x ∈ s) (hy : y ∈ s) : x ≺ y ∨ y ≺ x :=
  (eq_or_ne x y).elim (fun e => Or.inl <| e ▸ refl _) (h hx hy)

theorem IsChain.directedOn (H : IsChain r s) : DirectedOn r s := fun x hx y hy =>
  ((H.total hx hy).elim fun h => ⟨y, hy, h, refl _⟩) fun h => ⟨x, hx, refl _, h⟩

protected theorem IsChain.directed {f : β → α} {c : Set β} (h : IsChain (f ⁻¹'o r) c) :
    Directed r fun x : { a : β // a ∈ c } => f x :=
  fun ⟨a, ha⟩ ⟨b, hb⟩ =>
    (by_cases fun hab : a = b => by
      simp only [hab, exists_prop, and_self_iff, Subtype.exists]
      exact ⟨b, hb, refl _⟩)
    fun hab => ((h ha hb hab).elim fun h => ⟨⟨b, hb⟩, h, refl _⟩) fun h => ⟨⟨a, ha⟩, refl _, h⟩

theorem IsChain.exists3 (hchain : IsChain r s) [IsTrans α r] {a b c} (mem1 : a ∈ s) (mem2 : b ∈ s)
    (mem3 : c ∈ s) : ∃ (z : _) (_ : z ∈ s), r a z ∧ r b z ∧ r c z := by
  rcases directedOn_iff_directed.mpr (IsChain.directed hchain) a mem1 b mem2 with ⟨z, mem4, H1, H2⟩
  rcases directedOn_iff_directed.mpr (IsChain.directed hchain) z mem4 c mem3 with
    ⟨z', mem5, H3, H4⟩
  exact ⟨z', mem5, _root_.trans H1 H3, _root_.trans H2 H3, H4⟩

end Total

lemma IsChain.le_of_not_gt [Preorder α] (hs : IsChain (· ≤ ·) s)
    {x y : α} (hx : x ∈ s) (hy : y ∈ s) (h : ¬ x < y) : y ≤ x := by
  cases hs.total hx hy with
  | inr h' => exact h'
  | inl h' => simpa [lt_iff_le_not_ge, h'] using h

@[deprecated (since := "2025-05-11")] alias IsChain.le_of_not_lt := IsChain.le_of_not_gt

lemma IsChain.not_lt [Preorder α] (hs : IsChain (· ≤ ·) s)
    {x y : α} (hx : x ∈ s) (hy : y ∈ s) : ¬ x < y ↔ y ≤ x :=
  ⟨(hs.le_of_not_gt hx hy ·), fun h h' ↦ h'.not_ge h⟩

lemma IsChain.lt_of_not_ge [Preorder α] (hs : IsChain (· ≤ ·) s)
    {x y : α} (hx : x ∈ s) (hy : y ∈ s) (h : ¬ x ≤ y) : y < x :=
  (hs.total hx hy).elim (h · |>.elim) (lt_of_le_not_ge · h)

@[deprecated (since := "2025-05-11")] alias IsChain.lt_of_not_le := IsChain.lt_of_not_ge

lemma IsChain.not_le [Preorder α] (hs : IsChain (· ≤ ·) s)
    {x y : α} (hx : x ∈ s) (hy : y ∈ s) : ¬ x ≤ y ↔ y < x :=
  ⟨(hs.lt_of_not_ge hx hy ·), fun h h' ↦ h'.not_gt h⟩

theorem IsMaxChain.isChain (h : IsMaxChain r s) : IsChain r s :=
  h.1

theorem IsMaxChain.not_superChain (h : IsMaxChain r s) : ¬SuperChain r s t := fun ht =>
  ht.2.ne <| h.2 ht.1 ht.2.1

theorem IsMaxChain.bot_mem [LE α] [OrderBot α] (h : IsMaxChain (· ≤ ·) s) : ⊥ ∈ s :=
  (h.2 (h.1.insert fun _ _ _ => Or.inl bot_le) <| subset_insert _ _).symm ▸ mem_insert _ _

theorem IsMaxChain.top_mem [LE α] [OrderTop α] (h : IsMaxChain (· ≤ ·) s) : ⊤ ∈ s :=
  (h.2 (h.1.insert fun _ _ _ => Or.inr le_top) <| subset_insert _ _).symm ▸ mem_insert _ _

lemma IsMaxChain.image {s : β → β → Prop} (e : r ≃r s) {c : Set α} (hc : IsMaxChain r c) :
    IsMaxChain s (e '' c) where
  left := hc.isChain.image _ _ _ fun _ _ ↦ by exact e.map_rel_iff.2
  right t ht hf := by
    rw [← e.coe_fn_toEquiv, ← e.toEquiv.eq_preimage_iff_image_eq, preimage_equiv_eq_image_symm]
    exact hc.2 (ht.image _ _ _ fun _ _ ↦ by exact e.symm.map_rel_iff.2)
      ((e.toEquiv.subset_symm_image _ _).2 hf)

open Classical in
/-- Given a set `s`, if there exists a chain `t` strictly including `s`, then `SuccChain s`
is one of these chains. Otherwise it is `s`. -/
def SuccChain (r : α → α → Prop) (s : Set α) : Set α :=
  if h : ∃ t, IsChain r s ∧ SuperChain r s t then h.choose else s

theorem succChain_spec (h : ∃ t, IsChain r s ∧ SuperChain r s t) :
    SuperChain r s (SuccChain r s) := by
  have : IsChain r s ∧ SuperChain r s h.choose := h.choose_spec
  simpa [SuccChain, dif_pos, exists_and_left.mp h] using this.2

open Classical in
theorem IsChain.succ (hs : IsChain r s) : IsChain r (SuccChain r s) :=
  if h : ∃ t, IsChain r s ∧ SuperChain r s t then (succChain_spec h).1
  else by
    rw [exists_and_left] at h
    simpa [SuccChain, dif_neg, h] using hs

theorem IsChain.superChain_succChain (hs₁ : IsChain r s) (hs₂ : ¬IsMaxChain r s) :
    SuperChain r s (SuccChain r s) := by
  simp only [IsMaxChain, _root_.not_and, not_forall, exists_prop, exists_and_left] at hs₂
  obtain ⟨t, ht, hst⟩ := hs₂ hs₁
  exact succChain_spec ⟨t, hs₁, ht, ssubset_iff_subset_ne.2 hst⟩

open Classical in
theorem subset_succChain : s ⊆ SuccChain r s :=
  if h : ∃ t, IsChain r s ∧ SuperChain r s t then (succChain_spec h).2.1
  else by
    rw [exists_and_left] at h
    simp [SuccChain, dif_neg, h, Subset.rfl]

end Chain

/-! ### Flags -/


/-- The type of flags, aka maximal chains, of an order. -/
structure Flag (α : Type*) [LE α] where
  /-- The `carrier` of a flag is the underlying set. -/
  carrier : Set α
  /-- By definition, a flag is a chain -/
  Chain' : IsChain (· ≤ ·) carrier
  /-- By definition, a flag is a maximal chain -/
  max_chain' : ∀ ⦃s⦄, IsChain (· ≤ ·) s → carrier ⊆ s → carrier = s

namespace Flag

section LE

variable [LE α] {s t : Flag α} {a : α}

instance : SetLike (Flag α) α where
  coe := carrier
  coe_injective' s t h := by
    cases s
    cases t
    congr

@[ext]
theorem ext : (s : Set α) = t → s = t :=
  SetLike.ext'

theorem mem_coe_iff : a ∈ (s : Set α) ↔ a ∈ s :=
  Iff.rfl

@[simp]
theorem coe_mk (s : Set α) (h₁ h₂) : (mk s h₁ h₂ : Set α) = s :=
  rfl

@[simp]
theorem mk_coe (s : Flag α) : mk (s : Set α) s.Chain' s.max_chain' = s :=
  ext rfl

theorem chain_le (s : Flag α) : IsChain (· ≤ ·) (s : Set α) :=
  s.Chain'

protected theorem maxChain (s : Flag α) : IsMaxChain (· ≤ ·) (s : Set α) :=
  ⟨s.chain_le, s.max_chain'⟩

theorem top_mem [OrderTop α] (s : Flag α) : (⊤ : α) ∈ s :=
  s.maxChain.top_mem

theorem bot_mem [OrderBot α] (s : Flag α) : (⊥ : α) ∈ s :=
  s.maxChain.bot_mem

/-- Reinterpret a maximal chain as a flag. -/
def ofIsMaxChain (c : Set α) (hc : IsMaxChain (· ≤ ·) c) : Flag α := ⟨c, hc.isChain, hc.2⟩

@[simp, norm_cast]
lemma coe_ofIsMaxChain (c : Set α) (hc) : ofIsMaxChain c hc = c := rfl

end LE

section Preorder

variable [Preorder α] [Preorder β] {a b : α} {s : Flag α}

protected theorem le_or_le (s : Flag α) (ha : a ∈ s) (hb : b ∈ s) : a ≤ b ∨ b ≤ a :=
  s.chain_le.total ha hb

instance [OrderTop α] (s : Flag α) : OrderTop s :=
  Subtype.orderTop s.top_mem

instance [OrderBot α] (s : Flag α) : OrderBot s :=
  Subtype.orderBot s.bot_mem

instance [BoundedOrder α] (s : Flag α) : BoundedOrder s :=
  Subtype.boundedOrder s.bot_mem s.top_mem

lemma mem_iff_forall_le_or_ge : a ∈ s ↔ ∀ ⦃b⦄, b ∈ s → a ≤ b ∨ b ≤ a :=
  ⟨fun ha b => s.le_or_le ha, fun hb =>
    of_not_not fun ha =>
      Set.ne_insert_of_notMem _ ‹_› <|
        s.maxChain.2 (s.chain_le.insert fun c hc _ => hb hc) <| Set.subset_insert _ _⟩

/-- Flags are preserved under order isomorphisms. -/
def map (e : α ≃o β) : Flag α ≃ Flag β where
  toFun s := ofIsMaxChain _ (s.maxChain.image e)
  invFun s := ofIsMaxChain _ (s.maxChain.image e.symm)
  left_inv s := ext <| e.symm_image_image s
  right_inv s := ext <| e.image_symm_image s

@[simp, norm_cast] lemma coe_map (e : α ≃o β) (s : Flag α) : ↑(map e s) = e '' s := rfl

@[simp] lemma symm_map (e : α ≃o β) : (map e).symm = map e.symm := rfl

end Preorder

section PartialOrder

variable [PartialOrder α]

theorem chain_lt (s : Flag α) : IsChain (· < ·) (s : Set α) := s.chain_le.lt_of_le

instance [DecidableLE α] [DecidableLT α] [DecidableEq α] (s : Flag α) : LinearOrder s :=
  { Subtype.partialOrder _ with
    le_total := fun a b => s.le_or_le a.2 b.2
    toDecidableLE := Subtype.decidableLE
    toDecidableLT := Subtype.decidableLT
    toDecidableEq := Subtype.instDecidableEq }

end PartialOrder

instance [LinearOrder α] : Unique (Flag α) where
  default := ⟨univ, isChain_of_trichotomous _, fun s _ => s.subset_univ.antisymm'⟩
  uniq s := SetLike.coe_injective <| s.3 (isChain_of_trichotomous _) <| subset_univ _

end Flag
