/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Data.Set.NAry
import Mathlib.Data.ULift
import Mathlib.Order.CompleteLattice.Defs
import Mathlib.Order.Hom.Set

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

open Function OrderDual Set

variable {α β γ : Type*} {ι ι' : Sort*} {κ : ι → Sort*} {κ' : ι' → Sort*}

@[simp] lemma iSup_ulift {ι : Type*} [SupSet α] (f : ULift ι → α) :
    ⨆ i : ULift ι, f i = ⨆ i, f (.up i) := by simp [iSup]; congr with x; simp

@[simp] lemma iInf_ulift {ι : Type*} [InfSet α] (f : ULift ι → α) :
    ⨅ i : ULift ι, f i = ⨅ i, f (.up i) := by simp [iInf]; congr with x; simp

section

variable [CompleteSemilatticeSup α] {s t : Set α} {a b : α}

theorem sSup_le_sSup_of_isCofinalFor (h : IsCofinalFor s t) : sSup s ≤ sSup t :=
  IsLeast.mono (isLUB_sSup t) (isLUB_sSup s) <| upperBounds_mono_of_isCofinalFor h

@[deprecated "use `sSup_le_sSup_of_isCofinalFor` instead" (since := "2025-07-14")]
theorem sSup_le_sSup_of_forall_exists_le (h : ∀ x ∈ s, ∃ y ∈ t, x ≤ y) : sSup s ≤ sSup t :=
  sSup_le_sSup_of_isCofinalFor h

-- We will generalize this to conditionally complete lattices in `csSup_singleton`.
@[simp]
theorem sSup_singleton {a : α} : sSup {a} = a :=
  isLUB_singleton.sSup_eq

end

section

variable [CompleteSemilatticeInf α] {s t : Set α} {a b : α}

theorem sInf_le_sInf_of_isCoinitialFor (h : IsCoinitialFor s t) : sInf t ≤ sInf s :=
  IsGreatest.mono (isGLB_sInf t) (isGLB_sInf s) <| lowerBounds_mono_of_isCoinitialFor h

@[deprecated "use `sInf_le_sInf_of_isCoinitialFor` instead" (since := "2025-07-14")]
theorem sInf_le_sInf_of_forall_exists_le (h : ∀ x ∈ s, ∃ y ∈ t, y ≤ x) : sInf t ≤ sInf s :=
  sInf_le_sInf_of_isCoinitialFor h

-- We will generalize this to conditionally complete lattices in `csInf_singleton`.
@[simp]
theorem sInf_singleton {a : α} : sInf {a} = a :=
  isGLB_singleton.sInf_eq

end

open OrderDual

section

variable [CompleteLattice α] {s t : Set α} {b : α}

theorem sInf_le_sSup (hs : s.Nonempty) : sInf s ≤ sSup s :=
  isGLB_le_isLUB (isGLB_sInf s) (isLUB_sSup s) hs

theorem sSup_union {s t : Set α} : sSup (s ∪ t) = sSup s ⊔ sSup t :=
  ((isLUB_sSup s).union (isLUB_sSup t)).sSup_eq

theorem sInf_union {s t : Set α} : sInf (s ∪ t) = sInf s ⊓ sInf t :=
  ((isGLB_sInf s).union (isGLB_sInf t)).sInf_eq

theorem sSup_inter_le {s t : Set α} : sSup (s ∩ t) ≤ sSup s ⊓ sSup t :=
  sSup_le fun _ hb => le_inf (le_sSup hb.1) (le_sSup hb.2)

theorem le_sInf_inter {s t : Set α} : sInf s ⊔ sInf t ≤ sInf (s ∩ t) :=
  @sSup_inter_le αᵒᵈ _ _ _

@[simp]
theorem sSup_empty : sSup ∅ = (⊥ : α) :=
  (@isLUB_empty α _ _).sSup_eq

@[simp]
theorem sInf_empty : sInf ∅ = (⊤ : α) :=
  (@isGLB_empty α _ _).sInf_eq

@[simp]
theorem sSup_univ : sSup univ = (⊤ : α) :=
  (@isLUB_univ α _ _).sSup_eq

@[simp]
theorem sInf_univ : sInf univ = (⊥ : α) :=
  (@isGLB_univ α _ _).sInf_eq

-- TODO(Jeremy): get this automatically
@[simp]
theorem sSup_insert {a : α} {s : Set α} : sSup (insert a s) = a ⊔ sSup s :=
  ((isLUB_sSup s).insert a).sSup_eq

@[simp]
theorem sInf_insert {a : α} {s : Set α} : sInf (insert a s) = a ⊓ sInf s :=
  ((isGLB_sInf s).insert a).sInf_eq

theorem sSup_le_sSup_of_subset_insert_bot (h : s ⊆ insert ⊥ t) : sSup s ≤ sSup t :=
  (sSup_le_sSup h).trans_eq (sSup_insert.trans (bot_sup_eq _))

theorem sInf_le_sInf_of_subset_insert_top (h : s ⊆ insert ⊤ t) : sInf t ≤ sInf s :=
  (sInf_le_sInf h).trans_eq' (sInf_insert.trans (top_inf_eq _)).symm

@[simp]
theorem sSup_diff_singleton_bot (s : Set α) : sSup (s \ {⊥}) = sSup s :=
  (sSup_le_sSup diff_subset).antisymm <|
    sSup_le_sSup_of_subset_insert_bot <| subset_insert_diff_singleton _ _

@[simp]
theorem sInf_diff_singleton_top (s : Set α) : sInf (s \ {⊤}) = sInf s :=
  @sSup_diff_singleton_bot αᵒᵈ _ s

theorem sSup_pair {a b : α} : sSup {a, b} = a ⊔ b :=
  (@isLUB_pair α _ a b).sSup_eq

theorem sInf_pair {a b : α} : sInf {a, b} = a ⊓ b :=
  (@isGLB_pair α _ a b).sInf_eq

@[simp]
theorem sSup_eq_bot : sSup s = ⊥ ↔ ∀ a ∈ s, a = ⊥ :=
  ⟨fun h _ ha => bot_unique <| h ▸ le_sSup ha, fun h =>
    bot_unique <| sSup_le fun a ha => le_bot_iff.2 <| h a ha⟩

@[simp]
theorem sInf_eq_top : sInf s = ⊤ ↔ ∀ a ∈ s, a = ⊤ :=
  @sSup_eq_bot αᵒᵈ _ _

lemma sSup_eq_bot' {s : Set α} : sSup s = ⊥ ↔ s = ∅ ∨ s = {⊥} := by
  rw [sSup_eq_bot, ← subset_singleton_iff_eq, subset_singleton_iff]

theorem eq_singleton_bot_of_sSup_eq_bot_of_nonempty {s : Set α} (h_sup : sSup s = ⊥)
    (hne : s.Nonempty) : s = {⊥} := by
  rw [Set.eq_singleton_iff_nonempty_unique_mem]
  rw [sSup_eq_bot] at h_sup
  exact ⟨hne, h_sup⟩

theorem eq_singleton_top_of_sInf_eq_top_of_nonempty : sInf s = ⊤ → s.Nonempty → s = {⊤} :=
  @eq_singleton_bot_of_sSup_eq_bot_of_nonempty αᵒᵈ _ _

/-- Introduction rule to prove that `b` is the supremum of `s`: it suffices to check that `b`
is larger than all elements of `s`, and that this is not the case of any `w < b`.
See `csSup_eq_of_forall_le_of_forall_lt_exists_gt` for a version in conditionally complete
lattices. -/
theorem sSup_eq_of_forall_le_of_forall_lt_exists_gt (h₁ : ∀ a ∈ s, a ≤ b)
    (h₂ : ∀ w, w < b → ∃ a ∈ s, w < a) : sSup s = b :=
  (sSup_le h₁).eq_of_not_lt fun h =>
    let ⟨_, ha, ha'⟩ := h₂ _ h
    ((le_sSup ha).trans_lt ha').false

/-- Introduction rule to prove that `b` is the infimum of `s`: it suffices to check that `b`
is smaller than all elements of `s`, and that this is not the case of any `w > b`.
See `csInf_eq_of_forall_ge_of_forall_gt_exists_lt` for a version in conditionally complete
lattices. -/
theorem sInf_eq_of_forall_ge_of_forall_gt_exists_lt :
    (∀ a ∈ s, b ≤ a) → (∀ w, b < w → ∃ a ∈ s, a < w) → sInf s = b :=
  @sSup_eq_of_forall_le_of_forall_lt_exists_gt αᵒᵈ _ _ _

end

/-
### iSup & iInf
-/
section SupSet

variable [SupSet α] {f g : ι → α}

theorem sSup_range : sSup (range f) = iSup f :=
  rfl

theorem sSup_eq_iSup' (s : Set α) : sSup s = ⨆ a : s, (a : α) := by rw [iSup, Subtype.range_coe]

theorem iSup_congr (h : ∀ i, f i = g i) : ⨆ i, f i = ⨆ i, g i :=
  congr_arg _ <| funext h

theorem biSup_congr {p : ι → Prop} (h : ∀ i, p i → f i = g i) :
    ⨆ (i) (_ : p i), f i = ⨆ (i) (_ : p i), g i :=
  iSup_congr fun i ↦ iSup_congr (h i)

theorem biSup_congr' {p : ι → Prop} {f g : (i : ι) → p i → α}
    (h : ∀ i (hi : p i), f i hi = g i hi) :
    ⨆ i, ⨆ (hi : p i), f i hi = ⨆ i, ⨆ (hi : p i), g i hi := by
  grind

theorem Function.Surjective.iSup_comp {f : ι → ι'} (hf : Surjective f) (g : ι' → α) :
    ⨆ x, g (f x) = ⨆ y, g y := by
  simp only [iSup.eq_1]
  congr
  exact hf.range_comp g

theorem Equiv.iSup_comp {g : ι' → α} (e : ι ≃ ι') : ⨆ x, g (e x) = ⨆ y, g y :=
  e.surjective.iSup_comp _

protected theorem Function.Surjective.iSup_congr {g : ι' → α} (h : ι → ι') (h1 : Surjective h)
    (h2 : ∀ x, g (h x) = f x) : ⨆ x, f x = ⨆ y, g y := by
  convert h1.iSup_comp g
  exact (h2 _).symm

protected theorem Equiv.iSup_congr {g : ι' → α} (e : ι ≃ ι') (h : ∀ x, g (e x) = f x) :
    ⨆ x, f x = ⨆ y, g y :=
  e.surjective.iSup_congr _ h

@[congr]
theorem iSup_congr_Prop {p q : Prop} {f₁ : p → α} {f₂ : q → α} (pq : p ↔ q)
    (f : ∀ x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂ := by
  obtain rfl := propext pq
  congr with x
  apply f

theorem iSup_plift_up (f : PLift ι → α) : ⨆ i, f (PLift.up i) = ⨆ i, f i :=
  (PLift.up_surjective.iSup_congr _) fun _ => rfl

theorem iSup_plift_down (f : ι → α) : ⨆ i, f (PLift.down i) = ⨆ i, f i :=
  (PLift.down_surjective.iSup_congr _) fun _ => rfl

theorem iSup_range' (g : β → α) (f : ι → β) : ⨆ b : range f, g b = ⨆ i, g (f i) := by
  rw [iSup, iSup, ← image_eq_range, ← range_comp']

theorem sSup_image' {s : Set β} {f : β → α} : sSup (f '' s) = ⨆ a : s, f a := by
  rw [iSup, image_eq_range]

end SupSet

section InfSet

variable [InfSet α] {f g : ι → α}

theorem sInf_range : sInf (range f) = iInf f :=
  rfl

theorem sInf_eq_iInf' (s : Set α) : sInf s = ⨅ a : s, (a : α) :=
  @sSup_eq_iSup' αᵒᵈ _ _

theorem iInf_congr (h : ∀ i, f i = g i) : ⨅ i, f i = ⨅ i, g i :=
  congr_arg _ <| funext h

theorem biInf_congr {p : ι → Prop} (h : ∀ i, p i → f i = g i) :
    ⨅ (i) (_ : p i), f i = ⨅ (i) (_ : p i), g i :=
  biSup_congr (α := αᵒᵈ) h

theorem biInf_congr' {p : ι → Prop} {f g : (i : ι) → p i → α}
    (h : ∀ i (hi : p i), f i hi = g i hi) :
    ⨅ i, ⨅ (hi : p i), f i hi = ⨅ i, ⨅ (hi : p i), g i hi := by
  grind

theorem Function.Surjective.iInf_comp {f : ι → ι'} (hf : Surjective f) (g : ι' → α) :
    ⨅ x, g (f x) = ⨅ y, g y :=
  @Function.Surjective.iSup_comp αᵒᵈ _ _ _ f hf g

theorem Equiv.iInf_comp {g : ι' → α} (e : ι ≃ ι') : ⨅ x, g (e x) = ⨅ y, g y :=
  @Equiv.iSup_comp αᵒᵈ _ _ _ _ e

protected theorem Function.Surjective.iInf_congr {g : ι' → α} (h : ι → ι') (h1 : Surjective h)
    (h2 : ∀ x, g (h x) = f x) : ⨅ x, f x = ⨅ y, g y :=
  @Function.Surjective.iSup_congr αᵒᵈ _ _ _ _ _ h h1 h2

protected theorem Equiv.iInf_congr {g : ι' → α} (e : ι ≃ ι') (h : ∀ x, g (e x) = f x) :
    ⨅ x, f x = ⨅ y, g y :=
  @Equiv.iSup_congr αᵒᵈ _ _ _ _ _ e h

@[congr]
theorem iInf_congr_Prop {p q : Prop} {f₁ : p → α} {f₂ : q → α} (pq : p ↔ q)
    (f : ∀ x, f₁ (pq.mpr x) = f₂ x) : iInf f₁ = iInf f₂ :=
  @iSup_congr_Prop αᵒᵈ _ p q f₁ f₂ pq f

theorem iInf_plift_up (f : PLift ι → α) : ⨅ i, f (PLift.up i) = ⨅ i, f i :=
  (PLift.up_surjective.iInf_congr _) fun _ => rfl

theorem iInf_plift_down (f : ι → α) : ⨅ i, f (PLift.down i) = ⨅ i, f i :=
  (PLift.down_surjective.iInf_congr _) fun _ => rfl

theorem iInf_range' (g : β → α) (f : ι → β) : ⨅ b : range f, g b = ⨅ i, g (f i) :=
  @iSup_range' αᵒᵈ _ _ _ _ _

theorem sInf_image' {s : Set β} {f : β → α} : sInf (f '' s) = ⨅ a : s, f a :=
  @sSup_image' αᵒᵈ _ _ _ _

end InfSet

section

variable [CompleteLattice α] {f g s : ι → α} {a b : α}

theorem le_iSup (f : ι → α) (i : ι) : f i ≤ iSup f :=
  le_sSup ⟨i, rfl⟩

theorem iInf_le (f : ι → α) (i : ι) : iInf f ≤ f i :=
  sInf_le ⟨i, rfl⟩

lemma iInf_le_iSup [Nonempty ι] : ⨅ i, f i ≤ ⨆ i, f i :=
  (iInf_le _ (Classical.arbitrary _)).trans <| le_iSup _ (Classical.arbitrary _)

theorem isLUB_iSup : IsLUB (range f) (⨆ j, f j) :=
  isLUB_sSup _

theorem isGLB_iInf : IsGLB (range f) (⨅ j, f j) :=
  isGLB_sInf _

theorem IsLUB.iSup_eq (h : IsLUB (range f) a) : ⨆ j, f j = a :=
  h.sSup_eq

theorem IsGLB.iInf_eq (h : IsGLB (range f) a) : ⨅ j, f j = a :=
  h.sInf_eq

theorem le_iSup_of_le (i : ι) (h : a ≤ f i) : a ≤ iSup f :=
  h.trans <| le_iSup _ i

theorem iInf_le_of_le (i : ι) (h : f i ≤ a) : iInf f ≤ a :=
  (iInf_le _ i).trans h

theorem le_iSup₂ {f : ∀ i, κ i → α} (i : ι) (j : κ i) : f i j ≤ ⨆ (i) (j), f i j :=
  le_iSup_of_le i <| le_iSup (f i) j

theorem iInf₂_le {f : ∀ i, κ i → α} (i : ι) (j : κ i) : ⨅ (i) (j), f i j ≤ f i j :=
  iInf_le_of_le i <| iInf_le (f i) j

theorem le_iSup₂_of_le {f : ∀ i, κ i → α} (i : ι) (j : κ i) (h : a ≤ f i j) :
    a ≤ ⨆ (i) (j), f i j :=
  h.trans <| le_iSup₂ i j

theorem iInf₂_le_of_le {f : ∀ i, κ i → α} (i : ι) (j : κ i) (h : f i j ≤ a) :
    ⨅ (i) (j), f i j ≤ a :=
  (iInf₂_le i j).trans h

theorem iSup_le (h : ∀ i, f i ≤ a) : iSup f ≤ a :=
  sSup_le fun _ ⟨i, Eq⟩ => Eq ▸ h i

theorem le_iInf (h : ∀ i, a ≤ f i) : a ≤ iInf f :=
  le_sInf fun _ ⟨i, Eq⟩ => Eq ▸ h i

theorem iSup₂_le {f : ∀ i, κ i → α} (h : ∀ i j, f i j ≤ a) : ⨆ (i) (j), f i j ≤ a :=
  iSup_le fun i => iSup_le <| h i

theorem le_iInf₂ {f : ∀ i, κ i → α} (h : ∀ i j, a ≤ f i j) : a ≤ ⨅ (i) (j), f i j :=
  le_iInf fun i => le_iInf <| h i

theorem iSup₂_le_iSup (κ : ι → Sort*) (f : ι → α) : ⨆ (i) (_ : κ i), f i ≤ ⨆ i, f i :=
  iSup₂_le fun i _ => le_iSup f i

theorem iInf_le_iInf₂ (κ : ι → Sort*) (f : ι → α) : ⨅ i, f i ≤ ⨅ (i) (_ : κ i), f i :=
  le_iInf₂ fun i _ => iInf_le f i

@[gcongr]
theorem iSup_mono (h : ∀ i, f i ≤ g i) : iSup f ≤ iSup g :=
  iSup_le fun i => le_iSup_of_le i <| h i

@[gcongr]
theorem iInf_mono (h : ∀ i, f i ≤ g i) : iInf f ≤ iInf g :=
  le_iInf fun i => iInf_le_of_le i <| h i

theorem iSup₂_mono {f g : ∀ i, κ i → α} (h : ∀ i j, f i j ≤ g i j) :
    ⨆ (i) (j), f i j ≤ ⨆ (i) (j), g i j :=
  iSup_mono fun i => iSup_mono <| h i

theorem iInf₂_mono {f g : ∀ i, κ i → α} (h : ∀ i j, f i j ≤ g i j) :
    ⨅ (i) (j), f i j ≤ ⨅ (i) (j), g i j :=
  iInf_mono fun i => iInf_mono <| h i

theorem iSup_mono' {g : ι' → α} (h : ∀ i, ∃ i', f i ≤ g i') : iSup f ≤ iSup g :=
  iSup_le fun i => Exists.elim (h i) le_iSup_of_le

theorem iInf_mono' {g : ι' → α} (h : ∀ i', ∃ i, f i ≤ g i') : iInf f ≤ iInf g :=
  le_iInf fun i' => Exists.elim (h i') iInf_le_of_le

theorem iSup₂_mono' {f : ∀ i, κ i → α} {g : ∀ i', κ' i' → α} (h : ∀ i j, ∃ i' j', f i j ≤ g i' j') :
    ⨆ (i) (j), f i j ≤ ⨆ (i) (j), g i j :=
  iSup₂_le fun i j =>
    let ⟨i', j', h⟩ := h i j
    le_iSup₂_of_le i' j' h

theorem iInf₂_mono' {f : ∀ i, κ i → α} {g : ∀ i', κ' i' → α} (h : ∀ i j, ∃ i' j', f i' j' ≤ g i j) :
    ⨅ (i) (j), f i j ≤ ⨅ (i) (j), g i j :=
  le_iInf₂ fun i j =>
    let ⟨i', j', h⟩ := h i j
    iInf₂_le_of_le i' j' h

theorem iSup_const_mono (h : ι → ι') : ⨆ _ : ι, a ≤ ⨆ _ : ι', a :=
  iSup_le <| le_iSup _ ∘ h

theorem iInf_const_mono (h : ι' → ι) : ⨅ _ : ι, a ≤ ⨅ _ : ι', a :=
  le_iInf <| iInf_le _ ∘ h

theorem iSup_iInf_le_iInf_iSup (f : ι → ι' → α) : ⨆ i, ⨅ j, f i j ≤ ⨅ j, ⨆ i, f i j :=
  iSup_le fun i => iInf_mono fun j => le_iSup (fun i => f i j) i

theorem biSup_mono {p q : ι → Prop} (hpq : ∀ i, p i → q i) :
    ⨆ (i) (_ : p i), f i ≤ ⨆ (i) (_ : q i), f i :=
  iSup_mono fun i => iSup_const_mono (hpq i)

theorem biInf_mono {p q : ι → Prop} (hpq : ∀ i, p i → q i) :
    ⨅ (i) (_ : q i), f i ≤ ⨅ (i) (_ : p i), f i :=
  iInf_mono fun i => iInf_const_mono (hpq i)

@[simp]
theorem iSup_le_iff : iSup f ≤ a ↔ ∀ i, f i ≤ a :=
  (isLUB_le_iff isLUB_iSup).trans forall_mem_range

@[simp]
theorem le_iInf_iff : a ≤ iInf f ↔ ∀ i, a ≤ f i :=
  (le_isGLB_iff isGLB_iInf).trans forall_mem_range

theorem iSup₂_le_iff {f : ∀ i, κ i → α} : ⨆ (i) (j), f i j ≤ a ↔ ∀ i j, f i j ≤ a := by
  simp_rw [iSup_le_iff]

theorem le_iInf₂_iff {f : ∀ i, κ i → α} : (a ≤ ⨅ (i) (j), f i j) ↔ ∀ i j, a ≤ f i j := by
  simp_rw [le_iInf_iff]

theorem iSup_lt_iff : iSup f < a ↔ ∃ b, b < a ∧ ∀ i, f i ≤ b :=
  ⟨fun h => ⟨iSup f, h, le_iSup f⟩, fun ⟨_, h, hb⟩ => (iSup_le hb).trans_lt h⟩

theorem lt_iInf_iff : a < iInf f ↔ ∃ b, a < b ∧ ∀ i, b ≤ f i :=
  ⟨fun h => ⟨iInf f, h, iInf_le f⟩, fun ⟨_, h, hb⟩ => h.trans_le <| le_iInf hb⟩

theorem sSup_eq_iSup {s : Set α} : sSup s = ⨆ a ∈ s, a :=
  le_antisymm (sSup_le le_iSup₂) (iSup₂_le fun _ => le_sSup)

theorem sInf_eq_iInf {s : Set α} : sInf s = ⨅ a ∈ s, a :=
  @sSup_eq_iSup αᵒᵈ _ _

lemma sSup_lowerBounds_eq_sInf (s : Set α) : sSup (lowerBounds s) = sInf s :=
  (isLUB_sSup _).unique (isGLB_sInf _).isLUB

lemma sInf_upperBounds_eq_csSup (s : Set α) : sInf (upperBounds s) = sSup s :=
  (isGLB_sInf _).unique (isLUB_sSup _).isGLB

theorem Monotone.le_map_iSup [CompleteLattice β] {f : α → β} (hf : Monotone f) :
    ⨆ i, f (s i) ≤ f (iSup s) :=
  iSup_le fun _ => hf <| le_iSup _ _

theorem Antitone.le_map_iInf [CompleteLattice β] {f : α → β} (hf : Antitone f) :
    ⨆ i, f (s i) ≤ f (iInf s) :=
  hf.dual_left.le_map_iSup

theorem Monotone.le_map_iSup₂ [CompleteLattice β] {f : α → β} (hf : Monotone f) (s : ∀ i, κ i → α) :
    ⨆ (i) (j), f (s i j) ≤ f (⨆ (i) (j), s i j) :=
  iSup₂_le fun _ _ => hf <| le_iSup₂ _ _

theorem Antitone.le_map_iInf₂ [CompleteLattice β] {f : α → β} (hf : Antitone f) (s : ∀ i, κ i → α) :
    ⨆ (i) (j), f (s i j) ≤ f (⨅ (i) (j), s i j) :=
  hf.dual_left.le_map_iSup₂ _

theorem Monotone.le_map_sSup [CompleteLattice β] {s : Set α} {f : α → β} (hf : Monotone f) :
    ⨆ a ∈ s, f a ≤ f (sSup s) := by rw [sSup_eq_iSup]; exact hf.le_map_iSup₂ _

theorem Antitone.le_map_sInf [CompleteLattice β] {s : Set α} {f : α → β} (hf : Antitone f) :
    ⨆ a ∈ s, f a ≤ f (sInf s) :=
  hf.dual_left.le_map_sSup

theorem OrderIso.map_iSup [CompleteLattice β] (f : α ≃o β) (x : ι → α) :
    f (⨆ i, x i) = ⨆ i, f (x i) :=
  eq_of_forall_ge_iff <| f.surjective.forall.2
  fun x => by simp only [f.le_iff_le, iSup_le_iff]

lemma OrderIso.map_iSup₂ [CompleteLattice β] (f : α ≃o β) (x : ∀ i, κ i → α) :
    f (⨆ i, ⨆ j, x i j) = ⨆ i, ⨆ j, f (x i j) :=
  eq_of_forall_ge_iff <| f.surjective.forall.2
  fun x => by simp only [f.le_iff_le, iSup_le_iff]

theorem OrderIso.map_iInf [CompleteLattice β] (f : α ≃o β) (x : ι → α) :
    f (⨅ i, x i) = ⨅ i, f (x i) :=
  OrderIso.map_iSup f.dual _

theorem OrderIso.map_iInf₂ [CompleteLattice β] (f : α ≃o β) (x : ∀ i, κ i → α) :
    f (⨅ i, ⨅ j, x i j) = ⨅ i, ⨅ j, f (x i j) :=
  OrderIso.map_iSup₂ f.dual _

theorem OrderIso.map_sSup [CompleteLattice β] (f : α ≃o β) (s : Set α) :
    f (sSup s) = ⨆ a ∈ s, f a := by
  simp only [sSup_eq_iSup, OrderIso.map_iSup]

theorem OrderIso.map_sInf [CompleteLattice β] (f : α ≃o β) (s : Set α) :
    f (sInf s) = ⨅ a ∈ s, f a :=
  OrderIso.map_sSup f.dual _

theorem iSup_comp_le {ι' : Sort*} (f : ι' → α) (g : ι → ι') : ⨆ x, f (g x) ≤ ⨆ y, f y :=
  iSup_mono' fun _ => ⟨_, le_rfl⟩

theorem le_iInf_comp {ι' : Sort*} (f : ι' → α) (g : ι → ι') : ⨅ y, f y ≤ ⨅ x, f (g x) :=
  iInf_mono' fun _ => ⟨_, le_rfl⟩

theorem Monotone.iSup_comp_eq [Preorder β] {f : β → α} (hf : Monotone f) {s : ι → β}
    (hs : ∀ x, ∃ i, x ≤ s i) : ⨆ x, f (s x) = ⨆ y, f y :=
  le_antisymm (iSup_comp_le _ _) (iSup_mono' fun x => (hs x).imp fun _ hi => hf hi)

theorem Monotone.iInf_comp_eq [Preorder β] {f : β → α} (hf : Monotone f) {s : ι → β}
    (hs : ∀ x, ∃ i, s i ≤ x) : ⨅ x, f (s x) = ⨅ y, f y :=
  le_antisymm (iInf_mono' fun x => (hs x).imp fun _ hi => hf hi) (le_iInf_comp _ _)

theorem Antitone.map_iSup_le [CompleteLattice β] {f : α → β} (hf : Antitone f) :
    f (iSup s) ≤ ⨅ i, f (s i) :=
  le_iInf fun _ => hf <| le_iSup _ _

theorem Monotone.map_iInf_le [CompleteLattice β] {f : α → β} (hf : Monotone f) :
    f (iInf s) ≤ ⨅ i, f (s i) :=
  hf.dual_left.map_iSup_le

theorem Antitone.map_iSup₂_le [CompleteLattice β] {f : α → β} (hf : Antitone f) (s : ∀ i, κ i → α) :
    f (⨆ (i) (j), s i j) ≤ ⨅ (i) (j), f (s i j) :=
  hf.dual.le_map_iInf₂ _

theorem Monotone.map_iInf₂_le [CompleteLattice β] {f : α → β} (hf : Monotone f) (s : ∀ i, κ i → α) :
    f (⨅ (i) (j), s i j) ≤ ⨅ (i) (j), f (s i j) :=
  hf.dual.le_map_iSup₂ _

theorem Antitone.map_sSup_le [CompleteLattice β] {s : Set α} {f : α → β} (hf : Antitone f) :
    f (sSup s) ≤ ⨅ a ∈ s, f a := by
  rw [sSup_eq_iSup]
  exact hf.map_iSup₂_le _

theorem Monotone.map_sInf_le [CompleteLattice β] {s : Set α} {f : α → β} (hf : Monotone f) :
    f (sInf s) ≤ ⨅ a ∈ s, f a :=
  hf.dual_left.map_sSup_le

theorem iSup_const_le : ⨆ _ : ι, a ≤ a :=
  iSup_le fun _ => le_rfl

theorem le_iInf_const : a ≤ ⨅ _ : ι, a :=
  le_iInf fun _ => le_rfl

-- We generalize this to conditionally complete lattices in `ciSup_const` and `ciInf_const`.
theorem iSup_const [Nonempty ι] : ⨆ _ : ι, a = a := by rw [iSup, range_const, sSup_singleton]

theorem iInf_const [Nonempty ι] : ⨅ _ : ι, a = a :=
  @iSup_const αᵒᵈ _ _ a _

lemma iSup_unique [Unique ι] (f : ι → α) : ⨆ i, f i = f default := by
  simp only [congr_arg f (Unique.eq_default _), iSup_const]

lemma iInf_unique [Unique ι] (f : ι → α) : ⨅ i, f i = f default := by
  simp only [congr_arg f (Unique.eq_default _), iInf_const]

@[simp]
theorem iSup_bot : (⨆ _ : ι, ⊥ : α) = ⊥ :=
  bot_unique iSup_const_le

@[simp]
theorem iInf_top : (⨅ _ : ι, ⊤ : α) = ⊤ :=
  top_unique le_iInf_const

@[simp]
theorem iSup_eq_bot : iSup s = ⊥ ↔ ∀ i, s i = ⊥ :=
  sSup_eq_bot.trans forall_mem_range

@[simp]
theorem iInf_eq_top : iInf s = ⊤ ↔ ∀ i, s i = ⊤ :=
  sInf_eq_top.trans forall_mem_range

@[simp] lemma bot_lt_iSup : ⊥ < ⨆ i, s i ↔ ∃ i, ⊥ < s i := by simp [bot_lt_iff_ne_bot]
@[simp] lemma iInf_lt_top : ⨅ i, s i < ⊤ ↔ ∃ i, s i < ⊤ := by simp [lt_top_iff_ne_top]

theorem iSup₂_eq_bot {f : ∀ i, κ i → α} : ⨆ (i) (j), f i j = ⊥ ↔ ∀ i j, f i j = ⊥ := by
  simp

theorem iInf₂_eq_top {f : ∀ i, κ i → α} : ⨅ (i) (j), f i j = ⊤ ↔ ∀ i j, f i j = ⊤ := by
  simp

@[simp]
theorem iSup_pos {p : Prop} {f : p → α} (hp : p) : ⨆ h : p, f h = f hp :=
  le_antisymm (iSup_le fun _ => le_rfl) (le_iSup _ _)

@[simp]
theorem iInf_pos {p : Prop} {f : p → α} (hp : p) : ⨅ h : p, f h = f hp :=
  le_antisymm (iInf_le _ _) (le_iInf fun _ => le_rfl)

@[simp]
theorem iSup_neg {p : Prop} {f : p → α} (hp : ¬p) : ⨆ h : p, f h = ⊥ :=
  le_antisymm (iSup_le fun h => (hp h).elim) bot_le

@[simp]
theorem iInf_neg {p : Prop} {f : p → α} (hp : ¬p) : ⨅ h : p, f h = ⊤ :=
  le_antisymm le_top <| le_iInf fun h => (hp h).elim

/-- Introduction rule to prove that `b` is the supremum of `f`: it suffices to check that `b`
is larger than `f i` for all `i`, and that this is not the case of any `w<b`.
See `ciSup_eq_of_forall_le_of_forall_lt_exists_gt` for a version in conditionally complete
lattices. -/
theorem iSup_eq_of_forall_le_of_forall_lt_exists_gt {f : ι → α} (h₁ : ∀ i, f i ≤ b)
    (h₂ : ∀ w, w < b → ∃ i, w < f i) : ⨆ i : ι, f i = b :=
  sSup_eq_of_forall_le_of_forall_lt_exists_gt (forall_mem_range.mpr h₁) fun w hw =>
    exists_range_iff.mpr <| h₂ w hw

/-- Introduction rule to prove that `b` is the infimum of `f`: it suffices to check that `b`
is smaller than `f i` for all `i`, and that this is not the case of any `w>b`.
See `ciInf_eq_of_forall_ge_of_forall_gt_exists_lt` for a version in conditionally complete
lattices. -/
theorem iInf_eq_of_forall_ge_of_forall_gt_exists_lt :
    (∀ i, b ≤ f i) → (∀ w, b < w → ∃ i, f i < w) → ⨅ i, f i = b :=
  @iSup_eq_of_forall_le_of_forall_lt_exists_gt αᵒᵈ _ _ _ _

theorem iSup_eq_dif {p : Prop} [Decidable p] (a : p → α) :
    ⨆ h : p, a h = if h : p then a h else ⊥ := by by_cases h : p <;> simp [h]

theorem iSup_eq_if {p : Prop} [Decidable p] (a : α) : ⨆ _ : p, a = if p then a else ⊥ :=
  iSup_eq_dif fun _ => a

theorem iInf_eq_dif {p : Prop} [Decidable p] (a : p → α) :
    ⨅ h : p, a h = if h : p then a h else ⊤ :=
  @iSup_eq_dif αᵒᵈ _ _ _ _

theorem iInf_eq_if {p : Prop} [Decidable p] (a : α) : ⨅ _ : p, a = if p then a else ⊤ :=
  iInf_eq_dif fun _ => a

theorem iSup_comm {f : ι → ι' → α} : ⨆ (i) (j), f i j = ⨆ (j) (i), f i j :=
  le_antisymm (iSup_le fun i => iSup_mono fun j => le_iSup (fun i => f i j) i)
    (iSup_le fun _ => iSup_mono fun _ => le_iSup _ _)

theorem iInf_comm {f : ι → ι' → α} : ⨅ (i) (j), f i j = ⨅ (j) (i), f i j :=
  @iSup_comm αᵒᵈ _ _ _ _

theorem iSup₂_comm {ι₁ ι₂ : Sort*} {κ₁ : ι₁ → Sort*} {κ₂ : ι₂ → Sort*}
    (f : ∀ i₁, κ₁ i₁ → ∀ i₂, κ₂ i₂ → α) :
    ⨆ (i₁) (j₁) (i₂) (j₂), f i₁ j₁ i₂ j₂ = ⨆ (i₂) (j₂) (i₁) (j₁), f i₁ j₁ i₂ j₂ := by
  simp only [@iSup_comm _ (κ₁ _), @iSup_comm _ ι₁]

theorem iInf₂_comm {ι₁ ι₂ : Sort*} {κ₁ : ι₁ → Sort*} {κ₂ : ι₂ → Sort*}
    (f : ∀ i₁, κ₁ i₁ → ∀ i₂, κ₂ i₂ → α) :
    ⨅ (i₁) (j₁) (i₂) (j₂), f i₁ j₁ i₂ j₂ = ⨅ (i₂) (j₂) (i₁) (j₁), f i₁ j₁ i₂ j₂ := by
  simp only [@iInf_comm _ (κ₁ _), @iInf_comm _ ι₁]

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
@[simp]
theorem iSup_iSup_eq_left {b : β} {f : ∀ x : β, x = b → α} : ⨆ x, ⨆ h : x = b, f x h = f b rfl :=
  (@le_iSup₂ _ _ _ _ f b rfl).antisymm'
    (iSup_le fun c =>
      iSup_le <| by
        rintro rfl
        rfl)

@[simp]
theorem iInf_iInf_eq_left {b : β} {f : ∀ x : β, x = b → α} : ⨅ x, ⨅ h : x = b, f x h = f b rfl :=
  @iSup_iSup_eq_left αᵒᵈ _ _ _ _

@[simp]
theorem iSup_iSup_eq_right {b : β} {f : ∀ x : β, b = x → α} : ⨆ x, ⨆ h : b = x, f x h = f b rfl :=
  (le_iSup₂ b rfl).antisymm'
    (iSup₂_le fun c => by
      rintro rfl
      rfl)

@[simp]
theorem iInf_iInf_eq_right {b : β} {f : ∀ x : β, b = x → α} : ⨅ x, ⨅ h : b = x, f x h = f b rfl :=
  @iSup_iSup_eq_right αᵒᵈ _ _ _ _

theorem iSup_subtype {p : ι → Prop} {f : Subtype p → α} : iSup f = ⨆ (i) (h : p i), f ⟨i, h⟩ :=
  le_antisymm (iSup_le fun ⟨i, h⟩ => @le_iSup₂ _ _ p _ (fun i h => f ⟨i, h⟩) i h)
    (iSup₂_le fun _ _ => le_iSup _ _)

theorem iInf_subtype : ∀ {p : ι → Prop} {f : Subtype p → α}, iInf f = ⨅ (i) (h : p i), f ⟨i, h⟩ :=
  @iSup_subtype αᵒᵈ _ _

theorem iSup_subtype' {p : ι → Prop} {f : ∀ i, p i → α} :
    ⨆ (i) (h), f i h = ⨆ x : Subtype p, f x x.property :=
  (@iSup_subtype _ _ _ p fun x => f x.val x.property).symm

theorem iInf_subtype' {p : ι → Prop} {f : ∀ i, p i → α} :
    ⨅ (i) (h : p i), f i h = ⨅ x : Subtype p, f x x.property :=
  (@iInf_subtype _ _ _ p fun x => f x.val x.property).symm

theorem iSup_subtype'' {ι} (s : Set ι) (f : ι → α) : ⨆ i : s, f i = ⨆ (t : ι) (_ : t ∈ s), f t :=
  iSup_subtype

theorem iInf_subtype'' {ι} (s : Set ι) (f : ι → α) : ⨅ i : s, f i = ⨅ (t : ι) (_ : t ∈ s), f t :=
  iInf_subtype

theorem biSup_const {a : α} {s : Set β} (hs : s.Nonempty) : ⨆ i ∈ s, a = a := by
  haveI : Nonempty s := Set.nonempty_coe_sort.mpr hs
  rw [← iSup_subtype'', iSup_const]

theorem biInf_const {a : α} {s : Set β} (hs : s.Nonempty) : ⨅ i ∈ s, a = a :=
  biSup_const (α := αᵒᵈ) hs

theorem iSup_sup_eq : ⨆ x, f x ⊔ g x = (⨆ x, f x) ⊔ ⨆ x, g x :=
  le_antisymm (iSup_le fun _ => sup_le_sup (le_iSup _ _) <| le_iSup _ _)
    (sup_le (iSup_mono fun _ => le_sup_left) <| iSup_mono fun _ => le_sup_right)

theorem iInf_inf_eq : ⨅ x, f x ⊓ g x = (⨅ x, f x) ⊓ ⨅ x, g x :=
  @iSup_sup_eq αᵒᵈ _ _ _ _

lemma Equiv.biSup_comp {ι ι' : Type*} {g : ι' → α} (e : ι ≃ ι') (s : Set ι') :
    ⨆ i ∈ e.symm '' s, g (e i) = ⨆ i ∈ s, g i := by
  simpa only [iSup_subtype'] using (image e.symm s).symm.iSup_comp (g := g ∘ (↑))

lemma Equiv.biInf_comp {ι ι' : Type*} {g : ι' → α} (e : ι ≃ ι') (s : Set ι') :
    ⨅ i ∈ e.symm '' s, g (e i) = ⨅ i ∈ s, g i :=
  e.biSup_comp s (α := αᵒᵈ)

lemma biInf_le {ι : Type*} {s : Set ι} (f : ι → α) {i : ι} (hi : i ∈ s) : ⨅ i ∈ s, f i ≤ f i :=
  iInf₂_le i hi

lemma le_biSup {ι : Type*} {s : Set ι} (f : ι → α) {i : ι} (hi : i ∈ s) : f i ≤ ⨆ i ∈ s, f i :=
  biInf_le (α := αᵒᵈ) f hi

lemma biInf_le_biSup {ι : Type*} {s : Set ι} (hs : s.Nonempty) {f : ι → α} :
    ⨅ i ∈ s, f i ≤ ⨆ i ∈ s, f i :=
  (biInf_le _ hs.choose_spec).trans <| le_biSup _ hs.choose_spec

/- TODO: here is another example where more flexible pattern matching might help.

begin
  apply @le_antisymm,
  safe, pose h := f a ⊓ g a, begin [smt] ematch, ematch end
end
-/
theorem iSup_sup [Nonempty ι] {f : ι → α} {a : α} : (⨆ x, f x) ⊔ a = ⨆ x, f x ⊔ a := by
  rw [iSup_sup_eq, iSup_const]

theorem iInf_inf [Nonempty ι] {f : ι → α} {a : α} : (⨅ x, f x) ⊓ a = ⨅ x, f x ⊓ a := by
  rw [iInf_inf_eq, iInf_const]

theorem sup_iSup [Nonempty ι] {f : ι → α} {a : α} : (a ⊔ ⨆ x, f x) = ⨆ x, a ⊔ f x := by
  rw [iSup_sup_eq, iSup_const]

theorem inf_iInf [Nonempty ι] {f : ι → α} {a : α} : (a ⊓ ⨅ x, f x) = ⨅ x, a ⊓ f x := by
  rw [iInf_inf_eq, iInf_const]

theorem biSup_sup {p : ι → Prop} {f : ∀ i, p i → α} {a : α} (h : ∃ i, p i) :
    (⨆ (i) (h : p i), f i h) ⊔ a = ⨆ (i) (h : p i), f i h ⊔ a := by
  haveI : Nonempty { i // p i } :=
    let ⟨i, hi⟩ := h
    ⟨⟨i, hi⟩⟩
  rw [iSup_subtype', iSup_subtype', iSup_sup]

theorem sup_biSup {p : ι → Prop} {f : ∀ i, p i → α} {a : α} (h : ∃ i, p i) :
    (a ⊔ ⨆ (i) (h : p i), f i h) = ⨆ (i) (h : p i), a ⊔ f i h := by
  simpa only [sup_comm] using @biSup_sup α _ _ p _ _ h

theorem biInf_inf {p : ι → Prop} {f : ∀ i, p i → α} {a : α} (h : ∃ i, p i) :
    (⨅ (i) (h : p i), f i h) ⊓ a = ⨅ (i) (h : p i), f i h ⊓ a :=
  @biSup_sup αᵒᵈ ι _ p f _ h

theorem inf_biInf {p : ι → Prop} {f : ∀ i, p i → α} {a : α} (h : ∃ i, p i) :
    (a ⊓ ⨅ (i) (h : p i), f i h) = ⨅ (i) (h : p i), a ⊓ f i h :=
  @sup_biSup αᵒᵈ ι _ p f _ h

lemma biSup_lt_eq_iSup {ι : Type*} [LT ι] [NoMaxOrder ι] {f : ι → α} :
    ⨆ (i) (j < i), f j = ⨆ i, f i := by
  apply le_antisymm
  · exact iSup_le fun _ ↦ iSup₂_le fun _ _ ↦ le_iSup _ _
  · refine iSup_le fun j ↦ ?_
    obtain ⟨i, jlt⟩ := exists_gt j
    exact le_iSup_of_le i (le_iSup₂_of_le j jlt le_rfl)

lemma biSup_le_eq_iSup {ι : Type*} [Preorder ι] {f : ι → α} :
    ⨆ (i) (j ≤ i), f j = ⨆ i, f i := by
  apply le_antisymm
  · exact iSup_le fun _ ↦ iSup₂_le fun _ _ ↦ le_iSup _ _
  · exact iSup_le fun j ↦ le_iSup_of_le j (le_iSup₂_of_le j le_rfl le_rfl)

lemma biInf_lt_eq_iInf {ι : Type*} [LT ι] [NoMaxOrder ι] {f : ι → α} :
    ⨅ (i) (j < i), f j = ⨅ i, f i :=
  biSup_lt_eq_iSup (α := αᵒᵈ)

lemma biInf_le_eq_iInf {ι : Type*} [Preorder ι] {f : ι → α} : ⨅ (i) (j ≤ i), f j = ⨅ i, f i :=
  biSup_le_eq_iSup (α := αᵒᵈ)

lemma biSup_gt_eq_iSup {ι : Type*} [LT ι] [NoMinOrder ι] {f : ι → α} :
    ⨆ (i) (j > i), f j = ⨆ i, f i :=
  biSup_lt_eq_iSup (ι := ιᵒᵈ)

lemma biSup_ge_eq_iSup {ι : Type*} [Preorder ι] {f : ι → α} : ⨆ (i) (j ≥ i), f j = ⨆ i, f i :=
  biSup_le_eq_iSup (ι := ιᵒᵈ)

lemma biInf_gt_eq_iInf {ι : Type*} [LT ι] [NoMinOrder ι] {f : ι → α} :
    ⨅ (i) (j > i), f j = ⨅ i, f i :=
  biInf_lt_eq_iInf (ι := ιᵒᵈ)

lemma biInf_ge_eq_iInf {ι : Type*} [Preorder ι] {f : ι → α} : ⨅ (i) (j ≥ i), f j = ⨅ i, f i :=
  biInf_le_eq_iInf (ι := ιᵒᵈ)

lemma biSup_le_eq_of_monotone [Preorder β] {f : β → α} (hf : Monotone f) (b : β) :
    ⨆ (b' ≤ b), f b' = f b :=
  le_antisymm (iSup₂_le_iff.2 (fun _ hji ↦ hf hji))
    (le_iSup_of_le b (ge_of_eq (iSup_pos le_rfl)))

lemma biInf_le_eq_of_antitone [Preorder β] {f : β → α} (hf : Antitone f) (b : β) :
    ⨅ (b' ≤ b), f b' = f b :=
  biSup_le_eq_of_monotone (α := αᵒᵈ) hf.dual_right b

lemma biSup_ge_eq_of_antitone [Preorder β] {f : β → α} (hf : Antitone f) (b : β) :
    ⨆ (b' ≥ b), f b' = f b :=
  biSup_le_eq_of_monotone (β := βᵒᵈ) hf.dual_left b

lemma biInf_ge_eq_of_monotone [Preorder β] {f : β → α} (hf : Monotone f) (b : β) :
    ⨅ (b' ≥ b), f b' = f b :=
  biInf_le_eq_of_antitone (β := βᵒᵈ) hf.dual_left b

/-! ### `iSup` and `iInf` under `Prop` -/

theorem iSup_false {s : False → α} : iSup s = ⊥ := by simp

theorem iInf_false {s : False → α} : iInf s = ⊤ := by simp

theorem iSup_true {s : True → α} : iSup s = s trivial :=
  iSup_pos trivial

theorem iInf_true {s : True → α} : iInf s = s trivial :=
  iInf_pos trivial

@[simp]
theorem iSup_exists {p : ι → Prop} {f : Exists p → α} : ⨆ x, f x = ⨆ (i) (h), f ⟨i, h⟩ :=
  le_antisymm (iSup_le fun ⟨i, h⟩ => @le_iSup₂ _ _ _ _ (fun _ _ => _) i h)
    (iSup₂_le fun _ _ => le_iSup _ _)

@[simp]
theorem iInf_exists {p : ι → Prop} {f : Exists p → α} : ⨅ x, f x = ⨅ (i) (h), f ⟨i, h⟩ :=
  @iSup_exists αᵒᵈ _ _ _ _

theorem iSup_and {p q : Prop} {s : p ∧ q → α} : iSup s = ⨆ (h₁) (h₂), s ⟨h₁, h₂⟩ :=
  le_antisymm (iSup_le fun ⟨i, h⟩ => @le_iSup₂ _ _ _ _ (fun _ _ => _) i h)
    (iSup₂_le fun _ _ => le_iSup _ _)

theorem iInf_and {p q : Prop} {s : p ∧ q → α} : iInf s = ⨅ (h₁) (h₂), s ⟨h₁, h₂⟩ :=
  @iSup_and αᵒᵈ _ _ _ _

/-- The symmetric case of `iSup_and`, useful for rewriting into a supremum over a conjunction -/
theorem iSup_and' {p q : Prop} {s : p → q → α} :
    ⨆ (h₁ : p) (h₂ : q), s h₁ h₂ = ⨆ h : p ∧ q, s h.1 h.2 :=
  Eq.symm iSup_and

/-- The symmetric case of `iInf_and`, useful for rewriting into an infimum over a conjunction -/
theorem iInf_and' {p q : Prop} {s : p → q → α} :
    ⨅ (h₁ : p) (h₂ : q), s h₁ h₂ = ⨅ h : p ∧ q, s h.1 h.2 :=
  Eq.symm iInf_and

theorem iSup_or {p q : Prop} {s : p ∨ q → α} :
    ⨆ x, s x = (⨆ i, s (Or.inl i)) ⊔ ⨆ j, s (Or.inr j) :=
  le_antisymm
    (iSup_le fun i =>
      match i with
      | Or.inl _ => le_sup_of_le_left <| le_iSup (fun _ => s _) _
      | Or.inr _ => le_sup_of_le_right <| le_iSup (fun _ => s _) _)
    (sup_le (iSup_comp_le _ _) (iSup_comp_le _ _))

theorem iInf_or {p q : Prop} {s : p ∨ q → α} :
    ⨅ x, s x = (⨅ i, s (Or.inl i)) ⊓ ⨅ j, s (Or.inr j) :=
  @iSup_or αᵒᵈ _ _ _ _

section

variable (p : ι → Prop) [DecidablePred p]

theorem iSup_dite (f : ∀ i, p i → α) (g : ∀ i, ¬p i → α) :
    ⨆ i, (if h : p i then f i h else g i h) = (⨆ (i) (h : p i), f i h) ⊔ ⨆ (i) (h : ¬p i),
    g i h := by
  rw [← iSup_sup_eq]
  congr 1 with i
  split_ifs with h <;> simp [h]

theorem iInf_dite (f : ∀ i, p i → α) (g : ∀ i, ¬p i → α) :
    ⨅ i, (if h : p i then f i h else g i h) = (⨅ (i) (h : p i), f i h) ⊓ ⨅ (i) (h : ¬p i), g i h :=
  iSup_dite p (show ∀ i, p i → αᵒᵈ from f) g

theorem iSup_ite (f g : ι → α) :
    ⨆ i, (if p i then f i else g i) = (⨆ (i) (_ : p i), f i) ⊔ ⨆ (i) (_ : ¬p i), g i :=
  iSup_dite _ _ _

theorem iInf_ite (f g : ι → α) :
    ⨅ i, (if p i then f i else g i) = (⨅ (i) (_ : p i), f i) ⊓ ⨅ (i) (_ : ¬p i), g i :=
  iInf_dite _ _ _

end

theorem iSup_range {g : β → α} {f : ι → β} : ⨆ b ∈ range f, g b = ⨆ i, g (f i) := by
  rw [← iSup_subtype'', iSup_range']

theorem iInf_range : ∀ {g : β → α} {f : ι → β}, ⨅ b ∈ range f, g b = ⨅ i, g (f i) :=
  @iSup_range αᵒᵈ _ _ _

theorem sSup_image {s : Set β} {f : β → α} : sSup (f '' s) = ⨆ a ∈ s, f a := by
  rw [← iSup_subtype'', sSup_image']

theorem sInf_image {s : Set β} {f : β → α} : sInf (f '' s) = ⨅ a ∈ s, f a :=
  @sSup_image αᵒᵈ _ _ _ _

theorem OrderIso.map_sSup_eq_sSup_symm_preimage [CompleteLattice β] (f : α ≃o β) (s : Set α) :
    f (sSup s) = sSup (f.symm ⁻¹' s) := by
  rw [map_sSup, ← sSup_image, f.image_eq_preimage]

theorem OrderIso.map_sInf_eq_sInf_symm_preimage [CompleteLattice β] (f : α ≃o β) (s : Set α) :
    f (sInf s) = sInf (f.symm ⁻¹' s) := by
  rw [map_sInf, ← sInf_image, f.image_eq_preimage]

/-
### iSup and iInf under set constructions
-/
theorem iSup_emptyset {f : β → α} : ⨆ x ∈ (∅ : Set β), f x = ⊥ := by simp

theorem iInf_emptyset {f : β → α} : ⨅ x ∈ (∅ : Set β), f x = ⊤ := by simp

theorem iSup_univ {f : β → α} : ⨆ x ∈ (univ : Set β), f x = ⨆ x, f x := by simp

theorem iInf_univ {f : β → α} : ⨅ x ∈ (univ : Set β), f x = ⨅ x, f x := by simp

theorem iSup_union {f : β → α} {s t : Set β} :
    ⨆ x ∈ s ∪ t, f x = (⨆ x ∈ s, f x) ⊔ ⨆ x ∈ t, f x := by
  simp_rw [mem_union, iSup_or, iSup_sup_eq]

theorem iInf_union {f : β → α} {s t : Set β} : ⨅ x ∈ s ∪ t, f x = (⨅ x ∈ s, f x) ⊓ ⨅ x ∈ t, f x :=
  @iSup_union αᵒᵈ _ _ _ _ _

theorem iSup_split (f : β → α) (p : β → Prop) :
    ⨆ i, f i = (⨆ (i) (_ : p i), f i) ⊔ ⨆ (i) (_ : ¬p i), f i := by
  simpa [Classical.em] using @iSup_union _ _ _ f { i | p i } { i | ¬p i }

theorem iInf_split :
    ∀ (f : β → α) (p : β → Prop), ⨅ i, f i = (⨅ (i) (_ : p i), f i) ⊓ ⨅ (i) (_ : ¬p i), f i :=
  @iSup_split αᵒᵈ _ _

theorem iSup_split_single (f : β → α) (i₀ : β) : ⨆ i, f i = f i₀ ⊔ ⨆ (i) (_ : i ≠ i₀), f i := by
  convert iSup_split f (fun i => i = i₀)
  simp

theorem iInf_split_single (f : β → α) (i₀ : β) : ⨅ i, f i = f i₀ ⊓ ⨅ (i) (_ : i ≠ i₀), f i :=
  @iSup_split_single αᵒᵈ _ _ _ _

theorem iSup_le_iSup_of_subset {f : β → α} {s t : Set β} : s ⊆ t → ⨆ x ∈ s, f x ≤ ⨆ x ∈ t, f x :=
  biSup_mono

theorem iInf_le_iInf_of_subset {f : β → α} {s t : Set β} : s ⊆ t → ⨅ x ∈ t, f x ≤ ⨅ x ∈ s, f x :=
  biInf_mono

theorem iSup_insert {f : β → α} {s : Set β} {b : β} :
    ⨆ x ∈ insert b s, f x = f b ⊔ ⨆ x ∈ s, f x :=
  Eq.trans iSup_union <| congr_arg (fun x => x ⊔ ⨆ x ∈ s, f x) iSup_iSup_eq_left

theorem iInf_insert {f : β → α} {s : Set β} {b : β} :
    ⨅ x ∈ insert b s, f x = f b ⊓ ⨅ x ∈ s, f x :=
  Eq.trans iInf_union <| congr_arg (fun x => x ⊓ ⨅ x ∈ s, f x) iInf_iInf_eq_left

theorem iSup_singleton {f : β → α} {b : β} : ⨆ x ∈ (singleton b : Set β), f x = f b := by simp

theorem iInf_singleton {f : β → α} {b : β} : ⨅ x ∈ (singleton b : Set β), f x = f b := by simp

theorem iSup_pair {f : β → α} {a b : β} : ⨆ x ∈ ({a, b} : Set β), f x = f a ⊔ f b := by
  rw [iSup_insert, iSup_singleton]

theorem iInf_pair {f : β → α} {a b : β} : ⨅ x ∈ ({a, b} : Set β), f x = f a ⊓ f b := by
  rw [iInf_insert, iInf_singleton]

theorem iSup_image {γ} {f : β → γ} {g : γ → α} {t : Set β} :
    ⨆ c ∈ f '' t, g c = ⨆ b ∈ t, g (f b) := by
  rw [← sSup_image, ← sSup_image, ← image_comp, comp_def]

theorem iInf_image :
    ∀ {γ} {f : β → γ} {g : γ → α} {t : Set β}, ⨅ c ∈ f '' t, g c = ⨅ b ∈ t, g (f b) :=
  @iSup_image αᵒᵈ _ _

theorem iSup_extend_bot {e : ι → β} (he : Injective e) (f : ι → α) :
    ⨆ j, extend e f ⊥ j = ⨆ i, f i := by
  rw [iSup_split _ fun j => ∃ i, e i = j]
  simp +contextual [he.extend_apply, extend_apply', @iSup_comm _ β ι]

theorem iInf_extend_top {e : ι → β} (he : Injective e) (f : ι → α) :
    ⨅ j, extend e f ⊤ j = iInf f :=
  @iSup_extend_bot αᵒᵈ _ _ _ _ he _

section le

variable {ι : Type*} [PartialOrder ι] (f : ι → α) (i : ι)

theorem biSup_le_eq_sup : (⨆ j ≤ i, f j) = (⨆ j < i, f j) ⊔ f i := by
  rw [iSup_split_single _ i]
  -- Squeezed for a ~10x speedup, though it's still reasonably fast unsqueezed.
  simp only [le_refl, iSup_pos, iSup_and', lt_iff_le_and_ne, and_comm, sup_comm]

theorem biInf_le_eq_inf : (⨅ j ≤ i, f j) = (⨅ j < i, f j) ⊓ f i :=
  biSup_le_eq_sup (α := αᵒᵈ) f i

theorem biSup_ge_eq_sup : (⨆ j ≥ i, f j) = f i ⊔ (⨆ j > i, f j) := by
  rw [iSup_split_single _ i]
  -- Squeezed for a ~10x speedup, though it's still reasonably fast unsqueezed.
  simp only [ge_iff_le, le_refl, iSup_pos, ne_comm, iSup_and', gt_iff_lt, lt_iff_le_and_ne,
    and_comm]

theorem biInf_ge_eq_inf : (⨅ j ≥ i, f j) = f i ⊓ (⨅ j > i, f j) :=
  biSup_ge_eq_sup (α := αᵒᵈ) f i

end le

/-!
### `iSup` and `iInf` under `Type`
-/


theorem iSup_of_empty' {α ι} [SupSet α] [IsEmpty ι] (f : ι → α) : iSup f = sSup (∅ : Set α) :=
  congr_arg sSup (range_eq_empty f)

theorem iInf_of_isEmpty {α ι} [InfSet α] [IsEmpty ι] (f : ι → α) : iInf f = sInf (∅ : Set α) :=
  congr_arg sInf (range_eq_empty f)

theorem iSup_of_empty [IsEmpty ι] (f : ι → α) : iSup f = ⊥ :=
  (iSup_of_empty' f).trans sSup_empty

theorem iInf_of_empty [IsEmpty ι] (f : ι → α) : iInf f = ⊤ :=
  @iSup_of_empty αᵒᵈ _ _ _ f

theorem isGLB_biInf {s : Set β} {f : β → α} : IsGLB (f '' s) (⨅ x ∈ s, f x) := by
  simpa only [range_comp, Subtype.range_coe, iInf_subtype'] using
    @isGLB_iInf α s _ (f ∘ fun x => (x : β))

theorem isLUB_biSup {s : Set β} {f : β → α} : IsLUB (f '' s) (⨆ x ∈ s, f x) := by
  simpa only [range_comp, Subtype.range_coe, iSup_subtype'] using
    @isLUB_iSup α s _ (f ∘ fun x => (x : β))

theorem iSup_sigma {p : β → Type*} {f : Sigma p → α} : ⨆ x, f x = ⨆ (i) (j), f ⟨i, j⟩ :=
  eq_of_forall_ge_iff fun c => by simp only [iSup_le_iff, Sigma.forall]

theorem iInf_sigma {p : β → Type*} {f : Sigma p → α} : ⨅ x, f x = ⨅ (i) (j), f ⟨i, j⟩ :=
  @iSup_sigma αᵒᵈ _ _ _ _

lemma iSup_sigma' {κ : β → Type*} (f : ∀ i, κ i → α) :
    (⨆ i, ⨆ j, f i j) = ⨆ x : Σ i, κ i, f x.1 x.2 := (iSup_sigma (f := fun x ↦ f x.1 x.2)).symm

lemma iInf_sigma' {κ : β → Type*} (f : ∀ i, κ i → α) :
    (⨅ i, ⨅ j, f i j) = ⨅ x : Σ i, κ i, f x.1 x.2 := (iInf_sigma (f := fun x ↦ f x.1 x.2)).symm

lemma iSup_psigma {ι : Sort*} {κ : ι → Sort*} (f : (Σ' i, κ i) → α) :
    ⨆ ij, f ij = ⨆ i, ⨆ j, f ⟨i, j⟩ :=
  eq_of_forall_ge_iff fun c ↦ by simp only [iSup_le_iff, PSigma.forall]

lemma iInf_psigma {ι : Sort*} {κ : ι → Sort*} (f : (Σ' i, κ i) → α) :
    ⨅ ij, f ij = ⨅ i, ⨅ j, f ⟨i, j⟩ :=
  eq_of_forall_le_iff fun c ↦ by simp only [le_iInf_iff, PSigma.forall]

lemma iSup_psigma' {ι : Sort*} {κ : ι → Sort*} (f : ∀ i, κ i → α) :
    (⨆ i, ⨆ j, f i j) = ⨆ ij : Σ' i, κ i, f ij.1 ij.2 := (iSup_psigma fun x ↦ f x.1 x.2).symm

lemma iInf_psigma' {ι : Sort*} {κ : ι → Sort*} (f : ∀ i, κ i → α) :
    (⨅ i, ⨅ j, f i j) = ⨅ ij : Σ' i, κ i, f ij.1 ij.2 := (iInf_psigma fun x ↦ f x.1 x.2).symm

theorem iSup_prod {f : β × γ → α} : ⨆ x, f x = ⨆ (i) (j), f (i, j) :=
  eq_of_forall_ge_iff fun c => by simp only [iSup_le_iff, Prod.forall]

theorem iInf_prod {f : β × γ → α} : ⨅ x, f x = ⨅ (i) (j), f (i, j) :=
  @iSup_prod αᵒᵈ _ _ _ _

lemma iSup_prod' (f : β → γ → α) : (⨆ i, ⨆ j, f i j) = ⨆ x : β × γ, f x.1 x.2 :=
(iSup_prod (f := fun x ↦ f x.1 x.2)).symm

lemma iInf_prod' (f : β → γ → α) : (⨅ i, ⨅ j, f i j) = ⨅ x : β × γ, f x.1 x.2 :=
(iInf_prod (f := fun x ↦ f x.1 x.2)).symm

theorem biSup_prod {f : β × γ → α} {s : Set β} {t : Set γ} :
    ⨆ x ∈ s ×ˢ t, f x = ⨆ (a ∈ s) (b ∈ t), f (a, b) := by
  simp_rw [iSup_prod, mem_prod, iSup_and]
  exact iSup_congr fun _ => iSup_comm

theorem biSup_prod' {f : β → γ → α} {s : Set β} {t : Set γ} :
    ⨆ x ∈ s ×ˢ t, f x.1 x.2 = ⨆ (a ∈ s) (b ∈ t), f a b :=
  biSup_prod

theorem biInf_prod {f : β × γ → α} {s : Set β} {t : Set γ} :
    ⨅ x ∈ s ×ˢ t, f x = ⨅ (a ∈ s) (b ∈ t), f (a, b) :=
  @biSup_prod αᵒᵈ _ _ _ _ _ _

theorem biInf_prod' {f : β → γ → α} {s : Set β} {t : Set γ} :
    ⨅ x ∈ s ×ˢ t, f x.1 x.2 = ⨅ (a ∈ s) (b ∈ t), f a b :=
  biInf_prod

theorem iSup_image2 {γ δ} (f : β → γ → δ) (s : Set β) (t : Set γ) (g : δ → α) :
    ⨆ d ∈ image2 f s t, g d = ⨆ b ∈ s, ⨆ c ∈ t, g (f b c) := by
  rw [← image_prod, iSup_image, biSup_prod]

theorem iInf_image2 {γ δ} (f : β → γ → δ) (s : Set β) (t : Set γ) (g : δ → α) :
    ⨅ d ∈ image2 f s t, g d = ⨅ b ∈ s, ⨅ c ∈ t, g (f b c) :=
  iSup_image2 f s t (toDual ∘ g)

theorem iSup_sum {f : β ⊕ γ → α} : ⨆ x, f x = (⨆ i, f (Sum.inl i)) ⊔ ⨆ j, f (Sum.inr j) :=
  eq_of_forall_ge_iff fun c => by simp only [sup_le_iff, iSup_le_iff, Sum.forall]

theorem iInf_sum {f : β ⊕ γ → α} : ⨅ x, f x = (⨅ i, f (Sum.inl i)) ⊓ ⨅ j, f (Sum.inr j) :=
  @iSup_sum αᵒᵈ _ _ _ _

theorem iSup_option (f : Option β → α) : ⨆ o, f o = f none ⊔ ⨆ b, f (Option.some b) :=
  eq_of_forall_ge_iff fun c => by simp only [iSup_le_iff, sup_le_iff, Option.forall]

theorem iInf_option (f : Option β → α) : ⨅ o, f o = f none ⊓ ⨅ b, f (Option.some b) :=
  @iSup_option αᵒᵈ _ _ _

/-- A version of `iSup_option` useful for rewriting right-to-left. -/
theorem iSup_option_elim (a : α) (f : β → α) : ⨆ o : Option β, o.elim a f = a ⊔ ⨆ b, f b := by
  simp [iSup_option]

/-- A version of `iInf_option` useful for rewriting right-to-left. -/
theorem iInf_option_elim (a : α) (f : β → α) : ⨅ o : Option β, o.elim a f = a ⊓ ⨅ b, f b :=
  @iSup_option_elim αᵒᵈ _ _ _ _

/-- When taking the supremum of `f : ι → α`, the elements of `ι` on which `f` gives `⊥` can be
dropped, without changing the result. -/
@[simp]
theorem iSup_ne_bot_subtype (f : ι → α) : ⨆ i : { i // f i ≠ ⊥ }, f i = ⨆ i, f i := by
  by_cases htriv : ∀ i, f i = ⊥
  · simp only [iSup_bot, (funext htriv : f = _)]
  refine (iSup_comp_le f _).antisymm (iSup_mono' fun i => ?_)
  by_cases hi : f i = ⊥
  · rw [hi]
    obtain ⟨i₀, hi₀⟩ := not_forall.mp htriv
    exact ⟨⟨i₀, hi₀⟩, bot_le⟩
  · exact ⟨⟨i, hi⟩, rfl.le⟩

/-- When taking the infimum of `f : ι → α`, the elements of `ι` on which `f` gives `⊤` can be
dropped, without changing the result. -/
theorem iInf_ne_top_subtype (f : ι → α) : ⨅ i : { i // f i ≠ ⊤ }, f i = ⨅ i, f i :=
  @iSup_ne_bot_subtype αᵒᵈ ι _ f

theorem sSup_image2 {f : β → γ → α} {s : Set β} {t : Set γ} :
    sSup (image2 f s t) = ⨆ (a ∈ s) (b ∈ t), f a b := by rw [← image_prod, sSup_image, biSup_prod]

theorem sInf_image2 {f : β → γ → α} {s : Set β} {t : Set γ} :
    sInf (image2 f s t) = ⨅ (a ∈ s) (b ∈ t), f a b := by rw [← image_prod, sInf_image, biInf_prod]

end

section CompleteLinearOrder

variable [CompleteLinearOrder α]

theorem iSup_eq_top (f : ι → α) : iSup f = ⊤ ↔ ∀ b < ⊤, ∃ i, b < f i := by
  simp only [← sSup_range, sSup_eq_top, Set.exists_range_iff]

theorem iInf_eq_bot (f : ι → α) : iInf f = ⊥ ↔ ∀ b > ⊥, ∃ i, f i < b := by
  simp only [← sInf_range, sInf_eq_bot, Set.exists_range_iff]

lemma iSup₂_eq_top (f : ∀ i, κ i → α) : ⨆ i, ⨆ j, f i j = ⊤ ↔ ∀ b < ⊤, ∃ i j, b < f i j := by
  simp_rw [iSup_psigma', iSup_eq_top, PSigma.exists]

lemma iInf₂_eq_bot (f : ∀ i, κ i → α) : ⨅ i, ⨅ j, f i j = ⊥ ↔ ∀ b > ⊥, ∃ i j, f i j < b := by
  simp_rw [iInf_psigma', iInf_eq_bot, PSigma.exists]

end CompleteLinearOrder

/-!
### Instances
-/


instance Prop.instCompleteLattice : CompleteLattice Prop where
  __ := Prop.instBoundedOrder
  __ := Prop.instDistribLattice
  sSup s := ∃ a ∈ s, a
  le_sSup _ a h p := ⟨a, h, p⟩
  sSup_le _ _ h := fun ⟨b, h', p⟩ => h b h' p
  sInf s := ∀ a, a ∈ s → a
  sInf_le _ a h p := p a h
  le_sInf _ _ h p b hb := h b hb p

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

instance Pi.supSet {α : Type*} {β : α → Type*} [∀ i, SupSet (β i)] : SupSet (∀ i, β i) :=
  ⟨fun s i => ⨆ f : s, (f : ∀ i, β i) i⟩

instance Pi.infSet {α : Type*} {β : α → Type*} [∀ i, InfSet (β i)] : InfSet (∀ i, β i) :=
  ⟨fun s i => ⨅ f : s, (f : ∀ i, β i) i⟩

instance Pi.instCompleteLattice {α : Type*} {β : α → Type*} [∀ i, CompleteLattice (β i)] :
    CompleteLattice (∀ i, β i) where
  __ := instBoundedOrder
  le_sSup s f hf := fun i => le_iSup (fun f : s => (f : ∀ i, β i) i) ⟨f, hf⟩
  sInf_le s f hf := fun i => iInf_le (fun f : s => (f : ∀ i, β i) i) ⟨f, hf⟩
  sSup_le _ _ hf := fun i => iSup_le fun g => hf g g.2 i
  le_sInf _ _ hf := fun i => le_iInf fun g => hf g g.2 i

@[simp]
theorem sSup_apply {α : Type*} {β : α → Type*} [∀ i, SupSet (β i)] {s : Set (∀ a, β a)} {a : α} :
    (sSup s) a = ⨆ f : s, (f : ∀ a, β a) a :=
  rfl

@[simp]
theorem sInf_apply {α : Type*} {β : α → Type*} [∀ i, InfSet (β i)] {s : Set (∀ a, β a)} {a : α} :
    sInf s a = ⨅ f : s, (f : ∀ a, β a) a :=
  rfl

@[simp]
theorem iSup_apply {α : Type*} {β : α → Type*} {ι : Sort*} [∀ i, SupSet (β i)] {f : ι → ∀ a, β a}
    {a : α} : (⨆ i, f i) a = ⨆ i, f i a := by
  rw [iSup, sSup_apply, iSup, iSup, ← image_eq_range (fun f : ∀ i, β i => f a) (range f), ←
    range_comp]; rfl

@[simp]
theorem iInf_apply {α : Type*} {β : α → Type*} {ι : Sort*} [∀ i, InfSet (β i)] {f : ι → ∀ a, β a}
    {a : α} : (⨅ i, f i) a = ⨅ i, f i a :=
  @iSup_apply α (fun i => (β i)ᵒᵈ) _ _ _ _

theorem unary_relation_sSup_iff {α : Type*} (s : Set (α → Prop)) {a : α} :
    sSup s a ↔ ∃ r : α → Prop, r ∈ s ∧ r a := by
  rw [sSup_apply]
  simp

theorem unary_relation_sInf_iff {α : Type*} (s : Set (α → Prop)) {a : α} :
    sInf s a ↔ ∀ r : α → Prop, r ∈ s → r a := by
  rw [sInf_apply]
  simp

theorem binary_relation_sSup_iff {α β : Type*} (s : Set (α → β → Prop)) {a : α} {b : β} :
    sSup s a b ↔ ∃ r : α → β → Prop, r ∈ s ∧ r a b := by
  rw [sSup_apply]
  simp

theorem binary_relation_sInf_iff {α β : Type*} (s : Set (α → β → Prop)) {a : α} {b : β} :
    sInf s a b ↔ ∀ r : α → β → Prop, r ∈ s → r a b := by
  rw [sInf_apply]
  simp

section CompleteLattice

variable [Preorder α] [CompleteLattice β] {s : Set (α → β)} {f : ι → α → β}

protected lemma Monotone.sSup (hs : ∀ f ∈ s, Monotone f) : Monotone (sSup s) :=
  fun _ _ h ↦ iSup_mono fun f ↦ hs f f.2 h

protected lemma Monotone.sInf (hs : ∀ f ∈ s, Monotone f) : Monotone (sInf s) :=
  fun _ _ h ↦ iInf_mono fun f ↦ hs f f.2 h

protected lemma Antitone.sSup (hs : ∀ f ∈ s, Antitone f) : Antitone (sSup s) :=
  fun _ _ h ↦ iSup_mono fun f ↦ hs f f.2 h

protected lemma Antitone.sInf (hs : ∀ f ∈ s, Antitone f) : Antitone (sInf s) :=
  fun _ _ h ↦ iInf_mono fun f ↦ hs f f.2 h

protected lemma Monotone.iSup (hf : ∀ i, Monotone (f i)) : Monotone (⨆ i, f i) :=
  Monotone.sSup (by simpa)
protected lemma Monotone.iInf (hf : ∀ i, Monotone (f i)) : Monotone (⨅ i, f i) :=
  Monotone.sInf (by simpa)
protected lemma Antitone.iSup (hf : ∀ i, Antitone (f i)) : Antitone (⨆ i, f i) :=
  Antitone.sSup (by simpa)
protected lemma Antitone.iInf (hf : ∀ i, Antitone (f i)) : Antitone (⨅ i, f i) :=
  Antitone.sInf (by simpa)

end CompleteLattice

namespace Prod

variable (α β)

instance supSet [SupSet α] [SupSet β] : SupSet (α × β) :=
  ⟨fun s => (sSup (Prod.fst '' s), sSup (Prod.snd '' s))⟩

instance infSet [InfSet α] [InfSet β] : InfSet (α × β) :=
  ⟨fun s => (sInf (Prod.fst '' s), sInf (Prod.snd '' s))⟩

variable {α β}

theorem fst_sInf [InfSet α] [InfSet β] (s : Set (α × β)) : (sInf s).fst = sInf (Prod.fst '' s) :=
  rfl

theorem snd_sInf [InfSet α] [InfSet β] (s : Set (α × β)) : (sInf s).snd = sInf (Prod.snd '' s) :=
  rfl

theorem swap_sInf [InfSet α] [InfSet β] (s : Set (α × β)) : (sInf s).swap = sInf (Prod.swap '' s) :=
  Prod.ext (congr_arg sInf <| image_comp Prod.fst swap s)
    (congr_arg sInf <| image_comp Prod.snd swap s)

theorem fst_sSup [SupSet α] [SupSet β] (s : Set (α × β)) : (sSup s).fst = sSup (Prod.fst '' s) :=
  rfl

theorem snd_sSup [SupSet α] [SupSet β] (s : Set (α × β)) : (sSup s).snd = sSup (Prod.snd '' s) :=
  rfl

theorem swap_sSup [SupSet α] [SupSet β] (s : Set (α × β)) : (sSup s).swap = sSup (Prod.swap '' s) :=
  Prod.ext (congr_arg sSup <| image_comp Prod.fst swap s)
    (congr_arg sSup <| image_comp Prod.snd swap s)

theorem fst_iInf [InfSet α] [InfSet β] (f : ι → α × β) : (iInf f).fst = ⨅ i, (f i).fst :=
  congr_arg sInf (range_comp _ _).symm

theorem snd_iInf [InfSet α] [InfSet β] (f : ι → α × β) : (iInf f).snd = ⨅ i, (f i).snd :=
  congr_arg sInf (range_comp _ _).symm

theorem swap_iInf [InfSet α] [InfSet β] (f : ι → α × β) : (iInf f).swap = ⨅ i, (f i).swap := by
  simp_rw [iInf, swap_sInf, ← range_comp, comp_def]

theorem iInf_mk [InfSet α] [InfSet β] (f : ι → α) (g : ι → β) :
    ⨅ i, (f i, g i) = (⨅ i, f i, ⨅ i, g i) :=
  congr_arg₂ Prod.mk (fst_iInf _) (snd_iInf _)

theorem fst_iSup [SupSet α] [SupSet β] (f : ι → α × β) : (iSup f).fst = ⨆ i, (f i).fst :=
  congr_arg sSup (range_comp _ _).symm

theorem snd_iSup [SupSet α] [SupSet β] (f : ι → α × β) : (iSup f).snd = ⨆ i, (f i).snd :=
  congr_arg sSup (range_comp _ _).symm

theorem swap_iSup [SupSet α] [SupSet β] (f : ι → α × β) : (iSup f).swap = ⨆ i, (f i).swap := by
  simp_rw [iSup, swap_sSup, ← range_comp, comp_def]

theorem iSup_mk [SupSet α] [SupSet β] (f : ι → α) (g : ι → β) :
    ⨆ i, (f i, g i) = (⨆ i, f i, ⨆ i, g i) :=
  congr_arg₂ Prod.mk (fst_iSup _) (snd_iSup _)

instance instCompleteLattice [CompleteLattice α] [CompleteLattice β] : CompleteLattice (α × β) where
  __ := instBoundedOrder α β
  le_sSup _ _ hab := ⟨le_sSup <| mem_image_of_mem _ hab, le_sSup <| mem_image_of_mem _ hab⟩
  sSup_le _ _ h :=
    ⟨sSup_le <| forall_mem_image.2 fun p hp => (h p hp).1,
      sSup_le <| forall_mem_image.2 fun p hp => (h p hp).2⟩
  sInf_le _ _ hab := ⟨sInf_le <| mem_image_of_mem _ hab, sInf_le <| mem_image_of_mem _ hab⟩
  le_sInf _ _ h :=
    ⟨le_sInf <| forall_mem_image.2 fun p hp => (h p hp).1,
      le_sInf <| forall_mem_image.2 fun p hp => (h p hp).2⟩

end Prod

lemma sInf_prod [InfSet α] [InfSet β] {s : Set α} {t : Set β} (hs : s.Nonempty) (ht : t.Nonempty) :
    sInf (s ×ˢ t) = (sInf s, sInf t) :=
congr_arg₂ Prod.mk (congr_arg sInf <| fst_image_prod _ ht) (congr_arg sInf <| snd_image_prod hs _)

lemma sSup_prod [SupSet α] [SupSet β] {s : Set α} {t : Set β} (hs : s.Nonempty) (ht : t.Nonempty) :
    sSup (s ×ˢ t) = (sSup s, sSup t) :=
congr_arg₂ Prod.mk (congr_arg sSup <| fst_image_prod _ ht) (congr_arg sSup <| snd_image_prod hs _)

-- See note [reducible non-instances]
/-- Pullback a `CompleteLattice` along an injection. -/
protected abbrev Function.Injective.completeLattice [Max α] [Min α] [SupSet α] [InfSet α] [Top α]
    [Bot α] [CompleteLattice β] (f : α → β) (hf : Function.Injective f)
    (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b)
    (map_sSup : ∀ s, f (sSup s) = ⨆ a ∈ s, f a) (map_sInf : ∀ s, f (sInf s) = ⨅ a ∈ s, f a)
    (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥) : CompleteLattice α where
  -- we cannot use BoundedOrder.lift here as the `LE` instance doesn't exist yet
  __ := hf.lattice f map_sup map_inf
  le_sSup _ a h := (le_iSup₂ a h).trans (map_sSup _).ge
  sSup_le _ _ h := (map_sSup _).trans_le <| iSup₂_le h
  sInf_le _ a h := (map_sInf _).trans_le <| iInf₂_le a h
  le_sInf _ _ h := (le_iInf₂ h).trans (map_sInf _).ge
  top := ⊤
  le_top _ := (@le_top β _ _ _).trans map_top.ge
  bot := ⊥
  bot_le _ := map_bot.le.trans bot_le
