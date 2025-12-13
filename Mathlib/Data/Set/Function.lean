/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Andrew Zipperer, Haitao Zhang, Minchao Wu, Yury Kudryashov
-/
module

public import Mathlib.Data.Set.Prod
public import Mathlib.Data.Set.Restrict

/-!
# Functions over sets

This file contains basic results on the following predicates of functions and sets:

* `Set.EqOn f₁ f₂ s` : functions `f₁` and `f₂` are equal at every point of `s`;
* `Set.MapsTo f s t` : `f` sends every point of `s` to a point of `t`;
* `Set.InjOn f s` : restriction of `f` to `s` is injective;
* `Set.SurjOn f s t` : every point in `s` has a preimage in `s`;
* `Set.BijOn f s t` : `f` is a bijection between `s` and `t`;
* `Set.LeftInvOn f' f s` : for every `x ∈ s` we have `f' (f x) = x`;
* `Set.RightInvOn f' f t` : for every `y ∈ t` we have `f (f' y) = y`;
* `Set.InvOn f' f s t` : `f'` is a two-side inverse of `f` on `s` and `t`, i.e.
  we have `Set.LeftInvOn f' f s` and `Set.RightInvOn f' f t`.
-/

@[expose] public section

variable {α β γ δ : Type*} {ι : Sort*} {π : α → Type*}

open Equiv Equiv.Perm Function

namespace Set

/-! ### Equality on a set -/
section equality

variable {s s₁ s₂ : Set α} {f₁ f₂ f₃ : α → β} {g : β → γ} {a : α}

/-- This lemma exists for use by `grind`/`aesop` as a forward rule. -/
@[aesop safe forward, grind →]
lemma EqOn.eq_of_mem (h : s.EqOn f₁ f₂) (ha : a ∈ s) : f₁ a = f₂ a :=
  h ha

@[simp]
theorem eqOn_empty (f₁ f₂ : α → β) : EqOn f₁ f₂ ∅ := fun _ => False.elim

@[simp]
theorem eqOn_singleton : Set.EqOn f₁ f₂ {a} ↔ f₁ a = f₂ a := by
  simp [Set.EqOn]

@[simp]
theorem eqOn_univ (f₁ f₂ : α → β) : EqOn f₁ f₂ univ ↔ f₁ = f₂ := by
  simp [EqOn, funext_iff]

@[symm]
theorem EqOn.symm (h : EqOn f₁ f₂ s) : EqOn f₂ f₁ s := fun _ hx => (h hx).symm

theorem eqOn_comm : EqOn f₁ f₂ s ↔ EqOn f₂ f₁ s :=
  ⟨EqOn.symm, EqOn.symm⟩

-- This cannot be tagged as `@[refl]` with the current argument order.
-- See note below at `EqOn.trans`.
theorem eqOn_refl (f : α → β) (s : Set α) : EqOn f f s := fun _ _ => rfl

-- Note: this was formerly tagged with `@[trans]`, and although the `trans` attribute accepted it
-- the `trans` tactic could not use it.
-- An update to the trans tactic coming in https://github.com/leanprover-community/mathlib4/pull/7014 will reject this attribute.
-- It can be restored by changing the argument order from `EqOn f₁ f₂ s` to `EqOn s f₁ f₂`.
-- This change will be made separately: [zulip](https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Reordering.20arguments.20of.20.60Set.2EEqOn.60/near/390467581).
theorem EqOn.trans (h₁ : EqOn f₁ f₂ s) (h₂ : EqOn f₂ f₃ s) : EqOn f₁ f₃ s := fun _ hx =>
  (h₁ hx).trans (h₂ hx)

theorem EqOn.image_eq (heq : EqOn f₁ f₂ s) : f₁ '' s = f₂ '' s := by grind

/-- Variant of `EqOn.image_eq`, for one function being the identity. -/
theorem EqOn.image_eq_self {f : α → α} (h : Set.EqOn f id s) : f '' s = s := by grind

theorem EqOn.inter_preimage_eq (heq : EqOn f₁ f₂ s) (t : Set β) : s ∩ f₁ ⁻¹' t = s ∩ f₂ ⁻¹' t := by
  grind

theorem EqOn.mono (hs : s₁ ⊆ s₂) (hf : EqOn f₁ f₂ s₂) : EqOn f₁ f₂ s₁ := fun _ hx => hf (hs hx)

@[simp]
theorem eqOn_union : EqOn f₁ f₂ (s₁ ∪ s₂) ↔ EqOn f₁ f₂ s₁ ∧ EqOn f₁ f₂ s₂ :=
  forall₂_or_left

theorem EqOn.union (h₁ : EqOn f₁ f₂ s₁) (h₂ : EqOn f₁ f₂ s₂) : EqOn f₁ f₂ (s₁ ∪ s₂) :=
  eqOn_union.2 ⟨h₁, h₂⟩

theorem EqOn.comp_left (h : s.EqOn f₁ f₂) : s.EqOn (g ∘ f₁) (g ∘ f₂) := fun _ ha =>
  congr_arg _ <| h ha

theorem EqOn.comp_left₂ {α β δ γ} {op : α → β → δ} {a₁ a₂ : γ → α}
    {b₁ b₂ : γ → β} {s : Set γ} (ha : s.EqOn a₁ a₂) (hb : s.EqOn b₁ b₂) :
    s.EqOn (fun x ↦ op (a₁ x) (b₁ x)) (fun x ↦ op (a₂ x) (b₂ x)) :=
  fun _ hx ↦ congr_arg₂ _ (ha hx) (hb hx)

@[simp]
theorem eqOn_range {ι : Sort*} {f : ι → α} {g₁ g₂ : α → β} :
    EqOn g₁ g₂ (range f) ↔ g₁ ∘ f = g₂ ∘ f :=
  forall_mem_range.trans <| funext_iff.symm

alias ⟨EqOn.comp_eq, _⟩ := eqOn_range

end equality

variable {s s₁ s₂ : Set α} {t t₁ t₂ : Set β} {p : Set γ} {f f₁ f₂ : α → β} {g g₁ g₂ : β → γ}
  {f' f₁' f₂' : β → α} {g' : γ → β} {a : α} {b : β}

section MapsTo

theorem mapsTo_iff_image_subset : MapsTo f s t ↔ f '' s ⊆ t :=
  image_subset_iff.symm

@[deprecated (since := "2025-08-30")] alias mapsTo' := mapsTo_iff_image_subset

theorem mapsTo_prodMap_diagonal : MapsTo (Prod.map f f) (diagonal α) (diagonal β) :=
  diagonal_subset_iff.2 fun _ => rfl

theorem MapsTo.subset_preimage (hf : MapsTo f s t) : s ⊆ f ⁻¹' t := hf

theorem mapsTo_iff_subset_preimage : MapsTo f s t ↔ s ⊆ f ⁻¹' t := Iff.rfl

@[simp]
theorem mapsTo_singleton {x : α} : MapsTo f {x} t ↔ f x ∈ t :=
  singleton_subset_iff

theorem mapsTo_empty (f : α → β) (t : Set β) : MapsTo f ∅ t :=
  empty_subset _

@[simp] theorem mapsTo_empty_iff : MapsTo f s ∅ ↔ s = ∅ := by
  simp [mapsTo_iff_image_subset, subset_empty_iff]

/-- If `f` maps `s` to `t` and `s` is non-empty, `t` is non-empty. -/
theorem MapsTo.nonempty (h : MapsTo f s t) (hs : s.Nonempty) : t.Nonempty :=
  (hs.image f).mono (mapsTo_iff_image_subset.mp h)

theorem MapsTo.image_subset (h : MapsTo f s t) : f '' s ⊆ t :=
  mapsTo_iff_image_subset.1 h

theorem MapsTo.congr (h₁ : MapsTo f₁ s t) (h : EqOn f₁ f₂ s) : MapsTo f₂ s t := fun _ hx =>
  h hx ▸ h₁ hx

theorem EqOn.comp_right (hg : t.EqOn g₁ g₂) (hf : s.MapsTo f t) : s.EqOn (g₁ ∘ f) (g₂ ∘ f) :=
  fun _ ha => hg <| hf ha

theorem EqOn.mapsTo_iff (H : EqOn f₁ f₂ s) : MapsTo f₁ s t ↔ MapsTo f₂ s t :=
  ⟨fun h => h.congr H, fun h => h.congr H.symm⟩

theorem MapsTo.comp (h₁ : MapsTo g t p) (h₂ : MapsTo f s t) : MapsTo (g ∘ f) s p := fun _ h =>
  h₁ (h₂ h)

theorem mapsTo_id (s : Set α) : MapsTo id s s := fun _ => id

theorem MapsTo.iterate {f : α → α} {s : Set α} (h : MapsTo f s s) : ∀ n, MapsTo f^[n] s s
  | 0 => fun _ => id
  | n + 1 => (MapsTo.iterate h n).comp h

theorem MapsTo.iterate_restrict {f : α → α} {s : Set α} (h : MapsTo f s s) (n : ℕ) :
    (h.restrict f s s)^[n] = (h.iterate n).restrict _ _ _ := by
  ext
  simpa using coe_iterate_restrict _ _ _

lemma mapsTo_of_subsingleton' [Subsingleton β] (f : α → β) (h : s.Nonempty → t.Nonempty) :
    MapsTo f s t :=
  fun a ha ↦ Subsingleton.mem_iff_nonempty.2 <| h ⟨a, ha⟩

lemma mapsTo_of_subsingleton [Subsingleton α] (f : α → α) (s : Set α) : MapsTo f s s :=
  mapsTo_of_subsingleton' _ id

theorem MapsTo.mono (hf : MapsTo f s₁ t₁) (hs : s₂ ⊆ s₁) (ht : t₁ ⊆ t₂) : MapsTo f s₂ t₂ :=
  fun _ hx => ht (hf <| hs hx)

theorem MapsTo.mono_left (hf : MapsTo f s₁ t) (hs : s₂ ⊆ s₁) : MapsTo f s₂ t := fun _ hx =>
  hf (hs hx)

theorem MapsTo.mono_right (hf : MapsTo f s t₁) (ht : t₁ ⊆ t₂) : MapsTo f s t₂ := fun _ hx =>
  ht (hf hx)

theorem MapsTo.union_union (h₁ : MapsTo f s₁ t₁) (h₂ : MapsTo f s₂ t₂) :
    MapsTo f (s₁ ∪ s₂) (t₁ ∪ t₂) := fun _ hx =>
  hx.elim (fun hx => Or.inl <| h₁ hx) fun hx => Or.inr <| h₂ hx

theorem MapsTo.union (h₁ : MapsTo f s₁ t) (h₂ : MapsTo f s₂ t) : MapsTo f (s₁ ∪ s₂) t :=
  union_self t ▸ h₁.union_union h₂

@[simp]
theorem mapsTo_union : MapsTo f (s₁ ∪ s₂) t ↔ MapsTo f s₁ t ∧ MapsTo f s₂ t :=
  ⟨fun h =>
    ⟨h.mono subset_union_left (Subset.refl t),
      h.mono subset_union_right (Subset.refl t)⟩,
    fun h => h.1.union h.2⟩

theorem MapsTo.inter (h₁ : MapsTo f s t₁) (h₂ : MapsTo f s t₂) : MapsTo f s (t₁ ∩ t₂) := fun _ hx =>
  ⟨h₁ hx, h₂ hx⟩

lemma MapsTo.insert (h : MapsTo f s t) (x : α) : MapsTo f (insert x s) (insert (f x) t) := by
  simpa [← singleton_union] using h.mono_right subset_union_right

theorem MapsTo.inter_inter (h₁ : MapsTo f s₁ t₁) (h₂ : MapsTo f s₂ t₂) :
    MapsTo f (s₁ ∩ s₂) (t₁ ∩ t₂) := fun _ hx => ⟨h₁ hx.1, h₂ hx.2⟩

@[simp]
theorem mapsTo_inter : MapsTo f s (t₁ ∩ t₂) ↔ MapsTo f s t₁ ∧ MapsTo f s t₂ :=
  ⟨fun h =>
    ⟨h.mono (Subset.refl s) inter_subset_left,
      h.mono (Subset.refl s) inter_subset_right⟩,
    fun h => h.1.inter h.2⟩

theorem mapsTo_univ (f : α → β) (s : Set α) : MapsTo f s univ := fun _ _ => trivial

theorem mapsTo_range (f : α → β) (s : Set α) : MapsTo f s (range f) :=
  (mapsTo_image f s).mono (Subset.refl s) (image_subset_range _ _)

@[simp]
theorem mapsTo_image_iff {f : α → β} {g : γ → α} {s : Set γ} {t : Set β} :
    MapsTo f (g '' s) t ↔ MapsTo (f ∘ g) s t :=
  ⟨fun h c hc => h ⟨c, hc, rfl⟩, fun h _ ⟨_, hc⟩ => hc.2 ▸ h hc.1⟩

lemma MapsTo.comp_left (g : β → γ) (hf : MapsTo f s t) : MapsTo (g ∘ f) s (g '' t) :=
  fun x hx ↦ ⟨f x, hf hx, rfl⟩

lemma MapsTo.comp_right {s : Set β} {t : Set γ} (hg : MapsTo g s t) (f : α → β) :
    MapsTo (g ∘ f) (f ⁻¹' s) t := fun _ hx ↦ hg hx

@[simp]
lemma mapsTo_univ_iff : MapsTo f univ t ↔ ∀ x, f x ∈ t :=
  ⟨fun h _ => h (mem_univ _), fun h x _ => h x⟩

@[simp]
lemma mapsTo_range_iff {g : ι → α} : MapsTo f (range g) t ↔ ∀ i, f (g i) ∈ t :=
  forall_mem_range

theorem MapsTo.mem_iff (h : MapsTo f s t) (hc : MapsTo f sᶜ tᶜ) {x} : f x ∈ t ↔ x ∈ s :=
  ⟨fun ht => by_contra fun hs => hc hs ht, fun hx => h hx⟩

end MapsTo

/-! ### Injectivity on a set -/
section injOn

theorem Subsingleton.injOn (hs : s.Subsingleton) (f : α → β) : InjOn f s := fun _ hx _ hy _ =>
  hs hx hy

@[simp]
theorem injOn_empty (f : α → β) : InjOn f ∅ :=
  subsingleton_empty.injOn f
@[simp]
theorem injOn_singleton (f : α → β) (a : α) : InjOn f {a} :=
  subsingleton_singleton.injOn f

@[simp] lemma injOn_pair {b : α} : InjOn f {a, b} ↔ f a = f b → a = b := by unfold InjOn; aesop

@[simp low] lemma injOn_of_eq_iff_eq (s : Set α) (h : ∀ x y, f x = f y ↔ x = y) : Set.InjOn f s :=
  fun x _ y _ => (h x y).mp

theorem InjOn.eq_iff {x y} (h : InjOn f s) (hx : x ∈ s) (hy : y ∈ s) : f x = f y ↔ x = y :=
  ⟨h hx hy, fun h => h ▸ rfl⟩

theorem InjOn.ne_iff {x y} (h : InjOn f s) (hx : x ∈ s) (hy : y ∈ s) : f x ≠ f y ↔ x ≠ y :=
  (h.eq_iff hx hy).not

alias ⟨_, InjOn.ne⟩ := InjOn.ne_iff

theorem InjOn.congr (h₁ : InjOn f₁ s) (h : EqOn f₁ f₂ s) : InjOn f₂ s := fun _ hx _ hy =>
  h hx ▸ h hy ▸ h₁ hx hy

theorem EqOn.injOn_iff (H : EqOn f₁ f₂ s) : InjOn f₁ s ↔ InjOn f₂ s :=
  ⟨fun h => h.congr H, fun h => h.congr H.symm⟩

theorem InjOn.mono (h : s₁ ⊆ s₂) (ht : InjOn f s₂) : InjOn f s₁ := fun _ hx _ hy H =>
  ht (h hx) (h hy) H

theorem injOn_union (h : Disjoint s₁ s₂) :
    InjOn f (s₁ ∪ s₂) ↔ InjOn f s₁ ∧ InjOn f s₂ ∧ ∀ x ∈ s₁, ∀ y ∈ s₂, f x ≠ f y := by
  refine ⟨fun H => ⟨H.mono subset_union_left, H.mono subset_union_right, ?_⟩, ?_⟩
  · intro x hx y hy hxy
    obtain rfl : x = y := H (Or.inl hx) (Or.inr hy) hxy
    exact h.le_bot ⟨hx, hy⟩
  · rintro ⟨h₁, h₂, h₁₂⟩
    rintro x (hx | hx) y (hy | hy) hxy
    exacts [h₁ hx hy hxy, (h₁₂ _ hx _ hy hxy).elim, (h₁₂ _ hy _ hx hxy.symm).elim, h₂ hx hy hxy]

theorem injOn_insert {f : α → β} {s : Set α} {a : α} (has : a ∉ s) :
    Set.InjOn f (insert a s) ↔ Set.InjOn f s ∧ f a ∉ f '' s := by
  rw [← union_singleton, injOn_union (disjoint_singleton_right.2 has)]
  simp

@[simp] lemma injOn_univ : InjOn f univ ↔ Injective f := by simp [InjOn, Injective]

@[deprecated injOn_univ (since := "2025-10-27")]
theorem injective_iff_injOn_univ : Injective f ↔ InjOn f univ := injOn_univ.symm

theorem injOn_of_injective (h : Injective f) {s : Set α} : InjOn f s := fun _ _ _ _ hxy => h hxy

alias _root_.Function.Injective.injOn := injOn_of_injective

-- A specialization of `injOn_of_injective` for `Subtype.val`.
theorem injOn_subtype_val {s : Set { x // p x }} : Set.InjOn Subtype.val s :=
  Subtype.coe_injective.injOn

lemma injOn_id (s : Set α) : InjOn id s := injective_id.injOn

theorem InjOn.comp (hg : InjOn g t) (hf : InjOn f s) (h : MapsTo f s t) : InjOn (g ∘ f) s :=
  fun _ hx _ hy heq => hf hx hy <| hg (h hx) (h hy) heq

lemma InjOn.of_comp (h : InjOn (g ∘ f) s) : InjOn f s :=
  fun _ hx _ hy heq ↦ h hx hy (by simp [heq])

lemma InjOn.image_of_comp (h : InjOn (g ∘ f) s) : InjOn g (f '' s) :=
  forall_mem_image.2 fun _x hx ↦ forall_mem_image.2 fun _y hy heq ↦ congr_arg f <| h hx hy heq

lemma InjOn.comp_iff (hf : InjOn f s) : InjOn (g ∘ f) s ↔ InjOn g (f '' s) :=
  ⟨image_of_comp, fun h ↦ InjOn.comp h hf <| mapsTo_image f s⟩

lemma InjOn.iterate {f : α → α} {s : Set α} (h : InjOn f s) (hf : MapsTo f s s) :
    ∀ n, InjOn f^[n] s
  | 0 => injOn_id _
  | (n + 1) => (h.iterate hf n).comp h hf

lemma injOn_of_subsingleton [Subsingleton α] (f : α → β) (s : Set α) : InjOn f s :=
  (injective_of_subsingleton _).injOn

theorem _root_.Function.Injective.injOn_range (h : Injective (g ∘ f)) : InjOn g (range f) := by
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ H
  exact congr_arg f (h H)

theorem _root_.Set.InjOn.injective_iff (s : Set β) (h : InjOn g s) (hs : range f ⊆ s) :
    Injective (g ∘ f) ↔ Injective f :=
  ⟨(·.of_comp), fun h _ ↦ by aesop⟩

theorem exists_injOn_iff_injective [Nonempty β] :
    (∃ f : α → β, InjOn f s) ↔ ∃ f : s → β, Injective f :=
  ⟨fun ⟨_, hf⟩ => ⟨_, hf.injective⟩,
   fun ⟨f, hf⟩ => by
    lift f to α → β using trivial
    exact ⟨f, injOn_iff_injective.2 hf⟩⟩

theorem injOn_preimage {B : Set (Set β)} (hB : B ⊆ 𝒫 range f) : InjOn (preimage f) B :=
  fun _ hs _ ht hst => (preimage_eq_preimage' (hB hs) (hB ht)).1 hst

theorem InjOn.mem_of_mem_image {x} (hf : InjOn f s) (hs : s₁ ⊆ s) (h : x ∈ s) (h₁ : f x ∈ f '' s₁) :
    x ∈ s₁ :=
  let ⟨_, h', Eq⟩ := h₁
  hf (hs h') h Eq ▸ h'

theorem InjOn.mem_image_iff {x} (hf : InjOn f s) (hs : s₁ ⊆ s) (hx : x ∈ s) :
    f x ∈ f '' s₁ ↔ x ∈ s₁ :=
  ⟨hf.mem_of_mem_image hs hx, mem_image_of_mem f⟩

theorem InjOn.preimage_image_inter (hf : InjOn f s) (hs : s₁ ⊆ s) : f ⁻¹' (f '' s₁) ∩ s = s₁ :=
  ext fun _ => ⟨fun ⟨h₁, h₂⟩ => hf.mem_of_mem_image hs h₂ h₁, fun h => ⟨mem_image_of_mem _ h, hs h⟩⟩

theorem EqOn.cancel_left (h : s.EqOn (g ∘ f₁) (g ∘ f₂)) (hg : t.InjOn g) (hf₁ : s.MapsTo f₁ t)
    (hf₂ : s.MapsTo f₂ t) : s.EqOn f₁ f₂ := fun _ ha => hg (hf₁ ha) (hf₂ ha) (h ha)

theorem InjOn.cancel_left (hg : t.InjOn g) (hf₁ : s.MapsTo f₁ t) (hf₂ : s.MapsTo f₂ t) :
    s.EqOn (g ∘ f₁) (g ∘ f₂) ↔ s.EqOn f₁ f₂ :=
  ⟨fun h => h.cancel_left hg hf₁ hf₂, EqOn.comp_left⟩

lemma InjOn.image_inter {s t u : Set α} (hf : u.InjOn f) (hs : s ⊆ u) (ht : t ⊆ u) :
    f '' (s ∩ t) = f '' s ∩ f '' t := by
  apply Subset.antisymm (image_inter_subset _ _ _)
  intro x ⟨⟨y, ys, hy⟩, ⟨z, zt, hz⟩⟩
  have : y = z := by
    apply hf (hs ys) (ht zt)
    rwa [← hz] at hy
  rw [← this] at zt
  exact ⟨y, ⟨ys, zt⟩, hy⟩

lemma InjOn.image (h : s.InjOn f) : s.powerset.InjOn (image f) :=
  fun s₁ hs₁ s₂ hs₂ h' ↦ by rw [← h.preimage_image_inter hs₁, h', h.preimage_image_inter hs₂]

theorem InjOn.image_eq_image_iff (h : s.InjOn f) (h₁ : s₁ ⊆ s) (h₂ : s₂ ⊆ s) :
    f '' s₁ = f '' s₂ ↔ s₁ = s₂ :=
  h.image.eq_iff h₁ h₂

lemma InjOn.image_subset_image_iff (h : s.InjOn f) (h₁ : s₁ ⊆ s) (h₂ : s₂ ⊆ s) :
    f '' s₁ ⊆ f '' s₂ ↔ s₁ ⊆ s₂ := by
  refine ⟨fun h' ↦ ?_, image_mono⟩
  rw [← h.preimage_image_inter h₁, ← h.preimage_image_inter h₂]
  exact inter_subset_inter_left _ (preimage_mono h')

lemma InjOn.image_ssubset_image_iff (h : s.InjOn f) (h₁ : s₁ ⊆ s) (h₂ : s₂ ⊆ s) :
    f '' s₁ ⊂ f '' s₂ ↔ s₁ ⊂ s₂ := by
  simp_rw [ssubset_def, h.image_subset_image_iff h₁ h₂, h.image_subset_image_iff h₂ h₁]

-- TODO: can this move to a better place?
theorem _root_.Disjoint.image {s t u : Set α} {f : α → β} (h : Disjoint s t) (hf : u.InjOn f)
    (hs : s ⊆ u) (ht : t ⊆ u) : Disjoint (f '' s) (f '' t) := by
  rw [disjoint_iff_inter_eq_empty] at h ⊢
  rw [← hf.image_inter hs ht, h, image_empty]

lemma InjOn.image_diff {t : Set α} (h : s.InjOn f) : f '' (s \ t) = f '' s \ f '' (s ∩ t) := by
  refine subset_antisymm (subset_diff.2 ⟨image_mono diff_subset, ?_⟩)
    (diff_subset_iff.2 (by rw [← image_union, inter_union_diff]))
  exact Disjoint.image disjoint_sdiff_inter h diff_subset inter_subset_left

lemma InjOn.image_diff_subset {f : α → β} {t : Set α} (h : InjOn f s) (hst : t ⊆ s) :
    f '' (s \ t) = f '' s \ f '' t := by
  rw [h.image_diff, inter_eq_self_of_subset_right hst]

alias image_diff_of_injOn := InjOn.image_diff_subset

theorem InjOn.imageFactorization_injective (h : InjOn f s) :
    Injective (s.imageFactorization f) :=
  fun ⟨x, hx⟩ ⟨y, hy⟩ h' ↦ by simpa [imageFactorization, h.eq_iff hx hy] using h'

@[simp] theorem imageFactorization_injective_iff : Injective (s.imageFactorization f) ↔ InjOn f s :=
  ⟨fun h x hx y hy _ ↦ by simpa using @h ⟨x, hx⟩ ⟨y, hy⟩ (by simpa [imageFactorization]),
    InjOn.imageFactorization_injective⟩

end injOn

section graphOn
variable {x : α × β}

@[simp] lemma mem_graphOn : x ∈ s.graphOn f ↔ x.1 ∈ s ∧ f x.1 = x.2 := .rfl

lemma graphOn_eq_image (s : Set α) (f : α → β) : s.graphOn f = (fun x ↦ (x, f x)) '' s := by
  aesop (add simp graphOn)

@[simp] lemma graphOn_empty (f : α → β) : graphOn f ∅ = ∅ := by simp [graphOn]
@[simp] lemma graphOn_eq_empty : graphOn f s = ∅ ↔ s = ∅ := by simp [graphOn_eq_image]
@[simp] lemma graphOn_nonempty : (s.graphOn f).Nonempty ↔ s.Nonempty := by simp [graphOn_eq_image]

protected alias ⟨_, Nonempty.graphOn⟩ := graphOn_nonempty

lemma graphOn_union (f : α → β) (s t : Set α) : graphOn f (s ∪ t) = graphOn f s ∪ graphOn f t := by
  simp [graphOn_eq_image, image_union]

@[simp]
lemma graphOn_singleton (f : α → β) (x : α) : graphOn f {x} = {(x, f x)} := by
  simp [graphOn_eq_image]


@[simp]
lemma graphOn_insert (f : α → β) (x : α) (s : Set α) :
    graphOn f (insert x s) = insert (x, f x) (graphOn f s) := by
  simp [graphOn_eq_image, image_insert_eq]

@[simp]
lemma image_fst_graphOn (f : α → β) (s : Set α) : Prod.fst '' graphOn f s = s := by
  simp [graphOn_eq_image, image_image]

@[simp] lemma image_snd_graphOn (f : α → β) : Prod.snd '' s.graphOn f = f '' s := by ext x; simp

lemma fst_injOn_graph : (s.graphOn f).InjOn Prod.fst := by aesop (add simp InjOn)

lemma graphOn_comp (s : Set α) (f : α → β) (g : β → γ) :
    s.graphOn (g ∘ f) = (fun x ↦ (x.1, g x.2)) '' s.graphOn f := by
  simpa [graphOn_eq_image] using image_comp (fun x ↦ (x.1, g x.2)) (fun x ↦ (x, f x)) _

lemma graphOn_univ_eq_range : univ.graphOn f = range fun x ↦ (x, f x) := by simp [graphOn_eq_image]

@[simp] lemma graphOn_inj {g : α → β} : s.graphOn f = s.graphOn g ↔ s.EqOn f g := by
  simp [Set.ext_iff, funext_iff, forall_swap, EqOn]

lemma graphOn_univ_inj {g : α → β} : univ.graphOn f = univ.graphOn g ↔ f = g := by simp

lemma graphOn_univ_injective : Injective (univ.graphOn : (α → β) → Set (α × β)) :=
  fun _f _g ↦ graphOn_univ_inj.1

lemma exists_eq_graphOn_image_fst [Nonempty β] {s : Set (α × β)} :
    (∃ f : α → β, s = graphOn f (Prod.fst '' s)) ↔ InjOn Prod.fst s := by
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨f, hf⟩
    rw [hf, graphOn_eq_image]
    exact InjOn.image_of_comp <| injOn_id _
  · have : ∀ x ∈ Prod.fst '' s, ∃ y, (x, y) ∈ s := forall_mem_image.2 fun (x, y) h ↦ ⟨y, h⟩
    choose! f hf using this
    rw [forall_mem_image] at hf
    use f
    rw [graphOn_eq_image, image_image, EqOn.image_eq_self]
    exact fun x hx ↦ h (hf hx) hx rfl

lemma exists_eq_graphOn [Nonempty β] {s : Set (α × β)} :
    (∃ f t, s = graphOn f t) ↔ InjOn Prod.fst s :=
  .trans ⟨fun ⟨f, t, hs⟩ ↦ ⟨f, by rw [hs, image_fst_graphOn]⟩, fun ⟨f, hf⟩ ↦ ⟨f, _, hf⟩⟩
    exists_eq_graphOn_image_fst

lemma graphOn_prod_graphOn (s : Set α) (t : Set β) (f : α → γ) (g : β → δ) :
    s.graphOn f ×ˢ t.graphOn g = Equiv.prodProdProdComm .. ⁻¹' (s ×ˢ t).graphOn (Prod.map f g) := by
  aesop

lemma graphOn_prod_prodMap (s : Set α) (t : Set β) (f : α → γ) (g : β → δ) :
    (s ×ˢ t).graphOn (Prod.map f g) = Equiv.prodProdProdComm .. ⁻¹' s.graphOn f ×ˢ t.graphOn g := by
  aesop

lemma forall_mem_graphOn {α β : Type*} {f : α → β} {s : Set α} {p : α × β → Prop} :
    (∀ y ∈ s.graphOn f, p y) ↔ ∀ ⦃x : α⦄, x ∈ s → p (x, f x) := by
  rw [graphOn_eq_image, forall_mem_image]

lemma exists_mem_graphOn {α β : Type*} {f : α → β} {s : Set α} {p : α × β → Prop} :
    (∃ y ∈ s.graphOn f, p y) ↔ ∃ x ∈ s, p (x, f x) := by
  rw [graphOn_eq_image, exists_mem_image]

end graphOn

/-! ### Surjectivity on a set -/
section surjOn

theorem SurjOn.subset_range (h : SurjOn f s t) : t ⊆ range f :=
  Subset.trans h <| image_subset_range f s

theorem surjOn_iff_exists_map_subtype :
    SurjOn f s t ↔ ∃ (t' : Set β) (g : s → t'), t ⊆ t' ∧ Surjective g ∧ ∀ x : s, f x = g x :=
  ⟨fun h =>
    ⟨_, (mapsTo_image f s).restrict f s _, h, surjective_mapsTo_image_restrict _ _, fun _ => rfl⟩,
    fun ⟨t', g, htt', hg, hfg⟩ y hy =>
    let ⟨x, hx⟩ := hg ⟨y, htt' hy⟩
    ⟨x, x.2, by rw [hfg, hx, Subtype.coe_mk]⟩⟩

theorem surjOn_empty (f : α → β) (s : Set α) : SurjOn f s ∅ :=
  empty_subset _

@[simp] theorem surjOn_empty_iff : SurjOn f ∅ t ↔ t = ∅ := by
  simp [SurjOn, subset_empty_iff]

@[simp] lemma surjOn_singleton : SurjOn f s {b} ↔ b ∈ f '' s := singleton_subset_iff

@[simp] lemma surjOn_univ_of_subsingleton_nonempty [Subsingleton β] [Nonempty β] :
    SurjOn f s univ ↔ s.Nonempty := by
  cases nonempty_unique β; simp [univ_unique, Subsingleton.elim (f _) default, Set.Nonempty]

theorem surjOn_image (f : α → β) (s : Set α) : SurjOn f s (f '' s) :=
  Subset.rfl

theorem SurjOn.comap_nonempty (h : SurjOn f s t) (ht : t.Nonempty) : s.Nonempty :=
  (ht.mono h).of_image

theorem SurjOn.congr (h : SurjOn f₁ s t) (H : EqOn f₁ f₂ s) : SurjOn f₂ s t := by
  rwa [SurjOn, ← H.image_eq]

theorem EqOn.surjOn_iff (h : EqOn f₁ f₂ s) : SurjOn f₁ s t ↔ SurjOn f₂ s t :=
  ⟨fun H => H.congr h, fun H => H.congr h.symm⟩

theorem SurjOn.mono (hs : s₁ ⊆ s₂) (ht : t₁ ⊆ t₂) (hf : SurjOn f s₁ t₂) : SurjOn f s₂ t₁ :=
  Subset.trans ht <| Subset.trans hf <| image_mono hs

theorem SurjOn.union (h₁ : SurjOn f s t₁) (h₂ : SurjOn f s t₂) : SurjOn f s (t₁ ∪ t₂) := fun _ hx =>
  hx.elim (fun hx => h₁ hx) fun hx => h₂ hx

theorem SurjOn.union_union (h₁ : SurjOn f s₁ t₁) (h₂ : SurjOn f s₂ t₂) :
    SurjOn f (s₁ ∪ s₂) (t₁ ∪ t₂) :=
  (h₁.mono subset_union_left (Subset.refl _)).union
    (h₂.mono subset_union_right (Subset.refl _))

theorem SurjOn.inter_inter (h₁ : SurjOn f s₁ t₁) (h₂ : SurjOn f s₂ t₂) (h : InjOn f (s₁ ∪ s₂)) :
    SurjOn f (s₁ ∩ s₂) (t₁ ∩ t₂) := by
  intro y hy
  rcases h₁ hy.1 with ⟨x₁, hx₁, rfl⟩
  rcases h₂ hy.2 with ⟨x₂, hx₂, heq⟩
  obtain rfl : x₁ = x₂ := h (Or.inl hx₁) (Or.inr hx₂) heq.symm
  exact mem_image_of_mem f ⟨hx₁, hx₂⟩

theorem SurjOn.inter (h₁ : SurjOn f s₁ t) (h₂ : SurjOn f s₂ t) (h : InjOn f (s₁ ∪ s₂)) :
    SurjOn f (s₁ ∩ s₂) t :=
  inter_self t ▸ h₁.inter_inter h₂ h

lemma surjOn_id (s : Set α) : SurjOn id s s := by simp [SurjOn]

theorem SurjOn.comp (hg : SurjOn g t p) (hf : SurjOn f s t) : SurjOn (g ∘ f) s p :=
  Subset.trans hg <| Subset.trans (image_mono hf) <| image_comp g f s ▸ Subset.refl _

lemma SurjOn.of_comp (h : SurjOn (g ∘ f) s p) (hr : MapsTo f s t) : SurjOn g t p := by
  intro z hz
  obtain ⟨x, hx, rfl⟩ := h hz
  exact ⟨f x, hr hx, rfl⟩

lemma surjOn_comp_iff : SurjOn (g ∘ f) s p ↔ SurjOn g (f '' s) p :=
  ⟨fun h ↦ h.of_comp <| mapsTo_image f s, fun h ↦ h.comp <| surjOn_image _ _⟩

lemma SurjOn.iterate {f : α → α} {s : Set α} (h : SurjOn f s s) : ∀ n, SurjOn f^[n] s s
  | 0 => surjOn_id _
  | (n + 1) => (h.iterate n).comp h

lemma SurjOn.comp_left (hf : SurjOn f s t) (g : β → γ) : SurjOn (g ∘ f) s (g '' t) := by
  rw [SurjOn, image_comp g f]; exact image_mono hf

lemma SurjOn.comp_right {s : Set β} {t : Set γ} (hf : Surjective f) (hg : SurjOn g s t) :
    SurjOn (g ∘ f) (f ⁻¹' s) t := by
  rwa [SurjOn, image_comp g f, image_preimage_eq _ hf]

lemma surjOn_of_subsingleton' [Subsingleton β] (f : α → β) (h : t.Nonempty → s.Nonempty) :
    SurjOn f s t :=
  fun _ ha ↦ Subsingleton.mem_iff_nonempty.2 <| (h ⟨_, ha⟩).image _

lemma surjOn_of_subsingleton [Subsingleton α] (f : α → α) (s : Set α) : SurjOn f s s :=
  surjOn_of_subsingleton' _ id

@[simp] lemma surjOn_univ : SurjOn f univ univ ↔ Surjective f := by
  simp [Surjective, SurjOn, subset_def]

protected lemma _root_.Function.Surjective.surjOn (hf : Surjective f) : SurjOn f univ t :=
  (surjOn_univ.2 hf).mono .rfl (subset_univ _)

lemma SurjOn.surjective (hf : SurjOn f s .univ) : f.Surjective :=
  surjOn_univ.1 <| hf.mono s.subset_univ .rfl

@[deprecated surjOn_univ (since := "2025-10-31")]
theorem surjective_iff_surjOn_univ : Surjective f ↔ SurjOn f univ univ := surjOn_univ.symm

theorem SurjOn.image_eq_of_mapsTo (h₁ : SurjOn f s t) (h₂ : MapsTo f s t) : f '' s = t :=
  eq_of_subset_of_subset h₂.image_subset h₁

theorem image_eq_iff_surjOn_mapsTo : f '' s = t ↔ s.SurjOn f t ∧ s.MapsTo f t := by
  refine ⟨?_, fun h => h.1.image_eq_of_mapsTo h.2⟩
  rintro rfl
  exact ⟨s.surjOn_image f, s.mapsTo_image f⟩

lemma SurjOn.image_preimage (h : Set.SurjOn f s t) (ht : t₁ ⊆ t) : f '' (f ⁻¹' t₁) = t₁ :=
  image_preimage_eq_iff.2 fun _ hx ↦ mem_range_of_mem_image f s <| h <| ht hx

theorem SurjOn.mapsTo_compl (h : SurjOn f s t) (h' : Injective f) : MapsTo f sᶜ tᶜ :=
  fun _ hs ht =>
  let ⟨_, hx', HEq⟩ := h ht
  hs <| h' HEq ▸ hx'

theorem MapsTo.surjOn_compl (h : MapsTo f s t) (h' : Surjective f) : SurjOn f sᶜ tᶜ :=
  h'.forall.2 fun _ ht => (mem_image_of_mem _) fun hs => ht (h hs)

theorem EqOn.cancel_right (hf : s.EqOn (g₁ ∘ f) (g₂ ∘ f)) (hf' : s.SurjOn f t) : t.EqOn g₁ g₂ := by
  intro b hb
  obtain ⟨a, ha, rfl⟩ := hf' hb
  exact hf ha

theorem SurjOn.cancel_right (hf : s.SurjOn f t) (hf' : s.MapsTo f t) :
    s.EqOn (g₁ ∘ f) (g₂ ∘ f) ↔ t.EqOn g₁ g₂ :=
  ⟨fun h => h.cancel_right hf, fun h => h.comp_right hf'⟩

theorem eqOn_comp_right_iff : s.EqOn (g₁ ∘ f) (g₂ ∘ f) ↔ (f '' s).EqOn g₁ g₂ :=
  (s.surjOn_image f).cancel_right <| s.mapsTo_image f

theorem SurjOn.forall {p : β → Prop} (hf : s.SurjOn f t) (hf' : s.MapsTo f t) :
    (∀ y ∈ t, p y) ↔ (∀ x ∈ s, p (f x)) :=
  ⟨fun H x hx ↦ H (f x) (hf' hx), fun H _y hy ↦ let ⟨x, hx, hxy⟩ := hf hy; hxy ▸ H x hx⟩

theorem _root_.Subtype.coind_surjective {α β} {f : α → β} {p : Set β} (h : ∀ a, f a ∈ p)
    (hf : Set.SurjOn f Set.univ p) :
    (Subtype.coind f h).Surjective := fun ⟨_, hb⟩ ↦
  let ⟨a, _, ha⟩ := hf hb
  ⟨a, Subtype.coe_injective ha⟩

theorem _root_.Subtype.coind_bijective {α β} {f : α → β} {p : Set β} (h : ∀ a, f a ∈ p)
    (hf_inj : f.Injective) (hf_surj : Set.SurjOn f Set.univ p) :
    (Subtype.coind f h).Bijective :=
  ⟨Subtype.coind_injective h hf_inj, Subtype.coind_surjective h hf_surj⟩

end surjOn

/-! ### Bijectivity -/
section bijOn

theorem BijOn.mapsTo (h : BijOn f s t) : MapsTo f s t :=
  h.left

theorem BijOn.injOn (h : BijOn f s t) : InjOn f s :=
  h.right.left

theorem BijOn.surjOn (h : BijOn f s t) : SurjOn f s t :=
  h.right.right

theorem BijOn.mk (h₁ : MapsTo f s t) (h₂ : InjOn f s) (h₃ : SurjOn f s t) : BijOn f s t :=
  ⟨h₁, h₂, h₃⟩

theorem bijOn_empty (f : α → β) : BijOn f ∅ ∅ :=
  ⟨mapsTo_empty f ∅, injOn_empty f, surjOn_empty f ∅⟩

@[simp] theorem bijOn_empty_iff_left : BijOn f s ∅ ↔ s = ∅ :=
  ⟨fun h ↦ by simpa using h.mapsTo, by rintro rfl; exact bijOn_empty f⟩

@[simp] theorem bijOn_empty_iff_right : BijOn f ∅ t ↔ t = ∅ :=
  ⟨fun h ↦ by simpa using h.surjOn, by rintro rfl; exact bijOn_empty f⟩

@[simp] lemma bijOn_singleton : BijOn f {a} {b} ↔ f a = b := by simp [BijOn, eq_comm]

theorem BijOn.inter_mapsTo (h₁ : BijOn f s₁ t₁) (h₂ : MapsTo f s₂ t₂) (h₃ : s₁ ∩ f ⁻¹' t₂ ⊆ s₂) :
    BijOn f (s₁ ∩ s₂) (t₁ ∩ t₂) :=
  ⟨h₁.mapsTo.inter_inter h₂, h₁.injOn.mono inter_subset_left, fun _ hy =>
    let ⟨x, hx, hxy⟩ := h₁.surjOn hy.1
    ⟨x, ⟨hx, h₃ ⟨hx, hxy.symm.subst hy.2⟩⟩, hxy⟩⟩

theorem MapsTo.inter_bijOn (h₁ : MapsTo f s₁ t₁) (h₂ : BijOn f s₂ t₂) (h₃ : s₂ ∩ f ⁻¹' t₁ ⊆ s₁) :
    BijOn f (s₁ ∩ s₂) (t₁ ∩ t₂) :=
  inter_comm s₂ s₁ ▸ inter_comm t₂ t₁ ▸ h₂.inter_mapsTo h₁ h₃

theorem BijOn.inter (h₁ : BijOn f s₁ t₁) (h₂ : BijOn f s₂ t₂) (h : InjOn f (s₁ ∪ s₂)) :
    BijOn f (s₁ ∩ s₂) (t₁ ∩ t₂) :=
  ⟨h₁.mapsTo.inter_inter h₂.mapsTo, h₁.injOn.mono inter_subset_left,
    h₁.surjOn.inter_inter h₂.surjOn h⟩

theorem BijOn.union (h₁ : BijOn f s₁ t₁) (h₂ : BijOn f s₂ t₂) (h : InjOn f (s₁ ∪ s₂)) :
    BijOn f (s₁ ∪ s₂) (t₁ ∪ t₂) :=
  ⟨h₁.mapsTo.union_union h₂.mapsTo, h, h₁.surjOn.union_union h₂.surjOn⟩

theorem BijOn.subset_range (h : BijOn f s t) : t ⊆ range f :=
  h.surjOn.subset_range

theorem InjOn.bijOn_image (h : InjOn f s) : BijOn f s (f '' s) :=
  BijOn.mk (mapsTo_image f s) h (Subset.refl _)

theorem BijOn.congr (h₁ : BijOn f₁ s t) (h : EqOn f₁ f₂ s) : BijOn f₂ s t :=
  BijOn.mk (h₁.mapsTo.congr h) (h₁.injOn.congr h) (h₁.surjOn.congr h)

theorem EqOn.bijOn_iff (H : EqOn f₁ f₂ s) : BijOn f₁ s t ↔ BijOn f₂ s t :=
  ⟨fun h => h.congr H, fun h => h.congr H.symm⟩

theorem BijOn.image_eq (h : BijOn f s t) : f '' s = t :=
  h.surjOn.image_eq_of_mapsTo h.mapsTo

lemma BijOn.forall {p : β → Prop} (hf : BijOn f s t) : (∀ b ∈ t, p b) ↔ ∀ a ∈ s, p (f a) where
  mp h _ ha := h _ <| hf.mapsTo ha
  mpr h b hb := by obtain ⟨a, ha, rfl⟩ := hf.surjOn hb; exact h _ ha

lemma BijOn.exists {p : β → Prop} (hf : BijOn f s t) : (∃ b ∈ t, p b) ↔ ∃ a ∈ s, p (f a) where
  mp := by rintro ⟨b, hb, h⟩; obtain ⟨a, ha, rfl⟩ := hf.surjOn hb; exact ⟨a, ha, h⟩
  mpr := by rintro ⟨a, ha, h⟩; exact ⟨f a, hf.mapsTo ha, h⟩

lemma _root_.Equiv.image_eq_iff_bijOn (e : α ≃ β) : e '' s = t ↔ BijOn e s t :=
  ⟨fun h ↦ ⟨(mapsTo_image e s).mono_right h.subset, e.injective.injOn, h ▸ surjOn_image e s⟩,
  BijOn.image_eq⟩

lemma bijOn_id (s : Set α) : BijOn id s s := ⟨s.mapsTo_id, s.injOn_id, s.surjOn_id⟩

theorem BijOn.comp (hg : BijOn g t p) (hf : BijOn f s t) : BijOn (g ∘ f) s p :=
  BijOn.mk (hg.mapsTo.comp hf.mapsTo) (hg.injOn.comp hf.injOn hf.mapsTo) (hg.surjOn.comp hf.surjOn)

/-- If `f : α → β` and `g : β → γ` and if `f` is injective on `s`, then `f ∘ g` is a bijection
on `s` iff  `g` is a bijection on `f '' s`. -/
theorem bijOn_comp_iff (hf : InjOn f s) : BijOn (g ∘ f) s p ↔ BijOn g (f '' s) p := by
  simp only [BijOn, InjOn.comp_iff, surjOn_comp_iff, mapsTo_image_iff, hf]

/--
If we have a commutative square

```
α --f--> β
|        |
p₁       p₂
|        |
\/       \/
γ --g--> δ
```

and `f` induces a bijection from `s : Set α` to `t : Set β`, then `g`
induces a bijection from the image of `s` to the image of `t`, as long as `g` is
is injective on the image of `s`.
-/
theorem bijOn_image_image {p₁ : α → γ} {p₂ : β → δ} {g : γ → δ} (comm : ∀ a, p₂ (f a) = g (p₁ a))
    (hbij : BijOn f s t) (hinj : InjOn g (p₁ '' s)) : BijOn g (p₁ '' s) (p₂ '' t) := by
  obtain ⟨h1, h2, h3⟩ := hbij
  refine ⟨?_, hinj, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact ⟨f a, h1 ha, by rw [comm a]⟩
  · rintro _ ⟨b, hb, rfl⟩
    obtain ⟨a, ha, rfl⟩ := h3 hb
    grind

lemma BijOn.iterate {f : α → α} {s : Set α} (h : BijOn f s s) : ∀ n, BijOn f^[n] s s
  | 0 => s.bijOn_id
  | (n + 1) => (h.iterate n).comp h

lemma bijOn_of_subsingleton' [Subsingleton α] [Subsingleton β] (f : α → β)
    (h : s.Nonempty ↔ t.Nonempty) : BijOn f s t :=
  ⟨mapsTo_of_subsingleton' _ h.1, injOn_of_subsingleton _ _, surjOn_of_subsingleton' _ h.2⟩

lemma bijOn_of_subsingleton [Subsingleton α] (f : α → α) (s : Set α) : BijOn f s s :=
  bijOn_of_subsingleton' _ Iff.rfl

theorem BijOn.bijective (h : BijOn f s t) : Bijective (h.mapsTo.restrict f s t) :=
  ⟨fun x y h' => Subtype.ext <| h.injOn x.2 y.2 <| Subtype.ext_iff.1 h', fun ⟨_, hy⟩ =>
    let ⟨x, hx, hxy⟩ := h.surjOn hy
    ⟨⟨x, hx⟩, Subtype.ext hxy⟩⟩

@[simp] lemma bijOn_univ : BijOn f univ univ ↔ Bijective f := by simp [Bijective, BijOn]

protected alias ⟨_, _root_.Function.Bijective.bijOn_univ⟩ := bijOn_univ

@[deprecated bijOn_univ (since := "2025-10-31")]
theorem bijective_iff_bijOn_univ : Bijective f ↔ BijOn f univ univ := bijOn_univ.symm

theorem BijOn.compl (hst : BijOn f s t) (hf : Bijective f) : BijOn f sᶜ tᶜ :=
  ⟨hst.surjOn.mapsTo_compl hf.1, hf.1.injOn, hst.mapsTo.surjOn_compl hf.2⟩

theorem BijOn.subset_right {r : Set β} (hf : BijOn f s t) (hrt : r ⊆ t) :
    BijOn f (s ∩ f ⁻¹' r) r := by
  refine ⟨inter_subset_right, hf.injOn.mono inter_subset_left, fun x hx ↦ ?_⟩
  obtain ⟨y, hy, rfl⟩ := hf.surjOn (hrt hx)
  exact ⟨y, ⟨hy, hx⟩, rfl⟩

theorem BijOn.subset_left {r : Set α} (hf : BijOn f s t) (hrs : r ⊆ s) :
    BijOn f r (f '' r) :=
  (hf.injOn.mono hrs).bijOn_image

theorem BijOn.insert_iff (ha : a ∉ s) (hfa : f a ∉ t) :
    BijOn f (insert a s) (insert (f a) t) ↔ BijOn f s t where
  mp h := by
    have := congrArg (· \ {f a}) (image_insert_eq ▸ h.image_eq)
    simp only [mem_singleton_iff, insert_diff_of_mem] at this
    rw [diff_singleton_eq_self hfa, diff_singleton_eq_self] at this
    · exact ⟨by simp [← this, mapsTo_iff_image_subset], h.injOn.mono (subset_insert ..),
        by simp [← this, surjOn_image]⟩
    simp only [mem_image, not_exists, not_and]
    intro x hx
    rw [h.injOn.eq_iff (by simp [hx]) (by simp)]
    exact ha ∘ (· ▸ hx)
  mpr h := by
    repeat rw [insert_eq]
    refine (bijOn_singleton.mpr rfl).union h ?_
    simp only [singleton_union, injOn_insert fun x ↦ (hfa (h.mapsTo x)), h.injOn, mem_image,
      not_exists, not_and, true_and]
    exact fun _ hx h₂ ↦ hfa (h₂ ▸ h.mapsTo hx)

theorem BijOn.insert (h₁ : BijOn f s t) (h₂ : f a ∉ t) :
    BijOn f (insert a s) (insert (f a) t) :=
  (insert_iff (h₂ <| h₁.mapsTo ·) h₂).mpr h₁

theorem BijOn.sdiff_singleton (h₁ : BijOn f s t) (h₂ : a ∈ s) :
    BijOn f (s \ {a}) (t \ {f a}) := by
  convert h₁.subset_left diff_subset
  simp [h₁.injOn.image_diff, h₁.image_eq, h₂, inter_eq_self_of_subset_right]

end bijOn

/-! ### left inverse -/
namespace LeftInvOn

theorem eqOn (h : LeftInvOn f' f s) : EqOn (f' ∘ f) id s :=
  h

theorem eq (h : LeftInvOn f' f s) {x} (hx : x ∈ s) : f' (f x) = x :=
  h hx

theorem congr_left (h₁ : LeftInvOn f₁' f s) {t : Set β} (h₁' : MapsTo f s t)
    (heq : EqOn f₁' f₂' t) : LeftInvOn f₂' f s := fun _ hx => heq (h₁' hx) ▸ h₁ hx

theorem congr_right (h₁ : LeftInvOn f₁' f₁ s) (heq : EqOn f₁ f₂ s) : LeftInvOn f₁' f₂ s :=
  fun _ hx => heq hx ▸ h₁ hx

theorem injOn (h : LeftInvOn f₁' f s) : InjOn f s := fun x₁ h₁ x₂ h₂ heq =>
  calc
    x₁ = f₁' (f x₁) := Eq.symm <| h h₁
    _ = f₁' (f x₂) := congr_arg f₁' heq
    _ = x₂ := h h₂

theorem surjOn (h : LeftInvOn f' f s) (hf : MapsTo f s t) : SurjOn f' t s := fun x hx =>
  ⟨f x, hf hx, h hx⟩

theorem mapsTo (h : LeftInvOn f' f s) (hf : SurjOn f s t) :
    MapsTo f' t s := fun y hy => by
  let ⟨x, hs, hx⟩ := hf hy
  rwa [← hx, h hs]

lemma _root_.Set.leftInvOn_id (s : Set α) : LeftInvOn id id s := fun _ _ ↦ rfl

theorem comp (hf' : LeftInvOn f' f s) (hg' : LeftInvOn g' g t) (hf : MapsTo f s t) :
    LeftInvOn (f' ∘ g') (g ∘ f) s := fun x h =>
  calc
    (f' ∘ g') ((g ∘ f) x) = f' (f x) := congr_arg f' (hg' (hf h))
    _ = x := hf' h

theorem mono (hf : LeftInvOn f' f s) (ht : s₁ ⊆ s) : LeftInvOn f' f s₁ := fun _ hx =>
  hf (ht hx)

theorem image_inter' (hf : LeftInvOn f' f s) : f '' (s₁ ∩ s) = f' ⁻¹' s₁ ∩ f '' s := by
  apply Subset.antisymm
  · rintro _ ⟨x, ⟨h₁, h⟩, rfl⟩
    exact ⟨by rwa [mem_preimage, hf h], mem_image_of_mem _ h⟩
  · rintro _ ⟨h₁, ⟨x, h, rfl⟩⟩
    exact mem_image_of_mem _ ⟨by rwa [← hf h], h⟩

theorem image_inter (hf : LeftInvOn f' f s) :
    f '' (s₁ ∩ s) = f' ⁻¹' (s₁ ∩ s) ∩ f '' s := by
  rw [hf.image_inter']
  refine Subset.antisymm ?_ (inter_subset_inter_left _ (preimage_mono inter_subset_left))
  rintro _ ⟨h₁, x, hx, rfl⟩; exact ⟨⟨h₁, by rwa [hf hx]⟩, mem_image_of_mem _ hx⟩

theorem image_image (hf : LeftInvOn f' f s) : f' '' (f '' s) = s := by
  rw [Set.image_image, image_congr hf, image_id']

theorem image_image' (hf : LeftInvOn f' f s) (hs : s₁ ⊆ s) : f' '' (f '' s₁) = s₁ :=
  (hf.mono hs).image_image

end LeftInvOn

/-! ### Right inverse -/
section RightInvOn
namespace RightInvOn

theorem eqOn (h : RightInvOn f' f t) : EqOn (f ∘ f') id t :=
  h

theorem eq (h : RightInvOn f' f t) {y} (hy : y ∈ t) : f (f' y) = y :=
  h hy

theorem _root_.Set.LeftInvOn.rightInvOn_image (h : LeftInvOn f' f s) : RightInvOn f' f (f '' s) :=
  fun _y ⟨_x, hx, heq⟩ => heq ▸ (congr_arg f <| h.eq hx)

theorem congr_left (h₁ : RightInvOn f₁' f t) (heq : EqOn f₁' f₂' t) :
    RightInvOn f₂' f t :=
  h₁.congr_right heq

theorem congr_right (h₁ : RightInvOn f' f₁ t) (hg : MapsTo f' t s) (heq : EqOn f₁ f₂ s) :
    RightInvOn f' f₂ t :=
  LeftInvOn.congr_left h₁ hg heq

theorem surjOn (hf : RightInvOn f' f t) (hf' : MapsTo f' t s) : SurjOn f s t :=
  LeftInvOn.surjOn hf hf'

theorem mapsTo (h : RightInvOn f' f t) (hf : SurjOn f' t s) : MapsTo f s t :=
  LeftInvOn.mapsTo h hf

lemma _root_.Set.rightInvOn_id (s : Set α) : RightInvOn id id s := fun _ _ ↦ rfl

theorem comp (hf : RightInvOn f' f t) (hg : RightInvOn g' g p) (g'pt : MapsTo g' p t) :
    RightInvOn (f' ∘ g') (g ∘ f) p :=
  LeftInvOn.comp hg hf g'pt

theorem mono (hf : RightInvOn f' f t) (ht : t₁ ⊆ t) : RightInvOn f' f t₁ :=
  LeftInvOn.mono hf ht
end RightInvOn

theorem InjOn.rightInvOn_of_leftInvOn (hf : InjOn f s) (hf' : LeftInvOn f f' t)
    (h₁ : MapsTo f s t) (h₂ : MapsTo f' t s) : RightInvOn f f' s := fun _ h =>
  hf (h₂ <| h₁ h) h (hf' (h₁ h))

theorem eqOn_of_leftInvOn_of_rightInvOn (h₁ : LeftInvOn f₁' f s) (h₂ : RightInvOn f₂' f t)
    (h : MapsTo f₂' t s) : EqOn f₁' f₂' t := fun y hy =>
  calc
    f₁' y = (f₁' ∘ f ∘ f₂') y := congr_arg f₁' (h₂ hy).symm
    _ = f₂' y := h₁ (h hy)

theorem SurjOn.leftInvOn_of_rightInvOn (hf : SurjOn f s t) (hf' : RightInvOn f f' s) :
    LeftInvOn f f' t := fun y hy => by
  let ⟨x, hx, heq⟩ := hf hy
  rw [← heq, hf' hx]

end RightInvOn

/-! ### Two-side inverses -/
namespace InvOn

lemma _root_.Set.invOn_id (s : Set α) : InvOn id id s s := ⟨s.leftInvOn_id, s.rightInvOn_id⟩

lemma comp (hf : InvOn f' f s t) (hg : InvOn g' g t p) (fst : MapsTo f s t)
    (g'pt : MapsTo g' p t) :
    InvOn (f' ∘ g') (g ∘ f) s p :=
  ⟨hf.1.comp hg.1 fst, hf.2.comp hg.2 g'pt⟩

@[symm]
theorem symm (h : InvOn f' f s t) : InvOn f f' t s :=
  ⟨h.right, h.left⟩

theorem mono (h : InvOn f' f s t) (hs : s₁ ⊆ s) (ht : t₁ ⊆ t) : InvOn f' f s₁ t₁ :=
  ⟨h.1.mono hs, h.2.mono ht⟩

/-- If functions `f'` and `f` are inverse on `s` and `t`, `f` maps `s` into `t`, and `f'` maps `t`
into `s`, then `f` is a bijection between `s` and `t`. The `mapsTo` arguments can be deduced from
`surjOn` statements using `LeftInvOn.mapsTo` and `RightInvOn.mapsTo`. -/
theorem bijOn (h : InvOn f' f s t) (hf : MapsTo f s t) (hf' : MapsTo f' t s) : BijOn f s t :=
  ⟨hf, h.left.injOn, h.right.surjOn hf'⟩

end InvOn

end Set

/-! ### `invFunOn` is a left/right inverse -/
namespace Function

variable {s : Set α} {f : α → β} {a : α} {b : β}

/-- Construct the inverse for a function `f` on domain `s`. This function is a right inverse of `f`
on `f '' s`. For a computable version, see `Function.Embedding.invOfMemRange`. -/
noncomputable def invFunOn [Nonempty α] (f : α → β) (s : Set α) (b : β) : α :=
  open scoped Classical in
  if h : ∃ a, a ∈ s ∧ f a = b then Classical.choose h else Classical.choice ‹Nonempty α›

variable [Nonempty α]

theorem invFunOn_pos (h : ∃ a ∈ s, f a = b) : invFunOn f s b ∈ s ∧ f (invFunOn f s b) = b := by
  rw [invFunOn, dif_pos h]
  exact Classical.choose_spec h

theorem invFunOn_mem (h : ∃ a ∈ s, f a = b) : invFunOn f s b ∈ s :=
  (invFunOn_pos h).left

theorem invFunOn_eq (h : ∃ a ∈ s, f a = b) : f (invFunOn f s b) = b :=
  (invFunOn_pos h).right

theorem invFunOn_neg (h : ¬∃ a ∈ s, f a = b) : invFunOn f s b = Classical.choice ‹Nonempty α› := by
  rw [invFunOn, dif_neg h]

@[simp]
theorem invFunOn_apply_mem (h : a ∈ s) : invFunOn f s (f a) ∈ s :=
  invFunOn_mem ⟨a, h, rfl⟩

theorem invFunOn_apply_eq (h : a ∈ s) : f (invFunOn f s (f a)) = f a :=
  invFunOn_eq ⟨a, h, rfl⟩

end Function

open Function

namespace Set

variable {s s₁ s₂ : Set α} {t : Set β} {f : α → β}

theorem InjOn.leftInvOn_invFunOn [Nonempty α] (h : InjOn f s) : LeftInvOn (invFunOn f s) f s :=
  fun _a ha => h (invFunOn_apply_mem ha) ha (invFunOn_apply_eq ha)

theorem InjOn.invFunOn_image [Nonempty α] (h : InjOn f s₂) (ht : s₁ ⊆ s₂) :
    invFunOn f s₂ '' (f '' s₁) = s₁ :=
  h.leftInvOn_invFunOn.image_image' ht

theorem _root_.Function.leftInvOn_invFunOn_of_subset_image_image [Nonempty α]
    (h : s ⊆ (invFunOn f s) '' (f '' s)) : LeftInvOn (invFunOn f s) f s :=
  fun x hx ↦ by
    obtain ⟨-, ⟨x, hx', rfl⟩, rfl⟩ := h hx
    rw [invFunOn_apply_eq (f := f) hx']

theorem injOn_iff_invFunOn_image_image_eq_self [Nonempty α] :
    InjOn f s ↔ (invFunOn f s) '' (f '' s) = s :=
  ⟨fun h ↦ h.invFunOn_image Subset.rfl, fun h ↦
    (Function.leftInvOn_invFunOn_of_subset_image_image h.symm.subset).injOn⟩

theorem _root_.Function.invFunOn_injOn_image [Nonempty α] (f : α → β) (s : Set α) :
    Set.InjOn (invFunOn f s) (f '' s) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩ he
  rw [← invFunOn_apply_eq (f := f) hx, he, invFunOn_apply_eq (f := f) hx']

theorem _root_.Function.invFunOn_image_image_subset [Nonempty α] (f : α → β) (s : Set α) :
    (invFunOn f s) '' (f '' s) ⊆ s := by
  rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩; exact invFunOn_apply_mem hx

theorem SurjOn.rightInvOn_invFunOn [Nonempty α] (h : SurjOn f s t) :
    RightInvOn (invFunOn f s) f t := fun _y hy => invFunOn_eq <| h hy

theorem BijOn.invOn_invFunOn [Nonempty α] (h : BijOn f s t) : InvOn (invFunOn f s) f s t :=
  ⟨h.injOn.leftInvOn_invFunOn, h.surjOn.rightInvOn_invFunOn⟩

theorem SurjOn.invOn_invFunOn [Nonempty α] (h : SurjOn f s t) :
    InvOn (invFunOn f s) f (invFunOn f s '' t) t := by
  refine ⟨?_, h.rightInvOn_invFunOn⟩
  rintro _ ⟨y, hy, rfl⟩
  rw [h.rightInvOn_invFunOn hy]

theorem SurjOn.mapsTo_invFunOn [Nonempty α] (h : SurjOn f s t) : MapsTo (invFunOn f s) t s :=
  fun _y hy => mem_preimage.2 <| invFunOn_mem <| h hy

/-- This lemma is a special case of `rightInvOn_invFunOn.image_image'`; it may make more sense
to use the other lemma directly in an application. -/
theorem SurjOn.image_invFunOn_image_of_subset [Nonempty α] {r : Set β} (hf : SurjOn f s t)
    (hrt : r ⊆ t) : f '' (f.invFunOn s '' r) = r :=
  hf.rightInvOn_invFunOn.image_image' hrt

/-- This lemma is a special case of `rightInvOn_invFunOn.image_image`; it may make more sense
to use the other lemma directly in an application. -/
theorem SurjOn.image_invFunOn_image [Nonempty α] (hf : SurjOn f s t) :
    f '' (f.invFunOn s '' t) = t :=
  hf.rightInvOn_invFunOn.image_image

theorem SurjOn.bijOn_subset [Nonempty α] (h : SurjOn f s t) : BijOn f (invFunOn f s '' t) t := by
  refine h.invOn_invFunOn.bijOn ?_ (mapsTo_image _ _)
  rintro _ ⟨y, hy, rfl⟩
  rwa [h.rightInvOn_invFunOn hy]

theorem surjOn_iff_exists_bijOn_subset : SurjOn f s t ↔ ∃ s' ⊆ s, BijOn f s' t := by
  constructor
  · rcases eq_empty_or_nonempty t with (rfl | ht)
    · exact fun _ => ⟨∅, empty_subset _, bijOn_empty f⟩
    · intro h
      haveI : Nonempty α := ⟨Classical.choose (h.comap_nonempty ht)⟩
      exact ⟨_, h.mapsTo_invFunOn.image_subset, h.bijOn_subset⟩
  · rintro ⟨s', hs', hfs'⟩
    exact hfs'.surjOn.mono hs' (Subset.refl _)

alias ⟨SurjOn.exists_bijOn_subset, _⟩ := Set.surjOn_iff_exists_bijOn_subset

variable (f s)

lemma exists_subset_bijOn : ∃ s' ⊆ s, BijOn f s' (f '' s) :=
  surjOn_iff_exists_bijOn_subset.mp (surjOn_image f s)

lemma exists_image_eq_and_injOn : ∃ u, f '' u = f '' s ∧ InjOn f u :=
  let ⟨u, _, hfu⟩ := exists_subset_bijOn s f
  ⟨u, hfu.image_eq, hfu.injOn⟩

variable {f s}

lemma exists_image_eq_injOn_of_subset_range (ht : t ⊆ range f) :
    ∃ s, f '' s = t ∧ InjOn f s :=
  image_preimage_eq_of_subset ht ▸ exists_image_eq_and_injOn _ _

/-- If `f` maps `s` bijectively to `t` and a set `t'` is contained in the image of some `s₁ ⊇ s`,
then `s₁` has a subset containing `s` that `f` maps bijectively to `t'`. -/
theorem BijOn.exists_extend_of_subset {t' : Set β} (h : BijOn f s t) (hss₁ : s ⊆ s₁) (htt' : t ⊆ t')
    (ht' : SurjOn f s₁ t') : ∃ s', s ⊆ s' ∧ s' ⊆ s₁ ∧ Set.BijOn f s' t' := by
  obtain ⟨r, hrss, hbij⟩ := exists_subset_bijOn ((s₁ ∩ f ⁻¹' t') \ f ⁻¹' t) f
  rw [image_diff_preimage, image_inter_preimage] at hbij
  refine ⟨s ∪ r, subset_union_left, ?_, ?_, ?_, fun y hyt' ↦ ?_⟩
  · exact union_subset hss₁ <| hrss.trans <| diff_subset.trans inter_subset_left
  · rw [mapsTo_iff_image_subset, image_union, hbij.image_eq, h.image_eq, union_subset_iff]
    exact ⟨htt', diff_subset.trans inter_subset_right⟩
  · rw [injOn_union, and_iff_right h.injOn, and_iff_right hbij.injOn]
    · refine fun x hxs y hyr hxy ↦ (hrss hyr).2 ?_
      rw [← h.image_eq]
      exact ⟨x, hxs, hxy⟩
    exact (subset_diff.1 hrss).2.symm.mono_left h.mapsTo
  rw [image_union, h.image_eq, hbij.image_eq, union_diff_self]
  exact .inr ⟨ht' hyt', hyt'⟩

/-- If `f` maps `s` bijectively to `t`, and `t'` is a superset of `t` contained in the range of `f`,
then `f` maps some superset of `s` bijectively to `t'`. -/
theorem BijOn.exists_extend {t' : Set β} (h : BijOn f s t) (htt' : t ⊆ t') (ht' : t' ⊆ range f) :
    ∃ s', s ⊆ s' ∧ BijOn f s' t' := by
  simpa using h.exists_extend_of_subset (subset_univ s) htt' (by simpa [SurjOn])

theorem InjOn.exists_subset_injOn_subset_range_eq {r : Set α} (hinj : InjOn f r) (hrs : r ⊆ s) :
    ∃ u : Set α, r ⊆ u ∧ u ⊆ s ∧ f '' u = f '' s ∧ InjOn f u := by
  obtain ⟨u, hru, hus, h⟩ := hinj.bijOn_image.exists_extend_of_subset hrs
    (image_mono hrs) Subset.rfl
  exact ⟨u, hru, hus, h.image_eq, h.injOn⟩

theorem preimage_invFun_of_mem [n : Nonempty α] {f : α → β} (hf : Injective f) {s : Set α}
    (h : Classical.choice n ∈ s) : invFun f ⁻¹' s = f '' s ∪ (range f)ᶜ := by
  ext x
  rcases em (x ∈ range f) with (⟨a, rfl⟩ | hx)
  · simp only [mem_preimage, mem_union, mem_compl_iff, mem_range_self, not_true, or_false,
      leftInverse_invFun hf _, hf.mem_set_image]
  · simp only [mem_preimage, invFun_neg hx, h, hx, mem_union, mem_compl_iff, not_false_iff, or_true]

theorem preimage_invFun_of_notMem [n : Nonempty α] {f : α → β} (hf : Injective f) {s : Set α}
    (h : Classical.choice n ∉ s) : invFun f ⁻¹' s = f '' s := by
  ext x
  rcases em (x ∈ range f) with (⟨a, rfl⟩ | hx)
  · rw [mem_preimage, leftInverse_invFun hf, hf.mem_set_image]
  · have : x ∉ f '' s := fun h' => hx (image_subset_range _ _ h')
    simp only [mem_preimage, invFun_neg hx, h, this]

@[deprecated (since := "2025-05-23")] alias preimage_invFun_of_not_mem := preimage_invFun_of_notMem

lemma BijOn.symm {g : β → α} (h : InvOn f g t s) (hf : BijOn f s t) : BijOn g t s :=
  ⟨h.2.mapsTo hf.surjOn, h.1.injOn, h.2.surjOn hf.mapsTo⟩

lemma bijOn_comm {g : β → α} (h : InvOn f g t s) : BijOn f s t ↔ BijOn g t s :=
  ⟨BijOn.symm h, BijOn.symm h.symm⟩

/-- If `t ⊆ f '' s`, there exists a preimage of `t` under `f` contained in `s` such that
`f` restricted to `u` is injective. -/
lemma SurjOn.exists_subset_injOn_image_eq (hfs : s.SurjOn f t) :
    ∃ u ⊆ s, u.InjOn f ∧ f '' u = t := by
  choose x hmem heq using hfs
  exact ⟨range (fun a : t ↦ x a.2), by grind, fun _ ↦ by grind, by aesop⟩

end Set

namespace Function

open Set

variable {fa : α → α} {fb : β → β} {f : α → β} {g : β → γ} {s t : Set α}

theorem Injective.comp_injOn (hg : Injective g) (hf : s.InjOn f) : s.InjOn (g ∘ f) :=
  hg.injOn.comp hf (mapsTo_univ _ _)

theorem LeftInverse.leftInvOn {g : β → α} (h : LeftInverse f g) (s : Set β) : LeftInvOn f g s :=
  fun x _ => h x

theorem RightInverse.rightInvOn {g : β → α} (h : RightInverse f g) (s : Set α) :
    RightInvOn f g s := fun x _ => h x

theorem LeftInverse.rightInvOn_range {g : β → α} (h : LeftInverse f g) :
    RightInvOn f g (range g) :=
  forall_mem_range.2 fun i => congr_arg g (h i)

namespace Semiconj

theorem mapsTo_image (h : Semiconj f fa fb) (ha : MapsTo fa s t) : MapsTo fb (f '' s) (f '' t) :=
  fun _y ⟨x, hx, hy⟩ => hy ▸ ⟨fa x, ha hx, h x⟩

theorem mapsTo_image_right {t : Set β} (h : Semiconj f fa fb) (hst : MapsTo f s t) :
    MapsTo f (fa '' s) (fb '' t) :=
  mapsTo_image_iff.2 fun x hx ↦ ⟨f x, hst hx, (h x).symm⟩

theorem mapsTo_range (h : Semiconj f fa fb) : MapsTo fb (range f) (range f) := fun _y ⟨x, hy⟩ =>
  hy ▸ ⟨fa x, h x⟩

theorem surjOn_image (h : Semiconj f fa fb) (ha : SurjOn fa s t) : SurjOn fb (f '' s) (f '' t) := by
  rintro y ⟨x, hxt, rfl⟩
  rcases ha hxt with ⟨x, hxs, rfl⟩
  rw [h x]
  exact mem_image_of_mem _ (mem_image_of_mem _ hxs)

theorem surjOn_range (h : Semiconj f fa fb) (ha : Surjective fa) :
    SurjOn fb (range f) (range f) := by
  rw [← image_univ]
  exact h.surjOn_image ha.surjOn

theorem injOn_image (h : Semiconj f fa fb) (ha : InjOn fa s) (hf : InjOn f (fa '' s)) :
    InjOn fb (f '' s) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ H
  simp only [← h.eq] at H
  exact congr_arg f (ha hx hy <| hf (mem_image_of_mem fa hx) (mem_image_of_mem fa hy) H)

theorem injOn_range (h : Semiconj f fa fb) (ha : Injective fa) (hf : InjOn f (range fa)) :
    InjOn fb (range f) := by
  rw [← image_univ] at *
  exact h.injOn_image ha.injOn hf

theorem bijOn_image (h : Semiconj f fa fb) (ha : BijOn fa s t) (hf : InjOn f t) :
    BijOn fb (f '' s) (f '' t) :=
  ⟨h.mapsTo_image ha.mapsTo, h.injOn_image ha.injOn (ha.image_eq.symm ▸ hf),
    h.surjOn_image ha.surjOn⟩

theorem bijOn_range (h : Semiconj f fa fb) (ha : Bijective fa) (hf : Injective f) :
    BijOn fb (range f) (range f) := by
  rw [← image_univ]
  exact h.bijOn_image ha.bijOn_univ hf.injOn

theorem mapsTo_preimage (h : Semiconj f fa fb) {s t : Set β} (hb : MapsTo fb s t) :
    MapsTo fa (f ⁻¹' s) (f ⁻¹' t) := fun x hx => by simp only [mem_preimage, h x, hb hx]

theorem injOn_preimage (h : Semiconj f fa fb) {s : Set β} (hb : InjOn fb s)
    (hf : InjOn f (f ⁻¹' s)) : InjOn fa (f ⁻¹' s) := by
  intro x hx y hy H
  have := congr_arg f H
  rw [h.eq, h.eq] at this
  exact hf hx hy (hb hx hy this)

end Semiconj

theorem update_comp_eq_of_notMem_range' {α : Sort*} {β : Type*} {γ : β → Sort*} [DecidableEq β]
    (g : ∀ b, γ b) {f : α → β} {i : β} (a : γ i) (h : i ∉ Set.range f) :
    (fun j => update g i a (f j)) = fun j => g (f j) :=
  (update_comp_eq_of_forall_ne' _ _) fun x hx => h ⟨x, hx⟩

@[deprecated (since := "2025-05-23")]
alias update_comp_eq_of_not_mem_range' := update_comp_eq_of_notMem_range'

/-- Non-dependent version of `Function.update_comp_eq_of_notMem_range'` -/
theorem update_comp_eq_of_notMem_range {α : Sort*} {β : Type*} {γ : Sort*} [DecidableEq β]
    (g : β → γ) {f : α → β} {i : β} (a : γ) (h : i ∉ Set.range f) : update g i a ∘ f = g ∘ f :=
  update_comp_eq_of_notMem_range' g a h

@[deprecated (since := "2025-05-23")]
alias update_comp_eq_of_not_mem_range := update_comp_eq_of_notMem_range

theorem insert_injOn (s : Set α) : sᶜ.InjOn fun a => insert a s := fun _a ha _ _ =>
  (insert_inj ha).1

lemma apply_eq_of_range_eq_singleton {f : α → β} {b : β} (h : range f = {b}) (a : α) :
    f a = b := by
  simpa only [h, mem_singleton_iff] using mem_range_self (f := f) a

end Function

/-! ### Equivalences, permutations -/
namespace Set

variable {p : β → Prop} [DecidablePred p] {f : α ≃ Subtype p} {g g₁ g₂ : Perm α} {s t : Set α}

protected lemma MapsTo.extendDomain (h : MapsTo g s t) :
    MapsTo (g.extendDomain f) ((↑) ∘ f '' s) ((↑) ∘ f '' t) := by
  rintro _ ⟨a, ha, rfl⟩; exact ⟨_, h ha, by simp_rw [Function.comp_apply, extendDomain_apply_image]⟩

protected lemma SurjOn.extendDomain (h : SurjOn g s t) :
    SurjOn (g.extendDomain f) ((↑) ∘ f '' s) ((↑) ∘ f '' t) := by
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨b, hb, rfl⟩ := h ha
  exact ⟨_, ⟨_, hb, rfl⟩, by simp_rw [Function.comp_apply, extendDomain_apply_image]⟩

protected lemma BijOn.extendDomain (h : BijOn g s t) :
    BijOn (g.extendDomain f) ((↑) ∘ f '' s) ((↑) ∘ f '' t) :=
  ⟨h.mapsTo.extendDomain, (g.extendDomain f).injective.injOn, h.surjOn.extendDomain⟩

protected lemma LeftInvOn.extendDomain (h : LeftInvOn g₁ g₂ s) :
    LeftInvOn (g₁.extendDomain f) (g₂.extendDomain f) ((↑) ∘ f '' s) := by
  rintro _ ⟨a, ha, rfl⟩; simp_rw [Function.comp_apply, extendDomain_apply_image, h ha]

protected lemma RightInvOn.extendDomain (h : RightInvOn g₁ g₂ t) :
    RightInvOn (g₁.extendDomain f) (g₂.extendDomain f) ((↑) ∘ f '' t) := by
  rintro _ ⟨a, ha, rfl⟩; simp_rw [Function.comp_apply, extendDomain_apply_image, h ha]

protected lemma InvOn.extendDomain (h : InvOn g₁ g₂ s t) :
    InvOn (g₁.extendDomain f) (g₂.extendDomain f) ((↑) ∘ f '' s) ((↑) ∘ f '' t) :=
  ⟨h.1.extendDomain, h.2.extendDomain⟩

end Set

namespace Set
variable {α₁ α₂ β₁ β₂ : Type*} {s₁ : Set α₁} {s₂ : Set α₂} {t₁ : Set β₁} {t₂ : Set β₂}
  {f₁ : α₁ → β₁} {f₂ : α₂ → β₂} {g₁ : β₁ → α₁} {g₂ : β₂ → α₂}

lemma InjOn.prodMap (h₁ : s₁.InjOn f₁) (h₂ : s₂.InjOn f₂) :
    (s₁ ×ˢ s₂).InjOn fun x ↦ (f₁ x.1, f₂ x.2) :=
  fun x hx y hy ↦ by simp_rw [Prod.ext_iff]; exact And.imp (h₁ hx.1 hy.1) (h₂ hx.2 hy.2)

lemma SurjOn.prodMap (h₁ : SurjOn f₁ s₁ t₁) (h₂ : SurjOn f₂ s₂ t₂) :
    SurjOn (fun x ↦ (f₁ x.1, f₂ x.2)) (s₁ ×ˢ s₂) (t₁ ×ˢ t₂) := by
  rintro x hx
  obtain ⟨a₁, ha₁, hx₁⟩ := h₁ hx.1
  obtain ⟨a₂, ha₂, hx₂⟩ := h₂ hx.2
  exact ⟨(a₁, a₂), ⟨ha₁, ha₂⟩, Prod.ext hx₁ hx₂⟩

lemma MapsTo.prodMap (h₁ : MapsTo f₁ s₁ t₁) (h₂ : MapsTo f₂ s₂ t₂) :
    MapsTo (fun x ↦ (f₁ x.1, f₂ x.2)) (s₁ ×ˢ s₂) (t₁ ×ˢ t₂) :=
  fun _x hx ↦ ⟨h₁ hx.1, h₂ hx.2⟩

lemma BijOn.prodMap (h₁ : BijOn f₁ s₁ t₁) (h₂ : BijOn f₂ s₂ t₂) :
    BijOn (fun x ↦ (f₁ x.1, f₂ x.2)) (s₁ ×ˢ s₂) (t₁ ×ˢ t₂) :=
  ⟨h₁.mapsTo.prodMap h₂.mapsTo, h₁.injOn.prodMap h₂.injOn, h₁.surjOn.prodMap h₂.surjOn⟩

lemma LeftInvOn.prodMap (h₁ : LeftInvOn g₁ f₁ s₁) (h₂ : LeftInvOn g₂ f₂ s₂) :
    LeftInvOn (fun x ↦ (g₁ x.1, g₂ x.2)) (fun x ↦ (f₁ x.1, f₂ x.2)) (s₁ ×ˢ s₂) :=
  fun _x hx ↦ Prod.ext (h₁ hx.1) (h₂ hx.2)

lemma RightInvOn.prodMap (h₁ : RightInvOn g₁ f₁ t₁) (h₂ : RightInvOn g₂ f₂ t₂) :
    RightInvOn (fun x ↦ (g₁ x.1, g₂ x.2)) (fun x ↦ (f₁ x.1, f₂ x.2)) (t₁ ×ˢ t₂) :=
  fun _x hx ↦ Prod.ext (h₁ hx.1) (h₂ hx.2)

lemma InvOn.prodMap (h₁ : InvOn g₁ f₁ s₁ t₁) (h₂ : InvOn g₂ f₂ s₂ t₂) :
    InvOn (fun x ↦ (g₁ x.1, g₂ x.2)) (fun x ↦ (f₁ x.1, f₂ x.2)) (s₁ ×ˢ s₂) (t₁ ×ˢ t₂) :=
  ⟨h₁.1.prodMap h₂.1, h₁.2.prodMap h₂.2⟩

end Set

namespace Equiv
open Set

variable (e : α ≃ β) {s : Set α} {t : Set β}

lemma bijOn' (h₁ : MapsTo e s t) (h₂ : MapsTo e.symm t s) : BijOn e s t :=
  ⟨h₁, e.injective.injOn, fun b hb ↦ ⟨e.symm b, h₂ hb, apply_symm_apply _ _⟩⟩

protected lemma bijOn (h : ∀ a, e a ∈ t ↔ a ∈ s) : BijOn e s t :=
  e.bijOn' (fun _ ↦ (h _).2) fun b hb ↦ (h _).1 <| by rwa [apply_symm_apply]

lemma invOn : InvOn e e.symm t s :=
  ⟨e.rightInverse_symm.leftInvOn _, e.leftInverse_symm.leftInvOn _⟩

lemma bijOn_image : BijOn e s (e '' s) := e.injective.injOn.bijOn_image
lemma bijOn_symm_image : BijOn e.symm (e '' s) s := e.bijOn_image.symm e.invOn

variable {e}

@[simp] lemma bijOn_symm : BijOn e.symm t s ↔ BijOn e s t := bijOn_comm e.symm.invOn

alias ⟨_root_.Set.BijOn.of_equiv_symm, _root_.Set.BijOn.equiv_symm⟩ := bijOn_symm

variable [DecidableEq α] {a b : α}

lemma bijOn_swap (ha : a ∈ s) (hb : b ∈ s) : BijOn (swap a b) s s :=
  (swap a b).bijOn fun x ↦ by
    obtain rfl | hxa := eq_or_ne x a <;>
    obtain rfl | hxb := eq_or_ne x b <;>
    simp [*, swap_apply_of_ne_of_ne]

end Equiv
