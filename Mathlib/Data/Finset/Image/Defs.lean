/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Minchao Wu, Mario Carneiro
-/
import Mathlib.Data.Finset.Dedup

/-! # Image and map operations on finite sets

This file provides the finite analog of `Set.image`, along with some other similar functions.

Note there are two ways to take the image over a finset; via `Finset.image` which applies the
function then removes duplicates (requiring `DecidableEq`), or via `Finset.map` which exploits
injectivity of the function to avoid needing to deduplicate. Choosing between these is similar to
choosing between `insert` and `Finset.cons`, or between `Finset.union` and `Finset.disjUnion`.

## Main definitions

* `Finset.image`: Given a function `f : α → β`, `s.image f` is the image finset in `β`.
* `Finset.map`: Given an embedding `f : α ↪ β`, `s.map f` is the image finset in `β`.
* `Finset.filterMap` Given a function `f : α → Option β`, `s.filterMap f` is the
  image finset in `β`, filtering out `none`s.

-/
assert_not_exists OrderedCommMonoid
assert_not_exists MonoidWithZero
assert_not_exists MulAction

variable {α β γ : Type*}

open Multiset

open Function

namespace Finset

/-! ### map -/


section Map

open Function

/-- When `f` is an embedding of `α` in `β` and `s` is a finset in `α`, then `s.map f` is the image
finset in `β`. The embedding condition guarantees that there are no duplicates in the image. -/
def map (f : α ↪ β) (s : Finset α) : Finset β :=
  ⟨s.1.map f, s.2.map f.2⟩

@[simp]
theorem map_val (f : α ↪ β) (s : Finset α) : (map f s).1 = s.1.map f :=
  rfl

variable {f : α ↪ β} {s : Finset α}

@[simp]
theorem mem_map {b : β} : b ∈ s.map f ↔ ∃ a ∈ s, f a = b :=
  Multiset.mem_map

-- Porting note: Higher priority to apply before `mem_map`.
@[simp 1100]
theorem mem_map_equiv {f : α ≃ β} {b : β} : b ∈ s.map f.toEmbedding ↔ f.symm b ∈ s := by
  rw [mem_map]
  exact
    ⟨by
      rintro ⟨a, H, rfl⟩
      simpa, fun h => ⟨_, h, by simp⟩⟩

@[simp 1100]
theorem mem_map' (f : α ↪ β) {a} {s : Finset α} : f a ∈ s.map f ↔ a ∈ s :=
  mem_map_of_injective f.2

theorem mem_map_of_mem (f : α ↪ β) {a} {s : Finset α} : a ∈ s → f a ∈ s.map f :=
  (mem_map' _).2

theorem forall_mem_map {f : α ↪ β} {s : Finset α} {p : ∀ a, a ∈ s.map f → Prop} :
    (∀ y (H : y ∈ s.map f), p y H) ↔ ∀ x (H : x ∈ s), p (f x) (mem_map_of_mem _ H) :=
  ⟨fun h y hy => h (f y) (mem_map_of_mem _ hy),
   fun h x hx => by
    obtain ⟨y, hy, rfl⟩ := mem_map.1 hx
    exact h _ hy⟩

theorem apply_coe_mem_map (f : α ↪ β) (s : Finset α) (x : s) : f x ∈ s.map f :=
  mem_map_of_mem f x.prop

@[simp, norm_cast]
theorem coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) = f '' s :=
  Set.ext (by simp only [mem_coe, mem_map, Set.mem_image, implies_true])

theorem coe_map_subset_range (f : α ↪ β) (s : Finset α) : (s.map f : Set β) ⊆ Set.range f :=
  calc
    ↑(s.map f) = f '' s := coe_map f s
    _ ⊆ Set.range f := Set.image_subset_range f ↑s

/-- If the only elements outside `s` are those left fixed by `σ`, then mapping by `σ` has no effect.
-/
theorem map_perm {σ : Equiv.Perm α} (hs : { a | σ a ≠ a } ⊆ s) : s.map (σ : α ↪ α) = s :=
  coe_injective <| (coe_map _ _).trans <| Set.image_perm hs

theorem map_toFinset [DecidableEq α] [DecidableEq β] {s : Multiset α} :
    s.toFinset.map f = (s.map f).toFinset :=
  ext fun _ => by simp only [mem_map, Multiset.mem_map, exists_prop, Multiset.mem_toFinset]

@[simp]
theorem map_refl : s.map (Embedding.refl _) = s :=
  ext fun _ => by simpa only [mem_map, exists_prop] using exists_eq_right

@[simp]
theorem map_cast_heq {α β} (h : α = β) (s : Finset α) :
    HEq (s.map (Equiv.cast h).toEmbedding) s := by
  subst h
  simp

theorem map_map (f : α ↪ β) (g : β ↪ γ) (s : Finset α) : (s.map f).map g = s.map (f.trans g) :=
  eq_of_veq <| by simp only [map_val, Multiset.map_map]; rfl

theorem map_comm {β'} {f : β ↪ γ} {g : α ↪ β} {f' : α ↪ β'} {g' : β' ↪ γ}
    (h_comm : ∀ a, f (g a) = g' (f' a)) : (s.map g).map f = (s.map f').map g' := by
  simp_rw [map_map, Embedding.trans, Function.comp_def, h_comm]

theorem _root_.Function.Semiconj.finset_map {f : α ↪ β} {ga : α ↪ α} {gb : β ↪ β}
    (h : Function.Semiconj f ga gb) : Function.Semiconj (map f) (map ga) (map gb) := fun _ =>
  map_comm h

theorem _root_.Function.Commute.finset_map {f g : α ↪ α} (h : Function.Commute f g) :
    Function.Commute (map f) (map g) :=
  Function.Semiconj.finset_map h

@[simp]
theorem map_subset_map {s₁ s₂ : Finset α} : s₁.map f ⊆ s₂.map f ↔ s₁ ⊆ s₂ :=
  ⟨fun h _ xs => (mem_map' _).1 <| h <| (mem_map' f).2 xs,
   fun h => by simp [subset_def, Multiset.map_subset_map h]⟩

@[gcongr] alias ⟨_, _root_.GCongr.finsetMap_subset⟩ := map_subset_map

/-- The `Finset` version of `Equiv.subset_symm_image`. -/
theorem subset_map_symm {t : Finset β} {f : α ≃ β} : s ⊆ t.map f.symm ↔ s.map f ⊆ t := by
  constructor <;> intro h x hx
  · simp only [mem_map_equiv, Equiv.symm_symm] at hx
    simpa using h hx
  · simp only [mem_map_equiv]
    exact h (by simp [hx])

/-- The `Finset` version of `Equiv.symm_image_subset`. -/
theorem map_symm_subset {t : Finset β} {f : α ≃ β} : t.map f.symm ⊆ s ↔ t ⊆ s.map f := by
  simp only [← subset_map_symm, Equiv.symm_symm]

/-- Associate to an embedding `f` from `α` to `β` the order embedding that maps a finset to its
image under `f`. -/
def mapEmbedding (f : α ↪ β) : Finset α ↪o Finset β :=
  OrderEmbedding.ofMapLEIff (map f) fun _ _ => map_subset_map

@[simp]
theorem map_inj {s₁ s₂ : Finset α} : s₁.map f = s₂.map f ↔ s₁ = s₂ :=
  (mapEmbedding f).injective.eq_iff

theorem map_injective (f : α ↪ β) : Injective (map f) :=
  (mapEmbedding f).injective

@[simp]
theorem map_ssubset_map {s t : Finset α} : s.map f ⊂ t.map f ↔ s ⊂ t := (mapEmbedding f).lt_iff_lt

@[gcongr] alias ⟨_, _root_.GCongr.finsetMap_ssubset⟩ := map_ssubset_map

@[simp]
theorem mapEmbedding_apply : mapEmbedding f s = map f s :=
  rfl

end Map

/-! ### image -/


section Image

variable [DecidableEq β]

/-- `image f s` is the forward image of `s` under `f`. -/
def image (f : α → β) (s : Finset α) : Finset β :=
  (s.1.map f).toFinset

@[simp]
theorem image_val (f : α → β) (s : Finset α) : (image f s).1 = (s.1.map f).dedup :=
  rfl

variable {f g : α → β} {s : Finset α} {t : Finset β} {a : α} {b c : β}

@[simp]
theorem mem_image : b ∈ s.image f ↔ ∃ a ∈ s, f a = b := by
  simp only [mem_def, image_val, mem_dedup, Multiset.mem_map, exists_prop]

theorem mem_image_of_mem (f : α → β) {a} (h : a ∈ s) : f a ∈ s.image f :=
  mem_image.2 ⟨_, h, rfl⟩

lemma forall_mem_image {p : β → Prop} : (∀ y ∈ s.image f, p y) ↔ ∀ ⦃x⦄, x ∈ s → p (f x) := by simp
lemma exists_mem_image {p : β → Prop} : (∃ y ∈ s.image f, p y) ↔ ∃ x ∈ s, p (f x) := by simp

@[deprecated (since := "2024-11-23")] alias forall_image := forall_mem_image

theorem map_eq_image (f : α ↪ β) (s : Finset α) : s.map f = s.image f :=
  eq_of_veq (s.map f).2.dedup.symm

@[norm_cast]
theorem image_eq_map (f : α ↪ β) (s : Finset α) : s.image f = s.map f :=
  (map_eq_image f s).symm

instance canLift (c) (p) [CanLift β α c p] :
    CanLift (Finset β) (Finset α) (image c) fun s => ∀ x ∈ s, p x where
  prf := by
    rintro ⟨⟨l⟩, hd : l.Nodup⟩ hl
    lift l to List α using hl
    exact ⟨⟨l, hd.of_map _⟩, ext fun a => by simp⟩

theorem image_congr (h : (s : Set α).EqOn f g) : Finset.image f s = Finset.image g s := by
  ext
  simp_rw [mem_image, ← bex_def]
  exact exists₂_congr fun x hx => by rw [h hx]

theorem _root_.Function.Injective.mem_finset_image (hf : Injective f) :
    f a ∈ s.image f ↔ a ∈ s := by
  refine ⟨fun h => ?_, Finset.mem_image_of_mem f⟩
  obtain ⟨y, hy, heq⟩ := mem_image.1 h
  exact hf heq ▸ hy

@[simp, norm_cast]
theorem coe_image : ↑(s.image f) = f '' ↑s :=
  Set.ext <| by simp only [mem_coe, mem_image, Set.mem_image, implies_true]

theorem image_toFinset [DecidableEq α] {s : Multiset α} :
    s.toFinset.image f = (s.map f).toFinset :=
  ext fun _ => by simp only [mem_image, Multiset.mem_toFinset, exists_prop, Multiset.mem_map]

theorem image_val_of_injOn (H : Set.InjOn f s) : (image f s).1 = s.1.map f :=
  (s.2.map_on H).dedup

@[simp]
theorem image_id [DecidableEq α] : s.image id = s :=
  ext fun _ => by simp only [mem_image, exists_prop, id, exists_eq_right]

@[simp]
theorem image_id' [DecidableEq α] : (s.image fun x => x) = s :=
  image_id

theorem image_image [DecidableEq γ] {g : β → γ} : (s.image f).image g = s.image (g ∘ f) :=
  eq_of_veq <| by simp only [image_val, dedup_map_dedup_eq, Multiset.map_map]

theorem image_comm {β'} [DecidableEq β'] [DecidableEq γ] {f : β → γ} {g : α → β} {f' : α → β'}
    {g' : β' → γ} (h_comm : ∀ a, f (g a) = g' (f' a)) :
    (s.image g).image f = (s.image f').image g' := by simp_rw [image_image, comp_def, h_comm]

theorem _root_.Function.Semiconj.finset_image [DecidableEq α] {f : α → β} {ga : α → α} {gb : β → β}
    (h : Function.Semiconj f ga gb) : Function.Semiconj (image f) (image ga) (image gb) := fun _ =>
  image_comm h

theorem _root_.Function.Commute.finset_image [DecidableEq α] {f g : α → α}
    (h : Function.Commute f g) : Function.Commute (image f) (image g) :=
  Function.Semiconj.finset_image h

theorem image_subset_image {s₁ s₂ : Finset α} (h : s₁ ⊆ s₂) : s₁.image f ⊆ s₂.image f := by
  simp only [subset_def, image_val, subset_dedup', dedup_subset', Multiset.map_subset_map h]

theorem image_subset_iff : s.image f ⊆ t ↔ ∀ x ∈ s, f x ∈ t :=
  calc
    s.image f ⊆ t ↔ f '' ↑s ⊆ ↑t := by norm_cast
    _ ↔ _ := Set.image_subset_iff

theorem image_mono (f : α → β) : Monotone (Finset.image f) := fun _ _ => image_subset_image

lemma image_injective (hf : Injective f) : Injective (image f) := by
  simpa only [funext (map_eq_image _)] using map_injective ⟨f, hf⟩

lemma image_inj {t : Finset α} (hf : Injective f) : s.image f = t.image f ↔ s = t :=
  (image_injective hf).eq_iff

theorem image_subset_image_iff {t : Finset α} (hf : Injective f) :
    s.image f ⊆ t.image f ↔ s ⊆ t :=
  mod_cast Set.image_subset_image_iff hf (s := s) (t := t)

lemma image_ssubset_image {t : Finset α} (hf : Injective f) : s.image f ⊂ t.image f ↔ s ⊂ t := by
  simp_rw [← lt_iff_ssubset]
  exact lt_iff_lt_of_le_iff_le' (image_subset_image_iff hf) (image_subset_image_iff hf)

theorem coe_image_subset_range : ↑(s.image f) ⊆ Set.range f :=
  calc
    ↑(s.image f) = f '' ↑s := coe_image
    _ ⊆ Set.range f := Set.image_subset_range f ↑s

end Image

/-! ### filterMap -/

section FilterMap

/-- `filterMap f s` is a combination filter/map operation on `s`.
  The function `f : α → Option β` is applied to each element of `s`;
  if `f a` is `some b` then `b` is included in the result, otherwise
  `a` is excluded from the resulting finset.

  In notation, `filterMap f s` is the finset `{b : β | ∃ a ∈ s , f a = some b}`. -/
-- TODO: should there be `filterImage` too?
def filterMap (f : α → Option β) (s : Finset α)
    (f_inj : ∀ a a' b, b ∈ f a → b ∈ f a' → a = a') : Finset β :=
  ⟨s.val.filterMap f, s.nodup.filterMap f f_inj⟩

variable (f : α → Option β) (s' : Finset α) {s t : Finset α}
  {f_inj : ∀ a a' b, b ∈ f a → b ∈ f a' → a = a'}

@[simp]
theorem filterMap_val : (filterMap f s' f_inj).1 = s'.1.filterMap f := rfl

@[simp]
theorem mem_filterMap {b : β} : b ∈ s.filterMap f f_inj ↔ ∃ a ∈ s, f a = some b :=
  s.val.mem_filterMap f

@[simp, norm_cast]
theorem coe_filterMap : (s.filterMap f f_inj : Set β) = {b | ∃ a ∈ s, f a = some b} :=
  Set.ext (by simp only [mem_coe, mem_filterMap, Option.mem_def, Set.mem_setOf_eq, implies_true])

@[simp]
theorem filterMap_some : s.filterMap some (by simp) = s :=
  ext fun _ => by simp only [mem_filterMap, Option.some.injEq, exists_eq_right]

theorem filterMap_mono (h : s ⊆ t) :
    filterMap f s f_inj ⊆ filterMap f t f_inj := by
  rw [← val_le_iff] at h ⊢
  exact Multiset.filterMap_le_filterMap f h

end FilterMap

end Finset

theorem Multiset.toFinset_map [DecidableEq α] [DecidableEq β] (f : α → β) (m : Multiset α) :
    (m.map f).toFinset = m.toFinset.image f :=
  Finset.val_inj.1 (Multiset.dedup_map_dedup_eq _ _).symm

namespace Equiv

/-- Given an equivalence `α` to `β`, produce an equivalence between `Finset α` and `Finset β`. -/
protected def finsetCongr (e : α ≃ β) : Finset α ≃ Finset β where
  toFun s := s.map e.toEmbedding
  invFun s := s.map e.symm.toEmbedding
  left_inv s := by simp [Finset.map_map]
  right_inv s := by simp [Finset.map_map]

@[simp]
theorem finsetCongr_apply (e : α ≃ β) (s : Finset α) : e.finsetCongr s = s.map e.toEmbedding :=
  rfl

@[simp]
theorem finsetCongr_refl : (Equiv.refl α).finsetCongr = Equiv.refl _ := by
  ext
  simp

@[simp]
theorem finsetCongr_symm (e : α ≃ β) : e.finsetCongr.symm = e.symm.finsetCongr :=
  rfl

@[simp]
theorem finsetCongr_trans (e : α ≃ β) (e' : β ≃ γ) :
    e.finsetCongr.trans e'.finsetCongr = (e.trans e').finsetCongr := by
  ext
  simp [-Finset.mem_map, -Equiv.trans_toEmbedding]

theorem finsetCongr_toEmbedding (e : α ≃ β) :
    e.finsetCongr.toEmbedding = (Finset.mapEmbedding e.toEmbedding).toEmbedding :=
  rfl

/-- Given a predicate `p : α → Prop`, produces an equivalence between
  `Finset {a : α // p a}` and `{s : Finset α // ∀ a ∈ s, p a}`. -/
@[simps]
protected def finsetSubtypeComm (p : α → Prop) :
    Finset {a : α // p a} ≃ {s : Finset α // ∀ a ∈ s, p a} where
  toFun s := ⟨s.map ⟨fun a ↦ a.val, Subtype.val_injective⟩, fun _ h ↦
    have ⟨v, _, h⟩ := Embedding.coeFn_mk _ _ ▸ mem_map.mp h; h ▸ v.property⟩
  invFun s := s.val.attach.map (Subtype.impEmbedding _ _ s.property)
  left_inv s := by
    ext a; constructor <;> intro h <;>
    simp only [Finset.mem_map, Finset.mem_attach, true_and, Subtype.exists, Embedding.coeFn_mk,
      exists_and_right, exists_eq_right, Subtype.impEmbedding, Subtype.mk.injEq] at *
    · rcases h with ⟨_, ⟨_, h₁⟩, h₂⟩; exact h₂ ▸ h₁
    · use a, ⟨a.property, h⟩
  right_inv s := by
    ext a; constructor <;> intro h <;>
    simp only [Finset.mem_map, Finset.mem_attach, true_and, Subtype.exists, Embedding.coeFn_mk,
      exists_and_right, exists_eq_right, Subtype.impEmbedding, Subtype.mk.injEq] at *
    · rcases h with ⟨_, _, h₁, h₂⟩; exact h₂ ▸ h₁
    · use s.property _ h, a


end Equiv
