/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Order.Filter.Prod

#align_import order.filter.n_ary from "leanprover-community/mathlib"@"78f647f8517f021d839a7553d5dc97e79b508dea"

/-!
# N-ary maps of filter

This file defines the binary and ternary maps of filters. This is mostly useful to define pointwise
operations on filters.

## Main declarations

* `Filter.map₂`: Binary map of filters.

## Notes

This file is very similar to `Data.Set.NAry`, `Data.Finset.NAry` and `Data.Option.NAry`. Please
keep them in sync.
-/


open Function Set

open Filter

namespace Filter

variable {α α' β β' γ γ' δ δ' ε ε' : Type*} {m : α → β → γ} {f f₁ f₂ : Filter α}
  {g g₁ g₂ : Filter β} {h h₁ h₂ : Filter γ} {s s₁ s₂ : Set α} {t t₁ t₂ : Set β} {u : Set γ}
  {v : Set δ} {a : α} {b : β} {c : γ}

/-- The image of a binary function `m : α → β → γ` as a function `Filter α → Filter β → Filter γ`.
Mathematically this should be thought of as the image of the corresponding function `α × β → γ`. -/
def map₂ (m : α → β → γ) (f : Filter α) (g : Filter β) : Filter γ :=
  ((f ×ˢ g).map (uncurry m)).copy { s | ∃ u ∈ f, ∃ v ∈ g, image2 m u v ⊆ s } fun _ ↦ by
    simp only [mem_map, mem_prod_iff, image2_subset_iff, prod_subset_iff]; rfl
#align filter.map₂ Filter.map₂

@[simp 900]
theorem mem_map₂_iff : u ∈ map₂ m f g ↔ ∃ s ∈ f, ∃ t ∈ g, image2 m s t ⊆ u :=
  Iff.rfl
#align filter.mem_map₂_iff Filter.mem_map₂_iff

theorem image2_mem_map₂ (hs : s ∈ f) (ht : t ∈ g) : image2 m s t ∈ map₂ m f g :=
  ⟨_, hs, _, ht, Subset.rfl⟩
#align filter.image2_mem_map₂ Filter.image2_mem_map₂

theorem map_prod_eq_map₂ (m : α → β → γ) (f : Filter α) (g : Filter β) :
    Filter.map (fun p : α × β => m p.1 p.2) (f ×ˢ g) = map₂ m f g := by
  rw [map₂, copy_eq, uncurry_def]
#align filter.map_prod_eq_map₂ Filter.map_prod_eq_map₂

theorem map_prod_eq_map₂' (m : α × β → γ) (f : Filter α) (g : Filter β) :
    Filter.map m (f ×ˢ g) = map₂ (fun a b => m (a, b)) f g :=
  map_prod_eq_map₂ (curry m) f g
#align filter.map_prod_eq_map₂' Filter.map_prod_eq_map₂'

@[simp]
theorem map₂_mk_eq_prod (f : Filter α) (g : Filter β) : map₂ Prod.mk f g = f ×ˢ g := by
  simp only [← map_prod_eq_map₂, map_id']
#align filter.map₂_mk_eq_prod Filter.map₂_mk_eq_prod

-- lemma image2_mem_map₂_iff (hm : injective2 m) : image2 m s t ∈ map₂ m f g ↔ s ∈ f ∧ t ∈ g :=
-- ⟨by { rintro ⟨u, v, hu, hv, h⟩, rw image2_subset_image2_iff hm at h,
--   exact ⟨mem_of_superset hu h.1, mem_of_superset hv h.2⟩ }, λ h, image2_mem_map₂ h.1 h.2⟩
theorem map₂_mono (hf : f₁ ≤ f₂) (hg : g₁ ≤ g₂) : map₂ m f₁ g₁ ≤ map₂ m f₂ g₂ :=
  fun _ ⟨s, hs, t, ht, hst⟩ => ⟨s, hf hs, t, hg ht, hst⟩
#align filter.map₂_mono Filter.map₂_mono

theorem map₂_mono_left (h : g₁ ≤ g₂) : map₂ m f g₁ ≤ map₂ m f g₂ :=
  map₂_mono Subset.rfl h
#align filter.map₂_mono_left Filter.map₂_mono_left

theorem map₂_mono_right (h : f₁ ≤ f₂) : map₂ m f₁ g ≤ map₂ m f₂ g :=
  map₂_mono h Subset.rfl
#align filter.map₂_mono_right Filter.map₂_mono_right

@[simp]
theorem le_map₂_iff {h : Filter γ} :
    h ≤ map₂ m f g ↔ ∀ ⦃s⦄, s ∈ f → ∀ ⦃t⦄, t ∈ g → image2 m s t ∈ h :=
  ⟨fun H _ hs _ ht => H <| image2_mem_map₂ hs ht, fun H _ ⟨_, hs, _, ht, hu⟩ =>
    mem_of_superset (H hs ht) hu⟩
#align filter.le_map₂_iff Filter.le_map₂_iff

@[simp]
theorem map₂_eq_bot_iff : map₂ m f g = ⊥ ↔ f = ⊥ ∨ g = ⊥ := by simp [← map_prod_eq_map₂]
#align filter.map₂_eq_bot_iff Filter.map₂_eq_bot_iff

@[simp]
theorem map₂_bot_left : map₂ m ⊥ g = ⊥ := map₂_eq_bot_iff.2 <| .inl rfl
#align filter.map₂_bot_left Filter.map₂_bot_left

@[simp]
theorem map₂_bot_right : map₂ m f ⊥ = ⊥ := map₂_eq_bot_iff.2 <| .inr rfl
#align filter.map₂_bot_right Filter.map₂_bot_right

@[simp]
theorem map₂_neBot_iff : (map₂ m f g).NeBot ↔ f.NeBot ∧ g.NeBot := by simp [neBot_iff, not_or]
#align filter.map₂_ne_bot_iff Filter.map₂_neBot_iff

protected theorem NeBot.map₂ (hf : f.NeBot) (hg : g.NeBot) : (map₂ m f g).NeBot :=
  map₂_neBot_iff.2 ⟨hf, hg⟩
#align filter.ne_bot.map₂ Filter.NeBot.map₂

instance map₂.neBot [NeBot f] [NeBot g] : NeBot (map₂ m f g) := .map₂ ‹_› ‹_›

theorem NeBot.of_map₂_left (h : (map₂ m f g).NeBot) : f.NeBot :=
  (map₂_neBot_iff.1 h).1
#align filter.ne_bot.of_map₂_left Filter.NeBot.of_map₂_left

theorem NeBot.of_map₂_right (h : (map₂ m f g).NeBot) : g.NeBot :=
  (map₂_neBot_iff.1 h).2
#align filter.ne_bot.of_map₂_right Filter.NeBot.of_map₂_right

theorem map₂_sup_left : map₂ m (f₁ ⊔ f₂) g = map₂ m f₁ g ⊔ map₂ m f₂ g := by
  simp_rw [← map_prod_eq_map₂, sup_prod, map_sup]
#align filter.map₂_sup_left Filter.map₂_sup_left

theorem map₂_sup_right : map₂ m f (g₁ ⊔ g₂) = map₂ m f g₁ ⊔ map₂ m f g₂ := by
  simp_rw [← map_prod_eq_map₂, prod_sup, map_sup]
#align filter.map₂_sup_right Filter.map₂_sup_right

theorem map₂_inf_subset_left : map₂ m (f₁ ⊓ f₂) g ≤ map₂ m f₁ g ⊓ map₂ m f₂ g :=
  Monotone.map_inf_le (fun _ _ ↦ map₂_mono_right) f₁ f₂
#align filter.map₂_inf_subset_left Filter.map₂_inf_subset_left

theorem map₂_inf_subset_right : map₂ m f (g₁ ⊓ g₂) ≤ map₂ m f g₁ ⊓ map₂ m f g₂ :=
  Monotone.map_inf_le (fun _ _ ↦ map₂_mono_left) g₁ g₂
#align filter.map₂_inf_subset_right Filter.map₂_inf_subset_right

@[simp]
theorem map₂_pure_left : map₂ m (pure a) g = g.map (m a) := by
  rw [← map_prod_eq_map₂, pure_prod, map_map]; rfl
#align filter.map₂_pure_left Filter.map₂_pure_left

@[simp]
theorem map₂_pure_right : map₂ m f (pure b) = f.map (m · b) := by
  rw [← map_prod_eq_map₂, prod_pure, map_map]; rfl
#align filter.map₂_pure_right Filter.map₂_pure_right

theorem map₂_pure : map₂ m (pure a) (pure b) = pure (m a b) := by rw [map₂_pure_right, map_pure]
#align filter.map₂_pure Filter.map₂_pure

theorem map₂_swap (m : α → β → γ) (f : Filter α) (g : Filter β) :
    map₂ m f g = map₂ (fun a b => m b a) g f := by
  rw [← map_prod_eq_map₂, prod_comm, map_map, ← map_prod_eq_map₂, Function.comp_def]
#align filter.map₂_swap Filter.map₂_swap

@[simp]
theorem map₂_left [NeBot g] : map₂ (fun x _ => x) f g = f := by
  rw [← map_prod_eq_map₂, map_fst_prod]
#align filter.map₂_left Filter.map₂_left

@[simp]
theorem map₂_right [NeBot f] : map₂ (fun _ y => y) f g = g := by rw [map₂_swap, map₂_left]
#align filter.map₂_right Filter.map₂_right

#noalign filter.map₃
#noalign filter.map₂_map₂_left
#noalign filter.map₂_map₂_right

theorem map_map₂ (m : α → β → γ) (n : γ → δ) :
    (map₂ m f g).map n = map₂ (fun a b => n (m a b)) f g := by
  rw [← map_prod_eq_map₂, ← map_prod_eq_map₂, map_map]; rfl
#align filter.map_map₂ Filter.map_map₂

theorem map₂_map_left (m : γ → β → δ) (n : α → γ) :
    map₂ m (f.map n) g = map₂ (fun a b => m (n a) b) f g := by
  rw [← map_prod_eq_map₂, ← map_prod_eq_map₂, ← @map_id _ g, prod_map_map_eq, map_map, map_id]; rfl
#align filter.map₂_map_left Filter.map₂_map_left

theorem map₂_map_right (m : α → γ → δ) (n : β → γ) :
    map₂ m f (g.map n) = map₂ (fun a b => m a (n b)) f g := by
  rw [map₂_swap, map₂_map_left, map₂_swap]
#align filter.map₂_map_right Filter.map₂_map_right

@[simp]
theorem map₂_curry (m : α × β → γ) (f : Filter α) (g : Filter β) :
    map₂ (curry m) f g = (f ×ˢ g).map m :=
  (map_prod_eq_map₂' _ _ _).symm
#align filter.map₂_curry Filter.map₂_curry

@[simp]
theorem map_uncurry_prod (m : α → β → γ) (f : Filter α) (g : Filter β) :
    (f ×ˢ g).map (uncurry m) = map₂ m f g :=
  (map₂_curry (uncurry m) f g).symm
#align filter.map_uncurry_prod Filter.map_uncurry_prod

/-!
### Algebraic replacement rules

A collection of lemmas to transfer associativity, commutativity, distributivity, ... of operations
to the associativity, commutativity, distributivity, ... of `Filter.map₂` of those operations.

The proof pattern is `map₂_lemma operation_lemma`. For example, `map₂_comm mul_comm` proves that
`map₂ (*) f g = map₂ (*) g f` in a `CommSemigroup`.
-/

theorem map₂_assoc {m : δ → γ → ε} {n : α → β → δ} {m' : α → ε' → ε} {n' : β → γ → ε'}
    {h : Filter γ} (h_assoc : ∀ a b c, m (n a b) c = m' a (n' b c)) :
    map₂ m (map₂ n f g) h = map₂ m' f (map₂ n' g h) := by
  rw [← map_prod_eq_map₂ n, ← map_prod_eq_map₂ n', map₂_map_left, map₂_map_right,
    ← map_prod_eq_map₂, ← map_prod_eq_map₂, ← prod_assoc, map_map]
  simp only [h_assoc, Function.comp, Equiv.prodAssoc_apply]
#align filter.map₂_assoc Filter.map₂_assoc

theorem map₂_comm {n : β → α → γ} (h_comm : ∀ a b, m a b = n b a) : map₂ m f g = map₂ n g f :=
  (map₂_swap _ _ _).trans <| by simp_rw [h_comm]
#align filter.map₂_comm Filter.map₂_comm

theorem map₂_left_comm {m : α → δ → ε} {n : β → γ → δ} {m' : α → γ → δ'} {n' : β → δ' → ε}
    (h_left_comm : ∀ a b c, m a (n b c) = n' b (m' a c)) :
    map₂ m f (map₂ n g h) = map₂ n' g (map₂ m' f h) := by
  rw [map₂_swap m', map₂_swap m]
  exact map₂_assoc fun _ _ _ => h_left_comm _ _ _
#align filter.map₂_left_comm Filter.map₂_left_comm

theorem map₂_right_comm {m : δ → γ → ε} {n : α → β → δ} {m' : α → γ → δ'} {n' : δ' → β → ε}
    (h_right_comm : ∀ a b c, m (n a b) c = n' (m' a c) b) :
    map₂ m (map₂ n f g) h = map₂ n' (map₂ m' f h) g := by
  rw [map₂_swap n, map₂_swap n']
  exact map₂_assoc fun _ _ _ => h_right_comm _ _ _
#align filter.map₂_right_comm Filter.map₂_right_comm

theorem map_map₂_distrib {n : γ → δ} {m' : α' → β' → δ} {n₁ : α → α'} {n₂ : β → β'}
    (h_distrib : ∀ a b, n (m a b) = m' (n₁ a) (n₂ b)) :
    (map₂ m f g).map n = map₂ m' (f.map n₁) (g.map n₂) := by
  simp_rw [map_map₂, map₂_map_left, map₂_map_right, h_distrib]
#align filter.map_map₂_distrib Filter.map_map₂_distrib

/-- Symmetric statement to `Filter.map₂_map_left_comm`. -/
theorem map_map₂_distrib_left {n : γ → δ} {m' : α' → β → δ} {n' : α → α'}
    (h_distrib : ∀ a b, n (m a b) = m' (n' a) b) : (map₂ m f g).map n = map₂ m' (f.map n') g :=
  map_map₂_distrib h_distrib
#align filter.map_map₂_distrib_left Filter.map_map₂_distrib_left

/-- Symmetric statement to `Filter.map_map₂_right_comm`. -/
theorem map_map₂_distrib_right {n : γ → δ} {m' : α → β' → δ} {n' : β → β'}
    (h_distrib : ∀ a b, n (m a b) = m' a (n' b)) : (map₂ m f g).map n = map₂ m' f (g.map n') :=
  map_map₂_distrib h_distrib
#align filter.map_map₂_distrib_right Filter.map_map₂_distrib_right

/-- Symmetric statement to `Filter.map_map₂_distrib_left`. -/
theorem map₂_map_left_comm {m : α' → β → γ} {n : α → α'} {m' : α → β → δ} {n' : δ → γ}
    (h_left_comm : ∀ a b, m (n a) b = n' (m' a b)) : map₂ m (f.map n) g = (map₂ m' f g).map n' :=
  (map_map₂_distrib_left fun a b => (h_left_comm a b).symm).symm
#align filter.map₂_map_left_comm Filter.map₂_map_left_comm

/-- Symmetric statement to `Filter.map_map₂_distrib_right`. -/
theorem map_map₂_right_comm {m : α → β' → γ} {n : β → β'} {m' : α → β → δ} {n' : δ → γ}
    (h_right_comm : ∀ a b, m a (n b) = n' (m' a b)) : map₂ m f (g.map n) = (map₂ m' f g).map n' :=
  (map_map₂_distrib_right fun a b => (h_right_comm a b).symm).symm
#align filter.map_map₂_right_comm Filter.map_map₂_right_comm

/-- The other direction does not hold because of the `f-f` cross terms on the RHS. -/
theorem map₂_distrib_le_left {m : α → δ → ε} {n : β → γ → δ} {m₁ : α → β → β'} {m₂ : α → γ → γ'}
    {n' : β' → γ' → ε} (h_distrib : ∀ a b c, m a (n b c) = n' (m₁ a b) (m₂ a c)) :
    map₂ m f (map₂ n g h) ≤ map₂ n' (map₂ m₁ f g) (map₂ m₂ f h) := by
  rintro s ⟨t₁, ⟨u₁, hu₁, v, hv, ht₁⟩, t₂, ⟨u₂, hu₂, w, hw, ht₂⟩, hs⟩
  refine ⟨u₁ ∩ u₂, inter_mem hu₁ hu₂, _, image2_mem_map₂ hv hw, ?_⟩
  refine (image2_distrib_subset_left h_distrib).trans ((image2_subset ?_ ?_).trans hs)
  · exact (image2_subset_right <| inter_subset_left _ _).trans ht₁
  · exact (image2_subset_right <| inter_subset_right _ _).trans ht₂
#align filter.map₂_distrib_le_left Filter.map₂_distrib_le_left

/-- The other direction does not hold because of the `h`-`h` cross terms on the RHS. -/
theorem map₂_distrib_le_right {m : δ → γ → ε} {n : α → β → δ} {m₁ : α → γ → α'} {m₂ : β → γ → β'}
    {n' : α' → β' → ε} (h_distrib : ∀ a b c, m (n a b) c = n' (m₁ a c) (m₂ b c)) :
    map₂ m (map₂ n f g) h ≤ map₂ n' (map₂ m₁ f h) (map₂ m₂ g h) := by
  rintro s ⟨t₁, ⟨u, hu, w₁, hw₁, ht₁⟩, t₂, ⟨v, hv, w₂, hw₂, ht₂⟩, hs⟩
  refine ⟨_, image2_mem_map₂ hu hv, w₁ ∩ w₂, inter_mem hw₁ hw₂, ?_⟩
  refine (image2_distrib_subset_right h_distrib).trans ((image2_subset ?_ ?_).trans hs)
  · exact (image2_subset_left <| inter_subset_left _ _).trans ht₁
  · exact (image2_subset_left <| inter_subset_right _ _).trans ht₂
#align filter.map₂_distrib_le_right Filter.map₂_distrib_le_right

theorem map_map₂_antidistrib {n : γ → δ} {m' : β' → α' → δ} {n₁ : β → β'} {n₂ : α → α'}
    (h_antidistrib : ∀ a b, n (m a b) = m' (n₁ b) (n₂ a)) :
    (map₂ m f g).map n = map₂ m' (g.map n₁) (f.map n₂) := by
  rw [map₂_swap m]
  exact map_map₂_distrib fun _ _ => h_antidistrib _ _
#align filter.map_map₂_antidistrib Filter.map_map₂_antidistrib

/-- Symmetric statement to `Filter.map₂_map_left_anticomm`. -/
theorem map_map₂_antidistrib_left {n : γ → δ} {m' : β' → α → δ} {n' : β → β'}
    (h_antidistrib : ∀ a b, n (m a b) = m' (n' b) a) : (map₂ m f g).map n = map₂ m' (g.map n') f :=
  map_map₂_antidistrib h_antidistrib
#align filter.map_map₂_antidistrib_left Filter.map_map₂_antidistrib_left

/-- Symmetric statement to `Filter.map_map₂_right_anticomm`. -/
theorem map_map₂_antidistrib_right {n : γ → δ} {m' : β → α' → δ} {n' : α → α'}
    (h_antidistrib : ∀ a b, n (m a b) = m' b (n' a)) : (map₂ m f g).map n = map₂ m' g (f.map n') :=
  map_map₂_antidistrib h_antidistrib
#align filter.map_map₂_antidistrib_right Filter.map_map₂_antidistrib_right

/-- Symmetric statement to `Filter.map_map₂_antidistrib_left`. -/
theorem map₂_map_left_anticomm {m : α' → β → γ} {n : α → α'} {m' : β → α → δ} {n' : δ → γ}
    (h_left_anticomm : ∀ a b, m (n a) b = n' (m' b a)) :
    map₂ m (f.map n) g = (map₂ m' g f).map n' :=
  (map_map₂_antidistrib_left fun a b => (h_left_anticomm b a).symm).symm
#align filter.map₂_map_left_anticomm Filter.map₂_map_left_anticomm

/-- Symmetric statement to `Filter.map_map₂_antidistrib_right`. -/
theorem map_map₂_right_anticomm {m : α → β' → γ} {n : β → β'} {m' : β → α → δ} {n' : δ → γ}
    (h_right_anticomm : ∀ a b, m a (n b) = n' (m' b a)) :
    map₂ m f (g.map n) = (map₂ m' g f).map n' :=
  (map_map₂_antidistrib_right fun a b => (h_right_anticomm b a).symm).symm
#align filter.map_map₂_right_anticomm Filter.map_map₂_right_anticomm

/-- If `a` is a left identity for `f : α → β → β`, then `pure a` is a left identity for
`Filter.map₂ f`. -/
theorem map₂_left_identity {f : α → β → β} {a : α} (h : ∀ b, f a b = b) (l : Filter β) :
    map₂ f (pure a) l = l := by rw [map₂_pure_left, show f a = id from funext h, map_id]
#align filter.map₂_left_identity Filter.map₂_left_identity

/-- If `b` is a right identity for `f : α → β → α`, then `pure b` is a right identity for
`Filter.map₂ f`. -/
theorem map₂_right_identity {f : α → β → α} {b : β} (h : ∀ a, f a b = a) (l : Filter α) :
    map₂ f l (pure b) = l := by rw [map₂_pure_right, funext h, map_id']
#align filter.map₂_right_identity Filter.map₂_right_identity

end Filter
