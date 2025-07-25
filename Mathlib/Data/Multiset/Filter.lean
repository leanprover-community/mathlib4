/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Multiset.MapFold
import Mathlib.Data.Set.Function
import Mathlib.Order.Hom.Basic

/-!
# Filtering multisets by a predicate

## Main definitions

* `Multiset.filter`: `filter p s` is the multiset of elements in `s` that satisfy `p`.
* `Multiset.filterMap`: `filterMap f s` is the multiset of `b`s where `some b ∈ map f s`.
-/

-- No algebra should be required
assert_not_exists Monoid

universe v

open List Subtype Nat Function

variable {α : Type*} {β : Type v} {γ : Type*}

namespace Multiset

/-! ### `Multiset.filter` -/


section

variable (p : α → Prop) [DecidablePred p]

/-- `Filter p s` returns the elements in `s` (with the same multiplicities)
  which satisfy `p`, and removes the rest. -/
def filter (s : Multiset α) : Multiset α :=
  Quot.liftOn s (fun l => (List.filter p l : Multiset α)) fun _l₁ _l₂ h => Quot.sound <| h.filter p

@[simp, norm_cast] lemma filter_coe (l : List α) : filter p l = l.filter p := rfl

@[simp]
theorem filter_zero : filter p 0 = 0 :=
  rfl

@[congr]
theorem filter_congr {p q : α → Prop} [DecidablePred p] [DecidablePred q] {s : Multiset α} :
    (∀ x ∈ s, p x ↔ q x) → filter p s = filter q s :=
  Quot.inductionOn s fun _l h => congr_arg ofList <| List.filter_congr <| by simpa using h

@[simp]
theorem filter_add (s t : Multiset α) : filter p (s + t) = filter p s + filter p t :=
  Quotient.inductionOn₂ s t fun _l₁ _l₂ => congr_arg ofList <| filter_append _ _

@[simp]
theorem filter_le (s : Multiset α) : filter p s ≤ s :=
  Quot.inductionOn s fun _l => filter_sublist.subperm

@[simp]
theorem filter_subset (s : Multiset α) : filter p s ⊆ s :=
  subset_of_le <| filter_le _ _

@[gcongr]
theorem filter_le_filter {s t} (h : s ≤ t) : filter p s ≤ filter p t :=
  leInductionOn h fun h => (h.filter (p ·)).subperm

theorem monotone_filter_left : Monotone (filter p) := fun _s _t => filter_le_filter p

theorem monotone_filter_right (s : Multiset α) ⦃p q : α → Prop⦄ [DecidablePred p] [DecidablePred q]
    (h : ∀ b, p b → q b) :
    s.filter p ≤ s.filter q :=
  Quotient.inductionOn s fun l => (l.monotone_filter_right <| by simpa using h).subperm

variable {p}

@[simp]
theorem filter_cons_of_pos {a : α} (s) : p a → filter p (a ::ₘ s) = a ::ₘ filter p s :=
  Quot.inductionOn s fun _ h => congr_arg ofList <| List.filter_cons_of_pos <| by simpa using h

@[simp]
theorem filter_cons_of_neg {a : α} (s) : ¬p a → filter p (a ::ₘ s) = filter p s :=
  Quot.inductionOn s fun _ h => congr_arg ofList <| List.filter_cons_of_neg <| by simpa using h

@[simp]
theorem mem_filter {a : α} {s} : a ∈ filter p s ↔ a ∈ s ∧ p a :=
  Quot.inductionOn s fun _l => by simp

theorem of_mem_filter {a : α} {s} (h : a ∈ filter p s) : p a :=
  (mem_filter.1 h).2

theorem mem_of_mem_filter {a : α} {s} (h : a ∈ filter p s) : a ∈ s :=
  (mem_filter.1 h).1

theorem mem_filter_of_mem {a : α} {l} (m : a ∈ l) (h : p a) : a ∈ filter p l :=
  mem_filter.2 ⟨m, h⟩

theorem filter_eq_self {s} : filter p s = s ↔ ∀ a ∈ s, p a :=
  Quot.inductionOn s fun _l =>
    Iff.trans ⟨fun h => filter_sublist.eq_of_length (congr_arg card h),
      congr_arg ofList⟩ <| by simp

theorem filter_eq_nil {s} : filter p s = 0 ↔ ∀ a ∈ s, ¬p a :=
  Quot.inductionOn s fun _l =>
    Iff.trans ⟨fun h => eq_nil_of_length_eq_zero (congr_arg card h), congr_arg ofList⟩ (by simp)

theorem le_filter {s t} : s ≤ filter p t ↔ s ≤ t ∧ ∀ a ∈ s, p a :=
  ⟨fun h => ⟨le_trans h (filter_le _ _), fun _a m => of_mem_filter (mem_of_le h m)⟩, fun ⟨h, al⟩ =>
    filter_eq_self.2 al ▸ filter_le_filter p h⟩

theorem filter_cons {a : α} (s : Multiset α) :
    filter p (a ::ₘ s) = (if p a then {a} else 0) + filter p s := by
  split_ifs with h
  · rw [filter_cons_of_pos _ h, singleton_add]
  · rw [filter_cons_of_neg _ h, Multiset.zero_add]

theorem filter_singleton {a : α} (p : α → Prop) [DecidablePred p] :
    filter p {a} = if p a then {a} else ∅ := by
  simp only [singleton, filter_cons, filter_zero, Multiset.add_zero, empty_eq_zero]

variable (p)

@[simp]
theorem filter_filter (q) [DecidablePred q] (s : Multiset α) :
    filter p (filter q s) = filter (fun a => p a ∧ q a) s :=
  Quot.inductionOn s fun l => by simp

lemma filter_comm (q) [DecidablePred q] (s : Multiset α) :
    filter p (filter q s) = filter q (filter p s) := by simp [and_comm]

theorem filter_add_filter (q) [DecidablePred q] (s : Multiset α) :
    filter p s + filter q s = filter (fun a => p a ∨ q a) s + filter (fun a => p a ∧ q a) s :=
  Multiset.induction_on s rfl fun a s IH => by by_cases p a <;> by_cases q a <;> simp [*]

theorem filter_add_not (s : Multiset α) : filter p s + filter (fun a => ¬p a) s = s := by
  rw [filter_add_filter, filter_eq_self.2, filter_eq_nil.2]
  · simp only [Multiset.add_zero]
  · simp [-Bool.not_eq_true, -not_and]
  · simp only [implies_true, Decidable.em]

theorem filter_map (f : β → α) (s : Multiset β) : filter p (map f s) = map f (filter (p ∘ f) s) :=
  Quot.inductionOn s fun l => by simp [List.filter_map]; rfl

-- TODO: rename to `map_filter` when the deprecated alias above is removed.
lemma map_filter' {f : α → β} (hf : Injective f) (s : Multiset α)
    [DecidablePred fun b => ∃ a, p a ∧ f a = b] :
    (s.filter p).map f = (s.map f).filter fun b => ∃ a, p a ∧ f a = b := by
  simp [filter_map, hf.eq_iff]

lemma card_filter_le_iff (s : Multiset α) (P : α → Prop) [DecidablePred P] (n : ℕ) :
    card (s.filter P) ≤ n ↔ ∀ s' ≤ s, n < card s' → ∃ a ∈ s', ¬ P a := by
  fconstructor
  · intro H s' hs' s'_card
    by_contra! rid
    have card := card_le_card (monotone_filter_left P hs') |>.trans H
    exact s'_card.not_ge (filter_eq_self.mpr rid ▸ card)
  · contrapose!
    exact fun H ↦ ⟨s.filter P, filter_le _ _, H, fun a ha ↦ (mem_filter.mp ha).2⟩

/-! ### Simultaneously filter and map elements of a multiset -/


/-- `filterMap f s` is a combination filter/map operation on `s`.
  The function `f : α → Option β` is applied to each element of `s`;
  if `f a` is `some b` then `b` is added to the result, otherwise
  `a` is removed from the resulting multiset. -/
def filterMap (f : α → Option β) (s : Multiset α) : Multiset β :=
  Quot.liftOn s (fun l => (List.filterMap f l : Multiset β))
    fun _l₁ _l₂ h => Quot.sound <| h.filterMap f

@[simp, norm_cast]
lemma filterMap_coe (f : α → Option β) (l : List α) : filterMap f l = l.filterMap f := rfl

@[simp]
theorem filterMap_zero (f : α → Option β) : filterMap f 0 = 0 :=
  rfl

@[simp]
theorem filterMap_cons_none {f : α → Option β} (a : α) (s : Multiset α) (h : f a = none) :
    filterMap f (a ::ₘ s) = filterMap f s :=
  Quot.inductionOn s fun _ => congr_arg ofList <| List.filterMap_cons_none h

@[simp]
theorem filterMap_cons_some (f : α → Option β) (a : α) (s : Multiset α) {b : β}
    (h : f a = some b) : filterMap f (a ::ₘ s) = b ::ₘ filterMap f s :=
  Quot.inductionOn s fun _ => congr_arg ofList <| List.filterMap_cons_some h

theorem filterMap_eq_map (f : α → β) : filterMap (some ∘ f) = map f :=
  funext fun s =>
    Quot.inductionOn s fun l => congr_arg ofList <| congr_fun List.filterMap_eq_map l

theorem filterMap_eq_filter : filterMap (Option.guard p) = filter p :=
  funext fun s =>
    Quot.inductionOn s fun l => congr_arg ofList <| by
      rw [← List.filterMap_eq_filter]

theorem filterMap_filterMap (f : α → Option β) (g : β → Option γ) (s : Multiset α) :
    filterMap g (filterMap f s) = filterMap (fun x => (f x).bind g) s :=
  Quot.inductionOn s fun _ => congr_arg ofList List.filterMap_filterMap

theorem map_filterMap (f : α → Option β) (g : β → γ) (s : Multiset α) :
    map g (filterMap f s) = filterMap (fun x => (f x).map g) s :=
  Quot.inductionOn s fun _ => congr_arg ofList List.map_filterMap

theorem filterMap_map (f : α → β) (g : β → Option γ) (s : Multiset α) :
    filterMap g (map f s) = filterMap (g ∘ f) s :=
  Quot.inductionOn s fun _ => congr_arg ofList List.filterMap_map

theorem filter_filterMap (f : α → Option β) (p : β → Prop) [DecidablePred p] (s : Multiset α) :
    filter p (filterMap f s) = filterMap (fun x => (f x).filter p) s :=
  Quot.inductionOn s fun _ => congr_arg ofList List.filter_filterMap

theorem filterMap_filter (f : α → Option β) (s : Multiset α) :
    filterMap f (filter p s) = filterMap (fun x => if p x then f x else none) s :=
  Quot.inductionOn s fun l => congr_arg ofList <| by
    simpa using List.filterMap_filter (f := f) (p := p)

@[simp]
theorem filterMap_some (s : Multiset α) : filterMap some s = s :=
  Quot.inductionOn s fun _ => congr_arg ofList List.filterMap_some

@[simp]
theorem mem_filterMap (f : α → Option β) (s : Multiset α) {b : β} :
    b ∈ filterMap f s ↔ ∃ a, a ∈ s ∧ f a = some b :=
  Quot.inductionOn s fun _ => List.mem_filterMap

theorem map_filterMap_of_inv (f : α → Option β) (g : β → α) (H : ∀ x : α, (f x).map g = some x)
    (s : Multiset α) : map g (filterMap f s) = s :=
  Quot.inductionOn s fun _ => congr_arg ofList <| List.map_filterMap_of_inv H

@[gcongr]
theorem filterMap_le_filterMap (f : α → Option β) {s t : Multiset α} (h : s ≤ t) :
    filterMap f s ≤ filterMap f t :=
  leInductionOn h fun h => (h.filterMap _).subperm

/-! ### countP -/

theorem countP_eq_card_filter (s) : countP p s = card (filter p s) :=
  Quot.inductionOn s fun l => l.countP_eq_length_filter (p := (p ·))

@[simp]
theorem countP_filter (q) [DecidablePred q] (s : Multiset α) :
    countP p (filter q s) = countP (fun a => p a ∧ q a) s := by simp [countP_eq_card_filter]

theorem countP_eq_countP_filter_add (s) (p q : α → Prop) [DecidablePred p] [DecidablePred q] :
    countP p s = (filter q s).countP p + (filter (fun a => ¬q a) s).countP p :=
  Quot.inductionOn s fun l => by
    convert l.countP_eq_countP_filter_add (p ·) (q ·)
    simp

theorem countP_map (f : α → β) (s : Multiset α) (p : β → Prop) [DecidablePred p] :
    countP p (map f s) = card (s.filter fun a => p (f a)) := by
  refine Multiset.induction_on s ?_ fun a t IH => ?_
  · rw [map_zero, countP_zero, filter_zero, card_zero]
  · rw [map_cons, countP_cons, IH, filter_cons, card_add, apply_ite card, card_zero, card_singleton,
      Nat.add_comm]

lemma filter_attach (s : Multiset α) (p : α → Prop) [DecidablePred p] :
    (s.attach.filter fun a : {a // a ∈ s} ↦ p ↑a) =
      (s.filter p).attach.map (Subtype.map id fun _ ↦ Multiset.mem_of_mem_filter) :=
  Quotient.inductionOn s fun l ↦ congr_arg _ (List.filter_attach l p)

end

/-! ### Multiplicity of an element -/


section

variable [DecidableEq α] {s t u : Multiset α}

@[simp]
theorem count_filter_of_pos {p} [DecidablePred p] {a} {s : Multiset α} (h : p a) :
    count a (filter p s) = count a s :=
  Quot.inductionOn s fun _l => by
    simp only [quot_mk_to_coe'', filter_coe, coe_count]
    apply count_filter
    simpa using h

theorem count_filter_of_neg {p} [DecidablePred p] {a} {s : Multiset α} (h : ¬p a) :
    count a (filter p s) = 0 := by
  simp [h]

theorem count_filter {p} [DecidablePred p] {a} {s : Multiset α} :
    count a (filter p s) = if p a then count a s else 0 := by
  split_ifs with h
  · exact count_filter_of_pos h
  · exact count_filter_of_neg h

theorem count_map {α β : Type*} (f : α → β) (s : Multiset α) [DecidableEq β] (b : β) :
    count b (map f s) = card (s.filter fun a => b = f a) := by
  simp [count, countP_map]

/-- `Multiset.map f` preserves `count` if `f` is injective on the set of elements contained in
the multiset -/
theorem count_map_eq_count [DecidableEq β] (f : α → β) (s : Multiset α)
    (hf : Set.InjOn f { x : α | x ∈ s }) (x) (H : x ∈ s) : (s.map f).count (f x) = s.count x := by
  suffices (filter (fun a : α => f x = f a) s).count x = card (filter (fun a : α => f x = f a) s) by
    rw [count, countP_map, ← this]
    exact count_filter_of_pos <| rfl
  · rw [eq_replicate_card.2 fun b hb => (hf H (mem_filter.1 hb).left _).symm]
    · simp only [count_replicate, if_true, card_replicate]
    · simp only [mem_filter, and_imp, @eq_comm _ (f x), imp_self, implies_true]

/-- `Multiset.map f` preserves `count` if `f` is injective -/
theorem count_map_eq_count' [DecidableEq β] (f : α → β) (s : Multiset α) (hf : Function.Injective f)
    (x : α) : (s.map f).count (f x) = s.count x := by
  by_cases H : x ∈ s
  · exact count_map_eq_count f _ hf.injOn _ H
  · rw [count_eq_zero_of_notMem H, count_eq_zero, mem_map]
    rintro ⟨k, hks, hkx⟩
    rw [hf hkx] at hks
    contradiction

theorem filter_eq' (s : Multiset α) (b : α) : s.filter (· = b) = replicate (count b s) b :=
  Quotient.inductionOn s fun l => by
    simp only [quot_mk_to_coe, filter_coe, coe_count]
    rw [List.filter_eq, coe_replicate]

theorem filter_eq (s : Multiset α) (b : α) : s.filter (Eq b) = replicate (count b s) b := by
  simp_rw [← filter_eq', eq_comm]

end

/-! ### Subtraction -/

section sub
variable [DecidableEq α] {s t u : Multiset α} {a : α}

@[simp]
lemma filter_sub (p : α → Prop) [DecidablePred p] (s t : Multiset α) :
    filter p (s - t) = filter p s - filter p t := by
  revert s; refine Multiset.induction_on t (by simp) fun a t IH s => ?_
  rw [sub_cons, IH]
  by_cases h : p a
  · rw [filter_cons_of_pos _ h, sub_cons]
    congr
    by_cases m : a ∈ s
    · rw [← cons_inj_right a, ← filter_cons_of_pos _ h, cons_erase (mem_filter_of_mem m h),
        cons_erase m]
    · rw [erase_of_notMem m, erase_of_notMem (mt mem_of_mem_filter m)]
  · rw [filter_cons_of_neg _ h]
    by_cases m : a ∈ s
    · rw [(by rw [filter_cons_of_neg _ h] : filter p (erase s a) = filter p (a ::ₘ erase s a)),
        cons_erase m]
    · rw [erase_of_notMem m]

@[simp]
lemma sub_filter_eq_filter_not (p : α → Prop) [DecidablePred p] (s : Multiset α) :
    s - s.filter p = s.filter fun a ↦ ¬ p a := by ext a; by_cases h : p a <;> simp [h]

end sub

section Embedding

@[simp]
theorem map_le_map_iff {f : α → β} (hf : Function.Injective f) {s t : Multiset α} :
    s.map f ≤ t.map f ↔ s ≤ t := by
  classical
    refine ⟨fun h => le_iff_count.mpr fun a => ?_, map_le_map⟩
    simpa [count_map_eq_count' f _ hf] using le_iff_count.mp h (f a)

/-- Associate to an embedding `f` from `α` to `β` the order embedding that maps a multiset to its
image under `f`. -/
@[simps!]
def mapEmbedding (f : α ↪ β) : Multiset α ↪o Multiset β :=
  OrderEmbedding.ofMapLEIff (map f) fun _ _ => map_le_map_iff f.inj'

end Embedding

theorem count_eq_card_filter_eq [DecidableEq α] (s : Multiset α) (a : α) :
    s.count a = card (s.filter (a = ·)) := by rw [count, countP_eq_card_filter]

/--
Mapping a multiset through a predicate and counting the `True`s yields the cardinality of the set
filtered by the predicate. Note that this uses the notion of a multiset of `Prop`s - due to the
decidability requirements of `count`, the decidability instance on the LHS is different from the
RHS. In particular, the decidability instance on the left leaks `Classical.decEq`.
See [here](https://github.com/leanprover-community/mathlib/pull/11306#discussion_r782286812)
for more discussion.
-/
@[simp]
theorem map_count_True_eq_filter_card (s : Multiset α) (p : α → Prop) [DecidablePred p] :
    (s.map p).count True = card (s.filter p) := by
  simp only [count_eq_card_filter_eq, filter_map, card_map, Function.id_comp,
    eq_true_eq_id, Function.comp_apply]

section Map

lemma filter_attach' (s : Multiset α) (p : {a // a ∈ s} → Prop) [DecidableEq α]
    [DecidablePred p] :
    s.attach.filter p =
      (s.filter fun x ↦ ∃ h, p ⟨x, h⟩).attach.map (Subtype.map id fun _ ↦ mem_of_mem_filter) := by
  classical
  refine Multiset.map_injective Subtype.val_injective ?_
  rw [map_filter' _ Subtype.val_injective]
  simp only [Function.comp, Subtype.exists, Subtype.map,
    exists_and_right, exists_eq_right, attach_map_val, map_map, id]

end Map

section Nodup

variable {s : Multiset α}

theorem Nodup.filter (p : α → Prop) [DecidablePred p] {s} : Nodup s → Nodup (filter p s) :=
  Quot.induction_on s fun _ => List.Nodup.filter (p ·)

theorem Nodup.erase_eq_filter [DecidableEq α] (a : α) {s} :
    Nodup s → s.erase a = Multiset.filter (· ≠ a) s :=
  Quot.induction_on s fun _ d =>
    congr_arg ((↑) : List α → Multiset α) <| by simpa using List.Nodup.erase_eq_filter d a

protected theorem Nodup.filterMap (f : α → Option β) (H : ∀ a a' b, b ∈ f a → b ∈ f a' → a = a') :
    Nodup s → Nodup (filterMap f s) :=
  Quot.induction_on s fun _ => List.Nodup.filterMap H

theorem Nodup.mem_erase_iff [DecidableEq α] {a b : α} {l} (d : Nodup l) :
    a ∈ l.erase b ↔ a ≠ b ∧ a ∈ l := by
  rw [d.erase_eq_filter b, mem_filter, and_comm]

theorem Nodup.notMem_erase [DecidableEq α] {a : α} {s} (h : Nodup s) : a ∉ s.erase a := fun ha =>
  (h.mem_erase_iff.1 ha).1 rfl

@[deprecated (since := "2025-05-23")] alias Nodup.not_mem_erase := Nodup.notMem_erase

end Nodup

end Multiset
