/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.List.Pairwise
public import Mathlib.Data.Multiset.Sort
public import Mathlib.Order.RelIso.Set

/-!
# Construct a sorted list from a finset.
-/

@[expose] public section

namespace Finset

open Multiset Nat

variable {α β : Type*}

/-! ### sort -/


section sort

/-- `sort s` constructs a sorted list from the unordered set `s`.
  (Uses merge sort algorithm.) -/
def sort (s : Finset α) (r : α → α → Prop := by exact fun a b => a ≤ b)
    [DecidableRel r] [IsTrans α r] [Std.Antisymm r] [Std.Total r] : List α :=
  Multiset.sort s.1 r

section

variable (f : α ↪ β) (s : Finset α)
variable (r : α → α → Prop) [DecidableRel r] [IsTrans α r] [Std.Antisymm r] [Std.Total r]
variable (r' : β → β → Prop) [DecidableRel r'] [IsTrans β r'] [Std.Antisymm r'] [Std.Total r']

@[simp]
theorem sort_val : Multiset.sort s.val r = sort s r :=
  rfl

@[simp]
theorem pairwise_sort : List.Pairwise r (sort s r) :=
  Multiset.pairwise_sort _ _

@[simp]
theorem sort_eq : ↑(sort s r) = s.1 :=
  Multiset.sort_eq _ _

@[simp]
theorem sort_nodup : (sort s r).Nodup :=
  (by rw [sort_eq]; exact s.2 : @Multiset.Nodup α (sort s r))

@[simp]
theorem sort_toFinset [DecidableEq α] : (sort s r).toFinset = s :=
  List.toFinset_eq (s.sort_nodup r) ▸ eq_of_veq (s.sort_eq r)

@[simp]
theorem sort_empty : sort ∅ r = [] :=
  Multiset.sort_zero r

@[simp]
theorem sort_singleton (a : α) : sort {a} r = [a] :=
  Multiset.sort_singleton a r

theorem map_sort
    (hs : ∀ a ∈ s, ∀ b ∈ s, r a b ↔ r' (f a) (f b)) :
    (s.sort r).map f = (s.map f).sort r' :=
  Multiset.map_sort _ _ _ _ hs

theorem _root_.StrictMonoOn.map_finsetSort [LinearOrder α] [LinearOrder β]
    (hf : StrictMonoOn f s) :
    s.sort.map f = (s.map f).sort :=
  Finset.map_sort _ _ _ _ fun _a ha _b hb => (hf.le_iff_le ha hb).symm

@[simp]
theorem sort_range (n : ℕ) : sort (range n) = List.range n :=
  Multiset.sort_range n

open scoped List in
theorem sort_perm_toList : sort s r ~ s.toList := by
  rw [← Multiset.coe_eq_coe]
  simp only [coe_toList, sort_eq]

theorem _root_.List.toFinset_sort [DecidableEq α] {l : List α} (hl : l.Nodup) :
    sort l.toFinset r = l ↔ l.Pairwise r := by
  refine ⟨?_, ((sort_perm_toList _ r).trans (List.toFinset_toList hl)).eq_of_pairwise'
    (pairwise_sort _ _)⟩
  intro h
  rw [← h]
  exact pairwise_sort _ r

end

section

variable {m : Multiset α} {s : Finset α}
variable (r : α → α → Prop) [DecidableRel r] [IsTrans α r] [Std.Antisymm r] [Std.Total r]

@[simp]
theorem sort_mk (h : m.Nodup) : sort ⟨m, h⟩ r = m.sort r := rfl

@[simp]
theorem mem_sort {a : α} : a ∈ sort s r ↔ a ∈ s :=
  Multiset.mem_sort _

@[simp]
theorem length_sort : (sort s r).length = s.card :=
  Multiset.length_sort _

theorem sort_cons {a : α} (h₁ : ∀ b ∈ s, r a b) (h₂ : a ∉ s) :
    sort (cons a s h₂) r = a :: sort s r := by
  rw [sort, cons_val, Multiset.sort_cons a _ r h₁, sort_val]

theorem sort_insert [DecidableEq α] {a : α} (h₁ : ∀ b ∈ s, r a b) (h₂ : a ∉ s) :
    sort (insert a s) r = a :: sort s r := by
  rw [← cons_eq_insert _ _ h₂, sort_cons r h₁]

end

end sort

section SortLinearOrder

variable [LinearOrder α]

theorem sortedLT_sort (s : Finset α) : (sort s).SortedLT :=
  (pairwise_sort _ _).sortedLE.sortedLT_of_nodup (sort_nodup _ _)

@[deprecated (since := "2025-11-27")] alias sort_sorted_lt := sortedLT_sort

theorem sortedGT_sort (s : Finset α) : (sort s (· ≥ ·)).SortedGT :=
  (pairwise_sort _ _).sortedGE.sortedGT_of_nodup (sort_nodup _ _)

@[deprecated (since := "2025-11-27")] alias sort_sorted_gt := sortedGT_sort

theorem sorted_zero_eq_min'_aux (s : Finset α) (h : 0 < s.sort.length) (H : s.Nonempty) :
    s.sort.get ⟨0, h⟩ = s.min' H := by
  let l := s.sort
  apply le_antisymm
  · have : s.min' H ∈ l := (s.mem_sort (· ≤ ·)).mpr (s.min'_mem H)
    obtain ⟨i, hi⟩ : ∃ i, l.get i = s.min' H := List.mem_iff_get.1 this
    rw [← hi]
    exact (s.pairwise_sort (· ≤ ·)).rel_get_of_le (Nat.zero_le i)
  · have : l.get ⟨0, h⟩ ∈ s := (Finset.mem_sort (α := α) (· ≤ ·)).1 (List.get_mem l _)
    exact s.min'_le _ this

theorem sorted_zero_eq_min' {s : Finset α} {h : 0 < s.sort.length} :
    s.sort[0] = s.min' (card_pos.1 <| by rwa [length_sort] at h) :=
  sorted_zero_eq_min'_aux _ _ _

theorem min'_eq_sorted_zero {s : Finset α} {h : s.Nonempty} :
    s.min' h = s.sort[0]'(by rw [length_sort]; exact card_pos.2 h) :=
  (sorted_zero_eq_min'_aux _ _ _).symm

theorem sorted_last_eq_max'_aux (s : Finset α)
    (h : s.sort.length - 1 < s.sort.length) (H : s.Nonempty) :
    s.sort[s.sort.length - 1] = s.max' H := by
  let l := s.sort
  apply le_antisymm
  · have : l.get ⟨s.sort.length - 1, h⟩ ∈ s :=
      (s.mem_sort (· ≤ ·)).1 (List.get_mem l _)
    exact s.le_max' _ this
  · have : s.max' H ∈ l := (s.mem_sort (· ≤ ·)).mpr (s.max'_mem H)
    obtain ⟨i, hi⟩ : ∃ i, l.get i = s.max' H := List.mem_iff_get.1 this
    rw [← hi]
    exact (s.pairwise_sort (· ≤ ·)).rel_get_of_le (Nat.le_sub_one_of_lt i.prop)

theorem sorted_last_eq_max' {s : Finset α}
    {h : s.sort.length - 1 < s.sort.length} :
    s.sort[s.sort.length - 1] =
      s.max' (by rw [length_sort] at h; exact card_pos.1 (lt_of_le_of_lt bot_le h)) :=
  sorted_last_eq_max'_aux _ h _

theorem max'_eq_sorted_last {s : Finset α} {h : s.Nonempty} :
    s.max' h =
      s.sort[s.sort.length - 1]'
        (by simpa using Nat.sub_lt (card_pos.mpr h) Nat.zero_lt_one) :=
  (sorted_last_eq_max'_aux _ (by simpa using Nat.sub_lt (card_pos.mpr h) Nat.zero_lt_one) _).symm

/-- Given a finset `s` of cardinality `k` in a linear order `α`, the map `orderIsoOfFin s h`
is the increasing bijection between `Fin k` and `s` as an `OrderIso`. Here, `h` is a proof that
the cardinality of `s` is `k`. We use this instead of an iso `Fin s.card ≃o s` to avoid
casting issues in further uses of this function. -/
def orderIsoOfFin (s : Finset α) {k : ℕ} (h : s.card = k) : Fin k ≃o s :=
  OrderIso.trans (Fin.castOrderIso ((s.length_sort (· ≤ ·)).trans h).symm) <|
    (s.sortedLT_sort.getIso _).trans <| OrderIso.setCongr {x | x ∈ s.sort (· ≤ ·)} _ <| by simp

/-- Given a finset `s` of cardinality `k` in a linear order `α`, the map `orderEmbOfFin s h` is
the increasing bijection between `Fin k` and `s` as an order embedding into `α`. Here, `h` is a
proof that the cardinality of `s` is `k`. We use this instead of an embedding `Fin s.card ↪o α` to
avoid casting issues in further uses of this function. -/
def orderEmbOfFin (s : Finset α) {k : ℕ} (h : s.card = k) : Fin k ↪o α :=
  (orderIsoOfFin s h).toOrderEmbedding.trans (OrderEmbedding.subtype _)

@[simp]
theorem coe_orderIsoOfFin_apply (s : Finset α) {k : ℕ} (h : s.card = k) (i : Fin k) :
    ↑(orderIsoOfFin s h i) = orderEmbOfFin s h i :=
  rfl

theorem orderIsoOfFin_symm_apply (s : Finset α) {k : ℕ} (h : s.card = k) (x : s) :
    ↑((s.orderIsoOfFin h).symm x) = s.sort.idxOf ↑x :=
  rfl

theorem orderEmbOfFin_apply (s : Finset α) {k : ℕ} (h : s.card = k) (i : Fin k) :
    s.orderEmbOfFin h i = s.sort[i]'(by rw [length_sort, h]; exact i.2) :=
  rfl

@[simp]
theorem orderEmbOfFin_mem (s : Finset α) {k : ℕ} (h : s.card = k) (i : Fin k) :
    s.orderEmbOfFin h i ∈ s :=
  (s.orderIsoOfFin h i).2

@[simp]
theorem range_orderEmbOfFin (s : Finset α) {k : ℕ} (h : s.card = k) :
    Set.range (s.orderEmbOfFin h) = s := by
  simp [orderEmbOfFin]

@[simp]
theorem image_orderEmbOfFin_univ (s : Finset α) {k : ℕ} (h : s.card = k) :
    Finset.image (s.orderEmbOfFin h) Finset.univ = s := by
  apply Finset.coe_injective
  simp

@[simp]
theorem map_orderEmbOfFin_univ (s : Finset α) {k : ℕ} (h : s.card = k) :
    Finset.map (s.orderEmbOfFin h).toEmbedding Finset.univ = s := by
  simp [map_eq_image]

@[simp]
theorem listMap_orderEmbOfFin_finRange (s : Finset α) {k : ℕ} (h : s.card = k) :
    (List.finRange k).map (s.orderEmbOfFin h) = s.sort := by
  obtain rfl : k = s.sort.length := by simp [h]
  exact List.map_getElem_finRange s.sort

/-- The bijection `orderEmbOfFin s h` sends `0` to the minimum of `s`. -/
theorem orderEmbOfFin_zero {s : Finset α} {k : ℕ} (h : s.card = k) (hz : 0 < k) :
    orderEmbOfFin s h ⟨0, hz⟩ = s.min' (card_pos.mp (h.symm ▸ hz)) := by
  simp only [orderEmbOfFin_apply, Fin.getElem_fin, sorted_zero_eq_min']

/-- The bijection `orderEmbOfFin s h` sends `k-1` to the maximum of `s`. -/
theorem orderEmbOfFin_last {s : Finset α} {k : ℕ} (h : s.card = k) (hz : 0 < k) :
    orderEmbOfFin s h ⟨k - 1, Nat.sub_lt hz (Nat.succ_pos 0)⟩ =
      s.max' (card_pos.mp (h.symm ▸ hz)) := by
  simp [orderEmbOfFin_apply, max'_eq_sorted_last, h]

/-- `orderEmbOfFin {a} h` sends any argument to `a`. -/
@[simp]
theorem orderEmbOfFin_singleton (a : α) (i : Fin 1) :
    orderEmbOfFin {a} (card_singleton a) i = a := by
  rw [Subsingleton.elim i ⟨0, Nat.zero_lt_one⟩, orderEmbOfFin_zero _ Nat.zero_lt_one,
    min'_singleton]

/-- Any increasing map `f` from `Fin k` to a finset of cardinality `k` has to coincide with
the increasing bijection `orderEmbOfFin s h`. -/
theorem orderEmbOfFin_unique {s : Finset α} {k : ℕ} (h : s.card = k) {f : Fin k → α}
    (hfs : ∀ x, f x ∈ s) (hmono : StrictMono f) : f = s.orderEmbOfFin h := by
  rw [← hmono.range_inj (s.orderEmbOfFin h).strictMono, range_orderEmbOfFin, ← Set.image_univ,
    ← coe_univ, ← coe_image, coe_inj]
  refine eq_of_subset_of_card_le (fun x hx => ?_) ?_
  · rcases mem_image.1 hx with ⟨x, _, rfl⟩
    exact hfs x
  · rw [h, card_image_of_injective _ hmono.injective, card_univ, Fintype.card_fin]

/-- An order embedding `f` from `Fin k` to a finset of cardinality `k` has to coincide with
the increasing bijection `orderEmbOfFin s h`. -/
theorem orderEmbOfFin_unique' {s : Finset α} {k : ℕ} (h : s.card = k) {f : Fin k ↪o α}
    (hfs : ∀ x, f x ∈ s) : f = s.orderEmbOfFin h :=
  RelEmbedding.ext <| funext_iff.1 <| orderEmbOfFin_unique h hfs f.strictMono

/-- Two parametrizations `orderEmbOfFin` of the same set take the same value on `i` and `j` if
and only if `i = j`. Since they can be defined on a priori not defeq types `Fin k` and `Fin l`
(although necessarily `k = l`), the conclusion is rather written `(i : ℕ) = (j : ℕ)`. -/
@[simp]
theorem orderEmbOfFin_eq_orderEmbOfFin_iff {k l : ℕ} {s : Finset α} {i : Fin k} {j : Fin l}
    {h : s.card = k} {h' : s.card = l} :
    s.orderEmbOfFin h i = s.orderEmbOfFin h' j ↔ (i : ℕ) = (j : ℕ) := by
  substs k l
  exact (s.orderEmbOfFin rfl).eq_iff_eq.trans Fin.ext_iff

/-- Given a finset `s` of size at least `k` in a linear order `α`, the map `orderEmbOfCardLe`
is an order embedding from `Fin k` to `α` whose image is contained in `s`. Specifically, it maps
`Fin k` to an initial segment of `s`. -/
def orderEmbOfCardLe (s : Finset α) {k : ℕ} (h : k ≤ s.card) : Fin k ↪o α :=
  (Fin.castLEOrderEmb h).trans (s.orderEmbOfFin rfl)

theorem orderEmbOfCardLe_mem (s : Finset α) {k : ℕ} (h : k ≤ s.card) (a) :
    orderEmbOfCardLe s h a ∈ s := by
  simp [orderEmbOfCardLe]

lemma orderEmbOfFin_compl_singleton {n : ℕ} {i : Fin (n + 1)} {k : ℕ}
    (h : ({i}ᶜ : Finset _).card = k) :
    ({i}ᶜ : Finset _).orderEmbOfFin h =
      (Fin.castOrderIso <| by simp_all [card_compl]).toOrderEmbedding.trans
        (Fin.succAboveOrderEmb i) := by
  apply DFunLike.coe_injective
  rw [eq_comm]
  convert orderEmbOfFin_unique _ (fun x ↦ ?_)
    ((Fin.strictMono_succAbove _).comp (Fin.cast_strictMono _))
  · simp
  · simp [← h, card_compl]

@[simp]
lemma orderEmbOfFin_compl_singleton_eq_succAboveOrderEmb {n : ℕ} (i : Fin (n + 1)) :
    ({i}ᶜ : Finset _).orderEmbOfFin (by simp [card_compl]) = Fin.succAboveOrderEmb i :=
  orderEmbOfFin_compl_singleton _

lemma orderEmbOfFin_compl_singleton_apply {n : ℕ} {i : Fin (n + 1)} {k : ℕ}
    (h : ({i}ᶜ : Finset _).card = k) (j : Fin k) : ({i}ᶜ : Finset _).orderEmbOfFin h j =
      Fin.succAbove i (Fin.cast (h.symm.trans (by simp [card_compl])) j) := by
  rw [orderEmbOfFin_compl_singleton]
  simp

end SortLinearOrder

unsafe instance [Repr α] : Repr (Finset α) where
  reprPrec s _ :=
    -- multiset uses `0` not `∅` for empty sets
    if s.card = 0 then "∅" else repr s.1

end Finset

namespace Fin

theorem sort_univ (n : ℕ) : Finset.univ.sort (fun x y : Fin n => x ≤ y) = List.finRange n :=
  Finset.univ.sortedLT_sort.eq_of_mem_iff (List.sortedLT_finRange n) (by simp)

end Fin

/-- Given a `Fintype` `α` of cardinality `k`, the map `orderIsoFinOfCardEq s h` is the increasing
bijection between `Fin k` and `α` as an `OrderIso`. Here, `h` is a proof that the cardinality of `α`
is `k`. We use this instead of an iso `Fin (Fintype.card α) ≃o α` to avoid casting issues in further
uses of this function. -/
def Fintype.orderIsoFinOfCardEq
    (α : Type*) [LinearOrder α] [Fintype α] {k : ℕ} (h : Fintype.card α = k) :
    Fin k ≃o α :=
  (Finset.univ.orderIsoOfFin h).trans
    ((OrderIso.setCongr _ _ Finset.coe_univ).trans OrderIso.Set.univ)

/-- Any finite linear order order-embeds into any infinite linear order. -/
lemma nonempty_orderEmbedding_of_finite_infinite
    (α : Type*) [LinearOrder α] [hα : Finite α]
    (β : Type*) [LinearOrder β] [hβ : Infinite β] : Nonempty (α ↪o β) := by
  haveI := Fintype.ofFinite α
  obtain ⟨s, hs⟩ := Infinite.exists_subset_card_eq β (Fintype.card α)
  exact ⟨((Fintype.orderIsoFinOfCardEq α rfl).symm.toOrderEmbedding).trans (s.orderEmbOfFin hs)⟩

@[elab_as_elim, deprecated "Use `WellFoundedLT.induction _ h` instead." (since := "2026-04-10")]
lemma LinearOrder.strong_induction_of_finite
    {α : Type*} [LinearOrder α] [Finite α] {motive : α → Prop}
    (h : ∀ (j : α) (_ : ∀ (k : α), k < j → motive k), motive j) (i : α) :
    motive i := WellFoundedLT.induction _ h

lemma OrderEmbedding.range_eq_iff
    {α β : Type*} [LinearOrder α] [PartialOrder β] [Finite α]
    {f g : α ↪o β} :
    Set.range f = Set.range g ↔ f = g := by
  refine ⟨fun h ↦ ?_, by rintro rfl; rfl⟩
  let ef := (f.strictMono.strictMonoOn .univ).orderIso
  let eg := (g.strictMono.strictMonoOn .univ).orderIso
  let i : f '' .univ ≃o g '' .univ :=
    { __ := Equiv.setCongr (by simpa using h)
      map_rel_iff' := by rfl }
  have : (ef.trans i).trans eg.symm = .refl _ := by
    exact Subsingleton.elim _ _
  ext x
  simpa only [OrderIso.trans_apply, OrderIso.apply_symm_apply, OrderIso.refl_apply, Subtype.ext_iff]
    using congr(eg ($this ⟨x, Set.mem_univ x⟩))

lemma OrderHom.range_eq_iff {α β : Type*} [LinearOrder α] [PartialOrder β]
    [Finite α] {f g : α →o β}
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Set.range f = Set.range g ↔ f = g := by
  refine ⟨fun h ↦ ?_, by rintro rfl; rfl⟩
  ext : 2
  exact DFunLike.congr_fun ((OrderEmbedding.range_eq_iff
    (f := .ofStrictMono f (f.monotone.strictMono_of_injective hf))
    (g := .ofStrictMono g (g.monotone.strictMono_of_injective hg))).1 (by simpa)) _

lemma OrderHom.eq_id_of_injective {α : Type*} [LinearOrder α] [Finite α] (f : α →o α)
    (hf : Function.Injective f) :
    f = .id :=
  (range_eq_iff hf Function.injective_id).1 (by
    simpa [Set.range_eq_univ] using Finite.surjective_of_injective hf)
