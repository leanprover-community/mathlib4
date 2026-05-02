/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kenny Lau
-/
module

public import Mathlib.Data.List.Forall2

/-!
# Lists with no duplicates

`List.Nodup` is defined in `Data/List/Basic`. In this file we prove various properties of this
predicate.
-/

public section

universe u v

open Function

variable {α : Type u} {β : Type v} {l l₁ l₂ : List α} {r : α → α → Prop} {a : α}

namespace List

protected theorem Pairwise.nodup {l : List α} {r : α → α → Prop} [Std.Irrefl r] (h : Pairwise r l) :
    Nodup l :=
  h.imp ne_of_irrefl

open scoped Relator in
theorem rel_nodup {r : α → β → Prop} (hr : Relator.BiUnique r) : (Forall₂ r ⇒ (· ↔ ·)) Nodup Nodup
  | _, _, Forall₂.nil => by simp only [nodup_nil]
  | _, _, Forall₂.cons hab h => by
    simpa only [nodup_cons] using
      Relator.rel_and (Relator.rel_not (rel_mem hr hab h)) (rel_nodup hr h)

protected theorem Nodup.cons (ha : a ∉ l) (hl : Nodup l) : Nodup (a :: l) :=
  nodup_cons.2 ⟨ha, hl⟩

theorem nodup_singleton (a : α) : Nodup [a] :=
  pairwise_singleton _ _

theorem Nodup.of_cons (h : Nodup (a :: l)) : Nodup l :=
  (nodup_cons.1 h).2

theorem Nodup.notMem (h : (a :: l).Nodup) : a ∉ l :=
  (nodup_cons.1 h).1

theorem not_nodup_cons_of_mem : a ∈ l → ¬Nodup (a :: l) :=
  imp_not_comm.1 Nodup.notMem


theorem not_nodup_pair (a : α) : ¬Nodup [a, a] :=
  not_nodup_cons_of_mem <| mem_singleton_self _

theorem nodup_iff_sublist {l : List α} : Nodup l ↔ ∀ a, ¬[a, a] <+ l :=
  ⟨fun d a h => not_nodup_pair a (d.sublist h),
    by
      induction l <;> intro h; · exact nodup_nil
      case cons a l IH =>
        exact (IH fun a s => h a <| sublist_cons_of_sublist _ s).cons
          fun al => h a <| (singleton_sublist.2 al).cons_cons _⟩

@[simp]
theorem nodup_mergeSort {l : List α} {le : α → α → Bool} : (l.mergeSort le).Nodup ↔ l.Nodup :=
  (mergeSort_perm l le).nodup_iff

protected alias ⟨_, Nodup.mergeSort⟩ := nodup_mergeSort

theorem nodup_iff_injective_getElem {l : List α} :
    Nodup l ↔ Function.Injective (fun i : Fin l.length => l[i.1]) :=
  pairwise_iff_getElem.trans
    ⟨fun h i j hg => by
      obtain ⟨i, hi⟩ := i; obtain ⟨j, hj⟩ := j
      rcases Nat.lt_trichotomy i j with (hij | rfl | hji)
      · exact (h i j hi hj hij hg).elim
      · rfl
      · exact (h j i hj hi hji hg.symm).elim,
      fun hinj i j hi hj hij h => Nat.ne_of_lt hij (Fin.val_eq_of_eq (@hinj ⟨i, hi⟩ ⟨j, hj⟩ h))⟩

theorem nodup_iff_injective_get {l : List α} : Nodup l ↔ Function.Injective l.get :=
  nodup_iff_injective_getElem

protected theorem Nodup.injective_get {l : List α} (h : Nodup l) : Function.Injective l.get :=
  nodup_iff_injective_get.mp h

protected theorem _root_.Function.Injective.nodup {l : List α}
    (h : Function.Injective l.get) : l.Nodup := nodup_iff_injective_get.mpr h

theorem Nodup.get_inj_iff {l : List α} (h : Nodup l) {i j : Fin l.length} :
    l.get i = l.get j ↔ i = j :=
  (nodup_iff_injective_get.1 h).eq_iff

theorem Nodup.getElem_inj_iff {l : List α} (h : Nodup l)
    {i : Nat} {hi : i < l.length} {j : Nat} {hj : j < l.length} :
    l[i] = l[j] ↔ i = j := by
  have := @Nodup.get_inj_iff _ _ h ⟨i, hi⟩ ⟨j, hj⟩
  simpa

theorem nodup_iff_getElem?_ne_getElem? {l : List α} :
    l.Nodup ↔ ∀ i j : ℕ, i < j → j < l.length → l[i]? ≠ l[j]? := by
  grind [List.pairwise_iff_getElem]

theorem Nodup.ne_singleton_iff {l : List α} (h : Nodup l) (x : α) :
    l ≠ [x] ↔ l = [] ∨ ∃ y ∈ l, y ≠ x := by
  induction l with
  | nil => simp
  | cons hd tl hl =>
    specialize hl h.of_cons
    by_cases hx : tl = [x]
    · simpa [hx, and_comm, and_or_left] using h
    · rw [← Ne, hl] at hx
      rcases hx with (rfl | ⟨y, hy, hx⟩)
      · simp
      · suffices ∃ y ∈ hd :: tl, y ≠ x by simpa [ne_nil_of_mem hy]
        exact ⟨y, mem_cons_of_mem _ hy, hx⟩

theorem not_nodup_of_get_eq_of_ne (xs : List α) (n m : Fin xs.length)
    (h : xs.get n = xs.get m) (hne : n ≠ m) : ¬Nodup xs := by
  rw [nodup_iff_injective_get]
  exact fun hinj => hne (hinj h)

lemma Nodup.head_eq_getLast_iff (hnd : l.Nodup) (hne : l ≠ []) :
    l.head hne = l.getLast hne ↔ ∃ x, l = [x] :=
  ⟨fun h => by cases l <;> grind, fun ⟨x, hx⟩ => by grind⟩

@[deprecated Nodup.idxOf_getElem (since := "2025-11-10")]
theorem idxOf_getElem [DecidableEq α] {l : List α} : Nodup l → (i : Nat) → (h : i < l.length) →
    idxOf l[i] l = i := Nodup.idxOf_getElem

-- This is incorrectly named and should be `idxOf_get`;
-- this already exists, so will require a deprecation dance.
theorem get_idxOf [BEq α] [LawfulBEq α] {l : List α} (H : Nodup l) (i : Fin l.length) :
    idxOf (get l i) l = i := by
  simp [H]

theorem nodup_iff_count_le_one [BEq α] [LawfulBEq α] {l : List α} : Nodup l ↔ ∀ a, count a l ≤ 1 :=
  nodup_iff_sublist.trans <|
    forall_congr' fun a =>
      have : replicate 2 a <+ l ↔ 1 < count a l := replicate_sublist_iff ..
      (not_congr this).trans Nat.not_lt

theorem nodup_iff_count_eq_one [BEq α] [LawfulBEq α] : Nodup l ↔ ∀ a ∈ l, count a l = 1 :=
  nodup_iff_count_le_one.trans <| forall_congr' fun x => by rw [← count_pos_iff]; grind

theorem get_bijective_iff [BEq α] [LawfulBEq α] : l.get.Bijective ↔ ∀ a, l.count a = 1 :=
  ⟨fun h a ↦ (nodup_iff_count_eq_one.mp <| nodup_iff_injective_get.mpr h.injective)
    a <| mem_iff_get.mpr <| h.surjective a,
  fun h ↦ ⟨nodup_iff_injective_get.mp <| nodup_iff_count_eq_one.mpr fun a _ ↦ h a,
    fun a ↦ mem_iff_get.mp <| List.one_le_count_iff.mp <| by grind⟩⟩

theorem getElem_bijective_iff [BEq α] [LawfulBEq α] :
    (fun (n : Fin l.length) ↦ l[n]).Bijective ↔ ∀ a, l.count a = 1 :=
  get_bijective_iff

@[simp]
theorem count_eq_one_of_mem [BEq α] [LawfulBEq α] {a : α} {l : List α} (d : Nodup l) (h : a ∈ l) :
    count a l = 1 :=
  nodup_iff_count_eq_one.mp d a h

@[deprecated (since := "2025-11-07")] alias count_eq_of_nodup := Nodup.count

theorem Nodup.of_append_left : Nodup (l₁ ++ l₂) → Nodup l₁ :=
  Nodup.sublist (sublist_append_left l₁ l₂)

theorem Nodup.of_append_right : Nodup (l₁ ++ l₂) → Nodup l₂ :=
  Nodup.sublist (sublist_append_right l₁ l₂)

/-- This is a variant of the `nodup_append` from the standard library,
which does not use `Disjoint`. -/
theorem nodup_append' {l₁ l₂ : List α} :
    Nodup (l₁ ++ l₂) ↔ Nodup l₁ ∧ Nodup l₂ ∧ Disjoint l₁ l₂ := by
  simp only [Nodup, pairwise_append, disjoint_iff_ne]

theorem disjoint_of_nodup_append {l₁ l₂ : List α} (d : Nodup (l₁ ++ l₂)) : Disjoint l₁ l₂ :=
  (nodup_append'.1 d).2.2

protected alias Nodup.disjoint := disjoint_of_nodup_append

theorem Nodup.append (d₁ : Nodup l₁) (d₂ : Nodup l₂) (dj : Disjoint l₁ l₂) : Nodup (l₁ ++ l₂) :=
  nodup_append'.2 ⟨d₁, d₂, dj⟩

theorem nodup_append_comm {l₁ l₂ : List α} : Nodup (l₁ ++ l₂) ↔ Nodup (l₂ ++ l₁) := by
  simp only [nodup_append', and_left_comm, disjoint_comm]

theorem nodup_middle {a : α} {l₁ l₂ : List α} :
    Nodup (l₁ ++ a :: l₂) ↔ Nodup (a :: (l₁ ++ l₂)) := by
  simp only [nodup_append', not_or, and_left_comm, and_assoc, nodup_cons, mem_append,
    disjoint_cons_right]

theorem Nodup.of_map (f : α → β) {l : List α} : Nodup (map f l) → Nodup l :=
  (Pairwise.of_map f) fun _ _ => mt <| congr_arg f

theorem Nodup.map_on {f : α → β} (H : ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) (d : Nodup l) :
    (map f l).Nodup :=
  Pairwise.map _ (fun a b ⟨ma, mb, n⟩ e => n (H a ma b mb e)) (Pairwise.and_mem.1 d)

theorem inj_on_of_nodup_map {f : α → β} {l : List α} (d : Nodup (map f l)) :
    ∀ ⦃x⦄, x ∈ l → ∀ ⦃y⦄, y ∈ l → f x = f y → x = y := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [map, nodup_cons, mem_map, not_exists, not_and, ← Ne.eq_def] at d
    simp only [mem_cons]
    rintro _ (rfl | h₁) _ (rfl | h₂) h₃
    · rfl
    · apply (d.1 _ h₂ h₃.symm).elim
    · apply (d.1 _ h₁ h₃).elim
    · apply ih d.2 h₁ h₂ h₃

theorem nodup_map_iff_inj_on {f : α → β} {l : List α} (d : Nodup l) :
    Nodup (map f l) ↔ ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y :=
  ⟨inj_on_of_nodup_map, fun h => d.map_on h⟩

protected theorem Nodup.map {f : α → β} (hf : Injective f) : Nodup l → Nodup (map f l) :=
  Nodup.map_on fun _ _ _ _ h => hf h

theorem nodup_map_iff {f : α → β} {l : List α} (hf : Injective f) : Nodup (map f l) ↔ Nodup l :=
  ⟨Nodup.of_map _, Nodup.map hf⟩

@[simp]
theorem nodup_attach {l : List α} : Nodup (attach l) ↔ Nodup l :=
  ⟨fun h => attach_map_subtype_val l ▸ h.map fun _ _ => Subtype.ext, fun h =>
    Nodup.of_map Subtype.val ((attach_map_subtype_val l).symm ▸ h)⟩

protected alias ⟨Nodup.of_attach, Nodup.attach⟩ := nodup_attach

theorem Nodup.pmap {p : α → Prop} {f : ∀ a, p a → β} {l : List α} {H}
    (hf : ∀ a ha b hb, f a ha = f b hb → a = b) (h : Nodup l) : Nodup (pmap f l H) := by
  grind

theorem Nodup.filter (p : α → Bool) {l} : Nodup l → Nodup (filter p l) := by
  simpa using Pairwise.filter p

@[simp]
theorem nodup_reverse {l : List α} : Nodup (reverse l) ↔ Nodup l :=
  pairwise_reverse.trans <| by simp only [Nodup, Ne, eq_comm]

theorem nodup_concat (l : List α) (u : α) : (l.concat u).Nodup ↔ u ∉ l ∧ l.Nodup := by
  rw [← nodup_reverse]
  simp

lemma nodup_tail_reverse (l : List α) (h : l[0]? = l.getLast?) :
    Nodup l.reverse.tail ↔ Nodup l.tail := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases hl : l = []
    · simp_all
    · simp_all only [List.tail_reverse, List.nodup_reverse,
        List.dropLast_cons_of_ne_nil hl, List.tail_cons]
      simp only [length_cons, Nat.zero_lt_succ, getElem?_eq_getElem,
        Nat.add_one_sub_one, Nat.lt_add_one, Option.some.injEq, List.getElem_cons,
        show l.length ≠ 0 by aesop, ↓reduceDIte, getLast?_eq_getElem?] at h
      rw [h,
        show l.Nodup = (l.dropLast ++ [l.getLast hl]).Nodup by
          simp [List.dropLast_eq_take],
        List.nodup_append_comm]
      simp [List.getLast_eq_getElem]

lemma Nodup.head_suffix_mem (h : l₁.IsSuffix l₂) (hne : l₂ ≠ []) (hl : l₂.head hne ∈ l₁)
    (hnd : l₂.Nodup) : l₁ = l₂ := by
  cases h
  grind

lemma Nodup.getLast_prefix_mem (h : l₁.IsPrefix l₂) (hne : l₂ ≠ []) (hl : l₂.getLast hne ∈ l₁)
    (hnd : l₂.Nodup) : l₁ = l₂ := by
  cases h
  grind

theorem Nodup.erase_getElem [BEq α] [LawfulBEq α] {l : List α} (hl : l.Nodup)
    (i : Nat) (h : i < l.length) : l.erase l[i] = l.eraseIdx ↑i := by
  induction l generalizing i with
  | nil => simp
  | cons a l IH =>
    cases i with
    | zero => simp
    | succ i => grind

theorem Nodup.erase_get [BEq α] [LawfulBEq α] {l : List α} (hl : l.Nodup) (i : Fin l.length) :
    l.erase (l.get i) = l.eraseIdx ↑i := by
  simp [erase_getElem, hl]

theorem Nodup.diff [BEq α] [LawfulBEq α] : l₁.Nodup → (l₁.diff l₂).Nodup :=
  Nodup.sublist <| diff_sublist _ _

theorem nodup_flatten {L : List (List α)} :
    Nodup (flatten L) ↔ (∀ l ∈ L, Nodup l) ∧ Pairwise Disjoint L := by
  simp only [Nodup, pairwise_flatten, disjoint_left.symm, forall_mem_ne]

theorem nodup_flatMap {l₁ : List α} {f : α → List β} :
    Nodup (l₁.flatMap f) ↔
      (∀ x ∈ l₁, Nodup (f x)) ∧ Pairwise (Disjoint on f) l₁ := by
  simp only [List.flatMap, nodup_flatten, pairwise_map, and_comm, mem_map,
    exists_imp, and_imp]
  rw [show (∀ (l : List β) (x : α), f x = l → x ∈ l₁ → Nodup l) ↔ ∀ x : α, x ∈ l₁ → Nodup (f x)
      from forall_comm.trans <| forall_congr' fun _ => forall_eq']

protected theorem Nodup.product {l₂ : List β} (d₁ : l₁.Nodup) (d₂ : l₂.Nodup) :
    (l₁ ×ˢ l₂).Nodup :=
  nodup_flatMap.2
    ⟨fun a _ => d₂.map <| LeftInverse.injective fun b => (rfl : (a, b).2 = b),
      d₁.imp fun {a₁ a₂} n x h₁ h₂ => by
        rcases mem_map.1 h₁ with ⟨b₁, _, rfl⟩
        rcases mem_map.1 h₂ with ⟨b₂, mb₂, ⟨⟩⟩
        exact n rfl⟩

theorem Nodup.sigma {σ : α → Type*} {l₂ : ∀ a, List (σ a)} (d₁ : Nodup l₁)
    (d₂ : ∀ a, Nodup (l₂ a)) : (l₁.sigma l₂).Nodup :=
  nodup_flatMap.2
    ⟨fun a _ => (d₂ a).map fun b b' h => by injection h with _ h,
      d₁.imp fun {a₁ a₂} n x h₁ h₂ => by
        rcases mem_map.1 h₁ with ⟨b₁, _, rfl⟩
        rcases mem_map.1 h₂ with ⟨b₂, mb₂, ⟨⟩⟩
        exact n rfl⟩

protected theorem Nodup.filterMap {f : α → Option β} (h : ∀ a a' b, b ∈ f a → b ∈ f a' → a = a') :
    Nodup l → Nodup (filterMap f l) :=
  (Pairwise.filterMap f) @fun a a' n b bm b' bm' e => n <| h a a' b' (by rw [← e]; exact bm) bm'

protected theorem Nodup.concat (h : a ∉ l) (h' : l.Nodup) : (l.concat a).Nodup := by
  rw [concat_eq_append]; exact h'.append (nodup_singleton _) (disjoint_singleton.2 h)

protected theorem Nodup.insert [BEq α] [LawfulBEq α] (h : l.Nodup) : (l.insert a).Nodup :=
  if h' : a ∈ l then by rw [insert_of_mem h']; exact h
  else by rw [insert_of_not_mem h', nodup_cons]; constructor <;> assumption

theorem Nodup.union [BEq α] [LawfulBEq α] (l₁ : List α) (h : Nodup l₂) : (l₁ ∪ l₂).Nodup := by
  induction l₁ generalizing l₂ with
  | nil => exact h
  | cons a l₁ ih => exact (ih h).insert

theorem Nodup.inter [BEq α] (l₂ : List α) : Nodup l₁ → Nodup (l₁ ∩ l₂) :=
  Nodup.filter _

theorem Nodup.diff_eq_filter [BEq α] [LawfulBEq α] :
    ∀ {l₁ l₂ : List α} (_ : l₁.Nodup), l₁.diff l₂ = l₁.filter (· ∉ l₂)
  | l₁, [], _ => by simp
  | l₁, a :: l₂, hl₁ => by
    rw [diff_cons, (hl₁.erase _).diff_eq_filter, hl₁.erase_eq_filter, filter_filter]
    simp only [decide_not, bne, Bool.and_comm, decide_mem_cons, Bool.not_or]

theorem Nodup.mem_diff_iff [BEq α] [LawfulBEq α] (hl₁ : l₁.Nodup) :
    a ∈ l₁.diff l₂ ↔ a ∈ l₁ ∧ a ∉ l₂ := by
  rw [hl₁.diff_eq_filter, mem_filter, decide_eq_true_iff]

protected theorem Nodup.set :
    ∀ {l : List α} {n : ℕ} {a : α} (_ : l.Nodup) (_ : a ∉ l), (l.set n a).Nodup
  | [], _, _, _, _ => nodup_nil
  | _ :: _, 0, _, hl, ha => nodup_cons.2 ⟨mt (mem_cons_of_mem _) ha, (nodup_cons.1 hl).2⟩
  | _ :: _, _ + 1, _, hl, ha =>
    nodup_cons.2
      ⟨fun h =>
        (mem_or_eq_of_mem_set h).elim (nodup_cons.1 hl).1 fun hba => ha (hba ▸ mem_cons_self),
        hl.of_cons.set (mt (mem_cons_of_mem _) ha)⟩

theorem Nodup.map_update [DecidableEq α] {l : List α} (hl : l.Nodup) (f : α → β) (x : α) (y : β) :
    l.map (Function.update f x y) =
      if x ∈ l then (l.map f).set (l.idxOf x) y else l.map f := by
  induction l with | nil => simp | cons hd tl ihl => ?_
  rw [nodup_cons] at hl
  simp only [mem_cons, map, ihl hl.2]
  by_cases H : hd = x
  · subst hd
    simp [hl.1]
  · simp [Ne.symm H, H, ← apply_ite (cons (f hd))]

theorem Nodup.pairwise_of_forall_ne {l : List α} {r : α → α → Prop} (hl : l.Nodup)
    (h : ∀ a ∈ l, ∀ b ∈ l, a ≠ b → r a b) : l.Pairwise r := by
  grind [List.pairwise_iff_forall_sublist]

theorem Nodup.take_eq_filter_mem [BEq α] [LawfulBEq α] :
    ∀ {l : List α} {n : ℕ} (_ : l.Nodup), l.take n = l.filter (l.take n).elem
  | [], n, _ => by simp
  | b::l, 0, _ => by simp
  | b::l, n + 1, hl => by
    rw [take_succ_cons, Nodup.take_eq_filter_mem (Nodup.of_cons hl), filter_cons_of_pos (by simp)]
    congr 1
    refine List.filter_congr ?_
    intro x hx
    have : x ≠ b := fun h => (nodup_cons.1 hl).1 (h ▸ hx)
    simp +contextual [List.mem_filter, this, hx]
end List

theorem Option.toList_nodup : ∀ o : Option α, o.toList.Nodup
  | none => List.nodup_nil
  | some x => List.nodup_singleton x
