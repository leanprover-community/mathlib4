/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
import Mathlib.Data.List.Count
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.Duplicate
import Mathlib.Data.List.InsertNth
import Mathlib.Data.List.Lattice
import Mathlib.Data.List.Permutation
import Mathlib.Data.Nat.Factorial.Basic
import Batteries.Data.List.Perm

/-!
# List Permutations

This file introduces the `List.Perm` relation, which is true if two lists are permutations of one
another.

## Notation

The notation `~` is used for permutation equivalence.
-/

-- Make sure we don't import algebra
assert_not_exists Monoid

open Nat

namespace List
variable {α β : Type*} {l l₁ l₂ : List α} {a : α}

instance : Trans (@List.Perm α) (@List.Perm α) List.Perm where
  trans := @List.Perm.trans α

open Perm (swap)

attribute [refl] Perm.refl

lemma perm_rfl : l ~ l := Perm.refl _

-- Porting note: used rec_on in mathlib3; lean4 eqn compiler still doesn't like it
attribute [symm] Perm.symm

attribute [trans] Perm.trans

theorem Perm.subset_congr_left {l₁ l₂ l₃ : List α} (h : l₁ ~ l₂) : l₁ ⊆ l₃ ↔ l₂ ⊆ l₃ :=
  ⟨h.symm.subset.trans, h.subset.trans⟩

theorem Perm.subset_congr_right {l₁ l₂ l₃ : List α} (h : l₁ ~ l₂) : l₃ ⊆ l₁ ↔ l₃ ⊆ l₂ :=
  ⟨fun h' => h'.trans h.subset, fun h' => h'.trans h.symm.subset⟩

/-- Variant of `Perm.foldr_eq` with explicit commutativity argument. -/
theorem Perm.foldr_eq' {f : α → β → β} {l₁ l₂ : List α} (p : l₁ ~ l₂)
    (comm : ∀ x ∈ l₁, ∀ y ∈ l₁, ∀ z, f y (f x z) = f x (f y z))
    (init : β) : foldr f init l₁ = foldr f init l₂ := by
  induction p using recOnSwap' generalizing init with
  | nil => simp
  | cons x _p IH =>
    simp only [foldr]
    congr 1
    apply IH; intros; apply comm <;> exact .tail _ ‹_›
  | swap' x y _p IH =>
    simp only [foldr]
    rw [comm x (.tail _ <| .head _) y (.head _)]
    congr 2
    apply IH; intros; apply comm <;> exact .tail _ (.tail _ ‹_›)
  | trans p₁ _p₂ IH₁ IH₂ =>
    refine (IH₁ comm init).trans (IH₂ ?_ _)
    intros; apply comm <;> apply p₁.symm.subset <;> assumption

section Rel

open Relator

variable {γ : Type*} {δ : Type*} {r : α → β → Prop} {p : γ → δ → Prop}

local infixr:80 " ∘r " => Relation.Comp

theorem perm_comp_perm : (Perm ∘r Perm : List α → List α → Prop) = Perm := by
  funext a c; apply propext
  constructor
  · exact fun ⟨b, hab, hba⟩ => Perm.trans hab hba
  · exact fun h => ⟨a, Perm.refl a, h⟩

theorem perm_comp_forall₂ {l u v} (hlu : Perm l u) (huv : Forall₂ r u v) :
    (Forall₂ r ∘r Perm) l v := by
  induction hlu generalizing v with
  | nil => cases huv; exact ⟨[], Forall₂.nil, Perm.nil⟩
  | cons u _hlu ih =>
    cases' huv with _ b _ v hab huv'
    rcases ih huv' with ⟨l₂, h₁₂, h₂₃⟩
    exact ⟨b :: l₂, Forall₂.cons hab h₁₂, h₂₃.cons _⟩
  | swap a₁ a₂ h₂₃ =>
    cases' huv with _ b₁ _ l₂ h₁ hr₂₃
    cases' hr₂₃ with _ b₂ _ l₂ h₂ h₁₂
    exact ⟨b₂ :: b₁ :: l₂, Forall₂.cons h₂ (Forall₂.cons h₁ h₁₂), Perm.swap _ _ _⟩
  | trans _ _ ih₁ ih₂ =>
    rcases ih₂ huv with ⟨lb₂, hab₂, h₂₃⟩
    rcases ih₁ hab₂ with ⟨lb₁, hab₁, h₁₂⟩
    exact ⟨lb₁, hab₁, Perm.trans h₁₂ h₂₃⟩

theorem forall₂_comp_perm_eq_perm_comp_forall₂ : Forall₂ r ∘r Perm = Perm ∘r Forall₂ r := by
  funext l₁ l₃; apply propext
  constructor
  · intro h
    rcases h with ⟨l₂, h₁₂, h₂₃⟩
    have : Forall₂ (flip r) l₂ l₁ := h₁₂.flip
    rcases perm_comp_forall₂ h₂₃.symm this with ⟨l', h₁, h₂⟩
    exact ⟨l', h₂.symm, h₁.flip⟩
  · exact fun ⟨l₂, h₁₂, h₂₃⟩ => perm_comp_forall₂ h₁₂ h₂₃

theorem rel_perm_imp (hr : RightUnique r) : (Forall₂ r ⇒ Forall₂ r ⇒ (· → ·)) Perm Perm :=
  fun a b h₁ c d h₂ h =>
  have : (flip (Forall₂ r) ∘r Perm ∘r Forall₂ r) b d := ⟨a, h₁, c, h, h₂⟩
  have : ((flip (Forall₂ r) ∘r Forall₂ r) ∘r Perm) b d := by
    rwa [← forall₂_comp_perm_eq_perm_comp_forall₂, ← Relation.comp_assoc] at this
  let ⟨b', ⟨c', hbc, hcb⟩, hbd⟩ := this
  have : b' = b := right_unique_forall₂' hr hcb hbc
  this ▸ hbd

theorem rel_perm (hr : BiUnique r) : (Forall₂ r ⇒ Forall₂ r ⇒ (· ↔ ·)) Perm Perm :=
  fun _a _b hab _c _d hcd =>
  Iff.intro (rel_perm_imp hr.2 hab hcd) (rel_perm_imp hr.left.flip hab.flip hcd.flip)

end Rel

section Subperm



attribute [refl] Subperm.refl

attribute [trans] Subperm.trans

end Subperm

lemma subperm_iff : l₁ <+~ l₂ ↔ ∃ l, l ~ l₂ ∧ l₁ <+ l := by
  refine ⟨?_, fun ⟨l, h₁, h₂⟩ ↦ h₂.subperm.trans h₁.subperm⟩
  rintro ⟨l, h₁, h₂⟩
  obtain ⟨l', h₂⟩ := h₂.exists_perm_append
  exact ⟨l₁ ++ l', (h₂.trans (h₁.append_right _)).symm, (prefix_append _ _).sublist⟩

@[simp] lemma subperm_singleton_iff : l <+~ [a] ↔ l = [] ∨ l = [a] := by
  constructor
  · rw [subperm_iff]
    rintro ⟨s, hla, h⟩
    rwa [perm_singleton.mp hla, sublist_singleton] at h
  · rintro (rfl | rfl)
    exacts [nil_subperm, Subperm.refl _]

attribute [simp] nil_subperm

@[simp]
theorem subperm_nil : List.Subperm l [] ↔ l = [] :=
  ⟨fun h ↦ length_eq_zero.1 <| Nat.le_zero.1 h.length_le, by rintro rfl; rfl⟩

lemma subperm_cons_self : l <+~ a :: l := ⟨l, Perm.refl _, sublist_cons_self _ _⟩

lemma count_eq_count_filter_add [DecidableEq α] (P : α → Prop) [DecidablePred P]
    (l : List α) (a : α) :
    count a l = count a (l.filter P) + count a (l.filter (¬ P ·)) := by
  convert countP_eq_countP_filter_add l _ P
  simp only [decide_not]

theorem Perm.foldl_eq {f : β → α → β} {l₁ l₂ : List α} [rcomm : RightCommutative f] (p : l₁ ~ l₂) :
    ∀ b, foldl f b l₁ = foldl f b l₂ :=
  p.foldl_eq' fun x _hx y _hy z => rcomm.right_comm z x y

theorem Perm.foldr_eq {f : α → β → β} {l₁ l₂ : List α} [lcomm : LeftCommutative f] (p : l₁ ~ l₂) :
    ∀ b, foldr f b l₁ = foldr f b l₂ := by
  intro b
  induction p using Perm.recOnSwap' generalizing b with
  | nil => rfl
  | cons _ _ r  => simp [r b]
  | swap' _ _ _ r => simp only [foldr_cons]; rw [lcomm.left_comm, r b]
  | trans _ _ r₁ r₂ => exact Eq.trans (r₁ b) (r₂ b)

section

variable {op : α → α → α} [IA : Std.Associative op] [IC : Std.Commutative op]

local notation a " * " b => op a b

local notation l " <*> " a => foldl op a l

theorem Perm.foldl_op_eq {l₁ l₂ : List α} {a : α} (h : l₁ ~ l₂) : (l₁ <*> a) = l₂ <*> a :=
  h.foldl_eq _

theorem Perm.foldr_op_eq {l₁ l₂ : List α} {a : α} (h : l₁ ~ l₂) : l₁.foldr op a = l₂.foldr op a :=
  h.foldr_eq _

@[deprecated (since := "2024-09-28")] alias Perm.fold_op_eq := Perm.foldl_op_eq

end

theorem perm_option_to_list {o₁ o₂ : Option α} : o₁.toList ~ o₂.toList ↔ o₁ = o₂ := by
  refine ⟨fun p => ?_, fun e => e ▸ Perm.refl _⟩
  cases' o₁ with a <;> cases' o₂ with b; · rfl
  · cases p.length_eq
  · cases p.length_eq
  · exact Option.mem_toList.1 (p.symm.subset <| by simp)

alias ⟨subperm.of_cons, subperm.cons⟩ := subperm_cons

-- Porting note: commented out
--attribute [protected] subperm.cons

theorem cons_subperm_of_mem {a : α} {l₁ l₂ : List α} (d₁ : Nodup l₁) (h₁ : a ∉ l₁) (h₂ : a ∈ l₂)
    (s : l₁ <+~ l₂) : a :: l₁ <+~ l₂ := by
  rcases s with ⟨l, p, s⟩
  induction s generalizing l₁ with
  | slnil => cases h₂
  | @cons r₁ r₂ b s' ih =>
    simp? at h₂ says simp only [mem_cons] at h₂
    cases' h₂ with e m
    · subst b
      exact ⟨a :: r₁, p.cons a, s'.cons₂ _⟩
    · rcases ih d₁ h₁ m p with ⟨t, p', s'⟩
      exact ⟨t, p', s'.cons _⟩
  | @cons₂ r₁ r₂ b _ ih =>
    have bm : b ∈ l₁ := p.subset <| mem_cons_self _ _
    have am : a ∈ r₂ := by
      simp only [find?, mem_cons] at h₂
      exact h₂.resolve_left fun e => h₁ <| e.symm ▸ bm
    rcases append_of_mem bm with ⟨t₁, t₂, rfl⟩
    have st : t₁ ++ t₂ <+ t₁ ++ b :: t₂ := by simp
    rcases ih (d₁.sublist st) (mt (fun x => st.subset x) h₁) am
        (Perm.cons_inv <| p.trans perm_middle) with
      ⟨t, p', s'⟩
    exact
      ⟨b :: t, (p'.cons b).trans <| (swap _ _ _).trans (perm_middle.symm.cons a), s'.cons₂ _⟩

protected theorem Nodup.subperm (d : Nodup l₁) (H : l₁ ⊆ l₂) : l₁ <+~ l₂ :=
  subperm_of_subset d H

section

variable [DecidableEq α]

theorem Perm.bagInter_right {l₁ l₂ : List α} (t : List α) (h : l₁ ~ l₂) :
    l₁.bagInter t ~ l₂.bagInter t := by
  induction h generalizing t with
  | nil => simp
  | cons x => by_cases x ∈ t <;> simp [*, Perm.cons]
  | swap x y =>
    by_cases h : x = y
    · simp [h]
    by_cases xt : x ∈ t <;> by_cases yt : y ∈ t
    · simp [xt, yt, mem_erase_of_ne h, mem_erase_of_ne (Ne.symm h), erase_comm, swap]
    · simp [xt, yt, mt mem_of_mem_erase, Perm.cons]
    · simp [xt, yt, mt mem_of_mem_erase, Perm.cons]
    · simp [xt, yt]
  | trans _ _ ih_1 ih_2 => exact (ih_1 _).trans (ih_2 _)

theorem Perm.bagInter_left (l : List α) {t₁ t₂ : List α} (p : t₁ ~ t₂) :
    l.bagInter t₁ = l.bagInter t₂ := by
  induction' l with a l IH generalizing t₁ t₂ p; · simp
  by_cases h : a ∈ t₁
  · simp [h, p.subset h, IH (p.erase _)]
  · simp [h, mt p.mem_iff.2 h, IH p]

theorem Perm.bagInter {l₁ l₂ t₁ t₂ : List α} (hl : l₁ ~ l₂) (ht : t₁ ~ t₂) :
    l₁.bagInter t₁ ~ l₂.bagInter t₂ :=
  ht.bagInter_left l₂ ▸ hl.bagInter_right _

theorem perm_replicate_append_replicate {l : List α} {a b : α} {m n : ℕ} (h : a ≠ b) :
    l ~ replicate m a ++ replicate n b ↔ count a l = m ∧ count b l = n ∧ l ⊆ [a, b] := by
  rw [perm_iff_count, ← Decidable.and_forall_ne a, ← Decidable.and_forall_ne b]
  suffices l ⊆ [a, b] ↔ ∀ c, c ≠ b → c ≠ a → c ∉ l by
    simp (config := { contextual := true }) [count_replicate, h, this, count_eq_zero, Ne.symm]
  trans ∀ c, c ∈ l → c = b ∨ c = a
  · simp [subset_def, or_comm]
  · exact forall_congr' fun _ => by rw [← and_imp, ← not_or, not_imp_not]

theorem Perm.dedup {l₁ l₂ : List α} (p : l₁ ~ l₂) : dedup l₁ ~ dedup l₂ :=
  perm_iff_count.2 fun a =>
    if h : a ∈ l₁ then by
      simp [h, nodup_dedup, p.subset h]
    else by
      simp [h, count_eq_zero_of_not_mem, mt p.mem_iff.2]

theorem Perm.inter_append {l t₁ t₂ : List α} (h : Disjoint t₁ t₂) :
    l ∩ (t₁ ++ t₂) ~ l ∩ t₁ ++ l ∩ t₂ := by
  induction l with
  | nil => simp
  | cons x xs l_ih =>
    by_cases h₁ : x ∈ t₁
    · have h₂ : x ∉ t₂ := h h₁
      simp [*]
    by_cases h₂ : x ∈ t₂
    · simp only [*, inter_cons_of_not_mem, false_or, mem_append, inter_cons_of_mem,
        not_false_iff]
      refine Perm.trans (Perm.cons _ l_ih) ?_
      change [x] ++ xs ∩ t₁ ++ xs ∩ t₂ ~ xs ∩ t₁ ++ ([x] ++ xs ∩ t₂)
      rw [← List.append_assoc]
      solve_by_elim [Perm.append_right, perm_append_comm]
    · simp [*]

end



theorem Perm.bind_left (l : List α) {f g : α → List β} (h : ∀ a ∈ l, f a ~ g a) :
    l.bind f ~ l.bind g :=
  Perm.join_congr <| by
    rwa [List.forall₂_map_right_iff, List.forall₂_map_left_iff, List.forall₂_same]

theorem bind_append_perm (l : List α) (f g : α → List β) :
    l.bind f ++ l.bind g ~ l.bind fun x => f x ++ g x := by
  induction' l with a l IH
  · simp
  simp only [bind_cons, append_assoc]
  refine (Perm.trans ?_ (IH.append_left _)).append_left _
  rw [← append_assoc, ← append_assoc]
  exact perm_append_comm.append_right _

theorem map_append_bind_perm (l : List α) (f : α → β) (g : α → List β) :
    l.map f ++ l.bind g ~ l.bind fun x => f x :: g x := by
  simpa [← map_eq_bind] using bind_append_perm l (fun x => [f x]) g

theorem Perm.product_right {l₁ l₂ : List α} (t₁ : List β) (p : l₁ ~ l₂) :
    product l₁ t₁ ~ product l₂ t₁ :=
  p.bind_right _

theorem Perm.product_left (l : List α) {t₁ t₂ : List β} (p : t₁ ~ t₂) :
    product l t₁ ~ product l t₂ :=
  (Perm.bind_left _) fun _ _ => p.map _

theorem Perm.product {l₁ l₂ : List α} {t₁ t₂ : List β} (p₁ : l₁ ~ l₂) (p₂ : t₁ ~ t₂) :
    product l₁ t₁ ~ product l₂ t₂ :=
  (p₁.product_right t₁).trans (p₂.product_left l₂)

theorem perm_lookmap (f : α → Option α) {l₁ l₂ : List α}
    (H : Pairwise (fun a b => ∀ c ∈ f a, ∀ d ∈ f b, a = b ∧ c = d) l₁) (p : l₁ ~ l₂) :
    lookmap f l₁ ~ lookmap f l₂ := by
  induction' p with a l₁ l₂ p IH a b l l₁ l₂ l₃ p₁ _ IH₁ IH₂; · simp
  · cases h : f a
    · simpa [h] using IH (pairwise_cons.1 H).2
    · simp [lookmap_cons_some _ _ h, p]
  · cases' h₁ : f a with c <;> cases' h₂ : f b with d
    · simpa [h₁, h₂] using swap _ _ _
    · simpa [h₁, lookmap_cons_some _ _ h₂] using swap _ _ _
    · simpa [lookmap_cons_some _ _ h₁, h₂] using swap _ _ _
    · rcases (pairwise_cons.1 H).1 _ (mem_cons.2 (Or.inl rfl)) _ h₂ _ h₁ with ⟨rfl, rfl⟩
      exact Perm.refl _
  · refine (IH₁ H).trans (IH₂ ((p₁.pairwise_iff ?_).1 H))
    intro x y h c hc d hd
    rw [@eq_comm _ y, @eq_comm _ c]
    apply h d hd c hc

theorem Perm.take_inter [DecidableEq α] {xs ys : List α} (n : ℕ) (h : xs ~ ys)
    (h' : ys.Nodup) : xs.take n ~ ys.inter (xs.take n) := by
  simp only [List.inter]
  exact Perm.trans (show xs.take n ~ xs.filter (xs.take n).elem by
      conv_lhs => rw [Nodup.take_eq_filter_mem ((Perm.nodup_iff h).2 h')])
    (Perm.filter _ h)

theorem Perm.drop_inter [DecidableEq α] {xs ys : List α} (n : ℕ) (h : xs ~ ys) (h' : ys.Nodup) :
    xs.drop n ~ ys.inter (xs.drop n) := by
  by_cases h'' : n ≤ xs.length
  · let n' := xs.length - n
    have h₀ : n = xs.length - n' := by rwa [Nat.sub_sub_self]
    have h₁ : xs.drop n = (xs.reverse.take n').reverse := by
      rw [take_reverse, h₀, reverse_reverse]
    rw [h₁]
    apply (reverse_perm _).trans
    rw [inter_reverse]
    apply Perm.take_inter _ _ h'
    apply (reverse_perm _).trans; assumption
  · have : drop n xs = [] := by
      apply eq_nil_of_length_eq_zero
      rw [length_drop, Nat.sub_eq_zero_iff_le]
      apply le_of_not_ge h''
    simp [this, List.inter]

theorem Perm.dropSlice_inter [DecidableEq α] {xs ys : List α} (n m : ℕ) (h : xs ~ ys)
    (h' : ys.Nodup) : List.dropSlice n m xs ~ ys ∩ List.dropSlice n m xs := by
  simp only [dropSlice_eq]
  have : n ≤ n + m := Nat.le_add_right _ _
  have h₂ := h.nodup_iff.2 h'
  apply Perm.trans _ (Perm.inter_append _).symm
  · exact Perm.append (Perm.take_inter _ h h') (Perm.drop_inter _ h h')
  · exact disjoint_take_drop h₂ this

-- enumerating permutations
section Permutations

theorem perm_of_mem_permutationsAux :
    ∀ {ts is l : List α}, l ∈ permutationsAux ts is → l ~ ts ++ is := by
  show ∀ (ts is l : List α), l ∈ permutationsAux ts is → l ~ ts ++ is
  refine permutationsAux.rec (by simp) ?_
  introv IH1 IH2 m
  rw [permutationsAux_cons, permutations, mem_foldr_permutationsAux2] at m
  rcases m with (m | ⟨l₁, l₂, m, _, rfl⟩)
  · exact (IH1 _ m).trans perm_middle
  · have p : l₁ ++ l₂ ~ is := by
      simp only [mem_cons] at m
      cases' m with e m
      · simp [e]
      exact is.append_nil ▸ IH2 _ m
    exact ((perm_middle.trans (p.cons _)).append_right _).trans (perm_append_comm.cons _)

theorem perm_of_mem_permutations {l₁ l₂ : List α} (h : l₁ ∈ permutations l₂) : l₁ ~ l₂ :=
  (eq_or_mem_of_mem_cons h).elim (fun e => e ▸ Perm.refl _) fun m =>
    append_nil l₂ ▸ perm_of_mem_permutationsAux m

theorem length_permutationsAux :
    ∀ ts is : List α, length (permutationsAux ts is) + is.length ! = (length ts + length is)! := by
  refine permutationsAux.rec (by simp) ?_
  intro t ts is IH1 IH2
  have IH2 : length (permutationsAux is nil) + 1 = is.length ! := by simpa using IH2
  simp only [factorial, Nat.mul_comm, add_eq] at IH1
  rw [permutationsAux_cons,
    length_foldr_permutationsAux2' _ _ _ _ _ fun l m => (perm_of_mem_permutations m).length_eq,
    permutations, length, length, IH2, Nat.succ_add, Nat.factorial_succ, Nat.mul_comm (_ + 1),
    ← Nat.succ_eq_add_one, ← IH1, Nat.add_comm (_ * _), Nat.add_assoc, Nat.mul_succ, Nat.mul_comm]

theorem length_permutations (l : List α) : length (permutations l) = (length l)! :=
  length_permutationsAux l []

theorem mem_permutations_of_perm_lemma {is l : List α}
    (H : l ~ [] ++ is → (∃ (ts' : _) (_ : ts' ~ []), l = ts' ++ is) ∨ l ∈ permutationsAux is []) :
    l ~ is → l ∈ permutations is := by simpa [permutations, perm_nil] using H

theorem mem_permutationsAux_of_perm :
    ∀ {ts is l : List α},
      l ~ is ++ ts → (∃ (is' : _) (_ : is' ~ is), l = is' ++ ts) ∨ l ∈ permutationsAux ts is := by
  show ∀ (ts is l : List α),
      l ~ is ++ ts → (∃ (is' : _) (_ : is' ~ is), l = is' ++ ts) ∨ l ∈ permutationsAux ts is
  refine permutationsAux.rec (by simp) ?_
  intro t ts is IH1 IH2 l p
  rw [permutationsAux_cons, mem_foldr_permutationsAux2]
  rcases IH1 _ (p.trans perm_middle) with (⟨is', p', e⟩ | m)
  · clear p
    subst e
    rcases append_of_mem (p'.symm.subset (mem_cons_self _ _)) with ⟨l₁, l₂, e⟩
    subst is'
    have p := (perm_middle.symm.trans p').cons_inv
    cases' l₂ with a l₂'
    · exact Or.inl ⟨l₁, by simpa using p⟩
    · exact Or.inr (Or.inr ⟨l₁, a :: l₂', mem_permutations_of_perm_lemma (IH2 _) p, by simp⟩)
  · exact Or.inr (Or.inl m)

@[simp]
theorem mem_permutations {s t : List α} : s ∈ permutations t ↔ s ~ t :=
  ⟨perm_of_mem_permutations, mem_permutations_of_perm_lemma mem_permutationsAux_of_perm⟩

-- Porting note: temporary theorem to solve diamond issue
private theorem DecEq_eq [DecidableEq α] :
    List.instBEq = @instBEqOfDecidableEq (List α) instDecidableEqList :=
  congr_arg BEq.mk <| by
    funext l₁ l₂
    show (l₁ == l₂) = _
    rw [Bool.eq_iff_iff, @beq_iff_eq _ (_), decide_eq_true_iff]

theorem perm_permutations'Aux_comm (a b : α) (l : List α) :
    (permutations'Aux a l).bind (permutations'Aux b) ~
      (permutations'Aux b l).bind (permutations'Aux a) := by
  induction' l with c l ih
  · simp [swap]
  simp only [permutations'Aux, bind_cons, map_cons, map_map, cons_append]
  apply Perm.swap'
  have :
    ∀ a b,
      (map (cons c) (permutations'Aux a l)).bind (permutations'Aux b) ~
        map (cons b ∘ cons c) (permutations'Aux a l) ++
          map (cons c) ((permutations'Aux a l).bind (permutations'Aux b)) := by
    intros a' b'
    simp only [bind_map, permutations'Aux]
    show List.bind (permutations'Aux _ l) (fun a => ([b' :: c :: a] ++
      map (cons c) (permutations'Aux _ a))) ~ _
    refine (bind_append_perm _ (fun x => [b' :: c :: x]) _).symm.trans ?_
    rw [← map_eq_bind, ← map_bind]
    exact Perm.refl _
  refine (((this _ _).append_left _).trans ?_).trans ((this _ _).append_left _).symm
  rw [← append_assoc, ← append_assoc]
  exact perm_append_comm.append (ih.map _)

theorem Perm.permutations' {s t : List α} (p : s ~ t) : permutations' s ~ permutations' t := by
  induction p with
  | nil => simp
  | cons _ _ IH => exact IH.bind_right _
  | swap =>
    dsimp
    rw [bind_assoc, bind_assoc]
    apply Perm.bind_left
    intro l' _
    apply perm_permutations'Aux_comm
  | trans _ _ IH₁ IH₂ => exact IH₁.trans IH₂

theorem permutations_perm_permutations' (ts : List α) : ts.permutations ~ ts.permutations' := by
  obtain ⟨n, h⟩ : ∃ n, length ts < n := ⟨_, Nat.lt_succ_self _⟩
  induction' n with n IH generalizing ts; · cases h
  refine List.reverseRecOn ts (fun _ => ?_) (fun ts t _ h => ?_) h; · simp [permutations]
  rw [← concat_eq_append, length_concat, Nat.succ_lt_succ_iff] at h
  have IH₂ := (IH ts.reverse (by rwa [length_reverse])).trans (reverse_perm _).permutations'
  simp only [permutations_append, foldr_permutationsAux2, permutationsAux_nil,
    permutationsAux_cons, append_nil]
  refine
    (perm_append_comm.trans ((IH₂.bind_right _).append ((IH _ h).map _))).trans
      (Perm.trans ?_ perm_append_comm.permutations')
  rw [map_eq_bind, singleton_append, permutations']
  refine (bind_append_perm _ _ _).trans ?_
  refine Perm.of_eq ?_
  congr
  funext _
  rw [permutations'Aux_eq_permutationsAux2, permutationsAux2_append]

@[simp]
theorem mem_permutations' {s t : List α} : s ∈ permutations' t ↔ s ~ t :=
  (permutations_perm_permutations' _).symm.mem_iff.trans mem_permutations

theorem Perm.permutations {s t : List α} (h : s ~ t) : permutations s ~ permutations t :=
  (permutations_perm_permutations' _).trans <|
    h.permutations'.trans (permutations_perm_permutations' _).symm

@[simp]
theorem perm_permutations_iff {s t : List α} : permutations s ~ permutations t ↔ s ~ t :=
  ⟨fun h => mem_permutations.1 <| h.mem_iff.1 <| mem_permutations.2 (Perm.refl _),
    Perm.permutations⟩

@[simp]
theorem perm_permutations'_iff {s t : List α} : permutations' s ~ permutations' t ↔ s ~ t :=
  ⟨fun h => mem_permutations'.1 <| h.mem_iff.1 <| mem_permutations'.2 (Perm.refl _),
    Perm.permutations'⟩

theorem getElem_permutations'Aux (s : List α) (x : α) (n : ℕ)
    (hn : n < length (permutations'Aux x s)) :
    (permutations'Aux x s)[n] = s.insertNth n x := by
  induction' s with y s IH generalizing n
  · simp only [length, Nat.zero_add, Nat.lt_one_iff] at hn
    simp [hn]
  · cases n
    · simp [get]
    · simpa [get] using IH _ _

theorem get_permutations'Aux (s : List α) (x : α) (n : ℕ)
    (hn : n < length (permutations'Aux x s)) :
    (permutations'Aux x s).get ⟨n, hn⟩ = s.insertNth n x := by
  simp [getElem_permutations'Aux]

theorem count_permutations'Aux_self [DecidableEq α] (l : List α) (x : α) :
    count (x :: l) (permutations'Aux x l) = length (takeWhile (x = ·) l) + 1 := by
  induction' l with y l IH generalizing x
  · simp [takeWhile, count]
  · rw [permutations'Aux, count_cons_self]
    by_cases hx : x = y
    · subst hx
      simpa [takeWhile, Nat.succ_inj', DecEq_eq] using IH _
    · rw [takeWhile]
      simp only [mem_map, cons.injEq, Ne.symm hx, false_and, and_false, exists_false,
        not_false_iff, count_eq_zero_of_not_mem, Nat.zero_add, hx, decide_False, length_nil]

@[simp]
theorem length_permutations'Aux (s : List α) (x : α) :
    length (permutations'Aux x s) = length s + 1 := by
  induction' s with y s IH
  · simp
  · simpa using IH

@[deprecated (since := "2024-06-12")]
theorem permutations'Aux_get_zero (s : List α) (x : α)
    (hn : 0 < length (permutations'Aux x s) := (by simp)) :
    (permutations'Aux x s).get ⟨0, hn⟩ = x :: s :=
  get_permutations'Aux _ _ _ _

theorem injective_permutations'Aux (x : α) : Function.Injective (permutations'Aux x) := by
  intro s t h
  apply insertNth_injective s.length x
  have hl : s.length = t.length := by simpa using congr_arg length h
  rw [← get_permutations'Aux s x s.length (by simp),
    ← get_permutations'Aux t x s.length (by simp [hl])]
  simp only [get_eq_getElem, h, hl]

theorem nodup_permutations'Aux_of_not_mem (s : List α) (x : α) (hx : x ∉ s) :
    Nodup (permutations'Aux x s) := by
  induction' s with y s IH
  · simp
  · simp only [not_or, mem_cons] at hx
    simp only [permutations'Aux, nodup_cons, mem_map, cons.injEq, exists_eq_right_right, not_and]
    refine ⟨fun _ => Ne.symm hx.left, ?_⟩
    rw [nodup_map_iff]
    · exact IH hx.right
    · simp

theorem nodup_permutations'Aux_iff {s : List α} {x : α} : Nodup (permutations'Aux x s) ↔ x ∉ s := by
  refine ⟨fun h H ↦ ?_, nodup_permutations'Aux_of_not_mem _ _⟩
  obtain ⟨⟨k, hk⟩, hk'⟩ := get_of_mem H
  rw [nodup_iff_injective_get] at h
  apply k.succ_ne_self.symm
  have kl : k < (permutations'Aux x s).length := by simpa [Nat.lt_succ_iff] using hk.le
  have k1l : k + 1 < (permutations'Aux x s).length := by simpa using hk
  rw [← @Fin.mk.inj_iff _ _ _ kl k1l]; apply h
  rw [get_permutations'Aux, get_permutations'Aux]
  have hl : length (insertNth k x s) = length (insertNth (k + 1) x s) := by
    rw [length_insertNth _ _ hk.le, length_insertNth _ _ (Nat.succ_le_of_lt hk)]
  refine ext_get hl fun n hn hn' => ?_
  rcases lt_trichotomy n k with (H | rfl | H)
  · rw [get_insertNth_of_lt _ _ _ _ H (H.trans hk),
      get_insertNth_of_lt _ _ _ _ (H.trans (Nat.lt_succ_self _))]
  · rw [get_insertNth_self _ _ _ hk.le, get_insertNth_of_lt _ _ _ _ (Nat.lt_succ_self _) hk, hk']
  · rcases (Nat.succ_le_of_lt H).eq_or_lt with (rfl | H')
    · rw [get_insertNth_self _ _ _ (Nat.succ_le_of_lt hk)]
      convert hk' using 1
      exact get_insertNth_add_succ _ _ _ 0 _
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt H'
      erw [length_insertNth _ _ hk.le, Nat.succ_lt_succ_iff, Nat.succ_add] at hn
      rw [get_insertNth_add_succ]
      · convert get_insertNth_add_succ s x k m.succ (by simpa using hn) using 2
        · simp [Nat.add_assoc, Nat.add_left_comm]
        · simp [Nat.add_left_comm, Nat.add_comm]
      · simpa [Nat.succ_add] using hn

theorem nodup_permutations (s : List α) (hs : Nodup s) : Nodup s.permutations := by
  rw [(permutations_perm_permutations' s).nodup_iff]
  induction' hs with x l h h' IH
  · simp
  · rw [permutations']
    rw [nodup_bind]
    constructor
    · intro ys hy
      rw [mem_permutations'] at hy
      rw [nodup_permutations'Aux_iff, hy.mem_iff]
      exact fun H => h x H rfl
    · refine IH.pairwise_of_forall_ne fun as ha bs hb H => ?_
      rw [disjoint_iff_ne]
      rintro a ha' b hb' rfl
      obtain ⟨⟨n, hn⟩, hn'⟩ := get_of_mem ha'
      obtain ⟨⟨m, hm⟩, hm'⟩ := get_of_mem hb'
      rw [mem_permutations'] at ha hb
      have hl : as.length = bs.length := (ha.trans hb.symm).length_eq
      simp only [Nat.lt_succ_iff, length_permutations'Aux] at hn hm
      rw [get_permutations'Aux] at hn' hm'
      have hx :
        (insertNth n x as)[m]'(by rwa [length_insertNth _ _ hn, Nat.lt_succ_iff, hl]) = x := by
        simp [hn', ← hm', hm]
      have hx' :
        (insertNth m x bs)[n]'(by rwa [length_insertNth _ _ hm, Nat.lt_succ_iff, ← hl]) = x := by
        simp [hm', ← hn', hn]
      rcases lt_trichotomy n m with (ht | ht | ht)
      · suffices x ∈ bs by exact h x (hb.subset this) rfl
        rw [← hx', getElem_insertNth_of_lt _ _ _ _ ht (ht.trans_le hm)]
        exact get_mem _ _ _
      · simp only [ht] at hm' hn'
        rw [← hm'] at hn'
        exact H (insertNth_injective _ _ hn')
      · suffices x ∈ as by exact h x (ha.subset this) rfl
        rw [← hx, getElem_insertNth_of_lt _ _ _ _ ht (ht.trans_le hn)]
        exact get_mem _ _ _

lemma permutations_take_two (x y : α) (s : List α) :
    (x :: y :: s).permutations.take 2 = [x :: y :: s, y :: x :: s] := by
  induction s <;> simp only [take, permutationsAux, permutationsAux.rec, permutationsAux2, id_eq]

@[simp]
theorem nodup_permutations_iff {s : List α} : Nodup s.permutations ↔ Nodup s := by
  refine ⟨?_, nodup_permutations s⟩
  contrapose
  rw [← exists_duplicate_iff_not_nodup]
  intro ⟨x, hs⟩
  rw [duplicate_iff_sublist] at hs
  obtain ⟨l, ht⟩ := List.Sublist.exists_perm_append hs
  rw [List.Perm.nodup_iff (List.Perm.permutations ht), ← exists_duplicate_iff_not_nodup]
  use x :: x :: l
  rw [List.duplicate_iff_sublist, ← permutations_take_two]
  exact take_sublist 2 _

-- TODO: `count s s.permutations = (zipWith count s s.tails).prod`
end Permutations

end List
