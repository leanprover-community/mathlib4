/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kenny Lau
-/
import Mathlib.Data.List.Forall2

#align_import data.list.zip from "leanprover-community/mathlib"@"134625f523e737f650a6ea7f0c82a6177e45e622"

/-!
# zip & unzip

This file provides results about `List.zipWith`, `List.zip` and `List.unzip` (definitions are in
core Lean).
`zipWith f l₁ l₂` applies `f : α → β → γ` pointwise to a list `l₁ : List α` and `l₂ : List β`. It
applies, until one of the lists is exhausted. For example,
`zipWith f [0, 1, 2] [6.28, 31] = [f 0 6.28, f 1 31]`.
`zip` is `zipWith` applied to `Prod.mk`. For example,
`zip [a₁, a₂] [b₁, b₂, b₃] = [(a₁, b₁), (a₂, b₂)]`.
`unzip` undoes `zip`. For example, `unzip [(a₁, b₁), (a₂, b₂)] = ([a₁, a₂], [b₁, b₂])`.
-/

-- Make sure we don't import algebra
assert_not_exists Monoid

universe u

open Nat

namespace List

variable {α : Type u} {β γ δ ε : Type*}

#align list.zip_with_cons_cons List.zipWith_cons_cons
#align list.zip_cons_cons List.zip_cons_cons
#align list.zip_with_nil_left List.zipWith_nil_left
#align list.zip_with_nil_right List.zipWith_nil_right
#align list.zip_with_eq_nil_iff List.zipWith_eq_nil_iff
#align list.zip_nil_left List.zip_nil_left
#align list.zip_nil_right List.zip_nil_right

@[simp]
theorem zip_swap : ∀ (l₁ : List α) (l₂ : List β), (zip l₁ l₂).map Prod.swap = zip l₂ l₁
  | [], l₂ => zip_nil_right.symm
  | l₁, [] => by rw [zip_nil_right]; rfl
  | a :: l₁, b :: l₂ => by
    simp only [zip_cons_cons, map_cons, zip_swap l₁ l₂, Prod.swap_prod_mk]
#align list.zip_swap List.zip_swap

#align list.length_zip_with List.length_zipWith

#align list.length_zip List.length_zip

theorem forall_zipWith {f : α → β → γ} {p : γ → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, length l₁ = length l₂ →
      (Forall p (zipWith f l₁ l₂) ↔ Forall₂ (fun x y => p (f x y)) l₁ l₂)
  | [], [], _ => by simp
  | a :: l₁, b :: l₂, h => by
    simp only [length_cons, succ_inj'] at h
    simp [forall_zipWith h]
#align list.all₂_zip_with List.forall_zipWith

theorem lt_length_left_of_zipWith {f : α → β → γ} {i : ℕ} {l : List α} {l' : List β}
    (h : i < (zipWith f l l').length) : i < l.length := by rw [length_zipWith] at h; omega
#align list.lt_length_left_of_zip_with List.lt_length_left_of_zipWith

theorem lt_length_right_of_zipWith {f : α → β → γ} {i : ℕ} {l : List α} {l' : List β}
    (h : i < (zipWith f l l').length) : i < l'.length := by rw [length_zipWith] at h; omega
#align list.lt_length_right_of_zip_with List.lt_length_right_of_zipWith

theorem lt_length_left_of_zip {i : ℕ} {l : List α} {l' : List β} (h : i < (zip l l').length) :
    i < l.length :=
  lt_length_left_of_zipWith h
#align list.lt_length_left_of_zip List.lt_length_left_of_zip

theorem lt_length_right_of_zip {i : ℕ} {l : List α} {l' : List β} (h : i < (zip l l').length) :
    i < l'.length :=
  lt_length_right_of_zipWith h
#align list.lt_length_right_of_zip List.lt_length_right_of_zip

#align list.zip_append List.zip_append
#align list.zip_map List.zip_map
#align list.zip_map_left List.zip_map_left
#align list.zip_map_right List.zip_map_right
#align list.zip_with_map List.zipWith_map
#align list.zip_with_map_left List.zipWith_map_left
#align list.zip_with_map_right List.zipWith_map_right
#align list.zip_map' List.zip_map'
#align list.map_zip_with List.map_zipWith

theorem mem_zip {a b} : ∀ {l₁ : List α} {l₂ : List β}, (a, b) ∈ zip l₁ l₂ → a ∈ l₁ ∧ b ∈ l₂
  | _ :: l₁, _ :: l₂, h => by
    cases' h with _ _ _ h
    · simp
    · have := mem_zip h
      exact ⟨Mem.tail _ this.1, Mem.tail _ this.2⟩
#align list.mem_zip List.mem_zip

#align list.map_fst_zip List.map_fst_zip
#align list.map_snd_zip List.map_snd_zip
#align list.unzip_nil List.unzip_nil
#align list.unzip_cons List.unzip_cons

theorem unzip_eq_map : ∀ l : List (α × β), unzip l = (l.map Prod.fst, l.map Prod.snd)
  | [] => rfl
  | (a, b) :: l => by simp only [unzip_cons, map_cons, unzip_eq_map l]
#align list.unzip_eq_map List.unzip_eq_map

theorem unzip_left (l : List (α × β)) : (unzip l).1 = l.map Prod.fst := by simp only [unzip_eq_map]
#align list.unzip_left List.unzip_left

theorem unzip_right (l : List (α × β)) : (unzip l).2 = l.map Prod.snd := by simp only [unzip_eq_map]
#align list.unzip_right List.unzip_right

theorem unzip_swap (l : List (α × β)) : unzip (l.map Prod.swap) = (unzip l).swap := by
  simp only [unzip_eq_map, map_map]
  rfl
#align list.unzip_swap List.unzip_swap

theorem zip_unzip : ∀ l : List (α × β), zip (unzip l).1 (unzip l).2 = l
  | [] => rfl
  | (a, b) :: l => by simp only [unzip_cons, zip_cons_cons, zip_unzip l]
#align list.zip_unzip List.zip_unzip

theorem unzip_zip_left :
    ∀ {l₁ : List α} {l₂ : List β}, length l₁ ≤ length l₂ → (unzip (zip l₁ l₂)).1 = l₁
  | [], l₂, _ => rfl
  | l₁, [], h => by rw [eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero h)]; rfl
  | a :: l₁, b :: l₂, h => by
    simp only [zip_cons_cons, unzip_cons, unzip_zip_left (le_of_succ_le_succ h)]
#align list.unzip_zip_left List.unzip_zip_left

theorem unzip_zip_right {l₁ : List α} {l₂ : List β} (h : length l₂ ≤ length l₁) :
    (unzip (zip l₁ l₂)).2 = l₂ := by rw [← zip_swap, unzip_swap]; exact unzip_zip_left h
#align list.unzip_zip_right List.unzip_zip_right

theorem unzip_zip {l₁ : List α} {l₂ : List β} (h : length l₁ = length l₂) :
    unzip (zip l₁ l₂) = (l₁, l₂) := by
  rw [← Prod.mk.eta (p := unzip (zip l₁ l₂)),
    unzip_zip_left (le_of_eq h), unzip_zip_right (ge_of_eq h)]
#align list.unzip_zip List.unzip_zip

theorem zip_of_prod {l : List α} {l' : List β} {lp : List (α × β)} (hl : lp.map Prod.fst = l)
    (hr : lp.map Prod.snd = l') : lp = l.zip l' := by
  rw [← hl, ← hr, ← zip_unzip lp, ← unzip_left, ← unzip_right, zip_unzip, zip_unzip]
#align list.zip_of_prod List.zip_of_prod

theorem map_prod_left_eq_zip {l : List α} (f : α → β) :
    (l.map fun x => (x, f x)) = l.zip (l.map f) := by
  rw [← zip_map']
  congr
  exact map_id _
#align list.map_prod_left_eq_zip List.map_prod_left_eq_zip

theorem map_prod_right_eq_zip {l : List α} (f : α → β) :
    (l.map fun x => (f x, x)) = (l.map f).zip l := by
  rw [← zip_map']
  congr
  exact map_id _
#align list.map_prod_right_eq_zip List.map_prod_right_eq_zip

theorem zipWith_comm (f : α → β → γ) :
    ∀ (la : List α) (lb : List β), zipWith f la lb = zipWith (fun b a => f a b) lb la
  | [], _ => List.zipWith_nil_right.symm
  | _ :: _, [] => rfl
  | _ :: as, _ :: bs => congr_arg _ (zipWith_comm f as bs)
#align list.zip_with_comm List.zipWith_comm

@[congr]
theorem zipWith_congr (f g : α → β → γ) (la : List α) (lb : List β)
    (h : List.Forall₂ (fun a b => f a b = g a b) la lb) : zipWith f la lb = zipWith g la lb := by
  induction' h with a b as bs hfg _ ih
  · rfl
  · exact congr_arg₂ _ hfg ih
#align list.zip_with_congr List.zipWith_congr

theorem zipWith_comm_of_comm (f : α → α → β) (comm : ∀ x y : α, f x y = f y x) (l l' : List α) :
    zipWith f l l' = zipWith f l' l := by
  rw [zipWith_comm]
  simp only [comm]
#align list.zip_with_comm_of_comm List.zipWith_comm_of_comm

@[simp]
theorem zipWith_same (f : α → α → δ) : ∀ l : List α, zipWith f l l = l.map fun a => f a a
  | [] => rfl
  | _ :: xs => congr_arg _ (zipWith_same f xs)
#align list.zip_with_same List.zipWith_same

theorem zipWith_zipWith_left (f : δ → γ → ε) (g : α → β → δ) :
    ∀ (la : List α) (lb : List β) (lc : List γ),
      zipWith f (zipWith g la lb) lc = zipWith3 (fun a b c => f (g a b) c) la lb lc
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | _ :: _, _ :: _, [] => rfl
  | _ :: as, _ :: bs, _ :: cs => congr_arg (cons _) <| zipWith_zipWith_left f g as bs cs
#align list.zip_with_zip_with_left List.zipWith_zipWith_left

theorem zipWith_zipWith_right (f : α → δ → ε) (g : β → γ → δ) :
    ∀ (la : List α) (lb : List β) (lc : List γ),
      zipWith f la (zipWith g lb lc) = zipWith3 (fun a b c => f a (g b c)) la lb lc
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | _ :: _, _ :: _, [] => rfl
  | _ :: as, _ :: bs, _ :: cs => congr_arg (cons _) <| zipWith_zipWith_right f g as bs cs
#align list.zip_with_zip_with_right List.zipWith_zipWith_right

@[simp]
theorem zipWith3_same_left (f : α → α → β → γ) :
    ∀ (la : List α) (lb : List β), zipWith3 f la la lb = zipWith (fun a b => f a a b) la lb
  | [], _ => rfl
  | _ :: _, [] => rfl
  | _ :: as, _ :: bs => congr_arg (cons _) <| zipWith3_same_left f as bs
#align list.zip_with3_same_left List.zipWith3_same_left

@[simp]
theorem zipWith3_same_mid (f : α → β → α → γ) :
    ∀ (la : List α) (lb : List β), zipWith3 f la lb la = zipWith (fun a b => f a b a) la lb
  | [], _ => rfl
  | _ :: _, [] => rfl
  | _ :: as, _ :: bs => congr_arg (cons _) <| zipWith3_same_mid f as bs
#align list.zip_with3_same_mid List.zipWith3_same_mid

@[simp]
theorem zipWith3_same_right (f : α → β → β → γ) :
    ∀ (la : List α) (lb : List β), zipWith3 f la lb lb = zipWith (fun a b => f a b b) la lb
  | [], _ => rfl
  | _ :: _, [] => rfl
  | _ :: as, _ :: bs => congr_arg (cons _) <| zipWith3_same_right f as bs
#align list.zip_with3_same_right List.zipWith3_same_right

instance (f : α → α → β) [IsSymmOp α β f] : IsSymmOp (List α) (List β) (zipWith f) :=
  ⟨zipWith_comm_of_comm f IsSymmOp.symm_op⟩

@[simp]
theorem length_revzip (l : List α) : length (revzip l) = length l := by
  simp only [revzip, length_zip, length_reverse, min_self]
#align list.length_revzip List.length_revzip

@[simp]
theorem unzip_revzip (l : List α) : (revzip l).unzip = (l, l.reverse) :=
  unzip_zip (length_reverse l).symm
#align list.unzip_revzip List.unzip_revzip

@[simp]
theorem revzip_map_fst (l : List α) : (revzip l).map Prod.fst = l := by
  rw [← unzip_left, unzip_revzip]
#align list.revzip_map_fst List.revzip_map_fst

@[simp]
theorem revzip_map_snd (l : List α) : (revzip l).map Prod.snd = l.reverse := by
  rw [← unzip_right, unzip_revzip]
#align list.revzip_map_snd List.revzip_map_snd

theorem reverse_revzip (l : List α) : reverse l.revzip = revzip l.reverse := by
  rw [← zip_unzip (revzip l).reverse]
  simp [unzip_eq_map, revzip, map_reverse, map_fst_zip, map_snd_zip]
#align list.reverse_revzip List.reverse_revzip

theorem revzip_swap (l : List α) : (revzip l).map Prod.swap = revzip l.reverse := by simp [revzip]
#align list.revzip_swap List.revzip_swap

theorem get?_zip_with (f : α → β → γ) (l₁ : List α) (l₂ : List β) (i : ℕ) :
    (zipWith f l₁ l₂).get? i = ((l₁.get? i).map f).bind fun g => (l₂.get? i).map g := by
  induction' l₁ with head tail generalizing l₂ i
  · rw [zipWith] <;> simp
  · cases l₂
    · simp only [zipWith, Seq.seq, Functor.map, get?, Option.map_none']
      cases (head :: tail).get? i <;> rfl
    · cases i <;> simp only [Option.map_some', get?, Option.some_bind', *]
#align list.nth_zip_with List.get?_zip_with

theorem get?_zip_with_eq_some {α β γ} (f : α → β → γ) (l₁ : List α) (l₂ : List β) (z : γ) (i : ℕ) :
    (zipWith f l₁ l₂).get? i = some z ↔
      ∃ x y, l₁.get? i = some x ∧ l₂.get? i = some y ∧ f x y = z := by
  induction l₁ generalizing l₂ i
  · simp [zipWith]
  · cases l₂ <;> simp only [zipWith, get?, exists_false, and_false_iff, false_and_iff]
    cases i <;> simp [*]
#align list.nth_zip_with_eq_some List.get?_zip_with_eq_some

theorem get?_zip_eq_some (l₁ : List α) (l₂ : List β) (z : α × β) (i : ℕ) :
    (zip l₁ l₂).get? i = some z ↔ l₁.get? i = some z.1 ∧ l₂.get? i = some z.2 := by
  cases z
  rw [zip, get?_zip_with_eq_some]; constructor
  · rintro ⟨x, y, h₀, h₁, h₂⟩
    simpa [h₀, h₁] using h₂
  · rintro ⟨h₀, h₁⟩
    exact ⟨_, _, h₀, h₁, rfl⟩
#align list.nth_zip_eq_some List.get?_zip_eq_some

@[simp]
theorem get_zipWith {f : α → β → γ} {l : List α} {l' : List β} {i : Fin (zipWith f l l').length} :
    (zipWith f l l').get i =
      f (l.get ⟨i, lt_length_left_of_zipWith i.isLt⟩)
        (l'.get ⟨i, lt_length_right_of_zipWith i.isLt⟩) := by
  rw [← Option.some_inj, ← get?_eq_get, get?_zip_with_eq_some]
  exact
    ⟨l.get ⟨i, lt_length_left_of_zipWith i.isLt⟩, l'.get ⟨i, lt_length_right_of_zipWith i.isLt⟩,
      by rw [get?_eq_get], by rw [get?_eq_get]; exact ⟨rfl, rfl⟩⟩

set_option linter.deprecated false in
@[simp, deprecated get_zipWith (since := "2024-05-09")]
theorem nthLe_zipWith {f : α → β → γ} {l : List α} {l' : List β} {i : ℕ}
    {h : i < (zipWith f l l').length} :
    (zipWith f l l').nthLe i h =
      f (l.nthLe i (lt_length_left_of_zipWith h)) (l'.nthLe i (lt_length_right_of_zipWith h)) :=
  get_zipWith (i := ⟨i, h⟩)
#align list.nth_le_zip_with List.nthLe_zipWith

@[simp]
theorem get_zip {l : List α} {l' : List β} {i : Fin (zip l l').length} :
    (zip l l').get i =
      (l.get ⟨i, lt_length_left_of_zip i.isLt⟩, l'.get ⟨i, lt_length_right_of_zip i.isLt⟩) :=
  get_zipWith

set_option linter.deprecated false in
@[simp, deprecated get_zip (since := "2024-05-09")]
theorem nthLe_zip {l : List α} {l' : List β} {i : ℕ} {h : i < (zip l l').length} :
    (zip l l').nthLe i h =
      (l.nthLe i (lt_length_left_of_zip h), l'.nthLe i (lt_length_right_of_zip h)) :=
  nthLe_zipWith
#align list.nth_le_zip List.nthLe_zip

theorem mem_zip_inits_tails {l : List α} {init tail : List α} :
    (init, tail) ∈ zip l.inits l.tails ↔ init ++ tail = l := by
  induction' l with hd tl ih generalizing init tail <;> simp_rw [tails, inits, zip_cons_cons]
  · simp
  · constructor <;> rw [mem_cons, zip_map_left, mem_map, Prod.exists]
    · rintro (⟨rfl, rfl⟩ | ⟨_, _, h, rfl, rfl⟩)
      · simp
      · simp [ih.mp h]
    · cases' init with hd' tl'
      · rintro rfl
        simp
      · intro h
        right
        use tl', tail
        simp_all
#align list.mem_zip_inits_tails List.mem_zip_inits_tails

theorem map_uncurry_zip_eq_zipWith (f : α → β → γ) (l : List α) (l' : List β) :
    map (Function.uncurry f) (l.zip l') = zipWith f l l' := by
  rw [zip]
  induction' l with hd tl hl generalizing l'
  · simp
  · cases' l' with hd' tl'
    · simp
    · simp [hl]
#align list.map_uncurry_zip_eq_zip_with List.map_uncurry_zip_eq_zipWith

section Distrib

/-! ### Operations that can be applied before or after a `zip_with` -/


variable (f : α → β → γ) (l : List α) (l' : List β) (n : ℕ)

#align list.zip_with_distrib_take List.zipWith_distrib_take
#align list.zip_with_distrib_drop List.zipWith_distrib_drop
#align list.zip_with_distrib_tail List.zipWith_distrib_tail
#align list.zip_with_append List.zipWith_append

theorem zipWith_distrib_reverse (h : l.length = l'.length) :
    (zipWith f l l').reverse = zipWith f l.reverse l'.reverse := by
  induction' l with hd tl hl generalizing l'
  · simp
  · cases' l' with hd' tl'
    · simp
    · simp only [Nat.add_left_inj, length] at h
      have : tl.reverse.length = tl'.reverse.length := by simp [h]
      simp [hl _ h, zipWith_append _ _ _ _ _ this]
#align list.zip_with_distrib_reverse List.zipWith_distrib_reverse

end Distrib

end List
