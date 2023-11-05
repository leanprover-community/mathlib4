/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kenny Lau
-/
import Mathlib.Data.List.BigOperators.Basic
import Mathlib.Algebra.Order.Monoid.MinMax

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


universe u

open Nat

namespace List

variable {α : Type u} {β γ δ ε : Type*}


@[simp]
theorem zipWith_eq_nil_iff {f : α → β → γ} {l l'} : zipWith f l l' = [] ↔ l = [] ∨ l' = [] := by
  cases l <;> cases l' <;> simp


@[simp]
theorem zip_swap : ∀ (l₁ : List α) (l₂ : List β), (zip l₁ l₂).map Prod.swap = zip l₂ l₁
  | [], l₂ => zip_nil_right.symm
  | l₁, [] => by rw [zip_nil_right]; rfl
  | a :: l₁, b :: l₂ => by
    simp only [zip_cons_cons, map_cons, zip_swap l₁ l₂, Prod.swap_prod_mk]



theorem forall_zipWith {f : α → β → γ} {p : γ → Prop} :
    ∀ {l₁ : List α} {l₂ : List β} (_h : length l₁ = length l₂),
      Forall p (zipWith f l₁ l₂) ↔ Forall₂ (fun x y => p (f x y)) l₁ l₂
  | [], [], _ => by simp
  | a :: l₁, b :: l₂, h => by
    simp only [length_cons, succ_inj'] at h
    simp [forall_zipWith h]

theorem lt_length_left_of_zipWith {f : α → β → γ} {i : ℕ} {l : List α} {l' : List β}
    (h : i < (zipWith f l l').length) : i < l.length := by
  rw [length_zipWith, lt_min_iff] at h
  exact h.left

theorem lt_length_right_of_zipWith {f : α → β → γ} {i : ℕ} {l : List α} {l' : List β}
    (h : i < (zipWith f l l').length) : i < l'.length := by
  rw [length_zipWith, lt_min_iff] at h
  exact h.right

theorem lt_length_left_of_zip {i : ℕ} {l : List α} {l' : List β} (h : i < (zip l l').length) :
    i < l.length :=
  lt_length_left_of_zipWith h

theorem lt_length_right_of_zip {i : ℕ} {l : List α} {l' : List β} (h : i < (zip l l').length) :
    i < l'.length :=
  lt_length_right_of_zipWith h

theorem zip_append :
    ∀ {l₁ r₁ : List α} {l₂ r₂ : List β} (_h : length l₁ = length l₂),
      zip (l₁ ++ r₁) (l₂ ++ r₂) = zip l₁ l₂ ++ zip r₁ r₂
  | [], r₁, l₂, r₂, h => by simp only [eq_nil_of_length_eq_zero h.symm]; rfl
  | l₁, r₁, [], r₂, h => by simp only [eq_nil_of_length_eq_zero h]; rfl
  | a :: l₁, r₁, b :: l₂, r₂, h => by
    simp only [cons_append, zip_cons_cons, zip_append (succ.inj h)]


theorem zip_map' (f : α → β) (g : α → γ) :
    ∀ l : List α, zip (l.map f) (l.map g) = l.map fun a => (f a, g a)
  | [] => rfl
  | a :: l => by simp only [map, zip_cons_cons, zip_map']

theorem map_zipWith {δ : Type*} (f : α → β) (g : γ → δ → α) (l : List γ) (l' : List δ) :
    map f (zipWith g l l') = zipWith (fun x y => f (g x y)) l l' := by
  induction' l with hd tl hl generalizing l'
  · simp
  · cases l'
    · simp
    · simp [hl]

theorem mem_zip {a b} : ∀ {l₁ : List α} {l₂ : List β}, (a, b) ∈ zip l₁ l₂ → a ∈ l₁ ∧ b ∈ l₂
  | _ :: l₁, _ :: l₂, h => by
    cases' h with _ _ _ h
    · simp
    · have := mem_zip h
      exact ⟨Mem.tail _ this.1, Mem.tail _ this.2⟩

theorem map_fst_zip :
    ∀ (l₁ : List α) (l₂ : List β), l₁.length ≤ l₂.length → map Prod.fst (zip l₁ l₂) = l₁
  | [], bs, _ => rfl
  | _ :: as, _ :: bs, h => by
    simp [succ_le_succ_iff] at h
    change _ :: map Prod.fst (zip as bs) = _ :: as
    rw [map_fst_zip as bs h]
  | a :: as, [], h => by simp at h

theorem map_snd_zip :
    ∀ (l₁ : List α) (l₂ : List β), l₂.length ≤ l₁.length → map Prod.snd (zip l₁ l₂) = l₂
  | _, [], _ => by
    rw [zip_nil_right]
    rfl
  | [], b :: bs, h => by simp at h
  | a :: as, b :: bs, h => by
    simp [succ_le_succ_iff] at h
    change _ :: map Prod.snd (zip as bs) = _ :: bs
    rw [map_snd_zip as bs h]



theorem unzip_eq_map : ∀ l : List (α × β), unzip l = (l.map Prod.fst, l.map Prod.snd)
  | [] => rfl
  | (a, b) :: l => by simp only [unzip_cons, map_cons, unzip_eq_map l]

theorem unzip_left (l : List (α × β)) : (unzip l).1 = l.map Prod.fst := by simp only [unzip_eq_map]

theorem unzip_right (l : List (α × β)) : (unzip l).2 = l.map Prod.snd := by simp only [unzip_eq_map]

theorem unzip_swap (l : List (α × β)) : unzip (l.map Prod.swap) = (unzip l).swap := by
  simp only [unzip_eq_map, map_map]
  rfl

theorem zip_unzip : ∀ l : List (α × β), zip (unzip l).1 (unzip l).2 = l
  | [] => rfl
  | (a, b) :: l => by simp only [unzip_cons, zip_cons_cons, zip_unzip l]

theorem unzip_zip_left :
    ∀ {l₁ : List α} {l₂ : List β}, length l₁ ≤ length l₂ → (unzip (zip l₁ l₂)).1 = l₁
  | [], l₂, _ => rfl
  | l₁, [], h => by rw [eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero h)]; rfl
  | a :: l₁, b :: l₂, h => by
    simp only [zip_cons_cons, unzip_cons, unzip_zip_left (le_of_succ_le_succ h)]

theorem unzip_zip_right {l₁ : List α} {l₂ : List β} (h : length l₂ ≤ length l₁) :
    (unzip (zip l₁ l₂)).2 = l₂ := by rw [← zip_swap, unzip_swap]; exact unzip_zip_left h

theorem unzip_zip {l₁ : List α} {l₂ : List β} (h : length l₁ = length l₂) :
    unzip (zip l₁ l₂) = (l₁, l₂) := by
  rw [← Prod.mk.eta (p := unzip (zip l₁ l₂)),
    unzip_zip_left (le_of_eq h), unzip_zip_right (ge_of_eq h)]

theorem zip_of_prod {l : List α} {l' : List β} {lp : List (α × β)} (hl : lp.map Prod.fst = l)
    (hr : lp.map Prod.snd = l') : lp = l.zip l' := by
  rw [← hl, ← hr, ← zip_unzip lp, ← unzip_left, ← unzip_right, zip_unzip, zip_unzip]

theorem map_prod_left_eq_zip {l : List α} (f : α → β) :
    (l.map fun x => (x, f x)) = l.zip (l.map f) := by
  rw [← zip_map']
  congr
  exact map_id _

theorem map_prod_right_eq_zip {l : List α} (f : α → β) :
    (l.map fun x => (f x, x)) = (l.map f).zip l := by
  rw [← zip_map']
  congr
  exact map_id _

theorem zipWith_comm (f : α → β → γ) :
    ∀ (la : List α) (lb : List β), zipWith f la lb = zipWith (fun b a => f a b) lb la
  | [], _ => List.zipWith_nil_right.symm
  | _ :: _, [] => rfl
  | _ :: as, _ :: bs => congr_arg _ (zipWith_comm f as bs)

@[congr]
theorem zipWith_congr (f g : α → β → γ) (la : List α) (lb : List β)
    (h : List.Forall₂ (fun a b => f a b = g a b) la lb) : zipWith f la lb = zipWith g la lb := by
  induction' h with a b as bs hfg _ ih
  · rfl
  · exact congr_arg₂ _ hfg ih

theorem zipWith_comm_of_comm (f : α → α → β) (comm : ∀ x y : α, f x y = f y x) (l l' : List α) :
    zipWith f l l' = zipWith f l' l := by
  rw [zipWith_comm]
  simp only [comm]

@[simp]
theorem zipWith_same (f : α → α → δ) : ∀ l : List α, zipWith f l l = l.map fun a => f a a
  | [] => rfl
  | _ :: xs => congr_arg _ (zipWith_same f xs)

theorem zipWith_zipWith_left (f : δ → γ → ε) (g : α → β → δ) :
    ∀ (la : List α) (lb : List β) (lc : List γ),
      zipWith f (zipWith g la lb) lc = zipWith3 (fun a b c => f (g a b) c) la lb lc
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | _ :: _, _ :: _, [] => rfl
  | _ :: as, _ :: bs, _ :: cs => congr_arg (cons _) <| zipWith_zipWith_left f g as bs cs

theorem zipWith_zipWith_right (f : α → δ → ε) (g : β → γ → δ) :
    ∀ (la : List α) (lb : List β) (lc : List γ),
      zipWith f la (zipWith g lb lc) = zipWith3 (fun a b c => f a (g b c)) la lb lc
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | _ :: _, _ :: _, [] => rfl
  | _ :: as, _ :: bs, _ :: cs => congr_arg (cons _) <| zipWith_zipWith_right f g as bs cs

@[simp]
theorem zipWith3_same_left (f : α → α → β → γ) :
    ∀ (la : List α) (lb : List β), zipWith3 f la la lb = zipWith (fun a b => f a a b) la lb
  | [], _ => rfl
  | _ :: _, [] => rfl
  | _ :: as, _ :: bs => congr_arg (cons _) <| zipWith3_same_left f as bs

@[simp]
theorem zipWith3_same_mid (f : α → β → α → γ) :
    ∀ (la : List α) (lb : List β), zipWith3 f la lb la = zipWith (fun a b => f a b a) la lb
  | [], _ => rfl
  | _ :: _, [] => rfl
  | _ :: as, _ :: bs => congr_arg (cons _) <| zipWith3_same_mid f as bs

@[simp]
theorem zipWith3_same_right (f : α → β → β → γ) :
    ∀ (la : List α) (lb : List β), zipWith3 f la lb lb = zipWith (fun a b => f a b b) la lb
  | [], _ => rfl
  | _ :: _, [] => rfl
  | _ :: as, _ :: bs => congr_arg (cons _) <| zipWith3_same_right f as bs

instance (f : α → α → β) [IsSymmOp α β f] : IsSymmOp (List α) (List β) (zipWith f) :=
  ⟨zipWith_comm_of_comm f IsSymmOp.symm_op⟩

@[simp]
theorem length_revzip (l : List α) : length (revzip l) = length l := by
  simp only [revzip, length_zip, length_reverse, min_self]

@[simp]
theorem unzip_revzip (l : List α) : (revzip l).unzip = (l, l.reverse) :=
  unzip_zip (length_reverse l).symm

@[simp]
theorem revzip_map_fst (l : List α) : (revzip l).map Prod.fst = l := by
  rw [← unzip_left, unzip_revzip]

@[simp]
theorem revzip_map_snd (l : List α) : (revzip l).map Prod.snd = l.reverse := by
  rw [← unzip_right, unzip_revzip]

theorem reverse_revzip (l : List α) : reverse l.revzip = revzip l.reverse := by
  rw [← zip_unzip (revzip l).reverse]
  simp [unzip_eq_map, revzip, map_reverse, map_fst_zip, map_snd_zip]

theorem revzip_swap (l : List α) : (revzip l).map Prod.swap = revzip l.reverse := by simp [revzip]

theorem get?_zip_with (f : α → β → γ) (l₁ : List α) (l₂ : List β) (i : ℕ) :
    (zipWith f l₁ l₂).get? i = ((l₁.get? i).map f).bind fun g => (l₂.get? i).map g := by
  induction' l₁ with head tail generalizing l₂ i
  · rw [zipWith] <;> simp
  · cases l₂
    simp only [zipWith, Seq.seq, Functor.map, get?, Option.map_none']
    · cases (head :: tail).get? i <;> rfl
    · cases i <;> simp only [Option.map_some', get?, Option.some_bind', *]

theorem get?_zip_with_eq_some {α β γ} (f : α → β → γ) (l₁ : List α) (l₂ : List β) (z : γ) (i : ℕ) :
    (zipWith f l₁ l₂).get? i = some z ↔
      ∃ x y, l₁.get? i = some x ∧ l₂.get? i = some y ∧ f x y = z := by
  induction l₁ generalizing l₂ i
  · simp [zipWith]
  · cases l₂ <;> simp only [zipWith, get?, exists_false, and_false_iff, false_and_iff]
    cases i <;> simp [*]

theorem get?_zip_eq_some (l₁ : List α) (l₂ : List β) (z : α × β) (i : ℕ) :
    (zip l₁ l₂).get? i = some z ↔ l₁.get? i = some z.1 ∧ l₂.get? i = some z.2 := by
  cases z
  rw [zip, get?_zip_with_eq_some]; constructor
  · rintro ⟨x, y, h₀, h₁, h₂⟩
    simpa [h₀, h₁] using h₂
  · rintro ⟨h₀, h₁⟩
    exact ⟨_, _, h₀, h₁, rfl⟩

@[simp]
theorem get_zipWith {f : α → β → γ} {l : List α} {l' : List β} {i : Fin (zipWith f l l').length} :
    (zipWith f l l').get i =
      f (l.get ⟨i, lt_length_left_of_zipWith i.isLt⟩)
        (l'.get ⟨i, lt_length_right_of_zipWith i.isLt⟩) := by
  rw [← Option.some_inj, ← get?_eq_get, get?_zip_with_eq_some]
  exact
    ⟨l.get ⟨i, lt_length_left_of_zipWith i.isLt⟩, l'.get ⟨i, lt_length_right_of_zipWith i.isLt⟩,
      by rw [get?_eq_get], by rw [get?_eq_get]; exact ⟨rfl, rfl⟩⟩

@[simp]
theorem nthLe_zipWith {f : α → β → γ} {l : List α} {l' : List β} {i : ℕ}
    {h : i < (zipWith f l l').length} :
    (zipWith f l l').nthLe i h =
      f (l.nthLe i (lt_length_left_of_zipWith h)) (l'.nthLe i (lt_length_right_of_zipWith h)) :=
  get_zipWith (i := ⟨i, h⟩)

@[simp]
theorem get_zip {l : List α} {l' : List β} {i : Fin (zip l l').length} :
    (zip l l').get i =
      (l.get ⟨i, lt_length_left_of_zip i.isLt⟩, l'.get ⟨i, lt_length_right_of_zip i.isLt⟩) :=
  get_zipWith

@[simp]
theorem nthLe_zip {l : List α} {l' : List β} {i : ℕ} {h : i < (zip l l').length} :
    (zip l l').nthLe i h =
      (l.nthLe i (lt_length_left_of_zip h), l'.nthLe i (lt_length_right_of_zip h)) :=
  nthLe_zipWith

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

theorem map_uncurry_zip_eq_zipWith (f : α → β → γ) (l : List α) (l' : List β) :
    map (Function.uncurry f) (l.zip l') = zipWith f l l' := by
  rw [zip]
  induction' l with hd tl hl generalizing l'
  · simp
  · cases' l' with hd' tl'
    · simp
    · simp [hl]

@[simp]
theorem sum_zipWith_distrib_left {γ : Type*} [Semiring γ] (f : α → β → γ) (n : γ) (l : List α)
    (l' : List β) : (l.zipWith (fun x y => n * f x y) l').sum = n * (l.zipWith f l').sum := by
  induction' l with hd tl hl generalizing f n l'
  · simp
  · cases' l' with hd' tl'
    · simp
    · simp [hl, mul_add]

section Distrib

/-! ### Operations that can be applied before or after a `zip_with` -/


variable (f : α → β → γ) (l : List α) (l' : List β) (n : ℕ)

theorem zipWith_distrib_take : (zipWith f l l').take n = zipWith f (l.take n) (l'.take n) := by
  induction' l with hd tl hl generalizing l' n
  · simp
  · cases l'
    · simp
    · cases n
      · simp
      · simp [hl]

theorem zipWith_distrib_drop : (zipWith f l l').drop n = zipWith f (l.drop n) (l'.drop n) := by
  induction' l with hd tl hl generalizing l' n
  · simp
  · cases l'
    · simp
    · cases n
      · simp
      · simp [hl]

theorem zipWith_distrib_tail : (zipWith f l l').tail = zipWith f l.tail l'.tail := by
  simp_rw [← drop_one, zipWith_distrib_drop]

theorem zipWith_append (f : α → β → γ) (l la : List α) (l' lb : List β)
    (h : l.length = l'.length) :
    zipWith f (l ++ la) (l' ++ lb) = zipWith f l l' ++ zipWith f la lb := by
  induction' l with hd tl hl generalizing l'
  · have : l' = [] := eq_nil_of_length_eq_zero (by simpa using h.symm)
    simp [this]
  · cases l'
    · simp at h
    · simp only [add_left_inj, length] at h
      simp [hl _ h]

theorem zipWith_distrib_reverse (h : l.length = l'.length) :
    (zipWith f l l').reverse = zipWith f l.reverse l'.reverse := by
  induction' l with hd tl hl generalizing l'
  · simp
  · cases' l' with hd' tl'
    · simp
    · simp only [add_left_inj, length] at h
      have : tl.reverse.length = tl'.reverse.length := by simp [h]
      simp [hl _ h, zipWith_append _ _ _ _ _ this]

end Distrib

section CommMonoid

variable [CommMonoid α]

@[to_additive]
theorem prod_mul_prod_eq_prod_zipWith_mul_prod_drop :
    ∀ L L' : List α,
      L.prod * L'.prod =
        (zipWith (· * ·) L L').prod * (L.drop L'.length).prod * (L'.drop L.length).prod
  | [], ys => by simp [Nat.zero_le]
  | xs, [] => by simp [Nat.zero_le]
  | x :: xs, y :: ys => by
    simp only [drop, length, zipWith_cons_cons, prod_cons]
    conv =>
      lhs; rw [mul_assoc]; right; rw [mul_comm, mul_assoc]; right
      rw [mul_comm, prod_mul_prod_eq_prod_zipWith_mul_prod_drop xs ys]
    simp only [add_eq, add_zero]
    ac_rfl

@[to_additive]
theorem prod_mul_prod_eq_prod_zipWith_of_length_eq (L L' : List α) (h : L.length = L'.length) :
    L.prod * L'.prod = (zipWith (· * ·) L L').prod := by
  apply (prod_mul_prod_eq_prod_zipWith_mul_prod_drop L L').trans
  rw [← h, drop_length, h, drop_length, prod_nil, mul_one, mul_one]

end CommMonoid

end List
