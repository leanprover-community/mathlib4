/-
Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seul Baek
-/
import Mathlib.Data.Nat.Order.Basic

#align_import data.list.func from "leanprover-community/mathlib"@"d11893b411025250c8e61ff2f12ccbd7ee35ab15"

/-!
# Lists as Functions

Definitions for using lists as finite representations of finitely-supported functions with domain
ℕ.

These include pointwise operations on lists, as well as get and set operations.

## Notations

An index notation is introduced in this file for setting a particular element of a list. With `as`
as a list `m` as an index, and `a` as a new element, the notation is `as {m ↦ a}`.

So, for example
`[1, 3, 5] {1 ↦ 9}` would result in `[1, 9, 5]`

This notation is in the locale `list.func`.
-/


open List

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

namespace List

namespace Func

variable {a : α}

variable {as as1 as2 as3 : List α}

/-- Elementwise negation of a list -/
def neg [Neg α] (as : List α) :=
  as.map fun a ↦ -a
#align list.func.neg List.Func.neg

variable [Inhabited α] [Inhabited β]

/-- Update element of a list by index. If the index is out of range, extend the list with default
elements
-/
@[simp]
def set (a : α) : List α → ℕ → List α
  | _ :: as, 0 => a :: as
  | [], 0 => [a]
  | h :: as, k + 1 => h :: set a as k
  | [], k + 1 => default :: set a ([] : List α) k
#align list.func.set List.Func.set

-- mathport name: list.func.set
@[inherit_doc]
scoped notation as " {" m " ↦ " a "}" => List.Func.set a as m

/-- Get element of a list by index. If the index is out of range, return the default element -/
@[simp]
def get : ℕ → List α → α
  | _, [] => default
  | 0, a :: _ => a
  | n + 1, _ :: as => get n as
#align list.func.get List.Func.get

/-- Pointwise equality of lists. If lists are different lengths, compare with the default
element.
-/
def Equiv (as1 as2 : List α) : Prop :=
  ∀ m : Nat, get m as1 = get m as2
#align list.func.equiv List.Func.Equiv

/-- Pointwise operations on lists. If lists are different lengths, use the default element. -/
@[simp]
def pointwise (f : α → β → γ) : List α → List β → List γ
  | [], [] => []
  | [], b :: bs => map (f default) (b :: bs)
  | a :: as, [] => map (fun x ↦ f x default) (a :: as)
  | a :: as, b :: bs => f a b :: pointwise f as bs
#align list.func.pointwise List.Func.pointwise

/-- Pointwise addition on lists. If lists are different lengths, use zero. -/
def add {α : Type u} [Zero α] [Add α] : List α → List α → List α :=
  @pointwise α α α ⟨0⟩ ⟨0⟩ (· + ·)
#align list.func.add List.Func.add

/-- Pointwise subtraction on lists. If lists are different lengths, use zero. -/
def sub {α : Type u} [Zero α] [Sub α] : List α → List α → List α :=
  @pointwise α α α ⟨0⟩ ⟨0⟩ (@Sub.sub α _)
#align list.func.sub List.Func.sub

-- set
theorem length_set : ∀ {m : ℕ} {as : List α}, as {m ↦ a}.length = max as.length (m + 1)
  | 0, [] => rfl
  | 0, a :: as => by
    rw [max_eq_left]
    -- ⊢ length ((a :: as) {0 ↦ a✝}) = length (a :: as)
    · rfl
      -- 🎉 no goals
    · simp [Nat.le_add_right]
      -- ⊢ 1 ≤ Nat.succ (length as)
      exact Nat.succ_le_succ (Nat.zero_le _)
      -- 🎉 no goals
  | m + 1, [] => by
    have := @length_set m []
    -- ⊢ length ([] {m + 1 ↦ a}) = max (length []) (m + 1 + 1)
    simp [set, length, @length_set m, Nat.zero_max]
    -- 🎉 no goals
  | m + 1, _ :: as => by
    simp [set, length, @length_set m, Nat.max_succ_succ]
    -- 🎉 no goals
#align list.func.length_set List.Func.length_set

-- porting note : @[simp] has been removed since `#lint` says this is
theorem get_nil {k : ℕ} : (get k [] : α) = default := by cases k <;> rfl
                                                         -- ⊢ get Nat.zero [] = default
                                                                     -- 🎉 no goals
                                                                     -- 🎉 no goals
#align list.func.get_nil List.Func.get_nil

theorem get_eq_default_of_le : ∀ (k : ℕ) {as : List α}, as.length ≤ k → get k as = default
  | 0, [], _ => rfl
  | 0, a :: as, h1 => by cases h1
                         -- 🎉 no goals
  | k + 1, [], _ => rfl
  | k + 1, _ :: as, h1 => by
    apply get_eq_default_of_le k
    -- ⊢ length as ≤ k
    rw [← Nat.succ_le_succ_iff]; apply h1
    -- ⊢ Nat.succ (length as) ≤ Nat.succ k
                                 -- 🎉 no goals
#align list.func.get_eq_default_of_le List.Func.get_eq_default_of_le

@[simp]
theorem get_set {a : α} : ∀ {k : ℕ} {as : List α}, get k (as {k ↦ a}) = a
  | 0, as => by cases as <;> rfl
                -- ⊢ get 0 ([] {0 ↦ a}) = a
                             -- 🎉 no goals
                             -- 🎉 no goals
  | k + 1, as => by cases as <;> simp [get_set]
                    -- ⊢ get (k + 1) ([] {k + 1 ↦ a}) = a
                                 -- 🎉 no goals
                                 -- 🎉 no goals
#align list.func.get_set List.Func.get_set

theorem eq_get_of_mem {a : α} : ∀ {as : List α}, a ∈ as → ∃ n : Nat, a = get n as
  | [], h => by cases h
                -- 🎉 no goals
  | b :: as, h => by
    rw [mem_cons] at h -- porting note : `mem_cons_iff` is now named `mem_cons`
    -- ⊢ ∃ n, a = get n (b :: as)
    cases h with
    | inl h => exact ⟨0, h⟩
    | inr h =>
      rcases eq_get_of_mem h with ⟨n, h⟩
      exact ⟨n + 1, h⟩
#noalign list.func.eq_get_of_mem
-- porting note : the signature has been changed to correct what was presumably a bug,
-- hence the #noalign

theorem mem_get_of_le : ∀ {n : ℕ} {as : List α}, n < as.length → get n as ∈ as
  | _, [], h1 => by cases h1
                    -- 🎉 no goals
  -- porting note : needed to add to `rw [mem_cons] here` in the two cases below
  -- and in other lemmas (presumably because previously lean could see through the def of `mem` ?)
  | 0, a :: as, _ => by rw [mem_cons]; exact Or.inl rfl
                        -- ⊢ get 0 (a :: as) = a ∨ get 0 (a :: as) ∈ as
                                       -- 🎉 no goals
  | n + 1, a :: as, h1 => by
    rw [mem_cons]; apply Or.inr; unfold get
    -- ⊢ get (n + 1) (a :: as) = a ∨ get (n + 1) (a :: as) ∈ as
                   -- ⊢ get (n + 1) (a :: as) ∈ as
                                 -- ⊢ get (Nat.add n 0) as ∈ as
    apply mem_get_of_le
    -- ⊢ Nat.add n 0 < length as
    apply Nat.lt_of_succ_lt_succ h1
    -- 🎉 no goals
#align list.func.mem_get_of_le List.Func.mem_get_of_le

theorem mem_get_of_ne_zero : ∀ {n : ℕ} {as : List α}, get n as ≠ default → get n as ∈ as
  | _, [], h1 => by exfalso; apply h1; rw [get_nil]
                    -- ⊢ False
                             -- ⊢ get x✝ [] = default
                                       -- 🎉 no goals
  | 0, a :: as, _ => by rw [mem_cons]; exact Or.inl rfl
                        -- ⊢ get 0 (a :: as) = a ∨ get 0 (a :: as) ∈ as
                                       -- 🎉 no goals
  | n + 1, a :: as, h1 => by
    rw [mem_cons]; unfold get
    -- ⊢ get (n + 1) (a :: as) = a ∨ get (n + 1) (a :: as) ∈ as
                   -- ⊢ get (Nat.add n 0) as = a ∨ get (Nat.add n 0) as ∈ as
    apply Or.inr (mem_get_of_ne_zero _)
    -- ⊢ get (Nat.add n 0) as ≠ default
    apply h1
    -- 🎉 no goals
#align list.func.mem_get_of_ne_zero List.Func.mem_get_of_ne_zero

theorem get_set_eq_of_ne {a : α} :
    ∀ {as : List α} (k : ℕ) (m : ℕ), m ≠ k → get m (as {k ↦ a}) = get m as
  | as, 0, m, h1 => by
    cases m
    -- ⊢ get Nat.zero (as {0 ↦ a}) = get Nat.zero as
    contradiction
    -- ⊢ get (Nat.succ n✝) (as {0 ↦ a}) = get (Nat.succ n✝) as
    cases as <;> simp only [set, get, get_nil]
    -- ⊢ get (Nat.succ n✝) ([] {0 ↦ a}) = get (Nat.succ n✝) []
                 -- 🎉 no goals
                 -- 🎉 no goals
  | as, k + 1, m, h1 => by
    -- porting note : I somewhat rearranged the case split
    cases as <;> cases m
    -- ⊢ get m ([] {k + 1 ↦ a}) = get m []
                 -- ⊢ get Nat.zero ([] {k + 1 ↦ a}) = get Nat.zero []
                 -- ⊢ get Nat.zero ((head✝ :: tail✝) {k + 1 ↦ a}) = get Nat.zero (head✝ :: tail✝)
    case nil =>
      simp only [set, get]
    case nil m =>
      have h3 : get m (nil {k ↦ a}) = default := by
        rw [get_set_eq_of_ne k m, get_nil]
        intro hc
        apply h1
        simp [hc]
      apply h3
    case zero =>
      simp only [set, get]
    case _ _ m =>
      apply get_set_eq_of_ne k m
      intro hc
      apply h1
      simp [hc]
#align list.func.get_set_eq_of_ne List.Func.get_set_eq_of_ne

theorem get_map {f : α → β} :
    ∀ {n : ℕ} {as : List α}, n < as.length → get n (as.map f) = f (get n as)
  | _, [], h => by cases h
                   -- 🎉 no goals
  | 0, a :: as, _ => rfl
  | n + 1, _ :: as, h1 => by
    have h2 : n < length as := by
      rw [← Nat.succ_le_iff, ← Nat.lt_succ_iff]
      apply h1
    apply get_map h2
    -- 🎉 no goals
#align list.func.get_map List.Func.get_map

theorem get_map' {f : α → β} {n : ℕ} {as : List α} :
    f default = default → get n (as.map f) = f (get n as) := by
  intro h1; by_cases h2 : n < as.length
  -- ⊢ get n (map f as) = f (get n as)
            -- ⊢ get n (map f as) = f (get n as)
  · apply get_map h2
    -- 🎉 no goals
  · rw [not_lt] at h2
    -- ⊢ get n (map f as) = f (get n as)
    rw [get_eq_default_of_le _ h2, get_eq_default_of_le, h1]
    -- ⊢ length (map f as) ≤ n
    rw [length_map]
    -- ⊢ length as ≤ n
    apply h2
    -- 🎉 no goals
#align list.func.get_map' List.Func.get_map'

theorem forall_val_of_forall_mem {as : List α} {p : α → Prop} :
    p default → (∀ x ∈ as, p x) → ∀ n, p (get n as) := by
  intro h1 h2 n
  -- ⊢ p (get n as)
  by_cases h3 : n < as.length
  -- ⊢ p (get n as)
  · apply h2 _ (mem_get_of_le h3)
    -- 🎉 no goals
  · rw [not_lt] at h3
    -- ⊢ p (get n as)
    rw [get_eq_default_of_le _ h3]
    -- ⊢ p default
    apply h1
    -- 🎉 no goals
#align list.func.forall_val_of_forall_mem List.Func.forall_val_of_forall_mem

-- equiv
theorem equiv_refl : Equiv as as := fun _ ↦ rfl
#align list.func.equiv_refl List.Func.equiv_refl

theorem equiv_symm : Equiv as1 as2 → Equiv as2 as1 := fun h1 k ↦ (h1 k).symm
#align list.func.equiv_symm List.Func.equiv_symm

theorem equiv_trans : Equiv as1 as2 → Equiv as2 as3 → Equiv as1 as3 := fun h1 h2 k ↦
  Eq.trans (h1 k) (h2 k)
#align list.func.equiv_trans List.Func.equiv_trans

theorem equiv_of_eq : as1 = as2 → Equiv as1 as2 := by intro h1; rw [h1]; apply equiv_refl
                                                      -- ⊢ Equiv as1 as2
                                                                -- ⊢ Equiv as2 as2
                                                                         -- 🎉 no goals
#align list.func.equiv_of_eq List.Func.equiv_of_eq

theorem eq_of_equiv : ∀ {as1 as2 : List α}, as1.length = as2.length → Equiv as1 as2 → as1 = as2
  | [], [], _, _ => rfl
  | _ :: _, [], h1, _ => by cases h1
                            -- 🎉 no goals
  | [], _ :: _, h1, _ => by cases h1
                            -- 🎉 no goals
  | a1 :: as1, a2 :: as2, h1, h2 => by
    congr
    -- ⊢ a1 = a2
    · apply h2 0
      -- 🎉 no goals
    · have h3 : as1.length = as2.length := by simpa [add_left_inj, add_comm, length] using h1
      -- ⊢ as1 = as2
      apply eq_of_equiv h3
      -- ⊢ Equiv as1 as2
      intro m
      -- ⊢ get m as1 = get m as2
      apply h2 (m + 1)
      -- 🎉 no goals
#align list.func.eq_of_equiv List.Func.eq_of_equiv

end Func

-- We want to drop the `Inhabited` instances for a moment,
-- so we close and open the namespace
namespace Func

-- neg
@[simp]
theorem get_neg [AddGroup α] {k : ℕ} {as : List α} : @get α ⟨0⟩ k (neg as) = -@get α ⟨0⟩ k as := by
  unfold neg
  -- ⊢ get k (map (fun a => -a) as) = -get k as
  rw [@get_map' α α ⟨0⟩ ⟨0⟩] -- porting note: had to add a `⟨0⟩` b/c of instance troubles
  -- ⊢ -default = default
  apply neg_zero
  -- 🎉 no goals
#align list.func.get_neg List.Func.get_neg

@[simp]
theorem length_neg [Neg α] (as : List α) : (neg as).length = as.length := by
  simp only [neg, length_map]
  -- 🎉 no goals
#align list.func.length_neg List.Func.length_neg

variable [Inhabited α] [Inhabited β]

-- pointwise
theorem nil_pointwise {f : α → β → γ} : ∀ bs : List β, pointwise f [] bs = bs.map (f default)
  | [] => rfl
  | b :: bs => by simp only [nil_pointwise bs, pointwise, eq_self_iff_true, and_self_iff, map]
                  -- 🎉 no goals
#align list.func.nil_pointwise List.Func.nil_pointwise

theorem pointwise_nil {f : α → β → γ} :
    ∀ as : List α, pointwise f as [] = as.map fun a ↦ f a default
  | [] => rfl
  | a :: as => by simp only [pointwise_nil as, pointwise, eq_self_iff_true, and_self_iff, List.map]
                  -- 🎉 no goals
#align list.func.pointwise_nil List.Func.pointwise_nil

theorem get_pointwise [Inhabited γ] {f : α → β → γ} (h1 : f default default = default) :
    ∀ (k : Nat) (as : List α) (bs : List β), get k (pointwise f as bs) = f (get k as) (get k bs)
  | k, [], [] => by simp only [h1, get_nil, pointwise, get]
                    -- 🎉 no goals
  | 0, [], b :: _ => by simp only [get_pointwise, get_nil, pointwise, get, Nat.zero_eq, map]
                        -- 🎉 no goals
  | k + 1, [], b :: bs => by
    have : get k (map (f default) bs) = f default (get k bs) := by
      simpa [nil_pointwise, get_nil] using get_pointwise h1 k [] bs
    simpa [get, get_nil, pointwise, map]
    -- 🎉 no goals
  | 0, a :: _, [] => by simp only [get_pointwise, get_nil, pointwise, get, Nat.zero_eq, map]
                        -- 🎉 no goals
  | k + 1, a :: as, [] => by
    simpa [get, get_nil, pointwise, map, pointwise_nil, get_nil] using get_pointwise h1 k as []
    -- 🎉 no goals
  | 0, a :: _, b :: _ => by simp only [pointwise, get]
                            -- 🎉 no goals
  | k + 1, _ :: as, _ :: bs => by
    simp only [get, Nat.add_eq, add_zero, get_pointwise h1 k as bs]
    -- 🎉 no goals
#align list.func.get_pointwise List.Func.get_pointwise

theorem length_pointwise {f : α → β → γ} :
    ∀ {as : List α} {bs : List β}, (pointwise f as bs).length = max as.length bs.length
  | [], [] => rfl
  | [], _ :: bs => by
    simp only [pointwise, length, length_map, max_eq_right (Nat.zero_le (length bs + 1))]
    -- 🎉 no goals
  | _ :: as, [] => by
    simp only [pointwise, length, length_map, max_eq_left (Nat.zero_le (length as + 1))]
    -- 🎉 no goals
  | _ :: as, _ :: bs => by
    simp only [pointwise, length, Nat.max_succ_succ, @length_pointwise _ as bs]
    -- 🎉 no goals
#align list.func.length_pointwise List.Func.length_pointwise

end Func

namespace Func

-- add
@[simp]
theorem get_add {α : Type u} [AddMonoid α] {k : ℕ} {xs ys : List α} :
    -- porting note : `@` and `⟨0⟩`s added b/c of instance troubles
    -- (similarly at other places below)
    @get α ⟨0⟩ k (add xs ys) = @get α ⟨0⟩ k xs + @get α ⟨0⟩ k ys := by
  apply @get_pointwise _ _ _ ⟨0⟩ ⟨0⟩ ⟨0⟩
  -- ⊢ default + default = default
  apply zero_add
  -- 🎉 no goals
#align list.func.get_add List.Func.get_add

@[simp]
theorem length_add {α : Type u} [Zero α] [Add α] {xs ys : List α} :
    (add xs ys).length = max xs.length ys.length :=
  @length_pointwise α α α ⟨0⟩ ⟨0⟩ _ _ _
#align list.func.length_add List.Func.length_add

@[simp]
theorem nil_add {α : Type u} [AddMonoid α] (as : List α) : add [] as = as := by
  rw [add, @nil_pointwise α α α ⟨0⟩ ⟨0⟩]
  -- ⊢ map (fun x => default + x) as = as
  apply Eq.trans _ (map_id as)
  -- ⊢ map (fun x => default + x) as = map id as
  congr with x
  -- ⊢ default + x = id x
  exact zero_add x
  -- 🎉 no goals
  -- porting note: instead of `zero_add`, it was the commented `rw` below
  -- (similarly at other places below)
  --rw [zero_add, id]
#align list.func.nil_add List.Func.nil_add

@[simp]
theorem add_nil {α : Type u} [AddMonoid α] (as : List α) : add as [] = as := by
  rw [add, @pointwise_nil α α α ⟨0⟩ ⟨0⟩]
  -- ⊢ map (fun a => a + default) as = as
  apply Eq.trans _ (map_id as)
  -- ⊢ map (fun a => a + default) as = map id as
  congr with x
  -- ⊢ x + default = id x
  exact add_zero x
  -- 🎉 no goals
#align list.func.add_nil List.Func.add_nil

theorem map_add_map {α : Type u} [AddMonoid α] (f g : α → α) {as : List α} :
    add (as.map f) (as.map g) = as.map fun x ↦ f x + g x := by
  apply @eq_of_equiv _ (⟨0⟩ : Inhabited α)
  -- ⊢ length (add (map f as) (map g as)) = length (map (fun x => f x + g x) as)
  · rw [length_map, length_add, max_eq_left, length_map]
    -- ⊢ length (map g as) ≤ length (map f as)
    apply le_of_eq
    -- ⊢ length (map g as) = length (map f as)
    rw [length_map, length_map]
    -- 🎉 no goals
  intro m
  -- ⊢ get m (add (map f as) (map g as)) = get m (map (fun x => f x + g x) as)
  rw [get_add]
  -- ⊢ get m (map f as) + get m (map g as) = get m (map (fun x => f x + g x) as)
  by_cases h : m < length as
  -- ⊢ get m (map f as) + get m (map g as) = get m (map (fun x => f x + g x) as)
  · repeat' rw [@get_map α α ⟨0⟩ ⟨0⟩ _ _ _ h]
    -- 🎉 no goals
  rw [not_lt] at h
  -- ⊢ get m (map f as) + get m (map g as) = get m (map (fun x => f x + g x) as)
  repeat' rw [@get_eq_default_of_le _ ⟨0⟩ m] <;> try rw [length_map]; apply h
  -- ⊢ default + default = default
  exact zero_add _
  -- 🎉 no goals
#align list.func.map_add_map List.Func.map_add_map

-- sub
@[simp]
theorem get_sub {α : Type u} [AddGroup α] {k : ℕ} {xs ys : List α} :
    @get α ⟨0⟩ k (sub xs ys) = @get α ⟨0⟩ k xs - @get α ⟨0⟩ k ys := by
  apply @get_pointwise _ _ _ ⟨0⟩ ⟨0⟩ ⟨0⟩
  -- ⊢ Sub.sub default default = default
  apply sub_zero
  -- 🎉 no goals
#align list.func.get_sub List.Func.get_sub

@[simp]
theorem length_sub [Zero α] [Sub α] {xs ys : List α} :
    (sub xs ys).length = max xs.length ys.length :=
  @length_pointwise α α α ⟨0⟩ ⟨0⟩ _ _ _
#align list.func.length_sub List.Func.length_sub

@[simp]
theorem nil_sub {α : Type*} [AddGroup α] (as : List α) : sub [] as = neg as := by
  rw [sub, @nil_pointwise _ _ _ ⟨0⟩ ⟨0⟩]
  -- ⊢ map (Sub.sub default) as = neg as
  congr with x
  -- ⊢ Sub.sub default x = -x
  exact zero_sub x
  -- 🎉 no goals
#align list.func.nil_sub List.Func.nil_sub

@[simp]
theorem sub_nil {α : Type*} [AddGroup α] (as : List α) : sub as [] = as := by
  rw [sub, @pointwise_nil _ _ _ ⟨0⟩ ⟨0⟩]
  -- ⊢ map (fun a => Sub.sub a default) as = as
  apply Eq.trans _ (map_id as)
  -- ⊢ map (fun a => Sub.sub a default) as = map id as
  congr with x
  -- ⊢ Sub.sub x default = id x
  exact sub_zero x
  -- 🎉 no goals
#align list.func.sub_nil List.Func.sub_nil

end Func

end List
