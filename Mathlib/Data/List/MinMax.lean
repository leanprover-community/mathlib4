/-
Copyright (c) 2019 Minchao Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Minchao Wu, Chris Hughes, Mantas Bakšys
-/
import Mathlib.Data.List.Basic

#align_import data.list.min_max from "leanprover-community/mathlib"@"6d0adfa76594f304b4650d098273d4366edeb61b"

/-!
# Minimum and maximum of lists

## Main definitions

The main definitions are `argmax`, `argmin`, `minimum` and `maximum` for lists.

`argmax f l` returns `some a`, where `a` of `l` that maximises `f a`. If there are `a b` such that
  `f a = f b`, it returns whichever of `a` or `b` comes first in the list.
  `argmax f [] = none`

`minimum l` returns a `WithTop α`, the smallest element of `l` for nonempty lists, and `⊤` for
`[]`
-/

set_option autoImplicit true


namespace List

variable {α β : Type*}

section ArgAux

variable (r : α → α → Prop) [DecidableRel r] {l : List α} {o : Option α} {a m : α}

/-- Auxiliary definition for `argmax` and `argmin`. -/
def argAux (a : Option α) (b : α) : Option α :=
  Option.casesOn a (some b) fun c => if r b c then some b else some c
#align list.arg_aux List.argAux

@[simp]
theorem foldl_argAux_eq_none : l.foldl (argAux r) o = none ↔ l = [] ∧ o = none :=
  List.reverseRecOn l (by simp) fun tl hd => by
                          -- 🎉 no goals
    simp [argAux]; cases foldl (argAux r) o tl <;> simp; try split_ifs <;> simp
    -- ⊢ (foldl (fun a b => Option.rec (some b) (fun val => if r b val then some b el …
                   -- ⊢ (none = none ↔ tl = [] ∧ o = none) → ¬Option.rec (some hd) (fun val => if r  …
                                                   -- 🎉 no goals
                                                   -- ⊢ (tl = [] → ¬o = none) → ¬(if r hd val✝ then some hd else some val✝) = none
                                                         -- 🎉 no goals
#align list.foldl_arg_aux_eq_none List.foldl_argAux_eq_none

private theorem foldl_argAux_mem (l) : ∀ a m : α, m ∈ foldl (argAux r) (some a) l → m ∈ a :: l :=
  List.reverseRecOn l (by simp [eq_comm])
                          -- 🎉 no goals
    (by
      intro tl hd ih a m
      -- ⊢ m ∈ foldl (argAux r) (some a) (tl ++ [hd]) → m ∈ a :: (tl ++ [hd])
      simp only [foldl_append, foldl_cons, foldl_nil, argAux]
      -- ⊢ m ∈ Option.rec (some hd) (fun val => if r hd val then some hd else some val) …
      cases hf : foldl (argAux r) (some a) tl
      -- ⊢ m ∈ Option.rec (some hd) (fun val => if r hd val then some hd else some val) …
      · simp (config := { contextual := true })
        -- 🎉 no goals
      · dsimp only
        -- ⊢ (m ∈ if r hd val✝ then some hd else some val✝) → m ∈ a :: (tl ++ [hd])
        split_ifs
        -- ⊢ m ∈ some hd → m ∈ a :: (tl ++ [hd])
        · simp (config := { contextual := true })
          -- 🎉 no goals
        · -- `finish [ih _ _ hf]` closes this goal
          simp only [List.mem_cons] at ih
          -- ⊢ m ∈ some val✝ → m ∈ a :: (tl ++ [hd])
          rcases ih _ _ hf with rfl | H
          -- ⊢ m ∈ some val✝ → m ∈ val✝ :: (tl ++ [hd])
          · simp (config := { contextual := true }) only [Option.mem_def, Option.some.injEq,
              find?, eq_comm, mem_cons, mem_append, mem_singleton, true_or, implies_true]
          · simp (config := { contextual := true }) [@eq_comm _ _ m, H])
            -- 🎉 no goals

@[simp]
theorem argAux_self (hr₀ : Irreflexive r) (a : α) : argAux r (some a) a = a :=
  if_neg <| hr₀ _
#align list.arg_aux_self List.argAux_self

theorem not_of_mem_foldl_argAux (hr₀ : Irreflexive r) (hr₁ : Transitive r) :
    ∀ {a m : α} {o : Option α}, a ∈ l → m ∈ foldl (argAux r) o l → ¬r a m := by
  induction' l using List.reverseRecOn with tl a ih
  -- ⊢ ∀ {a m : α} {o : Option α}, a ∈ [] → m ∈ foldl (argAux r) o [] → ¬r a m
  · simp
    -- 🎉 no goals
  intro b m o hb ho
  -- ⊢ ¬r b m
  rw [foldl_append, foldl_cons, foldl_nil, argAux] at ho
  -- ⊢ ¬r b m
  cases' hf : foldl (argAux r) o tl with c
  -- ⊢ ¬r b m
  · rw [hf] at ho
    -- ⊢ ¬r b m
    rw [foldl_argAux_eq_none] at hf
    -- ⊢ ¬r b m
    simp_all [hf.1, hf.2, hr₀ _]
    -- 🎉 no goals
  rw [hf, Option.mem_def] at ho
  -- ⊢ ¬r b m
  dsimp only at ho
  -- ⊢ ¬r b m
  split_ifs at ho with hac <;> cases' mem_append.1 hb with h h <;>
  -- ⊢ ¬r b m
                               -- ⊢ ¬r b m
                               -- ⊢ ¬r b m
    injection ho with ho <;> subst ho
    -- ⊢ ¬r b m
    -- ⊢ ¬r b m
    -- ⊢ ¬r b m
    -- ⊢ ¬r b m
                             -- ⊢ ¬r b a
                             -- ⊢ ¬r b a
                             -- ⊢ ¬r b c
                             -- ⊢ ¬r b c
  · exact fun hba => ih h hf (hr₁ hba hac)
    -- 🎉 no goals
  · simp_all [hr₀ _]
    -- 🎉 no goals
  · exact ih h hf
    -- 🎉 no goals
  · simp_all
    -- 🎉 no goals
#align list.not_of_mem_foldl_arg_aux List.not_of_mem_foldl_argAux

end ArgAux

section Preorder

variable [Preorder β] [@DecidableRel β (· < ·)] {f : α → β} {l : List α} {o : Option α} {a m : α}

/-- `argmax f l` returns `some a`, where `f a` is maximal among the elements of `l`, in the sense
that there is no `b ∈ l` with `f a < f b`. If `a`, `b` are such that `f a = f b`, it returns
whichever of `a` or `b` comes first in the list. `argmax f [] = none`. -/
def argmax (f : α → β) (l : List α) : Option α :=
  l.foldl (argAux fun b c => f c < f b) none
#align list.argmax List.argmax

/-- `argmin f l` returns `some a`, where `f a` is minimal among the elements of `l`, in the sense
that there is no `b ∈ l` with `f b < f a`. If `a`, `b` are such that `f a = f b`, it returns
whichever of `a` or `b` comes first in the list. `argmin f [] = none`. -/
def argmin (f : α → β) (l : List α) :=
  l.foldl (argAux fun b c => f b < f c) none
#align list.argmin List.argmin

@[simp]
theorem argmax_nil (f : α → β) : argmax f [] = none :=
  rfl
#align list.argmax_nil List.argmax_nil

@[simp]
theorem argmin_nil (f : α → β) : argmin f [] = none :=
  rfl
#align list.argmin_nil List.argmin_nil

@[simp]
theorem argmax_singleton {f : α → β} {a : α} : argmax f [a] = a :=
  rfl
#align list.argmax_singleton List.argmax_singleton

@[simp]
theorem argmin_singleton {f : α → β} {a : α} : argmin f [a] = a :=
  rfl
#align list.argmin_singleton List.argmin_singleton

theorem not_lt_of_mem_argmax : a ∈ l → m ∈ argmax f l → ¬f m < f a :=
  not_of_mem_foldl_argAux _ (fun x h => lt_irrefl (f x) h)
    (fun _ _ z hxy hyz => lt_trans (a := f z) hyz hxy)
#align list.not_lt_of_mem_argmax List.not_lt_of_mem_argmax

theorem not_lt_of_mem_argmin : a ∈ l → m ∈ argmin f l → ¬f a < f m :=
  not_of_mem_foldl_argAux _ (fun x h => lt_irrefl (f x) h)
    (fun x _ _ hxy hyz => lt_trans (a := f x) hxy hyz)
#align list.not_lt_of_mem_argmin List.not_lt_of_mem_argmin

theorem argmax_concat (f : α → β) (a : α) (l : List α) :
    argmax f (l ++ [a]) =
      Option.casesOn (argmax f l) (some a) fun c => if f c < f a then some a else some c :=
  by rw [argmax, argmax]; simp [argAux]
     -- ⊢ foldl (argAux fun b c => f c < f b) none (l ++ [a]) = Option.casesOn (foldl  …
                          -- 🎉 no goals
#align list.argmax_concat List.argmax_concat

theorem argmin_concat (f : α → β) (a : α) (l : List α) :
    argmin f (l ++ [a]) =
      Option.casesOn (argmin f l) (some a) fun c => if f a < f c then some a else some c :=
  @argmax_concat _ βᵒᵈ _ _ _ _ _
#align list.argmin_concat List.argmin_concat

theorem argmax_mem : ∀ {l : List α} {m : α}, m ∈ argmax f l → m ∈ l
  | [], m => by simp
                -- 🎉 no goals
  | hd :: tl, m => by simpa [argmax, argAux] using foldl_argAux_mem _ tl hd m
                      -- 🎉 no goals
#align list.argmax_mem List.argmax_mem

theorem argmin_mem : ∀ {l : List α} {m : α}, m ∈ argmin f l → m ∈ l :=
  @argmax_mem _ βᵒᵈ _ _ _
#align list.argmin_mem List.argmin_mem

@[simp]
theorem argmax_eq_none : l.argmax f = none ↔ l = [] := by simp [argmax]
                                                          -- 🎉 no goals
#align list.argmax_eq_none List.argmax_eq_none

@[simp]
theorem argmin_eq_none : l.argmin f = none ↔ l = [] :=
  @argmax_eq_none _ βᵒᵈ _ _ _ _
#align list.argmin_eq_none List.argmin_eq_none

end Preorder

section LinearOrder

variable [LinearOrder β] {f : α → β} {l : List α} {o : Option α} {a m : α}

theorem le_of_mem_argmax : a ∈ l → m ∈ argmax f l → f a ≤ f m := fun ha hm =>
  le_of_not_lt <| not_lt_of_mem_argmax ha hm
#align list.le_of_mem_argmax List.le_of_mem_argmax

theorem le_of_mem_argmin : a ∈ l → m ∈ argmin f l → f m ≤ f a :=
  @le_of_mem_argmax _ βᵒᵈ _ _ _ _ _
#align list.le_of_mem_argmin List.le_of_mem_argmin

theorem argmax_cons (f : α → β) (a : α) (l : List α) :
    argmax f (a :: l) =
      Option.casesOn (argmax f l) (some a) fun c => if f a < f c then some c else some a :=
  List.reverseRecOn l rfl fun hd tl ih => by
    rw [← cons_append, argmax_concat, ih, argmax_concat]
    -- ⊢ (Option.casesOn (Option.casesOn (argmax f hd) (some a) fun c => if f a < f c …
    cases' h : argmax f hd with m
    -- ⊢ (Option.casesOn (Option.casesOn none (some a) fun c => if f a < f c then som …
    · simp [h]
      -- 🎉 no goals
    dsimp
    -- ⊢ Option.rec (some tl) (fun val => if f val < f tl then some tl else some val) …
    rw [← apply_ite, ← apply_ite]
    -- ⊢ Option.rec (some tl) (fun val => if f val < f tl then some tl else some val) …
    dsimp
    -- ⊢ (if f (if f a < f m then m else a) < f tl then some tl else some (if f a < f …
    split_ifs <;> try rfl
                  -- 🎉 no goals
                  -- ⊢ some tl = some a
                  -- 🎉 no goals
                  -- 🎉 no goals
                  -- ⊢ some tl = some a
                  -- 🎉 no goals
                  -- 🎉 no goals
    · exact absurd (lt_trans ‹f a < f m› ‹_›) ‹_›
      -- 🎉 no goals
    · cases (‹f a < f tl›.lt_or_lt _).elim ‹_› ‹_›
      -- 🎉 no goals
#align list.argmax_cons List.argmax_cons

theorem argmin_cons (f : α → β) (a : α) (l : List α) :
    argmin f (a :: l) =
      Option.casesOn (argmin f l) (some a) fun c => if f c < f a then some c else some a :=
  @argmax_cons α βᵒᵈ _ _ _ _
#align list.argmin_cons List.argmin_cons

variable [DecidableEq α]

theorem index_of_argmax :
    ∀ {l : List α} {m : α}, m ∈ argmax f l → ∀ {a}, a ∈ l → f m ≤ f a → l.indexOf m ≤ l.indexOf a
  | [], m, _, _, _, _ => by simp
                            -- 🎉 no goals
  | hd :: tl, m, hm, a, ha, ham => by
    simp only [indexOf_cons, argmax_cons, Option.mem_def] at hm ⊢
    -- ⊢ (if m = hd then 0 else Nat.succ (indexOf m tl)) ≤ if a = hd then 0 else Nat. …
    cases h : argmax f tl
    -- ⊢ (if m = hd then 0 else Nat.succ (indexOf m tl)) ≤ if a = hd then 0 else Nat. …
    · rw [h] at hm
      -- ⊢ (if m = hd then 0 else Nat.succ (indexOf m tl)) ≤ if a = hd then 0 else Nat. …
      simp_all
      -- 🎉 no goals
    rw [h] at hm
    -- ⊢ (if m = hd then 0 else Nat.succ (indexOf m tl)) ≤ if a = hd then 0 else Nat. …
    dsimp only at hm
    -- ⊢ (if m = hd then 0 else Nat.succ (indexOf m tl)) ≤ if a = hd then 0 else Nat. …
    obtain ha | ha := ha <;> split_ifs at hm <;> injection hm with hm <;> subst hm
    -- ⊢ (if m = hd then 0 else Nat.succ (indexOf m tl)) ≤ if hd = hd then 0 else Nat …
                             -- ⊢ (if m = hd then 0 else Nat.succ (indexOf m tl)) ≤ if hd = hd then 0 else Nat …
                             -- ⊢ (if m = hd then 0 else Nat.succ (indexOf m tl)) ≤ if a = hd then 0 else Nat. …
                                                 -- ⊢ (if m = hd then 0 else Nat.succ (indexOf m tl)) ≤ if hd = hd then 0 else Nat …
                                                 -- ⊢ (if m = hd then 0 else Nat.succ (indexOf m tl)) ≤ if hd = hd then 0 else Nat …
                                                 -- ⊢ (if m = hd then 0 else Nat.succ (indexOf m tl)) ≤ if a = hd then 0 else Nat. …
                                                 -- ⊢ (if m = hd then 0 else Nat.succ (indexOf m tl)) ≤ if a = hd then 0 else Nat. …
                                                                          -- ⊢ (if val✝ = hd then 0 else Nat.succ (indexOf val✝ tl)) ≤ if hd = hd then 0 el …
                                                                          -- ⊢ (if hd = hd then 0 else Nat.succ (indexOf hd tl)) ≤ if hd = hd then 0 else N …
                                                                          -- ⊢ (if val✝ = hd then 0 else Nat.succ (indexOf val✝ tl)) ≤ if a = hd then 0 els …
                                                                          -- ⊢ (if hd = hd then 0 else Nat.succ (indexOf hd tl)) ≤ if a = hd then 0 else Na …
    · cases not_le_of_lt ‹_› ‹_›
      -- 🎉 no goals
    · rw [if_pos rfl]
      -- 🎉 no goals
    · rw [if_neg, if_neg]
      exact Nat.succ_le_succ (index_of_argmax h (by assumption) ham)
      -- ⊢ ¬a = hd
      · exact ne_of_apply_ne f (lt_of_lt_of_le ‹_› ‹_›).ne'
        -- 🎉 no goals
      · exact ne_of_apply_ne _ ‹f hd < f _›.ne'
        -- 🎉 no goals
    · rw [if_pos rfl]
      -- ⊢ 0 ≤ if a = hd then 0 else Nat.succ (indexOf a tl)
      exact Nat.zero_le _
      -- 🎉 no goals
#align list.index_of_argmax List.index_of_argmax

theorem index_of_argmin :
    ∀ {l : List α} {m : α}, m ∈ argmin f l → ∀ {a}, a ∈ l → f a ≤ f m → l.indexOf m ≤ l.indexOf a :=
  @index_of_argmax _ βᵒᵈ _ _ _
#align list.index_of_argmin List.index_of_argmin

theorem mem_argmax_iff :
    m ∈ argmax f l ↔
      m ∈ l ∧ (∀ a ∈ l, f a ≤ f m) ∧ ∀ a ∈ l, f m ≤ f a → l.indexOf m ≤ l.indexOf a :=
  ⟨fun hm => ⟨argmax_mem hm, fun a ha => le_of_mem_argmax ha hm, fun _ => index_of_argmax hm⟩,
    by
      rintro ⟨hml, ham, hma⟩
      -- ⊢ m ∈ argmax f l
      cases' harg : argmax f l with n
      -- ⊢ m ∈ none
      · simp_all
        -- 🎉 no goals
      · have :=
          _root_.le_antisymm (hma n (argmax_mem harg) (le_of_mem_argmax hml harg))
            (index_of_argmax harg hml (ham _ (argmax_mem harg)))
        rw [(indexOf_inj hml (argmax_mem harg)).1 this, Option.mem_def]⟩
        -- 🎉 no goals
#align list.mem_argmax_iff List.mem_argmax_iff

theorem argmax_eq_some_iff :
    argmax f l = some m ↔
      m ∈ l ∧ (∀ a ∈ l, f a ≤ f m) ∧ ∀ a ∈ l, f m ≤ f a → l.indexOf m ≤ l.indexOf a :=
  mem_argmax_iff
#align list.argmax_eq_some_iff List.argmax_eq_some_iff

theorem mem_argmin_iff :
    m ∈ argmin f l ↔
      m ∈ l ∧ (∀ a ∈ l, f m ≤ f a) ∧ ∀ a ∈ l, f a ≤ f m → l.indexOf m ≤ l.indexOf a :=
  @mem_argmax_iff _ βᵒᵈ _ _ _ _ _
#align list.mem_argmin_iff List.mem_argmin_iff

theorem argmin_eq_some_iff :
    argmin f l = some m ↔
      m ∈ l ∧ (∀ a ∈ l, f m ≤ f a) ∧ ∀ a ∈ l, f a ≤ f m → l.indexOf m ≤ l.indexOf a :=
  mem_argmin_iff
#align list.argmin_eq_some_iff List.argmin_eq_some_iff

end LinearOrder

section MaximumMinimum

section Preorder

variable [Preorder α] [@DecidableRel α (· < ·)] {l : List α} {a m : α}

/-- `maximum l` returns a `WithBot α`, the largest element of `l` for nonempty lists, and `⊥` for
`[]`  -/
def maximum (l : List α) : WithBot α :=
  argmax id l
#align list.maximum List.maximum

/-- `minimum l` returns a `WithTop α`, the smallest element of `l` for nonempty lists, and `⊤` for
`[]`  -/
def minimum (l : List α) : WithTop α :=
  argmin id l
#align list.minimum List.minimum

@[simp]
theorem maximum_nil : maximum ([] : List α) = ⊥ :=
  rfl
#align list.maximum_nil List.maximum_nil

@[simp]
theorem minimum_nil : minimum ([] : List α) = ⊤ :=
  rfl
#align list.minimum_nil List.minimum_nil

@[simp]
theorem maximum_singleton (a : α) : maximum [a] = a :=
  rfl
#align list.maximum_singleton List.maximum_singleton

@[simp]
theorem minimum_singleton (a : α) : minimum [a] = a :=
  rfl
#align list.minimum_singleton List.minimum_singleton

theorem maximum_mem {l : List α} {m : α} : (maximum l : WithTop α) = m → m ∈ l :=
  argmax_mem
#align list.maximum_mem List.maximum_mem

theorem minimum_mem {l : List α} {m : α} : (minimum l : WithBot α) = m → m ∈ l :=
  argmin_mem
#align list.minimum_mem List.minimum_mem

@[simp]
theorem maximum_eq_none {l : List α} : l.maximum = none ↔ l = [] :=
  argmax_eq_none
#align list.maximum_eq_none List.maximum_eq_none

@[simp]
theorem minimum_eq_none {l : List α} : l.minimum = none ↔ l = [] :=
  argmin_eq_none
#align list.minimum_eq_none List.minimum_eq_none

theorem not_lt_maximum_of_mem : a ∈ l → (maximum l : WithBot α) = m → ¬m < a :=
  not_lt_of_mem_argmax
#align list.not_lt_maximum_of_mem List.not_lt_maximum_of_mem

theorem minimum_not_lt_of_mem : a ∈ l → (minimum l : WithTop α) = m → ¬a < m :=
  not_lt_of_mem_argmin
#align list.minimum_not_lt_of_mem List.minimum_not_lt_of_mem

theorem not_lt_maximum_of_mem' (ha : a ∈ l) : ¬maximum l < (a : WithBot α) := by
  cases h : l.maximum
  -- ⊢ ¬none < ↑a
  · simp_all
    -- 🎉 no goals
  · simp [WithBot.some_eq_coe, WithBot.coe_lt_coe, not_lt_maximum_of_mem ha h, not_false_iff]
    -- 🎉 no goals
#align list.not_lt_maximum_of_mem' List.not_lt_maximum_of_mem'

theorem not_lt_minimum_of_mem' (ha : a ∈ l) : ¬(a : WithTop α) < minimum l :=
  @not_lt_maximum_of_mem' αᵒᵈ _ _ _ _ ha
#align list.not_lt_minimum_of_mem' List.not_lt_minimum_of_mem'

end Preorder

section LinearOrder

variable [LinearOrder α] {l : List α} {a m : α}

theorem maximum_concat (a : α) (l : List α) : maximum (l ++ [a]) = max (maximum l) a := by
  simp only [maximum, argmax_concat, id]
  -- ⊢ Option.rec (some a) (fun val => if val < a then some a else some val) (argma …
  cases h : argmax id l
  -- ⊢ Option.rec (some a) (fun val => if val < a then some a else some val) none = …
  · exact (max_eq_right bot_le).symm
    -- 🎉 no goals
  · simp [WithBot.some_eq_coe, max_def_lt, WithBot.coe_lt_coe]
    -- 🎉 no goals
#align list.maximum_concat List.maximum_concat

theorem le_maximum_of_mem : a ∈ l → (maximum l : WithBot α) = m → a ≤ m :=
  le_of_mem_argmax
#align list.le_maximum_of_mem List.le_maximum_of_mem

theorem minimum_le_of_mem : a ∈ l → (minimum l : WithTop α) = m → m ≤ a :=
  le_of_mem_argmin
#align list.minimum_le_of_mem List.minimum_le_of_mem

theorem le_maximum_of_mem' (ha : a ∈ l) : (a : WithBot α) ≤ maximum l :=
  le_of_not_lt <| not_lt_maximum_of_mem' ha
#align list.le_maximum_of_mem' List.le_maximum_of_mem'

theorem le_minimum_of_mem' (ha : a ∈ l) : minimum l ≤ (a : WithTop α) :=
  @le_maximum_of_mem' αᵒᵈ _ _ _ ha
#align list.le_minimum_of_mem' List.le_minimum_of_mem'

theorem minimum_concat (a : α) (l : List α) : minimum (l ++ [a]) = min (minimum l) a :=
  @maximum_concat αᵒᵈ _ _ _
#align list.minimum_concat List.minimum_concat

theorem maximum_cons (a : α) (l : List α) : maximum (a :: l) = max ↑a (maximum l) :=
  List.reverseRecOn l (by simp [@max_eq_left (WithBot α) _ _ _ bot_le]) fun tl hd ih => by
                          -- 🎉 no goals
    rw [← cons_append, maximum_concat, ih, maximum_concat, max_assoc]
    -- 🎉 no goals
#align list.maximum_cons List.maximum_cons

theorem minimum_cons (a : α) (l : List α) : minimum (a :: l) = min ↑a (minimum l) :=
  @maximum_cons αᵒᵈ _ _ _
#align list.minimum_cons List.minimum_cons

theorem maximum_eq_coe_iff : maximum l = m ↔ m ∈ l ∧ ∀ a ∈ l, a ≤ m := by
  rw [maximum, ← WithBot.some_eq_coe, argmax_eq_some_iff]
  -- ⊢ (m ∈ l ∧ (∀ (a : α), a ∈ l → id a ≤ id m) ∧ ∀ (a : α), a ∈ l → id m ≤ id a → …
  simp only [id_eq, and_congr_right_iff, and_iff_left_iff_imp]
  -- ⊢ m ∈ l → (∀ (a : α), a ∈ l → a ≤ m) → ∀ (a : α), a ∈ l → m ≤ a → indexOf m l  …
  intro _ h a hal hma
  -- ⊢ indexOf m l ≤ indexOf a l
  rw [_root_.le_antisymm hma (h a hal)]
  -- 🎉 no goals
#align list.maximum_eq_coe_iff List.maximum_eq_coe_iff

theorem minimum_eq_coe_iff : minimum l = m ↔ m ∈ l ∧ ∀ a ∈ l, m ≤ a :=
  @maximum_eq_coe_iff αᵒᵈ _ _ _
#align list.minimum_eq_coe_iff List.minimum_eq_coe_iff

theorem coe_le_maximum_iff : a ≤ l.maximum ↔ ∃ b, b ∈ l ∧ a ≤ b := by
  induction l with
  | nil => simp
  | cons h t ih =>
    simp [maximum_cons, ih]

theorem minimum_le_coe_iff : l.minimum ≤ a ↔ ∃ b, b ∈ l ∧ b ≤ a :=
  coe_le_maximum_iff (α := αᵒᵈ)

theorem maximum_ne_bot_of_ne_nil (h : l ≠ []) : l.maximum ≠ ⊥ :=
  match l, h with | _ :: _, _ => by simp [maximum_cons]
                                    -- 🎉 no goals

theorem minimum_ne_top_of_ne_nil (h : l ≠ []) : l.minimum ≠ ⊤ :=
  @maximum_ne_bot_of_ne_nil αᵒᵈ _ _ h

theorem maximum_ne_bot_of_length_pos (h : 0 < l.length) : l.maximum ≠ ⊥ :=
  match l, h with | _ :: _, _ => by simp [maximum_cons]
                                    -- 🎉 no goals

theorem minimum_ne_top_of_length_pos (h : 0 < l.length) : l.minimum ≠ ⊤ :=
  maximum_ne_bot_of_length_pos (α := αᵒᵈ) h

/-- The maximum value in a non-empty `List`. -/
def maximum_of_length_pos (h : 0 < l.length) : α :=
  WithBot.unbot l.maximum (maximum_ne_bot_of_length_pos h)

/-- The minimum value in a non-empty `List`. -/
def minimum_of_length_pos (h : 0 < l.length) : α :=
  maximum_of_length_pos (α := αᵒᵈ) h

@[simp]
lemma coe_maximum_of_length_pos (h : 0 < l.length) :
    (l.maximum_of_length_pos h : α) = l.maximum :=
  WithBot.coe_unbot _ _

@[simp]
lemma coe_minimum_of_length_pos (h : 0 < l.length) :
    (l.minimum_of_length_pos h : α) = l.minimum :=
  WithTop.coe_untop _ _

@[simp]
theorem le_maximum_of_length_pos_iff (h : 0 < l.length) :
    b ≤ maximum_of_length_pos h ↔ b ≤ l.maximum :=
  WithBot.le_unbot_iff _

@[simp]
theorem minimum_of_length_pos_le_iff (h : 0 < l.length) :
    minimum_of_length_pos h ≤ b ↔ l.minimum ≤ b :=
  le_maximum_of_length_pos_iff (α := αᵒᵈ) h

theorem le_maximum_of_length_pos_of_mem (h : a ∈ l) (w : 0 < l.length) :
     a ≤ l.maximum_of_length_pos w := by
  simp [le_maximum_of_length_pos_iff]
  -- ⊢ ↑a ≤ maximum l
  exact le_maximum_of_mem' h
  -- 🎉 no goals

theorem minimum_of_length_pos_le_of_mem (h : a ∈ l) (w : 0 < l.length) :
     l.minimum_of_length_pos w ≤ a :=
  le_maximum_of_length_pos_of_mem (α := αᵒᵈ) h w

theorem getElem_le_maximum_of_length_pos (w : i < l.length) (h := (Nat.zero_lt_of_lt w)) :
    l[i] ≤ l.maximum_of_length_pos h := by
  apply le_maximum_of_length_pos_of_mem
  -- ⊢ l[i] ∈ l
  exact get_mem l i w
  -- 🎉 no goals

theorem minimum_of_length_pos_le_getElem (w : i < l.length) (h := (Nat.zero_lt_of_lt w)) :
    l.minimum_of_length_pos h ≤ l[i] :=
  getElem_le_maximum_of_length_pos (α := αᵒᵈ) w

end LinearOrder

end MaximumMinimum

section Fold

variable [LinearOrder α]

section OrderBot

variable [OrderBot α] {l : List α}

@[simp]
theorem foldr_max_of_ne_nil (h : l ≠ []) : ↑(l.foldr max ⊥) = l.maximum := by
  induction' l with hd tl IH
  -- ⊢ ↑(foldr max ⊥ []) = maximum []
  · contradiction
    -- 🎉 no goals
  · rw [maximum_cons, foldr, WithBot.coe_max]
    -- ⊢ max ↑hd ↑(foldr max ⊥ tl) = max (↑hd) (maximum tl)
    by_cases h : tl = []
    -- ⊢ max ↑hd ↑(foldr max ⊥ tl) = max (↑hd) (maximum tl)
    · simp [h]
      -- 🎉 no goals
    · simp [IH h]
      -- 🎉 no goals
#align list.foldr_max_of_ne_nil List.foldr_max_of_ne_nil

theorem max_le_of_forall_le (l : List α) (a : α) (h : ∀ x ∈ l, x ≤ a) : l.foldr max ⊥ ≤ a := by
  induction' l with y l IH
  -- ⊢ foldr max ⊥ [] ≤ a
  · simp
    -- 🎉 no goals
  · simpa [h y (mem_cons_self _ _)] using IH fun x hx => h x <| mem_cons_of_mem _ hx
    -- 🎉 no goals
#align list.max_le_of_forall_le List.max_le_of_forall_le

theorem le_max_of_le {l : List α} {a x : α} (hx : x ∈ l) (h : a ≤ x) : a ≤ l.foldr max ⊥ := by
  induction' l with y l IH
  -- ⊢ a ≤ foldr max ⊥ []
  · exact absurd hx (not_mem_nil _)
    -- 🎉 no goals
  · obtain hl | hl := hx
    -- ⊢ a ≤ foldr max ⊥ (x :: l)
    simp only [foldr, foldr_cons]
    -- ⊢ a ≤ max x (foldr max ⊥ l)
    · exact le_max_of_le_left h
      -- 🎉 no goals
    · exact le_max_of_le_right (IH (by assumption))
      -- 🎉 no goals
#align list.le_max_of_le List.le_max_of_le

end OrderBot

section OrderTop

variable [OrderTop α] {l : List α}

@[simp]
theorem foldr_min_of_ne_nil (h : l ≠ []) : ↑(l.foldr min ⊤) = l.minimum :=
  @foldr_max_of_ne_nil αᵒᵈ _ _ _ h
#align list.foldr_min_of_ne_nil List.foldr_min_of_ne_nil

theorem le_min_of_forall_le (l : List α) (a : α) (h : ∀ x ∈ l, a ≤ x) : a ≤ l.foldr min ⊤ :=
  @max_le_of_forall_le αᵒᵈ _ _ _ _ h
#align list.le_min_of_forall_le List.le_min_of_forall_le

theorem min_le_of_le (l : List α) (a : α) {x : α} (hx : x ∈ l) (h : x ≤ a) : l.foldr min ⊤ ≤ a :=
  @le_max_of_le αᵒᵈ _ _ _ _ _ hx h
#align list.min_le_of_le List.min_le_of_le

end OrderTop

end Fold

end List
