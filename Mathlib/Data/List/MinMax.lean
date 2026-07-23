/-
Copyright (c) 2019 Minchao Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Minchao Wu, Chris Hughes, Mantas Bakšys
-/
module

public import Mathlib.Data.List.Basic
public import Mathlib.Order.BoundedOrder.Lattice
public import Mathlib.Data.List.Induction
public import Mathlib.Order.MinMax
public import Mathlib.Order.WithBot

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

@[expose] public section

namespace List

variable {α β : Type*}

section ArgAux

variable (r : α → α → Prop) [DecidableRel r] {l : List α} {o : Option α} {a : α}

/-- Auxiliary definition for `argmax` and `argmin`. -/
def argAux (a : Option α) (b : α) : Option α :=
  Option.casesOn a (some b) fun c => if r b c then some b else some c

@[simp]
theorem foldl_argAux_eq_none : l.foldl (argAux r) o = none ↔ l = [] ∧ o = none :=
  List.reverseRecOn l (by simp) fun tl hd => by
    simp only [foldl_append, foldl_cons, argAux, foldl_nil, append_eq_nil_iff]
    cases foldl (argAux r) o tl
    · simp
    · simp only
      split_ifs <;> simp

private theorem foldl_argAux_mem (l) : ∀ a m : α, m ∈ foldl (argAux r) (some a) l → m ∈ a :: l :=
  List.reverseRecOn l (by simp [eq_comm]) <| by
    intro _ _ _ _
    simp only [foldl_append, foldl_cons, foldl_nil, argAux]
    cases _ : foldl _ _ _ <;> grind

@[simp]
theorem argAux_self (hr₀ : Std.Irrefl r) (a : α) : argAux r (some a) a = a :=
  if_neg <| hr₀.irrefl _

theorem not_of_mem_foldl_argAux (hr₀ : Std.Irrefl r) (hr₁ : IsTrans α r) :
    ∀ {a m : α} {o : Option α}, a ∈ l → m ∈ foldl (argAux r) o l → ¬r a m := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton tl a ih => ?_
  intro b m o hb ho
  rw [foldl_append, foldl_cons, foldl_nil, argAux] at ho
  rcases hf : foldl (argAux r) o tl with - | c
  · rw [hf] at ho
    rw [foldl_argAux_eq_none] at hf
    simp_all [hf.1, hf.2, hr₀.irrefl _]
  rw [hf, Option.mem_def] at ho
  grind +splitIndPred

end ArgAux

section Preorder

variable [Preorder β] [DecidableLT β] {f : α → β} {l : List α} {a m : α}

/-- `argmax f l` returns `some a`, where `f a` is maximal among the elements of `l`, in the sense
that there is no `b ∈ l` with `f a < f b`. If `a`, `b` are such that `f a = f b`, it returns
whichever of `a` or `b` comes first in the list. `argmax f [] = none`. -/
@[to_dual
/-- `argmin f l` returns `some a`, where `f a` is minimal among the elements of `l`, in the sense
that there is no `b ∈ l` with `f b < f a`. If `a`, `b` are such that `f a = f b`, it returns
whichever of `a` or `b` comes first in the list. `argmin f [] = none`. -/]
def argmax (f : α → β) (l : List α) : Option α :=
  l.foldl (argAux fun b c => f c < f b) none

@[to_dual (attr := simp)]
theorem argmax_nil (f : α → β) : argmax f [] = none :=
  rfl

@[to_dual (attr := simp)]
theorem argmax_singleton {f : α → β} {a : α} : argmax f [a] = a :=
  rfl

@[to_dual]
theorem not_lt_of_mem_argmax : a ∈ l → m ∈ argmax f l → ¬f m < f a :=
  not_of_mem_foldl_argAux _ ⟨fun x h => lt_irrefl (f x) h⟩
    ⟨fun _ _ z hxy hyz => lt_trans (a := f z) hyz hxy⟩

@[to_dual]
theorem argmax_concat (f : α → β) (a : α) (l : List α) :
    argmax f (l ++ [a]) =
      Option.casesOn (argmax f l) (some a) fun c => if f c < f a then some a else some c := by
  rw [argmax, argmax]; simp [argAux]

@[to_dual]
theorem argmax_mem : ∀ {l : List α} {m : α}, m ∈ argmax f l → m ∈ l
  | [], m => by simp
  | hd :: tl, m => by simpa [argmax, argAux] using foldl_argAux_mem _ tl hd m

@[to_dual (attr := simp)]
theorem argmax_eq_none : l.argmax f = none ↔ l = [] := by simp [argmax]

end Preorder

section LinearOrder

variable [LinearOrder β] {f : α → β} {l : List α} {a m : α}

@[to_dual]
theorem le_of_mem_argmax : a ∈ l → m ∈ argmax f l → f a ≤ f m := fun ha hm =>
  le_of_not_gt <| not_lt_of_mem_argmax ha hm

@[to_dual]
theorem argmax_cons (f : α → β) (a : α) (l : List α) :
    argmax f (a :: l) =
      Option.casesOn (argmax f l) (some a) fun c => if f a < f c then some c else some a :=
  List.reverseRecOn l rfl fun hd tl ih => by
    rw [← cons_append, argmax_concat, ih, argmax_concat]
    rcases h : argmax f hd with - | m
    · simp
    dsimp
    rw [← apply_ite, ← apply_ite]
    grind -abstractProof -- Without `-abstractProof`, `to_dual` gives an error.

variable [DecidableEq α]

@[to_dual]
theorem index_of_argmax :
    ∀ {l : List α} {m : α}, m ∈ argmax f l → ∀ {a}, a ∈ l → f m ≤ f a → l.idxOf m ≤ l.idxOf a
  | [], m, _, _, _, _ => by simp
  | hd :: tl, m, hm, a, ha, ham => by
    simp only [idxOf_cons, argmax_cons, Option.mem_def] at hm ⊢
    cases h : argmax f tl
    · rw [h] at hm
      simp_all
    rw [h] at hm
    dsimp only at hm
    simp only [cond_eq_ite, beq_iff_eq]
    obtain ha | ha := ha <;> split_ifs at hm <;> injection hm with hm <;> subst hm
    · cases not_le_of_gt ‹_› ‹_›
    · rw [if_pos rfl]
    · rw [if_neg, if_neg]
      · exact Nat.succ_le_succ (index_of_argmax h (by assumption) ham)
      · exact ne_of_apply_ne f (lt_of_lt_of_le ‹_› ‹_›).ne
      · exact ne_of_apply_ne _ ‹f hd < f _›.ne
    · rw [if_pos rfl]
      exact Nat.zero_le _

@[to_dual]
theorem mem_argmax_iff :
    m ∈ argmax f l ↔
      m ∈ l ∧ (∀ a ∈ l, f a ≤ f m) ∧ ∀ a ∈ l, f m ≤ f a → l.idxOf m ≤ l.idxOf a :=
  ⟨fun hm => ⟨argmax_mem hm, fun _ ha => le_of_mem_argmax ha hm, fun _ => index_of_argmax hm⟩,
    by
      rintro ⟨hml, ham, hma⟩
      rcases harg : argmax f l with - | n
      · simp_all
      · have :=
          Nat.le_antisymm (hma n (argmax_mem harg) (le_of_mem_argmax hml harg))
            (index_of_argmax harg hml (ham _ (argmax_mem harg)))
        rw [(idxOf_inj hml).1 this, Option.mem_def]⟩

@[to_dual]
theorem argmax_eq_some_iff :
    argmax f l = some m ↔
      m ∈ l ∧ (∀ a ∈ l, f a ≤ f m) ∧ ∀ a ∈ l, f m ≤ f a → l.idxOf m ≤ l.idxOf a :=
  mem_argmax_iff

end LinearOrder

section MaximumMinimum

section Preorder

variable [Preorder α] [DecidableLT α] {l : List α} {a m : α}

/-- `maximum l` returns a `WithBot α`, the largest element of `l` for nonempty lists, and `⊥` for
`[]` -/
@[to_dual
/-- `minimum l` returns a `WithTop α`, the smallest element of `l` for nonempty lists, and `⊤` for
`[]` -/]
def maximum (l : List α) : WithBot α :=
  argmax id l

@[to_dual (attr := simp)]
theorem maximum_nil : maximum ([] : List α) = ⊥ :=
  rfl

@[to_dual (attr := simp)]
theorem maximum_singleton (a : α) : maximum [a] = a :=
  rfl

@[to_dual]
theorem maximum_mem {l : List α} {m : α} : (maximum l : WithTop α) = m → m ∈ l :=
  argmax_mem

@[to_dual (attr := simp)]
theorem maximum_eq_bot {l : List α} : l.maximum = ⊥ ↔ l = [] :=
  argmax_eq_none

@[to_dual not_lt_minimum_of_mem]
theorem not_maximum_lt_of_mem : a ∈ l → (maximum l : WithBot α) = m → ¬m < a :=
  not_lt_of_mem_argmax

@[to_dual not_lt_minimum_of_mem']
theorem not_maximum_lt_of_mem' (ha : a ∈ l) : ¬maximum l < (a : WithBot α) := by
  cases h : l.maximum <;> simp_all [not_maximum_lt_of_mem ha]

end Preorder

section LinearOrder

variable [LinearOrder α] {l : List α} {a m : α}

set_option backward.isDefEq.respectTransparency false in
@[to_dual]
theorem maximum_concat (a : α) (l : List α) : maximum (l ++ [a]) = max (maximum l) a := by
  simp only [maximum, argmax_concat, id]
  cases argmax id l
  · exact (max_eq_right bot_le).symm
  · simp [WithBot.some_eq_coe, max_def_lt, WithBot.coe_lt_coe]

@[to_dual minimum_le_of_mem]
theorem le_maximum_of_mem : a ∈ l → (maximum l : WithBot α) = m → a ≤ m :=
  le_of_mem_argmax

@[to_dual minimum_le_of_mem']
theorem le_maximum_of_mem' (ha : a ∈ l) : (a : WithBot α) ≤ maximum l :=
  le_of_not_gt <| not_maximum_lt_of_mem' ha

@[to_dual]
theorem maximum_cons (a : α) (l : List α) : maximum (a :: l) = max ↑a (maximum l) :=
  List.reverseRecOn l (by simp) fun tl hd ih => by
    rw [← cons_append, maximum_concat, ih, maximum_concat, max_assoc]

@[to_dual]
lemma maximum_append (l₁ l₂ : List α) : (l₁ ++ l₂).maximum = max l₁.maximum l₂.maximum := by
  induction l₁ with
  | nil => simp
  | cons _ _ ih => rw [maximum_cons, cons_append, maximum_cons, ih, ← max_assoc]

@[to_dual le_minimum_of_forall_le]
theorem maximum_le_of_forall_le {b : WithBot α} (h : ∀ a ∈ l, a ≤ b) : l.maximum ≤ b := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [maximum_cons, max_le_iff]
    exact ⟨h a (by simp), ih fun a w => h a (mem_cons.mpr (Or.inr w))⟩

@[to_dual minimum_anti]
theorem maximum_mono {l₁ l₂ : List α} (h : l₁ ⊆ l₂) : l₁.maximum ≤ l₂.maximum :=
  maximum_le_of_forall_le fun _ ↦ (le_maximum_of_mem' <| h ·)

set_option backward.isDefEq.respectTransparency false in
@[to_dual]
theorem maximum_eq_coe_iff : maximum l = m ↔ m ∈ l ∧ ∀ a ∈ l, a ≤ m := by
  rw [maximum, ← WithBot.some_eq_coe, argmax_eq_some_iff]
  simp only [id_eq, and_congr_right_iff, and_iff_left_iff_imp]
  intro _ h a hal hma
  rw [_root_.le_antisymm hma (h a hal)]

@[to_dual minimum_le_coe_iff]
theorem coe_le_maximum_iff : a ≤ l.maximum ↔ ∃ b, b ∈ l ∧ a ≤ b := by
  induction l <;> simp [maximum_cons, *]

@[to_dual]
theorem maximum_ne_bot_of_ne_nil (h : l ≠ []) : l.maximum ≠ ⊥ :=
  match l, h with | _ :: _, _ => by simp [maximum_cons]

@[to_dual]
theorem maximum_ne_bot_of_length_pos (h : 0 < l.length) : l.maximum ≠ ⊥ :=
  match l, h with | _ :: _, _ => by simp [maximum_cons]

/-- The maximum value in a non-empty `List`. -/
@[to_dual /-- The minimum value in a non-empty `List`. -/]
def maximum_of_length_pos (h : 0 < l.length) : α :=
  WithBot.unbot l.maximum (maximum_ne_bot_of_length_pos h)

@[to_dual (attr := simp)]
lemma coe_maximum_of_length_pos (h : 0 < l.length) :
    (l.maximum_of_length_pos h : α) = l.maximum :=
  WithBot.coe_unbot _ _

@[to_dual (attr := simp) minimum_of_length_pos_le_iff]
theorem le_maximum_of_length_pos_iff {b : α} (h : 0 < l.length) :
    b ≤ maximum_of_length_pos h ↔ b ≤ l.maximum :=
  WithBot.le_unbot_iff _

@[to_dual]
theorem maximum_of_length_pos_mem (h : 0 < l.length) :
    maximum_of_length_pos h ∈ l := by
  apply maximum_mem
  simp only [coe_maximum_of_length_pos]

@[to_dual minimum_of_length_pos_le_of_mem]
theorem le_maximum_of_length_pos_of_mem (h : a ∈ l) (w : 0 < l.length) :
    a ≤ l.maximum_of_length_pos w := by
  simp only [le_maximum_of_length_pos_iff]
  exact le_maximum_of_mem' h

@[to_dual minimum_of_length_pos_le_getElem]
theorem getElem_le_maximum_of_length_pos {i : ℕ} (w : i < l.length) (h := (Nat.zero_lt_of_lt w)) :
    l[i] ≤ l.maximum_of_length_pos h := by
  apply le_maximum_of_length_pos_of_mem
  exact getElem_mem _

@[to_dual]
theorem Perm.maximum_eq {l l' : List α} (h : l ~ l') :
    l.maximum = l'.maximum := by
  induction h with grind [maximum_cons]


@[to_dual]
lemma getD_max?_eq_unbotD_maximum (l : List α) (d : α) : l.max?.getD d = l.maximum.unbotD d := by
  cases hy : l.maximum with
  | bot => simp [List.maximum_eq_bot.mp hy]
  | coe y =>
    rw [List.maximum_eq_coe_iff] at hy
    simp only [WithBot.unbotD_coe]
    cases hz : l.max? with
    | none => simp [List.max?_eq_none_iff.mp hz] at hy
    | some z =>
      have : Std.Antisymm (α := α) (· ≤ ·) := ⟨fun _ _ => _root_.le_antisymm⟩
      rw [List.max?_eq_some_iff] at hz
      · rw [Option.getD_some]
        exact _root_.le_antisymm (hy.right _ hz.left) (hz.right _ hy.left)

end LinearOrder

end MaximumMinimum

section Fold

variable [LinearOrder α]

section OrderBot

variable [OrderBot α] {l : List α}

@[to_dual (attr := simp)]
theorem foldr_max_of_ne_nil (h : l ≠ []) : ↑(l.foldr max ⊥) = l.maximum := by
  induction l with
  | nil => contradiction
  | cons hd tl IH =>
    rw [maximum_cons, foldr, WithBot.coe_max]
    by_cases h : tl = []
    · simp [h]
    · simp [IH h]

@[to_dual]
theorem max_le_of_forall_le (l : List α) (a : α) (h : ∀ x ∈ l, x ≤ a) : l.foldr max ⊥ ≤ a := by
  induction l with
  | nil => simp
  | cons y l IH => simpa [h y mem_cons_self] using IH fun x hx => h x <| mem_cons_of_mem _ hx

@[to_dual]
theorem le_max_of_le {l : List α} {a x : α} (hx : x ∈ l) (h : a ≤ x) : a ≤ l.foldr max ⊥ := by
  induction l with
  | nil => exact absurd hx not_mem_nil
  | cons y l IH =>
    obtain hl | hl := hx
    · simp only [foldr]
      exact le_max_of_le_left h
    · exact le_max_of_le_right (IH (by assumption))

end OrderBot

/-- If `a ≤ x` for some `x` in the list `l`, and `b : α`, then `a ≤ l.foldr max b`. -/
@[to_dual min_le_of_le']
theorem le_max_of_le' {l : List α} {a x : α} (b : α) (hx : x ∈ l) (h : a ≤ x) :
    a ≤ l.foldr max b := by
  induction l with
  | nil => exact absurd hx List.not_mem_nil
  | cons y l IH =>
    simp only [List.foldr]
    obtain rfl | hl := mem_cons.mp hx
    · exact le_max_of_le_left h
    · exact le_max_of_le_right (IH hl)

end Fold

end List
