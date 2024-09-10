/-
Copyright (c) 2020 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro
-/
import Mathlib.Data.Set.Basic

/-!
# Well-founded relations

A relation is well-founded if it can be used for induction: for each `x`, `(∀ y, r y x → P y) → P x`
implies `P x`. Well-founded relations can be used for induction and recursion, including
construction of fixed points in the space of dependent functions `Π x : α , β x`.

The predicate `WellFounded` is defined in the core library. In this file we prove some extra lemmas
and provide a few new definitions: `WellFounded.min`, `WellFounded.sup`, and `WellFounded.succ`,
and an induction principle `WellFounded.induction_bot`.
-/


variable {α β γ : Type*}

namespace WellFounded

variable {r r' : α → α → Prop}

protected theorem isAsymm (h : WellFounded r) : IsAsymm α r := ⟨h.asymmetric⟩

protected theorem isIrrefl (h : WellFounded r) : IsIrrefl α r := @IsAsymm.isIrrefl α r h.isAsymm

instance [WellFoundedRelation α] : IsAsymm α WellFoundedRelation.rel :=
  WellFoundedRelation.wf.isAsymm

instance : IsIrrefl α WellFoundedRelation.rel := IsAsymm.isIrrefl

theorem mono (hr : WellFounded r) (h : ∀ a b, r' a b → r a b) : WellFounded r' :=
  Subrelation.wf (h _ _) hr

theorem onFun {α β : Sort*} {r : β → β → Prop} {f : α → β} :
    WellFounded r → WellFounded (r on f) :=
  InvImage.wf _

/-- If `r` is a well-founded relation, then any nonempty set has a minimal element
with respect to `r`. -/
theorem has_min {α} {r : α → α → Prop} (H : WellFounded r) (s : Set α) :
    s.Nonempty → ∃ a ∈ s, ∀ x ∈ s, ¬r x a
  | ⟨a, ha⟩ => show ∃ b ∈ s, ∀ x ∈ s, ¬r x b from
    Acc.recOn (H.apply a) (fun x _ IH =>
        not_imp_not.1 fun hne hx => hne <| ⟨x, hx, fun y hy hyx => hne <| IH y hyx hy⟩)
      ha

/-- A minimal element of a nonempty set in a well-founded order.

If you're working with a nonempty linear order, consider defining a
`ConditionallyCompleteLinearOrderBot` instance via
`WellFounded.conditionallyCompleteLinearOrderWithBot` and using `Inf` instead. -/
noncomputable def min {r : α → α → Prop} (H : WellFounded r) (s : Set α) (h : s.Nonempty) : α :=
  Classical.choose (H.has_min s h)

theorem min_mem {r : α → α → Prop} (H : WellFounded r) (s : Set α) (h : s.Nonempty) :
    H.min s h ∈ s :=
  let ⟨h, _⟩ := Classical.choose_spec (H.has_min s h)
  h

theorem not_lt_min {r : α → α → Prop} (H : WellFounded r) (s : Set α) (h : s.Nonempty) {x}
    (hx : x ∈ s) : ¬r x (H.min s h) :=
  let ⟨_, h'⟩ := Classical.choose_spec (H.has_min s h)
  h' _ hx

theorem wellFounded_iff_has_min {r : α → α → Prop} :
    WellFounded r ↔ ∀ s : Set α, s.Nonempty → ∃ m ∈ s, ∀ x ∈ s, ¬r x m := by
  refine ⟨fun h => h.has_min, fun h => ⟨fun x => ?_⟩⟩
  by_contra hx
  obtain ⟨m, hm, hm'⟩ := h {x | ¬Acc r x} ⟨x, hx⟩
  refine hm ⟨_, fun y hy => ?_⟩
  by_contra hy'
  exact hm' y hy' hy

open Set

/-- The supremum of a bounded, well-founded order -/
protected noncomputable def sup {r : α → α → Prop} (wf : WellFounded r) (s : Set α)
    (h : Bounded r s) : α :=
  wf.min { x | ∀ a ∈ s, r a x } h

protected theorem lt_sup {r : α → α → Prop} (wf : WellFounded r) {s : Set α} (h : Bounded r s) {x}
    (hx : x ∈ s) : r x (wf.sup s h) :=
  min_mem wf { x | ∀ a ∈ s, r a x } h x hx

section

open Classical in
/-- A successor of an element `x` in a well-founded order is a minimal element `y` such that
`x < y` if one exists. Otherwise it is `x` itself. -/
protected noncomputable def succ {r : α → α → Prop} (wf : WellFounded r) (x : α) : α :=
  if h : ∃ y, r x y then wf.min { y | r x y } h else x

protected theorem lt_succ {r : α → α → Prop} (wf : WellFounded r) {x : α} (h : ∃ y, r x y) :
    r x (wf.succ x) := by
  rw [WellFounded.succ, dif_pos h]
  apply min_mem

end

protected theorem lt_succ_iff {r : α → α → Prop} [wo : IsWellOrder α r] {x : α} (h : ∃ y, r x y)
    (y : α) : r y (wo.wf.succ x) ↔ r y x ∨ y = x := by
  constructor
  · intro h'
    have : ¬r x y := by
      intro hy
      rw [WellFounded.succ, dif_pos] at h'
      exact wo.wf.not_lt_min _ h hy h'
    rcases trichotomous_of r x y with (hy | hy | hy)
    · exfalso
      exact this hy
    · right
      exact hy.symm
    left
    exact hy
  rintro (hy | rfl); (· exact _root_.trans hy (wo.wf.lt_succ h)); exact wo.wf.lt_succ h

section LinearOrder

variable [LinearOrder β] [PartialOrder γ]

theorem min_le (h : WellFounded ((· < ·) : β → β → Prop)) {x : β} {s : Set β} (hx : x ∈ s)
    (hne : s.Nonempty := ⟨x, hx⟩) : h.min s hne ≤ x :=
  not_lt.1 <| h.not_lt_min _ _ hx

private theorem eq_strictMono_iff_eq_range_aux {f g : β → γ} (hf : StrictMono f)
    (hg : StrictMono g) (hfg : Set.range f = Set.range g) {b : β} (H : ∀ a < b, f a = g a) :
    f b ≤ g b := by
  obtain ⟨c, hc⟩ : g b ∈ Set.range f := by
    rw [hfg]
    exact Set.mem_range_self b
  rcases lt_or_le c b with hcb | hbc
  · rw [H c hcb] at hc
    rw [hg.injective hc] at hcb
    exact hcb.false.elim
  · rw [← hc]
    exact hf.monotone hbc

theorem eq_strictMono_iff_eq_range (h : WellFounded ((· < ·) : β → β → Prop))
    {f g : β → γ} (hf : StrictMono f) (hg : StrictMono g) :
    Set.range f = Set.range g ↔ f = g :=
  ⟨fun hfg => by
    funext a
    apply h.induction a
    exact fun b H =>
      le_antisymm (eq_strictMono_iff_eq_range_aux hf hg hfg H)
        (eq_strictMono_iff_eq_range_aux hg hf hfg.symm fun a hab => (H a hab).symm),
    congr_arg _⟩

theorem self_le_of_strictMono (h : WellFounded ((· < ·) : β → β → Prop))
    {f : β → β} (hf : StrictMono f) : ∀ n, n ≤ f n := by
  by_contra! h₁
  have h₂ := h.min_mem _ h₁
  exact h.not_lt_min _ h₁ (hf h₂) h₂

end LinearOrder

end WellFounded

namespace Function

variable (f : α → β)

section LT

variable [LT β] (h : WellFounded ((· < ·) : β → β → Prop))

/-- Given a function `f : α → β` where `β` carries a well-founded `<`, this is an element of `α`
whose image under `f` is minimal in the sense of `Function.not_lt_argmin`. -/
noncomputable def argmin [Nonempty α] : α :=
  WellFounded.min (InvImage.wf f h) Set.univ Set.univ_nonempty

theorem not_lt_argmin [Nonempty α] (a : α) : ¬f a < f (argmin f h) :=
  WellFounded.not_lt_min (InvImage.wf f h) _ _ (Set.mem_univ a)

/-- Given a function `f : α → β` where `β` carries a well-founded `<`, and a non-empty subset `s`
of `α`, this is an element of `s` whose image under `f` is minimal in the sense of
`Function.not_lt_argminOn`. -/
noncomputable def argminOn (s : Set α) (hs : s.Nonempty) : α :=
  WellFounded.min (InvImage.wf f h) s hs

@[simp]
theorem argminOn_mem (s : Set α) (hs : s.Nonempty) : argminOn f h s hs ∈ s :=
  WellFounded.min_mem _ _ _

-- Porting note (#11119): @[simp] removed as it will never apply
theorem not_lt_argminOn (s : Set α) {a : α} (ha : a ∈ s)
    (hs : s.Nonempty := Set.nonempty_of_mem ha) : ¬f a < f (argminOn f h s hs) :=
  WellFounded.not_lt_min (InvImage.wf f h) s hs ha

end LT

section LinearOrder

variable [LinearOrder β] (h : WellFounded ((· < ·) : β → β → Prop))

-- Porting note (#11119): @[simp] removed as it will never apply
theorem argmin_le (a : α) [Nonempty α] : f (argmin f h) ≤ f a :=
  not_lt.mp <| not_lt_argmin f h a

-- Porting note (#11119): @[simp] removed as it will never apply
theorem argminOn_le (s : Set α) {a : α} (ha : a ∈ s) (hs : s.Nonempty := Set.nonempty_of_mem ha) :
    f (argminOn f h s hs) ≤ f a :=
  not_lt.mp <| not_lt_argminOn f h s ha hs

end LinearOrder

end Function

section Induction

/-- Let `r` be a relation on `α`, let `f : α → β` be a function, let `C : β → Prop`, and
let `bot : α`. This induction principle shows that `C (f bot)` holds, given that
* some `a` that is accessible by `r` satisfies `C (f a)`, and
* for each `b` such that `f b ≠ f bot` and `C (f b)` holds, there is `c`
  satisfying `r c b` and `C (f c)`. -/
theorem Acc.induction_bot' {α β} {r : α → α → Prop} {a bot : α} (ha : Acc r a) {C : β → Prop}
    {f : α → β} (ih : ∀ b, f b ≠ f bot → C (f b) → ∃ c, r c b ∧ C (f c)) : C (f a) → C (f bot) :=
  (@Acc.recOn _ _ (fun x _ => C (f x) → C (f bot)) _ ha) fun x _ ih' hC =>
    (eq_or_ne (f x) (f bot)).elim (fun h => h ▸ hC) (fun h =>
      let ⟨y, hy₁, hy₂⟩ := ih x h hC
      ih' y hy₁ hy₂)

/-- Let `r` be a relation on `α`, let `C : α → Prop` and let `bot : α`.
This induction principle shows that `C bot` holds, given that
* some `a` that is accessible by `r` satisfies `C a`, and
* for each `b ≠ bot` such that `C b` holds, there is `c` satisfying `r c b` and `C c`. -/
theorem Acc.induction_bot {α} {r : α → α → Prop} {a bot : α} (ha : Acc r a) {C : α → Prop}
    (ih : ∀ b, b ≠ bot → C b → ∃ c, r c b ∧ C c) : C a → C bot :=
  ha.induction_bot' ih

/-- Let `r` be a well-founded relation on `α`, let `f : α → β` be a function,
let `C : β → Prop`, and let `bot : α`.
This induction principle shows that `C (f bot)` holds, given that
* some `a` satisfies `C (f a)`, and
* for each `b` such that `f b ≠ f bot` and `C (f b)` holds, there is `c`
  satisfying `r c b` and `C (f c)`. -/
theorem WellFounded.induction_bot' {α β} {r : α → α → Prop} (hwf : WellFounded r) {a bot : α}
    {C : β → Prop} {f : α → β} (ih : ∀ b, f b ≠ f bot → C (f b) → ∃ c, r c b ∧ C (f c)) :
    C (f a) → C (f bot) :=
  (hwf.apply a).induction_bot' ih

/-- Let `r` be a well-founded relation on `α`, let `C : α → Prop`, and let `bot : α`.
This induction principle shows that `C bot` holds, given that
* some `a` satisfies `C a`, and
* for each `b` that satisfies `C b`, there is `c` satisfying `r c b` and `C c`.

The naming is inspired by the fact that when `r` is transitive, it follows that `bot` is
the smallest element w.r.t. `r` that satisfies `C`. -/
theorem WellFounded.induction_bot {α} {r : α → α → Prop} (hwf : WellFounded r) {a bot : α}
    {C : α → Prop} (ih : ∀ b, b ≠ bot → C b → ∃ c, r c b ∧ C c) : C a → C bot :=
  hwf.induction_bot' ih

end Induction

section WellFoundedLT

variable [Preorder α] [Preorder β] {f : α → β}

theorem StrictMono.wellFoundedLT [WellFoundedLT β] (hf : StrictMono f) : WellFoundedLT α where
  wf := WellFounded.wellFounded_iff_has_min.2 fun s hne ↦ by
    have hs' : (f '' s).Nonempty := ⟨f hne.some, _, hne.some_mem, rfl⟩
    obtain ⟨x, hx, hex⟩ := WellFounded.min_mem wellFounded_lt (f '' s) hs'
    refine ⟨x, hx, fun y hy hlt ↦ ?_⟩
    apply WellFounded.not_lt_min wellFounded_lt (s.image f) hs' (Set.mem_image_of_mem _ hy)
    rw [← hex]
    exact hf hlt

theorem StrictAnti.wellFoundedLT [WellFoundedGT β] (hf : StrictAnti f) : WellFoundedLT α :=
  StrictMono.wellFoundedLT (β := βᵒᵈ) hf

theorem StrictMono.wellFoundedGT [WellFoundedGT β] (hf : StrictMono f) : WellFoundedGT α :=
  StrictMono.wellFoundedLT (α := αᵒᵈ) (β := βᵒᵈ) (fun _ _ h ↦ hf h)

theorem StrictAnti.wellFoundedGT [WellFoundedLT β] (hf : StrictAnti f) : WellFoundedGT α :=
  StrictMono.wellFoundedLT (α := αᵒᵈ) (fun _ _ h ↦ hf h)

end WellFoundedLT

/-- A nonempty linear order with well-founded `<` has a bottom element. -/
noncomputable def WellFoundedLT.toOrderBot {α} [LinearOrder α] [Nonempty α] [h : WellFoundedLT α] :
    OrderBot α where
  bot := h.wf.min _ Set.univ_nonempty
  bot_le a := h.wf.min_le (Set.mem_univ a)

/-- A nonempty linear order with well-founded `>` has a top element. -/
noncomputable def WellFoundedGT.toOrderTop {α} [LinearOrder α] [Nonempty α] [WellFoundedGT α] :
    OrderTop α :=
  have := WellFoundedLT.toOrderBot (α := αᵒᵈ)
  inferInstanceAs (OrderTop αᵒᵈᵒᵈ)
