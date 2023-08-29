/-
Copyright (c) 2020 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro
-/
import Mathlib.Data.Set.Image

#align_import order.well_founded from "leanprover-community/mathlib"@"2c84c2c5496117349007d97104e7bbb471381592"

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

#align well_founded_relation.r WellFoundedRelation.rel

protected theorem isAsymm (h : WellFounded r) : IsAsymm α r := ⟨h.asymmetric⟩
#align well_founded.is_asymm WellFounded.isAsymm

protected theorem isIrrefl (h : WellFounded r) : IsIrrefl α r := @IsAsymm.isIrrefl α r h.isAsymm
#align well_founded.is_irrefl WellFounded.isIrrefl

instance [WellFoundedRelation α] : IsAsymm α WellFoundedRelation.rel :=
  WellFoundedRelation.wf.isAsymm

instance : IsIrrefl α WellFoundedRelation.rel := IsAsymm.isIrrefl

theorem mono (hr : WellFounded r) (h : ∀ a b, r' a b → r a b) : WellFounded r' :=
  Subrelation.wf (h _ _) hr
#align well_founded.mono WellFounded.mono

theorem onFun {α β : Sort*} {r : β → β → Prop} {f : α → β} :
    WellFounded r → WellFounded (r on f) :=
  InvImage.wf _
#align well_founded.on_fun WellFounded.onFun

/-- If `r` is a well-founded relation, then any nonempty set has a minimal element
with respect to `r`. -/
theorem has_min {α} {r : α → α → Prop} (H : WellFounded r) (s : Set α) :
    s.Nonempty → ∃ a ∈ s, ∀ x ∈ s, ¬r x a
  | ⟨a, ha⟩ => show ∃ b ∈ s, ∀ x ∈ s, ¬r x b from
    Acc.recOn (H.apply a) (fun x _ IH =>
        not_imp_not.1 fun hne hx => hne <| ⟨x, hx, fun y hy hyx => hne <| IH y hyx hy⟩)
      ha
#align well_founded.has_min WellFounded.has_min

/-- A minimal element of a nonempty set in a well-founded order.

If you're working with a nonempty linear order, consider defining a
`ConditionallyCompleteLinearOrderBot` instance via
`WellFounded.conditionallyCompleteLinearOrderWithBot` and using `Inf` instead. -/
noncomputable def min {r : α → α → Prop} (H : WellFounded r) (s : Set α) (h : s.Nonempty) : α :=
  Classical.choose (H.has_min s h)
#align well_founded.min WellFounded.min

theorem min_mem {r : α → α → Prop} (H : WellFounded r) (s : Set α) (h : s.Nonempty) :
    H.min s h ∈ s :=
  let ⟨h, _⟩ := Classical.choose_spec (H.has_min s h)
  h
#align well_founded.min_mem WellFounded.min_mem

theorem not_lt_min {r : α → α → Prop} (H : WellFounded r) (s : Set α) (h : s.Nonempty) {x}
    (hx : x ∈ s) : ¬r x (H.min s h) :=
  let ⟨_, h'⟩ := Classical.choose_spec (H.has_min s h)
  h' _ hx
#align well_founded.not_lt_min WellFounded.not_lt_min

theorem wellFounded_iff_has_min {r : α → α → Prop} :
    WellFounded r ↔ ∀ s : Set α, s.Nonempty → ∃ m ∈ s, ∀ x ∈ s, ¬r x m := by
  refine ⟨fun h => h.has_min, fun h => ⟨fun x => ?_⟩⟩
  -- ⊢ Acc r x
  by_contra hx
  -- ⊢ False
  obtain ⟨m, hm, hm'⟩ := h {x | ¬Acc r x} ⟨x, hx⟩
  -- ⊢ False
  refine' hm ⟨_, fun y hy => _⟩
  -- ⊢ Acc r y
  by_contra hy'
  -- ⊢ False
  exact hm' y hy' hy
  -- 🎉 no goals
#align well_founded.well_founded_iff_has_min WellFounded.wellFounded_iff_has_min

open Set

/-- The supremum of a bounded, well-founded order -/
protected noncomputable def sup {r : α → α → Prop} (wf : WellFounded r) (s : Set α)
    (h : Bounded r s) : α :=
  wf.min { x | ∀ a ∈ s, r a x } h
#align well_founded.sup WellFounded.sup

protected theorem lt_sup {r : α → α → Prop} (wf : WellFounded r) {s : Set α} (h : Bounded r s) {x}
    (hx : x ∈ s) : r x (wf.sup s h) :=
  min_mem wf { x | ∀ a ∈ s, r a x } h x hx
#align well_founded.lt_sup WellFounded.lt_sup

section

open Classical

/-- A successor of an element `x` in a well-founded order is a minimal element `y` such that
`x < y` if one exists. Otherwise it is `x` itself. -/
protected noncomputable def succ {r : α → α → Prop} (wf : WellFounded r) (x : α) : α :=
  if h : ∃ y, r x y then wf.min { y | r x y } h else x
#align well_founded.succ WellFounded.succ

protected theorem lt_succ {r : α → α → Prop} (wf : WellFounded r) {x : α} (h : ∃ y, r x y) :
    r x (wf.succ x) := by
  rw [WellFounded.succ, dif_pos h]
  -- ⊢ r x (min wf {y | r x y} h)
  apply min_mem
  -- 🎉 no goals
#align well_founded.lt_succ WellFounded.lt_succ

end

protected theorem lt_succ_iff {r : α → α → Prop} [wo : IsWellOrder α r] {x : α} (h : ∃ y, r x y)
    (y : α) : r y (wo.wf.succ x) ↔ r y x ∨ y = x := by
  constructor
  -- ⊢ r y (WellFounded.succ (_ : WellFounded r) x) → r y x ∨ y = x
  · intro h'
    -- ⊢ r y x ∨ y = x
    have : ¬r x y := by
      intro hy
      rw [WellFounded.succ, dif_pos] at h'
      exact wo.wf.not_lt_min _ h hy h'
    rcases trichotomous_of r x y with (hy | hy | hy)
    exfalso
    exact this hy
    -- ⊢ r y x ∨ y = x
    right
    -- ⊢ y = x
    exact hy.symm
    -- ⊢ r y x ∨ y = x
    left
    -- ⊢ r y x
    exact hy
    -- 🎉 no goals
  rintro (hy | rfl); exact _root_.trans hy (wo.wf.lt_succ h); exact wo.wf.lt_succ h
  -- ⊢ r y (WellFounded.succ (_ : WellFounded r) x)
                     -- ⊢ r y (WellFounded.succ (_ : WellFounded r) y)
                                                              -- 🎉 no goals
#align well_founded.lt_succ_iff WellFounded.lt_succ_iff

section LinearOrder

variable [LinearOrder β] (h : WellFounded ((· < ·) : β → β → Prop)) [PartialOrder γ]

theorem min_le {x : β} {s : Set β} (hx : x ∈ s) (hne : s.Nonempty := ⟨x, hx⟩) : h.min s hne ≤ x :=
  not_lt.1 <| h.not_lt_min _ _ hx
#align well_founded.min_le WellFounded.min_le

private theorem eq_strictMono_iff_eq_range_aux {f g : β → γ} (hf : StrictMono f)
    (hg : StrictMono g) (hfg : Set.range f = Set.range g) {b : β} (H : ∀ a < b, f a = g a) :
    f b ≤ g b := by
  obtain ⟨c, hc⟩ : g b ∈ Set.range f := by
    rw [hfg]
    exact Set.mem_range_self b
  cases' lt_or_le c b with hcb hbc
  -- ⊢ f b ≤ g b
  · rw [H c hcb] at hc
    -- ⊢ f b ≤ g b
    rw [hg.injective hc] at hcb
    -- ⊢ f b ≤ g b
    exact hcb.false.elim
    -- 🎉 no goals
  · rw [← hc]
    -- ⊢ f b ≤ f c
    exact hf.monotone hbc
    -- 🎉 no goals

theorem eq_strictMono_iff_eq_range {f g : β → γ} (hf : StrictMono f) (hg : StrictMono g) :
    Set.range f = Set.range g ↔ f = g :=
  ⟨fun hfg => by
    funext a
    -- ⊢ f a = g a
    apply h.induction a
    -- ⊢ ∀ (x : β), (∀ (y : β), y < x → f y = g y) → f x = g x
    exact fun b H =>
      le_antisymm (eq_strictMono_iff_eq_range_aux hf hg hfg H)
        (eq_strictMono_iff_eq_range_aux hg hf hfg.symm fun a hab => (H a hab).symm),
    congr_arg _⟩
#align well_founded.eq_strict_mono_iff_eq_range WellFounded.eq_strictMono_iff_eq_range

theorem self_le_of_strictMono {f : β → β} (hf : StrictMono f) : ∀ n, n ≤ f n := by
  by_contra' h₁
  -- ⊢ False
  have h₂ := h.min_mem _ h₁
  -- ⊢ False
  exact h.not_lt_min _ h₁ (hf h₂) h₂
  -- 🎉 no goals
#align well_founded.self_le_of_strict_mono WellFounded.self_le_of_strictMono

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
#align function.argmin Function.argmin

theorem not_lt_argmin [Nonempty α] (a : α) : ¬f a < f (argmin f h) :=
  WellFounded.not_lt_min (InvImage.wf f h) _ _ (Set.mem_univ a)
#align function.not_lt_argmin Function.not_lt_argmin

/-- Given a function `f : α → β` where `β` carries a well-founded `<`, and a non-empty subset `s`
of `α`, this is an element of `s` whose image under `f` is minimal in the sense of
`Function.not_lt_argminOn`. -/
noncomputable def argminOn (s : Set α) (hs : s.Nonempty) : α :=
  WellFounded.min (InvImage.wf f h) s hs
#align function.argmin_on Function.argminOn

@[simp]
theorem argminOn_mem (s : Set α) (hs : s.Nonempty) : argminOn f h s hs ∈ s :=
  WellFounded.min_mem _ _ _
#align function.argmin_on_mem Function.argminOn_mem

--Porting note: @[simp] removed as it will never apply
theorem not_lt_argminOn (s : Set α) {a : α} (ha : a ∈ s)
    (hs : s.Nonempty := Set.nonempty_of_mem ha) : ¬f a < f (argminOn f h s hs) :=
  WellFounded.not_lt_min (InvImage.wf f h) s hs ha
#align function.not_lt_argmin_on Function.not_lt_argminOn

end LT

section LinearOrder

variable [LinearOrder β] (h : WellFounded ((· < ·) : β → β → Prop))

--Porting note: @[simp] removed as it will never apply
theorem argmin_le (a : α) [Nonempty α] : f (argmin f h) ≤ f a :=
  not_lt.mp <| not_lt_argmin f h a
#align function.argmin_le Function.argmin_le

--Porting note: @[simp] removed as it will never apply
theorem argminOn_le (s : Set α) {a : α} (ha : a ∈ s) (hs : s.Nonempty := Set.nonempty_of_mem ha) :
    f (argminOn f h s hs) ≤ f a :=
  not_lt.mp <| not_lt_argminOn f h s ha hs
#align function.argmin_on_le Function.argminOn_le

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
#align acc.induction_bot' Acc.induction_bot'

/-- Let `r` be a relation on `α`, let `C : α → Prop` and let `bot : α`.
This induction principle shows that `C bot` holds, given that
* some `a` that is accessible by `r` satisfies `C a`, and
* for each `b ≠ bot` such that `C b` holds, there is `c` satisfying `r c b` and `C c`. -/
theorem Acc.induction_bot {α} {r : α → α → Prop} {a bot : α} (ha : Acc r a) {C : α → Prop}
    (ih : ∀ b, b ≠ bot → C b → ∃ c, r c b ∧ C c) : C a → C bot :=
  ha.induction_bot' ih
#align acc.induction_bot Acc.induction_bot

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
#align well_founded.induction_bot' WellFounded.induction_bot'

/-- Let `r` be a well-founded relation on `α`, let `C : α → Prop`, and let `bot : α`.
This induction principle shows that `C bot` holds, given that
* some `a` satisfies `C a`, and
* for each `b` that satisfies `C b`, there is `c` satisfying `r c b` and `C c`.

The naming is inspired by the fact that when `r` is transitive, it follows that `bot` is
the smallest element w.r.t. `r` that satisfies `C`. -/
theorem WellFounded.induction_bot {α} {r : α → α → Prop} (hwf : WellFounded r) {a bot : α}
    {C : α → Prop} (ih : ∀ b, b ≠ bot → C b → ∃ c, r c b ∧ C c) : C a → C bot :=
  hwf.induction_bot' ih
#align well_founded.induction_bot WellFounded.induction_bot

end Induction
