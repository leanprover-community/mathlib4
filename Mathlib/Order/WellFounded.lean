/-
Copyright (c) 2020 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro
-/
import Mathlib.Data.Set.Function
import Mathlib.Order.Bounds.Defs

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

section deprecated

open Classical in
set_option linter.deprecated false in
/-- A successor of an element `x` in a well-founded order is a minimal element `y` such that
`x < y` if one exists. Otherwise it is `x` itself. -/
@[deprecated "If you have a linear order, consider defining a `SuccOrder` instance through
`ConditionallyCompleteLinearOrder.toSuccOrder`." (since := "2024-10-25")]
protected noncomputable def succ {r : α → α → Prop} (wf : WellFounded r) (x : α) : α :=
  if h : ∃ y, r x y then wf.min { y | r x y } h else x

set_option linter.deprecated false in
@[deprecated "No deprecation message was provided." (since := "2024-10-25")]
protected theorem lt_succ {r : α → α → Prop} (wf : WellFounded r) {x : α} (h : ∃ y, r x y) :
    r x (wf.succ x) := by
  rw [WellFounded.succ, dif_pos h]
  apply min_mem

set_option linter.deprecated false in
@[deprecated "No deprecation message was provided." (since := "2024-10-25")]
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

end deprecated

end WellFounded

section LinearOrder

variable [LinearOrder β] [Preorder γ]

theorem WellFounded.min_le (h : WellFounded ((· < ·) : β → β → Prop))
    {x : β} {s : Set β} (hx : x ∈ s) (hne : s.Nonempty := ⟨x, hx⟩) : h.min s hne ≤ x :=
  not_lt.1 <| h.not_lt_min _ _ hx

theorem Set.range_injOn_strictMono [WellFoundedLT β] :
    Set.InjOn Set.range { f : β → γ | StrictMono f } := by
  intro f hf g hg hfg
  ext a
  apply WellFoundedLT.induction a
  intro a IH
  obtain ⟨b, hb⟩ := hfg ▸ mem_range_self a
  obtain h | rfl | h := lt_trichotomy b a
  · rw [← IH b h] at hb
    cases (hf.injective hb).not_lt h
  · rw [hb]
  · obtain ⟨c, hc⟩ := hfg.symm ▸ mem_range_self a
    have := hg h
    rw [hb, ← hc, hf.lt_iff_lt] at this
    rw [IH c this] at hc
    cases (hg.injective hc).not_lt this

theorem Set.range_injOn_strictAnti [WellFoundedGT β] :
    Set.InjOn Set.range { f : β → γ | StrictAnti f } :=
  fun _ hf _ hg ↦ Set.range_injOn_strictMono (β := βᵒᵈ) hf.dual hg.dual

theorem StrictMono.range_inj [WellFoundedLT β] {f g : β → γ}
    (hf : StrictMono f) (hg : StrictMono g) : Set.range f = Set.range g ↔ f = g :=
  Set.range_injOn_strictMono.eq_iff hf hg

theorem StrictAnti.range_inj [WellFoundedGT β] {f g : β → γ}
    (hf : StrictAnti f) (hg : StrictAnti g) : Set.range f = Set.range g ↔ f = g :=
  Set.range_injOn_strictAnti.eq_iff hf hg

@[deprecated StrictMono.range_inj (since := "2024-09-11")]
theorem WellFounded.eq_strictMono_iff_eq_range (h : WellFounded ((· < ·) : β → β → Prop))
    {f g : β → γ} (hf : StrictMono f) (hg : StrictMono g) :
    Set.range f = Set.range g ↔ f = g :=
  @StrictMono.range_inj β γ _ _ ⟨h⟩ f g hf hg

/-- A strictly monotone function `f` on a well-order satisfies `x ≤ f x` for all `x`. -/
theorem StrictMono.id_le [WellFoundedLT β] {f : β → β} (hf : StrictMono f) : id ≤ f := by
  rw [Pi.le_def]
  by_contra! H
  obtain ⟨m, hm, hm'⟩ := wellFounded_lt.has_min _ H
  exact hm' _ (hf hm) hm

theorem StrictMono.le_apply [WellFoundedLT β] {f : β → β} (hf : StrictMono f) {x} : x ≤ f x :=
  hf.id_le x

/-- A strictly monotone function `f` on a cowell-order satisfies `f x ≤ x` for all `x`. -/
theorem StrictMono.le_id [WellFoundedGT β] {f : β → β} (hf : StrictMono f) : f ≤ id :=
  StrictMono.id_le (β := βᵒᵈ) hf.dual

theorem StrictMono.apply_le [WellFoundedGT β] {f : β → β} (hf : StrictMono f) {x} : f x ≤ x :=
  StrictMono.le_apply (β := βᵒᵈ) hf.dual

@[deprecated StrictMono.le_apply (since := "2024-09-11")]
theorem WellFounded.self_le_of_strictMono (h : WellFounded ((· < ·) : β → β → Prop))
    {f : β → β} (hf : StrictMono f) : ∀ n, n ≤ f n := by
  by_contra! h₁
  have h₂ := h.min_mem _ h₁
  exact h.not_lt_min _ h₁ (hf h₂) h₂

theorem StrictMono.not_bddAbove_range_of_wellFoundedLT {f : β → β} [WellFoundedLT β] [NoMaxOrder β]
    (hf : StrictMono f) : ¬ BddAbove (Set.range f) := by
  rintro ⟨a, ha⟩
  obtain ⟨b, hb⟩ := exists_gt a
  exact ((hf.le_apply.trans_lt (hf hb)).trans_le <| ha (Set.mem_range_self _)).false

theorem StrictMono.not_bddBelow_range_of_wellFoundedGT {f : β → β} [WellFoundedGT β] [NoMinOrder β]
    (hf : StrictMono f) : ¬ BddBelow (Set.range f) :=
  hf.dual.not_bddAbove_range_of_wellFoundedLT

end LinearOrder

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

-- Porting note (https://github.com/leanprover-community/mathlib4/issues/11119): @[simp] removed as it will never apply
theorem not_lt_argminOn (s : Set α) {a : α} (ha : a ∈ s)
    (hs : s.Nonempty := Set.nonempty_of_mem ha) : ¬f a < f (argminOn f h s hs) :=
  WellFounded.not_lt_min (InvImage.wf f h) s hs ha

end LT

section LinearOrder

variable [LinearOrder β] (h : WellFounded ((· < ·) : β → β → Prop))

-- Porting note (https://github.com/leanprover-community/mathlib4/issues/11119): @[simp] removed as it will never apply
theorem argmin_le (a : α) [Nonempty α] : f (argmin f h) ≤ f a :=
  not_lt.mp <| not_lt_argmin f h a

-- Porting note (https://github.com/leanprover-community/mathlib4/issues/11119): @[simp] removed as it will never apply
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
