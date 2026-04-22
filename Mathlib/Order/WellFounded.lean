/-
Copyright (c) 2020 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro
-/
module

public import Mathlib.Data.Set.Function
public import Mathlib.Order.Bounds.Defs

/-!
# Well-founded relations

A relation is well-founded if it can be used for induction: for each `x`, `(∀ y, r y x → P y) → P x`
implies `P x`. Well-founded relations can be used for induction and recursion, including
construction of fixed points in the space of dependent functions `Π x : α, β x`.

The predicate `WellFounded` is defined in the core library. In this file we prove some extra lemmas
and provide a few new definitions: `WellFounded.min`, `WellFounded.sup`, and `WellFounded.succ`,
and an induction principle `WellFounded.induction_bot`.
-/

@[expose] public section

theorem acc_def {α} {r : α → α → Prop} {a : α} : Acc r a ↔ ∀ b, r b a → Acc r b where
  mp h := h.rec fun _ h _ ↦ h
  mpr := .intro a

theorem exists_not_acc_lt_of_not_acc {α} {a : α} {r} (h : ¬Acc r a) : ∃ b, ¬Acc r b ∧ r b a := by
  rw [acc_def] at h
  push Not at h
  simpa only [and_comm]

theorem not_acc_iff_exists_descending_chain {α} {r : α → α → Prop} {x : α} :
    ¬Acc r x ↔ ∃ f : ℕ → α, f 0 = x ∧ ∀ n, r (f (n + 1)) (f n) where
  mp hx := let f : ℕ → {a : α // ¬Acc r a} :=
      Nat.rec ⟨x, hx⟩ fun _ a ↦ ⟨_, (exists_not_acc_lt_of_not_acc a.2).choose_spec.1⟩
    ⟨(f · |>.1), rfl, fun n ↦ (exists_not_acc_lt_of_not_acc (f n).2).choose_spec.2⟩
  mpr h acc := acc.rec
    (fun _x _ ih ⟨f, hf⟩ ↦ ih (f 1) (hf.1 ▸ hf.2 0) ⟨(f <| · + 1), rfl, fun _ ↦ hf.2 _⟩) h

theorem acc_iff_isEmpty_descending_chain {α} {r : α → α → Prop} {x : α} :
    Acc r x ↔ IsEmpty { f : ℕ → α // f 0 = x ∧ ∀ n, r (f (n + 1)) (f n) } := by
  contrapose!
  rw [nonempty_subtype]
  exact not_acc_iff_exists_descending_chain

/-- A relation is well-founded iff it doesn't have any infinite descending chain.

See `RelEmbedding.wellFounded_iff_isEmpty` for a version in terms of relation embeddings. -/
theorem wellFounded_iff_isEmpty_descending_chain {α} {r : α → α → Prop} :
    WellFounded r ↔ IsEmpty { f : ℕ → α // ∀ n, r (f (n + 1)) (f n) } where
  mp := fun ⟨h⟩ ↦ ⟨fun ⟨f, hf⟩ ↦ (acc_iff_isEmpty_descending_chain.mp (h (f 0))).false ⟨f, rfl, hf⟩⟩
  mpr h := ⟨fun _ ↦ acc_iff_isEmpty_descending_chain.mpr ⟨fun ⟨f, hf⟩ ↦ h.false ⟨f, hf.2⟩⟩⟩

variable {α β γ : Type*}

namespace WellFounded

variable {r r' : α → α → Prop}

protected theorem asymm (h : WellFounded r) : Std.Asymm r := ⟨h.asymmetric⟩

@[deprecated (since := "2026-01-07")] protected alias isAsymm := WellFounded.asymm

protected theorem irrefl (h : WellFounded r) : Std.Irrefl r := @Std.Asymm.irrefl α r h.asymm

@[deprecated (since := "2026-01-07")] protected alias isIrrefl := WellFounded.irrefl

instance [WellFoundedRelation α] : Std.Asymm (α := α) WellFoundedRelation.rel :=
  WellFoundedRelation.wf.asymm

theorem mono (hr : WellFounded r) (h : ∀ a b, r' a b → r a b) : WellFounded r' :=
  Subrelation.wf (h _ _) hr

open scoped Function in -- required for scoped `on` notation
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
`WellFoundedLT.conditionallyCompleteLinearOrderBot` and using `Inf` instead. -/
noncomputable def min {r : α → α → Prop} (H : WellFounded r) (s : Set α) (h : s.Nonempty) : α :=
  Classical.choose (H.has_min s h)

theorem min_mem {r : α → α → Prop} (H : WellFounded r) (s : Set α) (h : s.Nonempty) :
    H.min s h ∈ s :=
  let ⟨h, _⟩ := Classical.choose_spec (H.has_min s h)
  h

theorem prop_min {r : α → α → Prop} (H : WellFounded r) {p : α → Prop} (h : ∃ a, p a) :
    p (H.min {a | p a} h) :=
  H.min_mem {a | p a} h

theorem not_lt_min {r : α → α → Prop} (H : WellFounded r) (s : Set α) {x} (hx : x ∈ s) :
    ¬r x (H.min s ⟨x, hx⟩) :=
  let ⟨_, h'⟩ := Classical.choose_spec (H.has_min s ⟨x, hx⟩)
  h' _ hx

/-- The minimal element of a trichotomous well-founded order is unique -/
theorem min_eq_of_forall_not_lt [Std.Trichotomous r] (wf : WellFounded r) {s : Set α} {m : α}
    (hms : m ∈ s) (hrm : ∀ x ∈ s, ¬r x m) : wf.min s ⟨m, hms⟩ = m :=
  Std.Trichotomous.trichotomous _ m (hrm _ <| wf.min_mem s _) (wf.not_lt_min s hms)

theorem notMem_of_lt_min {wf : WellFounded r} {s : Set α} {hs : s.Nonempty} {x : α}
    (hx : r x (wf.min s hs)) : x ∉ s :=
  (wf.not_lt_min s · hx)

theorem mem_of_lt_min_compl {wf : WellFounded r} {s : Set α} {hs : sᶜ.Nonempty} {x : α}
    (hx : r x (wf.min sᶜ hs)) : x ∈ s :=
  Set.notMem_compl_iff.mp <| notMem_of_lt_min hx

theorem wellFounded_iff_has_min {r : α → α → Prop} :
    WellFounded r ↔ ∀ s : Set α, s.Nonempty → ∃ m ∈ s, ∀ x ∈ s, ¬r x m := by
  refine ⟨fun h => h.has_min, fun h => ⟨fun x => ?_⟩⟩
  by_contra hx
  obtain ⟨m, hm, hm'⟩ := h {x | ¬Acc r x} ⟨x, hx⟩
  refine hm ⟨_, fun y hy => ?_⟩
  by_contra hy'
  exact hm' y hy' hy

@[to_dual]
theorem wellFoundedLT_iff_exists_minimal [Preorder α] :
    WellFoundedLT α ↔ ∀ s : Set α, s.Nonempty → ∃ m, Minimal (· ∈ s) m := by
  simp only [isWellFounded_iff, wellFounded_iff_has_min, not_lt_iff_le_imp_ge, Minimal]

theorem isWellOrder_iff_exists_not_lt_and_eq_or_lt :
    IsWellOrder α r ↔ ∀ s : Set α, s.Nonempty → ∃ m ∈ s, ∀ x ∈ s, ¬r x m ∧ (m = x ∨ r m x) := by
  refine ⟨fun h s hs ↦ ?_, fun h ↦ @IsWellOrder.mk α r ⟨?_⟩ ⟨fun a b ↦ ?_⟩⟩
  · grind [h.wf.has_min, trichotomous_of r]
  · grind [wellFounded_iff_has_min]
  · grind [h {a, b} <| by simp]

theorem not_rel_apply_succ [h : IsWellFounded α r] (f : ℕ → α) : ∃ n, ¬ r (f (n + 1)) (f n) := by
  by_contra! hf
  exact (wellFounded_iff_isEmpty_descending_chain.1 h.wf).elim ⟨f, hf⟩

open Set

/-- The supremum of a bounded, well-founded order -/
protected noncomputable def sup {r : α → α → Prop} (wf : WellFounded r) (s : Set α)
    (h : Bounded r s) : α :=
  wf.min { x | ∀ a ∈ s, r a x } h

protected theorem lt_sup {r : α → α → Prop} (wf : WellFounded r) {s : Set α} (h : Bounded r s) {x}
    (hx : x ∈ s) : r x (wf.sup s h) :=
  min_mem wf { x | ∀ a ∈ s, r a x } h x hx

end WellFounded

section LinearOrder

variable [LinearOrder β] [Preorder γ]

-- TODO: the name `WellFounded.min` is incorrect when the assumption is that `>` is well-founded.
@[to_dual none]
theorem WellFounded.min_le (h : WellFounded ((· < ·) : β → β → Prop))
    {x : β} {s : Set β} (hx : x ∈ s) : h.min s ⟨x, hx⟩ ≤ x :=
  not_lt.1 <| h.not_lt_min _ hx

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

/-- A strictly monotone function `f` on a well-order satisfies `x ≤ f x` for all `x`. -/
theorem StrictMono.id_le [WellFoundedLT β] {f : β → β} (hf : StrictMono f) : id ≤ f := by
  rw [Pi.le_def]
  by_contra! H
  obtain ⟨m, hm, hm'⟩ := wellFounded_lt.has_min {i | f i < i} H
  exact hm' _ (hf hm) hm

theorem StrictMono.le_apply [WellFoundedLT β] {f : β → β} (hf : StrictMono f) {x} : x ≤ f x :=
  hf.id_le x

/-- A strictly monotone function `f` on a cowell-order satisfies `f x ≤ x` for all `x`. -/
theorem StrictMono.le_id [WellFoundedGT β] {f : β → β} (hf : StrictMono f) : f ≤ id :=
  StrictMono.id_le (β := βᵒᵈ) hf.dual

theorem StrictMono.apply_le [WellFoundedGT β] {f : β → β} (hf : StrictMono f) {x} : f x ≤ x :=
  StrictMono.le_apply (β := βᵒᵈ) hf.dual

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

variable [LT β] [WellFoundedLT β]

/-- Given a function `f : α → β` where `β` carries a well-founded `<`, this is an element of `α`
whose image under `f` is minimal in the sense of `Function.not_lt_argmin`.

See also `Set.Finite.exists_minimalFor` and related lemmas for the case when `α` is finite. -/
noncomputable def argmin [Nonempty α] : α :=
  WellFounded.min (InvImage.wf f wellFounded_lt) Set.univ Set.univ_nonempty

theorem not_lt_argmin [Nonempty α] (a : α) : ¬f a < f (argmin f) :=
  WellFounded.not_lt_min (InvImage.wf f wellFounded_lt) _ (Set.mem_univ a)

/-- Given a function `f : α → β` where `β` carries a well-founded `<`, and a non-empty subset `s`
of `α`, this is an element of `s` whose image under `f` is minimal in the sense of
`Function.not_lt_argminOn`.

See also `Set.Finite.exists_minimalFor` and related lemmas for the case when `α` or `s` is finite.

TODO Consider removing this definition in favour of `exists_minimalFor_of_wellFoundedLT`. -/
noncomputable def argminOn (s : Set α) (hs : s.Nonempty) : α :=
  WellFounded.min (InvImage.wf f wellFounded_lt) s hs

@[simp]
theorem argminOn_mem (s : Set α) (hs : s.Nonempty) : argminOn f s hs ∈ s :=
  WellFounded.min_mem _ _ _

theorem not_lt_argminOn (s : Set α) {a : α} (ha : a ∈ s) : ¬f a < f (argminOn f s ⟨a, ha⟩) :=
  WellFounded.not_lt_min (InvImage.wf f wellFounded_lt) s ha

end LT

section LinearOrder

variable [LinearOrder β] [WellFoundedLT β]

theorem argmin_le (a : α) [Nonempty α] : f (argmin f) ≤ f a :=
  not_lt.mp <| not_lt_argmin f a

theorem isMinimalFor_argmin [Nonempty α] :
    MinimalFor (fun _ ↦ True) f (argmin f) :=
  ⟨trivial, fun a _ _ ↦ argmin_le f a⟩

theorem argminOn_le (s : Set α) {a : α} (ha : a ∈ s) :
    f (argminOn f s ⟨a, ha⟩) ≤ f a :=
  not_lt.mp <| not_lt_argminOn f s ha

theorem isMinimalFor_argminOn (s : Set α) (hs : s.Nonempty) :
    MinimalFor (· ∈ s) f (argminOn f s hs) :=
  ⟨argminOn_mem f s hs, fun _ h _ ↦ argminOn_le f s h⟩

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
@[to_dual (attr := implicit_reducible)
/-- A nonempty linear order with well-founded `>` has a top element. -/]
noncomputable def WellFoundedLT.toOrderBot (α) [LinearOrder α] [Nonempty α] [h : WellFoundedLT α] :
    OrderBot α where
  bot := h.wf.min _ Set.univ_nonempty
  bot_le a := h.wf.min_le (Set.mem_univ a)

@[to_dual]
instance [LT α] [h : WellFoundedLT α] : WellFoundedLT (ULift α) where
  wf := InvImage.wf ULift.down h.wf
