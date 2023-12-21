/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Floris van Doorn
-/
import Mathlib.Order.Filter.AtTopBot
import Mathlib.Algebra.IndicatorFunction
/-!
# Functions that are eventually constant along a filter

In this file we define a predicate `Filter.EventuallyConst f l` saying that a function `f : α → β`
is eventually equal to a constant along a filter `l`. We also prove some basic properties of these
functions.
-/

open Set

namespace Filter

variable {l : Filter α} {f : α → β}

/-- The proposition that a function is eventually constant along a filter on the domain. -/
def EventuallyConst (f : α → β) (l : Filter α) : Prop :=
  ∃ c : β, f =ᶠ[l] fun _ ↦ c

lemma eventuallyConst_iff_tendsto : EventuallyConst f l ↔ ∃ x, Tendsto f l (pure x) := by
  simp_rw [EventuallyConst, EventuallyEq, tendsto_pure]

alias eventuallyConst_iff_tendsto ↔ EventuallyConst.exists_tendsto _

theorem eventuallyConst_pred' {p : α → Prop} :
    EventuallyConst p l ↔ (p =ᶠ[l] fun _ ↦ False) ∨ (p =ᶠ[l] fun _ ↦ True) := by
  simp only [EventuallyConst, Prop.exists_iff]

theorem eventuallyConst_pred {p : α → Prop} :
    EventuallyConst p l ↔ (∀ᶠ x in l, p x) ∨ (∀ᶠ x in l, ¬p x) := by
  simp [eventuallyConst_pred', or_comm, EventuallyEq]

theorem eventuallyConst_set' {s : Set α} :
    EventuallyConst s l ↔ (s =ᶠ[l] (∅ : Set α)) ∨ s =ᶠ[l] univ :=
  eventuallyConst_pred'

theorem eventuallyConst_set {s : Set α} :
    EventuallyConst s l ↔ (∀ᶠ x in l, x ∈ s) ∨ (∀ᶠ x in l, x ∉ s) :=
  eventuallyConst_pred

namespace EventuallyConst

@[simp] protected lemma bot [Nonempty β] : EventuallyConst f ⊥ := by
  simp [EventuallyConst, EventuallyEq]

protected lemma nonempty (h : EventuallyConst f l) : Nonempty β := nonempty_of_exists h

protected lemma const (c : β) : EventuallyConst (fun _ ↦ c) l :=
  ⟨c, eventually_of_forall fun _ ↦ rfl⟩

protected lemma congr (h : EventuallyConst f l) (hg : f =ᶠ[l] g) : EventuallyConst g l :=
  let ⟨c, hc⟩ := h; ⟨c, hg.symm.trans hc⟩

@[nontriviality]
lemma of_unique [Unique β] : EventuallyConst f l :=
  ⟨default, eventually_of_forall fun _ ↦ Unique.uniq _ _⟩

lemma mono (h : EventuallyConst f l) (hl' : l' ≤ l) : EventuallyConst f l' :=
  h.imp fun _c hc ↦ hl' hc

@[nontriviality]
lemma of_subsingleton [Subsingleton α] [Nonempty β] : EventuallyConst f l := by
  rcases isEmpty_or_nonempty α with h | h
  · simp only [l.filter_eq_bot_of_isEmpty, EventuallyConst.bot]
  · inhabit α
    refine ⟨f default, eventually_of_forall fun x ↦ congr_arg f <| Subsingleton.elim _ _⟩

lemma comp (h : EventuallyConst f l) (g : β → γ) : EventuallyConst (g ∘ f) l :=
  let ⟨c, hc⟩ := h
  ⟨g c, hc.fun_comp g⟩

@[to_additive]
protected lemma inv [Inv β] (h : EventuallyConst f l) : EventuallyConst (f⁻¹) l := h.comp Inv.inv

lemma comp_tendsto {lb : Filter β} {g : β → γ} (hg : EventuallyConst g lb)
    (hf : Tendsto f l lb) : EventuallyConst (g ∘ f) l :=
  let ⟨c, hc⟩ := hg; ⟨c, hf hc⟩

lemma apply {ι : Type*} {p : ι → Type*} {g : α → ∀ x, p x}
    (h : EventuallyConst g l) (i : ι) : EventuallyConst (g · i) l :=
  h.comp <| Function.eval i

lemma comp₂ {g : α → γ} (hf : EventuallyConst f l) (op : β → γ → δ) (hg : EventuallyConst g l) :
    EventuallyConst (fun x ↦ op (f x) (g x)) l :=
  let ⟨cf, hf⟩ := hf; let ⟨cg, hg⟩ := hg; ⟨op cf cg, hg.mp <| hf.mono fun _ ↦ congr_arg₂ op⟩

lemma prod_mk {g : α → γ} (hf : EventuallyConst f l) (hg : EventuallyConst g l) :
    EventuallyConst (fun x ↦ (f x, g x)) l :=
  hf.comp₂ Prod.mk hg

@[to_additive]
lemma mul [Mul β] {g : α → β} (hf : EventuallyConst f l) (hg : EventuallyConst g l) :
    EventuallyConst (f * g) l :=
  hf.comp₂ (· * ·) hg

@[to_additive]
lemma of_mulIndicator_const [One β] {s : Set α} {c : β} (hc : c ≠ 1)
    (h : EventuallyConst (s.mulIndicator fun _ ↦ c) l) : EventuallyConst s l := by
  rw [eventuallyConst_set]
  rcases h with ⟨d, hd⟩
  rcases eq_or_ne d 1 with rfl | hd₁
  · refine .inr <| hd.mono fun x hx ↦ ?_
    simpa only [mulIndicator_apply_eq_one, hc] using hx
  · refine .inl <| hd.mono fun x hx ↦ ?_
    simpa [hc] using ne_of_eq_of_ne hx hd₁

end EventuallyConst

theorem EventuallyEq.eventuallyConst_iff (h : f =ᶠ[l] g) :
    EventuallyConst f l ↔ EventuallyConst g l :=
  ⟨(.congr · h), (.congr · h.symm)⟩

lemma eventuallyConst_atTop [SemilatticeSup α] [Nonempty α] :
    EventuallyConst f atTop ↔ (∃ i, ∀ j, i ≤ j → f j = f i) := by
  constructor
  · rintro ⟨c, hc⟩
    rcases eventually_atTop.1 hc with ⟨i, hi⟩
    exact ⟨i, fun j hj ↦ (hi j hj).trans (hi i le_rfl).symm⟩
  · rintro ⟨i, hi⟩
    exact ⟨f i, eventually_atTop.2 ⟨i, hi⟩⟩

lemma eventuallyConst_atTop_nat {f : ℕ → α} :
    EventuallyConst f atTop ↔ ∃ n, ∀ m, n ≤ m → f (m + 1) = f m := by
  rw [eventuallyConst_atTop]
  refine exists_congr fun n ↦ ⟨fun h m hm ↦ ?_, fun h m hm ↦ ?_⟩
  · exact (h (m + 1) (hm.trans m.le_succ)).trans (h m hm).symm
  · induction m, hm using Nat.le_induction with
    | base => rfl
    | succ m hm ihm => exact (h m hm).trans ihm
