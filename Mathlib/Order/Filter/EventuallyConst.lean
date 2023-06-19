/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Floris van Doorn
-/
import Mathlib.Order.Filter.AtTopBot

open Set

namespace Filter

variable {l : Filter α} {f : α → β}

/-- The proposition that a function is eventually constant along a filter on the domain. -/
def EventuallyConst (f : α → β) (l : Filter α) : Prop :=
  ∃ c : β, f =ᶠ[l] fun _ ↦ c

lemma eventuallyConst_iff_tendsto : EventuallyConst f l ↔ ∃ x, Tendsto f l (pure x) := by
  simp_rw [EventuallyConst, EventuallyEq, tendsto_pure]

alias eventuallyConst_iff_tendsto ↔ EventuallyConst.exists_tendsto _

namespace EventuallyConst

protected lemma nonempty (h : EventuallyConst f l) : Nonempty β := nonempty_of_exists h

protected lemma const (c : β) : EventuallyConst (fun _ ↦ c) l :=
  ⟨c, eventually_of_forall fun _ ↦ rfl⟩

lemma of_unique [Unique β] : EventuallyConst f l :=
  ⟨default, eventually_of_forall fun _ ↦ Unique.uniq _ _⟩

lemma comp (h : EventuallyConst f l) (g : β → γ) : EventuallyConst (g ∘ f) l :=
  let ⟨c, hc⟩ := h
  ⟨g c, hc.fun_comp g⟩

lemma comp_tendsto {lb : Filter β} {g : β → γ} (hg : EventuallyConst g lb)
    (hf : Tendsto f l lb) : EventuallyConst (g ∘ f) l :=
  let ⟨c, hc⟩ := hg; ⟨c, hf hc⟩

lemma apply {ι : Type _} {p : ι → Type _} {g : α → ∀ x, p x}
    (h : EventuallyConst g l) (i : ι) : EventuallyConst (g · i) l :=
  h.comp <| Function.eval i

end EventuallyConst

theorem eventuallyConst_pred {p : α → Prop} :
    EventuallyConst p l ↔ (p =ᶠ[l] fun _ ↦ false) ∨ (p =ᶠ[l] fun _ ↦ true) := by
  simp only [EventuallyConst]

theorem eventuallyConst_set {s : Set α} :
    EventuallyConst s ↔ (s =ᶠ[l] (∅ : Set α)) ∨ s =ᶠ[l] univ

lemma EventuallyConst_at_top [semilattice_sup α] [nonempty α] :
  (∃ i, ∀ j, i ≤ j → g j = g i) ↔ EventuallyConst g at_top :=
begin
  simp_rw [EventuallyConst, eventually_at_top],
  split,
  { rintro ⟨i, hi⟩, refine ⟨g i, i, hi⟩ },
  { rintro ⟨y, i, hi⟩, use i, simp_rw [hi i le_rfl], exact hi },
end

lemma EventuallyConst_at_top_nat {g : ℕ → α} :
  (∃ n, ∀ m, n ≤ m → g (m + 1) = g m) ↔ EventuallyConst g at_top :=
begin
  rw [← EventuallyConst_at_top],
  apply exists_congr, intro n,
  split,
  { intros h m hm, induction hm with m hm ih, refl, rw [nat.succ_eq_add_one, h m hm, ih] },
  { intros h m hm, rw [h m hm, h (m + 1) hm.step] }
end

/-- The eventual value of an eventually-constant function.

For convenience, `eventual_value` may be applied to any function; if the input is not
eventually-constant the result should be regarded as a "junk" value. -/
noncomputable def eventual_value [nonempty β] (g : α → β) (f : Filter α) : β :=
classical.epsilon $ λ x : β, ∀ᶠ i in f, g i = x

lemma eventually_eq_eventual_value (h : EventuallyConst g f) :
  ∀ᶠ i in f, g i = @eventual_value _ _ h.nonempty g f :=
classical.epsilon_spec h

lemma eventual_value_unique [f.ne_bot] {y : β} (hy : ∀ᶠ i in f, g i = y) :
  y = @eventual_value _ _ ⟨y⟩ g f :=
by { obtain ⟨x, rfl, hx⟩ := (hy.and $ eventually_eq_eventual_value ⟨y, hy⟩).exists, exact hx }

/-- This lemma is sometimes useful if the elaborator uses the nonempty instance in
  `eventual_value_unique` to find the implicit argument `y`. -/
lemma eventual_value_unique' [f.ne_bot] {hβ : nonempty β} {y : β} (hy : ∀ᶠ i in f, g i = y) :
  eventual_value g f = y  :=
(eventual_value_unique hy).symm

lemma eventual_value_eq_fn {g : ℕ → β} {hβ : nonempty β} {n : ℕ} (h : ∀ m, n ≤ m → g m = g n) :
  eventual_value g at_top = g n :=
eventual_value_unique' $ eventually_of_mem (mem_at_top _) h

lemma EventuallyConst.exists_eventual_value_eq [f.ne_bot] (h : EventuallyConst g f) :
  ∃ i, @eventual_value _ _ h.nonempty g f = g i :=
begin
  obtain ⟨y, hy⟩ := h,
  obtain ⟨x, rfl⟩ := hy.exists,
  exact ⟨x, (eventual_value_unique hy).symm⟩
end

lemma EventuallyConst.tendsto [nonempty β] (h : EventuallyConst g f) :
  tendsto g f (pure (eventual_value g f)) :=
by { rw [tendsto_pure], exact eventually_eq_eventual_value h }

lemma eventual_value_compose [f.ne_bot] (h : EventuallyConst g f) (g' : β → γ) :
  @eventual_value _ _ (h.compose g').nonempty (g' ∘ g) f =
  g' (@eventual_value _ _ h.nonempty g f) :=
(eventual_value_unique $ (eventually_eq_eventual_value h).mono $ λ x, congr_arg g').symm

lemma eventual_value_apply {ι : Type*} {p : ι → Type*} [f.ne_bot] {g : α → ∀ x, p x}
  (h : EventuallyConst g f) (i : ι) :
  @eventual_value _ _ h.nonempty g f i = @eventual_value _ _ (h.apply i).nonempty (λ x, g x i) f :=
(eventual_value_compose h $ λ p, p i).symm

lemma EventuallyConst.tendsto_nhds [nonempty β] [topological_space β]
  (h : EventuallyConst g f) : tendsto g f (𝓝 (eventual_value g f)) :=
h.tendsto.mono_right $ pure_le_nhds _

/-- todo: generalize to `t1_space`. -/
lemma eventual_value_eq_lim [f.ne_bot] [nonempty β] [topological_space β] [t2_space β]
  (h : EventuallyConst g f) : eventual_value g f = lim f g :=
h.tendsto_nhds.lim_eq.symm

