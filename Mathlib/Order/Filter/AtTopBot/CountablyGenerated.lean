/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad, Yury Kudryashov, Patrick Massot
-/
module

public import Mathlib.Order.Filter.AtTopBot.Finite
public import Mathlib.Order.Filter.AtTopBot.Prod
public import Mathlib.Order.Filter.CountablyGenerated

/-!
# Convergence to infinity and countably generated filters

In this file we prove that

- `Filter.atTop` and `Filter.atBot` filters on a countable type are countably generated;
- `Filter.exists_seq_tendsto`: if `f` is a nontrivial countably generated filter,
  then there exists a sequence that converges. to `f`;
- `Filter.tendsto_iff_seq_tendsto`: convergence along a countably generated filter
  is equivalent to convergence along all sequences that converge to this filter.
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

open Set

namespace Filter

variable {α β : Type*}

instance (priority := 200) atTop.isCountablyGenerated [Preorder α] [Countable α] :
    (atTop : Filter <| α).IsCountablyGenerated :=
  isCountablyGenerated_seq _

instance (priority := 200) atBot.isCountablyGenerated [Preorder α] [Countable α] :
    (atBot : Filter <| α).IsCountablyGenerated :=
  isCountablyGenerated_seq _

instance instIsCountablyGeneratedAtTopProd [Preorder α] [IsCountablyGenerated (atTop : Filter α)]
    [Preorder β] [IsCountablyGenerated (atTop : Filter β)] :
    IsCountablyGenerated (atTop : Filter (α × β)) := by
  rw [← prod_atTop_atTop_eq]
  infer_instance

instance instIsCountablyGeneratedAtBotProd [Preorder α] [IsCountablyGenerated (atBot : Filter α)]
    [Preorder β] [IsCountablyGenerated (atBot : Filter β)] :
    IsCountablyGenerated (atBot : Filter (α × β)) := by
  rw [← prod_atBot_atBot_eq]
  infer_instance

instance _root_.OrderDual.instIsCountablyGeneratedAtTop [Preorder α]
    [IsCountablyGenerated (atBot : Filter α)] : IsCountablyGenerated (atTop : Filter αᵒᵈ) := ‹_›

instance _root_.OrderDual.instIsCountablyGeneratedAtBot [Preorder α]
    [IsCountablyGenerated (atTop : Filter α)] : IsCountablyGenerated (atBot : Filter αᵒᵈ) := ‹_›

lemma atTop_countable_basis [Preorder α] [IsDirectedOrder α] [Nonempty α] [Countable α] :
    HasCountableBasis (atTop : Filter α) (fun _ => True) Ici :=
  { atTop_basis with countable := to_countable _ }

lemma atBot_countable_basis [Preorder α] [IsCodirectedOrder α] [Nonempty α] [Countable α] :
    HasCountableBasis (atBot : Filter α) (fun _ => True) Iic :=
  { atBot_basis with countable := to_countable _ }

/-- If `f` is a nontrivial countably generated filter, then there exists a sequence that converges
to `f`. -/
theorem exists_seq_tendsto (f : Filter α) [IsCountablyGenerated f] [NeBot f] :
    ∃ x : ℕ → α, Tendsto x atTop f := by
  obtain ⟨B, h⟩ := f.exists_antitone_basis
  choose x hx using fun n => Filter.nonempty_of_mem (h.mem n)
  exact ⟨x, h.tendsto hx⟩

theorem exists_seq_monotone_tendsto_atTop_atTop (α : Type*) [Preorder α] [Nonempty α]
    [IsDirectedOrder α] [(atTop : Filter α).IsCountablyGenerated] :
    ∃ xs : ℕ → α, Monotone xs ∧ Tendsto xs atTop atTop := by
  obtain ⟨ys, h⟩ := exists_seq_tendsto (atTop : Filter α)
  choose c hleft hright using exists_ge_ge (α := α)
  set xs : ℕ → α := fun n => (List.range n).foldl (fun x n ↦ c x (ys n)) (ys 0)
  have hsucc (n : ℕ) : xs (n + 1) = c (xs n) (ys n) := by simp [xs, List.range_succ]
  refine ⟨xs, ?_, ?_⟩
  · refine monotone_nat_of_le_succ fun n ↦ ?_
    rw [hsucc]
    apply hleft
  · refine (tendsto_add_atTop_iff_nat 1).1 <| tendsto_atTop_mono (fun n ↦ ?_) h
    rw [hsucc]
    apply hright

theorem exists_seq_antitone_tendsto_atTop_atBot (α : Type*) [Preorder α] [Nonempty α]
    [IsCodirectedOrder α] [(atBot : Filter α).IsCountablyGenerated] :
    ∃ xs : ℕ → α, Antitone xs ∧ Tendsto xs atTop atBot :=
  exists_seq_monotone_tendsto_atTop_atTop αᵒᵈ

/-- An abstract version of continuity of sequentially continuous functions on metric spaces:
if a filter `k` is countably generated then `Tendsto f k l` iff for every sequence `u`
converging to `k`, `f ∘ u` tends to `l`. -/
theorem tendsto_iff_seq_tendsto {f : α → β} {k : Filter α} {l : Filter β} [k.IsCountablyGenerated] :
    Tendsto f k l ↔ ∀ x : ℕ → α, Tendsto x atTop k → Tendsto (f ∘ x) atTop l := by
  refine ⟨fun h x hx => h.comp hx, fun H s hs => ?_⟩
  contrapose! H
  have : NeBot (k ⊓ 𝓟 (f ⁻¹' sᶜ)) := by simpa [neBot_iff, inf_principal_eq_bot]
  rcases (k ⊓ 𝓟 (f ⁻¹' sᶜ)).exists_seq_tendsto with ⟨x, hx⟩
  rw [tendsto_inf, tendsto_principal] at hx
  refine ⟨x, hx.1, fun h => ?_⟩
  rcases (hx.2.and (h hs)).exists with ⟨N, hnotMem, hmem⟩
  exact hnotMem hmem

theorem tendsto_of_seq_tendsto {f : α → β} {k : Filter α} {l : Filter β} [k.IsCountablyGenerated] :
    (∀ x : ℕ → α, Tendsto x atTop k → Tendsto (f ∘ x) atTop l) → Tendsto f k l :=
  tendsto_iff_seq_tendsto.2

theorem eventually_iff_seq_eventually {ι : Type*} {l : Filter ι} {p : ι → Prop}
    [l.IsCountablyGenerated] :
    (∀ᶠ n in l, p n) ↔ ∀ x : ℕ → ι, Tendsto x atTop l → ∀ᶠ n : ℕ in atTop, p (x n) := by
  simpa using tendsto_iff_seq_tendsto (f := id) (l := 𝓟 {x | p x})

theorem frequently_iff_seq_frequently {ι : Type*} {l : Filter ι} {p : ι → Prop}
    [l.IsCountablyGenerated] :
    (∃ᶠ n in l, p n) ↔ ∃ x : ℕ → ι, Tendsto x atTop l ∧ ∃ᶠ n : ℕ in atTop, p (x n) := by
  simp only [Filter.Frequently, eventually_iff_seq_eventually (l := l)]
  push Not; rfl

theorem exists_seq_forall_of_frequently {ι : Type*} {l : Filter ι} {p : ι → Prop}
    [l.IsCountablyGenerated] (h : ∃ᶠ n in l, p n) :
    ∃ ns : ℕ → ι, Tendsto ns atTop l ∧ ∀ n, p (ns n) := by
  rw [frequently_iff_seq_frequently] at h
  obtain ⟨x, hx_tendsto, hx_freq⟩ := h
  obtain ⟨n_to_n, h_tendsto, h_freq⟩ := subseq_forall_of_frequently hx_tendsto hx_freq
  exact ⟨x ∘ n_to_n, h_tendsto, h_freq⟩

lemma frequently_iff_seq_forall {ι : Type*} {l : Filter ι} {p : ι → Prop}
    [l.IsCountablyGenerated] :
    (∃ᶠ n in l, p n) ↔ ∃ ns : ℕ → ι, Tendsto ns atTop l ∧ ∀ n, p (ns n) :=
  ⟨exists_seq_forall_of_frequently, fun ⟨_ns, hnsl, hpns⟩ ↦
    hnsl.frequently <| Frequently.of_forall hpns⟩

/-- A sequence converges if every subsequence has a convergent subsequence. -/
theorem tendsto_of_subseq_tendsto {ι : Type*} {x : ι → α} {f : Filter α} {l : Filter ι}
    [l.IsCountablyGenerated]
    (hxy : ∀ ns : ℕ → ι, Tendsto ns atTop l →
      ∃ ms : ℕ → ℕ, Tendsto (fun n => x (ns <| ms n)) atTop f) :
    Tendsto x l f := by
  contrapose! hxy
  obtain ⟨s, hs, hfreq⟩ : ∃ s ∈ f, ∃ᶠ n in l, x n ∉ s := by
    rwa [not_tendsto_iff_exists_frequently_notMem] at hxy
  obtain ⟨y, hy_tendsto, hy_freq⟩ := exists_seq_forall_of_frequently hfreq
  refine ⟨y, hy_tendsto, fun ms hms_tendsto ↦ ?_⟩
  rcases (hms_tendsto.eventually_mem hs).exists with ⟨n, hn⟩
  exact absurd hn <| hy_freq _

theorem exists_seq_comp_tendsto {ι : Type*} {g : Filter ι} [IsCountablyGenerated g] {u : ι → α}
    {f : Filter α} [IsCountablyGenerated f]
    (hx : NeBot (f ⊓ map u g)) : ∃ θ : ℕ → ι, Tendsto θ atTop g ∧ Tendsto (u ∘ θ) atTop f := by
  rw [← Filter.push_pull', map_neBot_iff] at hx
  obtain ⟨θ, hθ⟩ := exists_seq_tendsto (comap u f ⊓ g)
  exact ⟨θ, (tendsto_inf.1 hθ).2, tendsto_comap_iff.1 (tendsto_inf.1 hθ).1⟩

theorem subseq_tendsto_of_neBot {f : Filter α} [IsCountablyGenerated f] {u : ℕ → α}
    (hx : NeBot (f ⊓ map u atTop)) : ∃ θ : ℕ → ℕ, StrictMono θ ∧ Tendsto (u ∘ θ) atTop f := by
  obtain ⟨φ, hφ⟩ := exists_seq_comp_tendsto hx
  obtain ⟨ψ, hψ, hψφ⟩ : ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ StrictMono (φ ∘ ψ) :=
    strictMono_subseq_of_tendsto_atTop hφ.1
  exact ⟨φ ∘ ψ, hψφ, hφ.2.comp hψ.tendsto_atTop⟩

end Filter
