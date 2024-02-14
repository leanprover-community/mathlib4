/-
Copyright (c) 2023 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import Mathlib.Order.Filter.Cofinite
import Mathlib.Tactic.TFAE

/-!
# Functions with finite fibers

We define the predicate `Function.HasFiniteFibers` on functions, where `Function.HasFiniteFibers f`
means that the preimage by `f` of any finite set is finite. This has been expressed as
`Tendsto f cofinite cofinite` in the past, and we prove that this is indeed equivalent in
`Function.hasFiniteFibers_iff_tendsto_cofinite`, but having a separate definition makes the
API cleaner.
-/

open Function Set Filter

variable {α α' β β' γ : Type*}

namespace Function

/-- `Function.HasFiniteFibers f` means that the preimage by `f` of any finite set is finite. We
show in `Function.hasFiniteFibers_iff_finite_fibers` that this is actually equivalent to finiteness
of fibers. -/
def HasFiniteFibers (f : α → β) : Prop :=
  ∀ b, (f ⁻¹' {b}).Finite

/-- `Function.HasFiniteFibers f` means that the preimage by `f` of any finite set is finite. We
show in `Function.hasFiniteFibers_iff_finite_fibers` that this is actually equivalent to finiteness
of fibers. -/
def HasFiniteFibersOn (f : α → β) (U : Set α) : Prop :=
  ∀ b, (f ⁻¹' {b} ∩ U).Finite

variable {f : α → β} {U : Set α}

lemma hasFiniteFibers_iff_finite_fibers : HasFiniteFibers f ↔ ∀ b, (f ⁻¹' {b}).Finite :=
  Iff.rfl

lemma hasFiniteFibersOn_iff_finite_fibers_inter : HasFiniteFibersOn f U ↔
    ∀ b, (f ⁻¹' {b} ∩ U).Finite :=
  Iff.rfl

lemma HasFiniteFibers.hasFiniteFibersOn (hf : HasFiniteFibers f) :
    HasFiniteFibersOn f U :=
  fun b ↦ (hf b).subset <| inter_subset_left _ _

lemma HasFiniteFibersOn.mono {V : Set α} (hf : HasFiniteFibersOn f U) (hUV : V ⊆ U) :
    HasFiniteFibersOn f V :=
  fun b ↦ (hf b).subset <| inter_subset_inter_right _ hUV

section NonRelative

lemma Injective.hasFiniteFibers (hf : Injective f) :
    HasFiniteFibers f :=
  fun _ ↦ (subsingleton_singleton.preimage hf).finite

lemma hasFiniteFibers_TFAE : List.TFAE
    [ HasFiniteFibers f,
      Tendsto f cofinite cofinite,
      ∀ ⦃S⦄, S.Finite → (f ⁻¹' S).Finite ] := by
  tfae_have 3 → 1
  · exact fun H y ↦ H <| finite_singleton _
  tfae_have 1 → 2
  · intro H
    simpa [Tendsto, le_cofinite_iff_eventually_ne]
  tfae_have 2 → 3
  · intro H S hS
    simpa using H hS.compl_mem_cofinite
  tfae_finish

end NonRelative

lemma hasFiniteFibersOn_TFAE : List.TFAE
    [ HasFiniteFibersOn f U,
      Tendsto f (map ((↑) : U → α) cofinite) cofinite,
      ∀ ⦃S⦄, S.Finite → (f ⁻¹' S ∩ U).Finite,
      Tendsto (U.restrict f) cofinite cofinite,
      HasFiniteFibers (U.restrict f) ] := by
  tfae_have 3 → 1
  · exact fun H y ↦ H <| finite_singleton _
  tfae_have 1 → 2
  · intro H
    simpa [Tendsto, le_cofinite_iff_eventually_ne]
  tfae_have 2 → 3
  · intro H S hS
    simpa using H hS.compl_mem_cofinite
  tfae_finish

lemma hasFiniteFibersOn_iff_hasFiniteFibers :
    HasFiniteFibersOn f U ↔ HasFiniteFibers (U.restrict f) :=
  sorry

lemma InjOn.hasFiniteFibersOn {U : Set α} (hf : InjOn f U) :
    HasFiniteFibersOn f U :=
  sorry

-- OLD

lemma hasFiniteFibers_iff_finite_preimage : HasFiniteFibers f ↔ ∀ S, S.Finite → (f ⁻¹' S).Finite :=
  Iff.rfl

lemma hasFiniteFibersOn_iff_finite_preimage_inter : HasFiniteFibersOn f U ↔
    ∀ S, S.Finite → (f ⁻¹' S ∩ U).Finite :=
  Iff.rfl

lemma HasFiniteFibers.finite_preimage (hf : HasFiniteFibers f) {S : Set β} (hS : S.Finite) :
    (f ⁻¹' S).Finite := hf hS

alias HasFiniteFibers.finite_preimage ← _root_.Set.Finite.preimage'

lemma HasFiniteFibersOn.finite_preimage_inter (hf : HasFiniteFibersOn f U) {S : Set β} (hS : S.Finite) :
    (f ⁻¹' S ∩ U).Finite := hf hS

alias HasFiniteFibersOn.finite_preimage_inter ← _root_.Set.Finite.preimage_inter

lemma HasFiniteFibersOn.finite_preimage {S : Set β} (hf : HasFiniteFibersOn f (f ⁻¹' S))
    (hS : S.Finite) : (f ⁻¹' S).Finite := inter_self (f ⁻¹' S) ▸ hf hS

-- to be renamed `Set.Finite.preimage`
alias HasFiniteFibersOn.finite_preimage ← _root_.Set.Finite.preimage''

lemma HasFiniteFibers.hasFiniteFibersOn (hf : HasFiniteFibers f) :
    HasFiniteFibersOn f U :=
  fun _ hS ↦ (hf hS).subset <| inter_subset_left _ _

lemma HasFiniteFibersOn.mono {V : Set α} (hf : HasFiniteFibersOn f U) (hUV : V ⊆ U) :
    HasFiniteFibersOn f V :=
  fun _ hS ↦ (hf hS).subset <| inter_subset_inter_right _ hUV

lemma HasFiniteFibers.comp {g : β → γ} (hg : HasFiniteFibers g) (hf : HasFiniteFibers f) :
    HasFiniteFibers (g ∘ f) :=
  fun _ hS ↦ (hS.preimage' hg).preimage' hf

lemma HasFiniteFibersOn.comp {g : β → γ} {V : Set β} (hg : HasFiniteFibersOn g V)
    (hf : HasFiniteFibersOn f U) (h : MapsTo f U V) :
    HasFiniteFibersOn (g ∘ f) U := by
  intro S hS
  convert (hS.preimage_inter hg).preimage_inter hf using 1
  rw [preimage_inter, inter_assoc, inter_eq_self_of_subset_right h.subset_preimage, preimage_comp]

lemma Injective.hasFiniteFibers (hf : Injective f) :
    HasFiniteFibers f :=
  fun _ hS ↦ hS.preimage <| hf.injOn _

lemma InjOn.hasFiniteFibersOn {U : Set α} (hf : InjOn f U) :
    HasFiniteFibersOn f U :=
  sorry

lemma hasFiniteFibers_TFAE : List.TFAE
    [ HasFiniteFibers f,
      Tendsto f cofinite cofinite,
      ∀ y, (f ⁻¹' {y}).Finite ] := by
  tfae_have 1 → 3
  · exact fun H y ↦ H <| finite_singleton _
  tfae_have 3 → 2
  · intro H
    simpa [Tendsto, le_cofinite_iff_eventually_ne]
  tfae_have 2 → 1
  · intro H S hS
    simpa using H hS.compl_mem_cofinite
  tfae_finish

lemma hasFiniteFibers_iff_finite_fibers : HasFiniteFibers f ↔ ∀ y, (f ⁻¹' {y}).Finite :=
  hasFiniteFibers_TFAE.out 0 2

lemma hasFiniteFibers_iff_tendsto_cofinite : HasFiniteFibers f ↔ Tendsto f cofinite cofinite :=
  hasFiniteFibers_TFAE.out 0 1

alias hasFiniteFibers_iff_tendsto_cofinite ↔ HasFiniteFibers.tendsto_cofinite _

theorem HasFiniteFibers.comap_cofinite_eq (hf : HasFiniteFibers f) :
    comap f cofinite = cofinite :=
  (comap_cofinite_le f).antisymm hf.tendsto_cofinite.le_comap

theorem HasFiniteFibers.nat_tendsto_atTop {f : ℕ → ℕ} (hf : HasFiniteFibers f) :
    Tendsto f atTop atTop :=
  Nat.cofinite_eq_atTop ▸ hf.tendsto_cofinite

lemma HasFiniteFibers.prod_map {g : α' → β'} (hf : HasFiniteFibers f) (hg : HasFiniteFibers g) :
    HasFiniteFibers (Prod.map f g) := by
  rw [hasFiniteFibers_iff_tendsto_cofinite, ← coprod_cofinite, ← coprod_cofinite] at *
  exact hf.prod_map_coprod hg

lemma HasFiniteFibers.sum_map {g : α' → β'} (hf : HasFiniteFibers f) (hg : HasFiniteFibers g) :
    HasFiniteFibers (Sum.map f g) := by
  rw [hasFiniteFibers_iff_tendsto_cofinite, cofinite_sum, cofinite_sum] at *
  exact tendsto_sup_sup (tendsto_map' <| tendsto_map.comp hf) (tendsto_map' <| tendsto_map.comp hg)

end Function
