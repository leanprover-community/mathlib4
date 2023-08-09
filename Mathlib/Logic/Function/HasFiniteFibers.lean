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

open Function Set Filter List

namespace Function

/-- `Function.HasFiniteFibers f` means that the preimage by `f` of any finite set is finite. We
show in `Function.hasFiniteFibers_iff_finite_fibers` that this is actually equivalent to finiteness
of fibers. -/
def HasFiniteFibers (f : α → β) : Prop :=
  ∀ ⦃S : Set β⦄, S.Finite → (f ⁻¹' S).Finite

variable {f : α → β}

lemma hasFiniteFibers_iff_finite_preimage : HasFiniteFibers f ↔ ∀ S, S.Finite → (f ⁻¹' S).Finite :=
  Iff.rfl

lemma HasFiniteFibers.finite_preimage (hf : HasFiniteFibers f) {S : Set β} (hS : S.Finite) :
    (f ⁻¹' S).Finite := hf hS

alias HasFiniteFibers.finite_preimage ← _root_.Set.Finite.preimage'

lemma HasFiniteFibers.comp {g : β → γ} (hg : HasFiniteFibers g) (hf : HasFiniteFibers f) :
    HasFiniteFibers (g ∘ f) :=
  fun _ hS ↦ (hS.preimage' hg).preimage' hf

lemma Injective.hasFiniteFibers (hf : Injective f) :
    HasFiniteFibers f :=
  fun _ hS ↦ hS.preimage <| hf.injOn _

lemma hasFiniteFibers_TFAE : TFAE
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
