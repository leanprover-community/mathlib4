/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.MeasureTheory.MeasurableSpace.Defs
/-!
# σ-algebra of sets invariant under a self-map

In this file we define `MeasurableSpace.invariants (f : α → α)`
to be the σ-algebra of sets `s : Set α` such that
- `s` is measurable w.r.t. the canonical σ-algebra on `α`;
- and `f ⁻ˢ' s = s`.
-/

open Set Function
open scoped MeasureTheory

namespace MeasurableSpace

variable {α : Type*}

/-- Given a self-map `f : α → α`,
`invariants f` is the σ-algebra of measurable sets that are invariant under `f`.

A set `s` is `(invariants f)`-measurable
iff it is measurable w.r.t. the canonical σ-algebra on `α` and `f ⁻¹' s = s`. -/
def invariants [m : MeasurableSpace α] (f : α → α) : MeasurableSpace α :=
  { m ⊓ ⟨fun s ↦ f ⁻¹' s = s, by simp, by simp, fun f hf ↦ by simp [hf]⟩ with
    MeasurableSet' := fun s ↦ MeasurableSet[m] s ∧ f ⁻¹' s = s }

variable [MeasurableSpace α]

/-- A set `s` is `(invariants f)`-measurable
iff it is measurable w.r.t. the canonical σ-algebra on `α` and `f ⁻¹' s = s`. -/
theorem measurableSet_invariants {f : α → α} {s : Set α} :
    MeasurableSet[invariants f] s ↔ MeasurableSet s ∧ f ⁻¹' s = s :=
  .rfl

@[simp]
theorem invariants_id : invariants (id : α → α) = ‹MeasurableSpace α› :=
  ext fun _ ↦ ⟨And.left, fun h ↦ ⟨h, rfl⟩⟩

theorem invariants_le (f : α → α) : invariants f ≤ ‹MeasurableSpace α› := fun _ ↦ And.left

theorem inf_le_invariants_comp (f g : α → α) :
    invariants f ⊓ invariants g ≤ invariants (f ∘ g) := fun s hs ↦
  ⟨hs.1.1, by rw [preimage_comp, hs.1.2, hs.2.2]⟩

theorem le_invariants_iterate (f : α → α) (n : ℕ) :
    invariants f ≤ invariants (f^[n]) := by
  induction n with
  | zero => simp [invariants_le]
  | succ n ihn => exact le_trans (le_inf ihn le_rfl) (inf_le_invariants_comp _ _)

variable {β : Type*} [MeasurableSpace β]

theorem measurable_invariants_dom {f : α → α} {g : α → β} :
    Measurable[invariants f] g ↔ Measurable g ∧ ∀ s, MeasurableSet s → (g ∘ f) ⁻¹' s = g ⁻¹' s := by
  simp only [Measurable, ← forall_and]; rfl

theorem measurable_invariants_of_semiconj {fa : α → α} {fb : β → β} {g : α → β} (hg : Measurable g)
    (hfg : Semiconj g fa fb) : @Measurable _ _ (invariants fa) (invariants fb) g := fun s hs ↦
  ⟨hg hs.1, by rw [← preimage_comp, hfg.comp_eq, preimage_comp, hs.2]⟩

theorem comp_eq_of_measurable_invariants {f : α → α} {g : α → β} [MeasurableSingletonClass β]
    (h : Measurable[invariants f] g) : g ∘ f = g := by
  funext x
  suffices x ∈ f⁻¹' (g⁻¹' {g x}) by simpa
  rw [(h <| measurableSet_singleton (g x)).2, Set.mem_preimage, Set.mem_singleton_iff]

end MeasurableSpace
