/-
Copyright (c) 2024 Edward van de Meent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Edward van de Meent.
-/
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Topology.Bornology.Basic
import Mathlib.Tactic

/-!
# General Pseudo-Metric Spaces

In this file we introduce `GPseudoMetricSpace`.
This differs from `PseudoMetricSpace` by not requiring that the codomain of the metric be `ℝ`,
instead only requiring that it is an (additive) commutative monoid, with a linear ordering that
respects sensible assumptions about interactions between `+` and `≤`.
## Main Definitions

- `GDist β`: Endows a space `β` with a function `gdist β x y`.
- `GPseudoMetricSpace α β`: A space `α` endowed with a generic distance function with codomain `β`,
which may be equal to 0 for non-equal elements. the distance function is 0 for equal elements,
is commutative in its arguments, and satisifies the triangle inequality.
-/

open Set Filter Bornology
open scoped BigOperators Topology

/-- Construct a bornology from a generic distance function and metric space axioms. -/
@[reducible]
def Bornology.ofGDist {α : Type*} {β : Type*} [LinearOrderedAddCommMonoid β]
    (gdist : α → α → β) (gdist_comm : ∀ x y, gdist x y = gdist y x)
    (gdist_triangle : ∀ x y z, gdist x z ≤ gdist x y + gdist y z) : Bornology α :=
  Bornology.ofBounded { s : Set α | ∃ C, ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → gdist x y ≤ C }
    ⟨0,fun x hx y => hx.elim⟩
    (fun s ⟨c, hc⟩ t h => ⟨c, fun x hx y hy => hc (h hx) (h hy)⟩)
    (fun s hs t ht => by
      rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
      · rwa [empty_union]
      rcases t.eq_empty_or_nonempty with rfl | ⟨y, hy⟩
      · rwa [union_empty]
      rsuffices ⟨C, hC⟩ : ∃ C, ∀ z ∈ s ∪ t, gdist x z ≤ C
      · refine ⟨C + C, fun a ha b hb => (gdist_triangle a x b).trans ?_⟩
        simpa only [gdist_comm] using add_le_add (hC _ ha) (hC _ hb)
      rcases hs with ⟨Cs, hs⟩; rcases ht with ⟨Ct, ht⟩
      refine ⟨max Cs (gdist x y + Ct), fun z hz => hz.elim
        (fun hz => (hs hx hz).trans (le_max_left _ _))
        (fun hz => (gdist_triangle x y z).trans <|
          (add_le_add le_rfl (ht hy hz)).trans (le_max_right _ _))⟩)
    fun z => ⟨gdist z z, forall_eq.2 <| forall_eq.2 le_rfl⟩

/-the generic distance function on a space α which returns an element of type β -/
@[ext]
class GDist (α : Type*) (β : Type*) [LinearOrderedAddCommMonoid β] where
  protected gdist : α → α → β


/-the generic distance function on a space α which returns an element of type β,
with an explicit type parameter β for ease of inferring the return type-/
def gdist (β : Type*) [LinearOrderedAddCommMonoid β]{α :Type*} [GDist α β] (x y: α) : β :=
  GDist.gdist x y

export GDist (gdist)

variable {α : Type*} {β : Type*}
/- -/
private theorem gdist_nonneg' [LinearOrderedAddCommMonoid β] {x y : α} (gdist : α → α → β)
    (gdist_self : ∀ x : α, gdist x x = 0) (gdist_comm : ∀ x y : α, gdist x y = gdist y x)
    (gdist_triangle : ∀ x y z : α, gdist x z ≤ gdist x y + gdist y z) : 0 ≤ gdist x y := by
  have : 0 ≤ gdist x y + gdist x y :=
    calc 0 = gdist x x := (gdist_self _).symm
    _ ≤ gdist x y + gdist y x := gdist_triangle _ _ _
    _ = gdist x y + gdist x y:= by rw [gdist_comm]
  exact nonneg_add_self_iff.mp this

class GPseudoMetricSpace
    (α : Type*) (β : Type*) [LinearOrderedAddCommMonoid β] extends GDist α β where
  gdist_self : ∀ x : α, gdist x x = 0
  gdist_comm : ∀ x y : α, gdist x y = gdist y x

lemma cobounded_sets [LinearOrderedAddCommMonoid β] [GPseudoMetricSpace α β] (gdist : α → α → β)
    (gdist_comm : ∀ x y, gdist x y = gdist y x)
    (gdist_triangle : ∀ x y z, gdist x z ≤ gdist x y + gdist y z):
    (@Bornology.cobounded α (Bornology.ofGDist (gdist) gdist_comm gdist_triangle)
    ).sets =
    { (s:Set α) | ∃ (C : β), ∀ x ∈ sᶜ, ∀ y ∈ sᶜ, (gdist x y ≤ C) } :=
  by intros; rfl


@[ext]
theorem GPseudoMetricSpace.ext [LinearOrderedAddCommMonoid β] {m m' : GPseudoMetricSpace α β}
    (h : m.toGDist = m'.toGDist) : m = m' := by
  cases' m with d _ _ _ B hB
  cases' m' with d' _ _ _ B' hB'
  obtain rfl : d = d' := h
  congr
