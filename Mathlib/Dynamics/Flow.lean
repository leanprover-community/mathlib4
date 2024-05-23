/-
Copyright (c) 2020 Jean Lo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean Lo
-/
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Logic.Function.Iterate

#align_import dynamics.flow from "leanprover-community/mathlib"@"717c073262cd9d59b1a1dcda7e8ab570c5b63370"

/-!
# Flows and invariant sets

This file defines a flow on a topological space `α` by a topological
monoid `τ` as a continuous monoid-action of `τ` on `α`. Anticipating the
cases where `τ` is one of `ℕ`, `ℤ`, `ℝ⁺`, or `ℝ`, we use additive
notation for the monoids, though the definition does not require
commutativity.

A subset `s` of `α` is invariant under a family of maps `ϕₜ : α → α`
if `ϕₜ s ⊆ s` for all `t`. In many cases `ϕ` will be a flow on
`α`. For the cases where `ϕ` is a flow by an ordered (additive,
commutative) monoid, we additionally define forward invariance, where
`t` ranges over those elements which are nonnegative.

Additionally, we define such constructions as the restriction of a
flow onto an invariant subset, and the time-reversal of a flow by a
group.
-/


open Set Function Filter

/-!
### Invariant sets
-/
section Invariant

variable {τ : Type*} {α : Type*}

/-- A set `s ⊆ α` is invariant under `ϕ : τ → α → α` if
    `ϕ t s ⊆ s` for all `t` in `τ`. -/
def IsInvariant (ϕ : τ → α → α) (s : Set α) : Prop :=
  ∀ t, MapsTo (ϕ t) s s
#align is_invariant IsInvariant

variable (ϕ : τ → α → α) (s : Set α)

theorem isInvariant_iff_image : IsInvariant ϕ s ↔ ∀ t, ϕ t '' s ⊆ s := by
  simp_rw [IsInvariant, mapsTo']
#align is_invariant_iff_image isInvariant_iff_image

/-- A set `s ⊆ α` is forward-invariant under `ϕ : τ → α → α` if
    `ϕ t s ⊆ s` for all `t ≥ 0`. -/
def IsFwInvariant [Preorder τ] [Zero τ] (ϕ : τ → α → α) (s : Set α) : Prop :=
  ∀ ⦃t⦄, 0 ≤ t → MapsTo (ϕ t) s s
#align is_fw_invariant IsFwInvariant

theorem IsInvariant.isFwInvariant [Preorder τ] [Zero τ] {ϕ : τ → α → α} {s : Set α}
    (h : IsInvariant ϕ s) : IsFwInvariant ϕ s := fun t _ht => h t
#align is_invariant.is_fw_invariant IsInvariant.isFwInvariant

/-- If `τ` is a `CanonicallyOrderedAddCommMonoid` (e.g., `ℕ` or `ℝ≥0`), then the notions
`IsFwInvariant` and `IsInvariant` are equivalent. -/
theorem IsFwInvariant.isInvariant [CanonicallyOrderedAddCommMonoid τ] {ϕ : τ → α → α} {s : Set α}
    (h : IsFwInvariant ϕ s) : IsInvariant ϕ s := fun t => h (zero_le t)
#align is_fw_invariant.is_invariant IsFwInvariant.isInvariant

/-- If `τ` is a `CanonicallyOrderedAddCommMonoid` (e.g., `ℕ` or `ℝ≥0`), then the notions
`IsFwInvariant` and `IsInvariant` are equivalent. -/
theorem isFwInvariant_iff_isInvariant [CanonicallyOrderedAddCommMonoid τ] {ϕ : τ → α → α}
    {s : Set α} :
    IsFwInvariant ϕ s ↔ IsInvariant ϕ s :=
  ⟨IsFwInvariant.isInvariant, IsInvariant.isFwInvariant⟩
#align is_fw_invariant_iff_is_invariant isFwInvariant_iff_isInvariant

end Invariant

/-!
### Flows
-/

/-- A flow on a topological space `α` by an additive topological
    monoid `τ` is a continuous monoid action of `τ` on `α`. -/
structure Flow (τ : Type*) [TopologicalSpace τ] [AddMonoid τ] [ContinuousAdd τ] (α : Type*)
  [TopologicalSpace α] where
  /-- The map `τ → α → α` underlying a flow of `τ` on `α`. -/
  toFun : τ → α → α
  cont' : Continuous (uncurry toFun)
  map_add' : ∀ t₁ t₂ x, toFun (t₁ + t₂) x = toFun t₁ (toFun t₂ x)
  map_zero' : ∀ x, toFun 0 x = x
#align flow Flow

namespace Flow

variable {τ : Type*} [AddMonoid τ] [TopologicalSpace τ] [ContinuousAdd τ]
  {α : Type*} [TopologicalSpace α] (ϕ : Flow τ α)

instance : Inhabited (Flow τ α) :=
  ⟨{  toFun := fun _ x => x
      cont' := continuous_snd
      map_add' := fun _ _ _ => rfl
      map_zero' := fun _ => rfl }⟩

instance : CoeFun (Flow τ α) fun _ => τ → α → α := ⟨Flow.toFun⟩

@[ext]
theorem ext : ∀ {ϕ₁ ϕ₂ : Flow τ α}, (∀ t x, ϕ₁ t x = ϕ₂ t x) → ϕ₁ = ϕ₂
  | ⟨f₁, _, _, _⟩, ⟨f₂, _, _, _⟩, h => by
    congr
    funext
    exact h _ _
#align flow.ext Flow.ext

@[continuity]
protected theorem continuous {β : Type*} [TopologicalSpace β] {t : β → τ} (ht : Continuous t)
    {f : β → α} (hf : Continuous f) : Continuous fun x => ϕ (t x) (f x) :=
  ϕ.cont'.comp (ht.prod_mk hf)
#align flow.continuous Flow.continuous

alias _root_.Continuous.flow := Flow.continuous
#align continuous.flow Continuous.flow

theorem map_add (t₁ t₂ : τ) (x : α) : ϕ (t₁ + t₂) x = ϕ t₁ (ϕ t₂ x) := ϕ.map_add' _ _ _
#align flow.map_add Flow.map_add

@[simp]
theorem map_zero : ϕ 0 = id := funext ϕ.map_zero'
#align flow.map_zero Flow.map_zero

theorem map_zero_apply (x : α) : ϕ 0 x = x := ϕ.map_zero' x
#align flow.map_zero_apply Flow.map_zero_apply

/-- Iterations of a continuous function from a topological space `α`
    to itself defines a semiflow by `ℕ` on `α`. -/
def fromIter {g : α → α} (h : Continuous g) : Flow ℕ α where
  toFun n x := g^[n] x
  cont' := continuous_prod_of_discrete_left.mpr (Continuous.iterate h)
  map_add' := iterate_add_apply _
  map_zero' _x := rfl
#align flow.from_iter Flow.fromIter

/-- Restriction of a flow onto an invariant set. -/
def restrict {s : Set α} (h : IsInvariant ϕ s) : Flow τ (↥s) where
  toFun t := (h t).restrict _ _ _
  cont' := (ϕ.continuous continuous_fst continuous_subtype_val.snd').subtype_mk _
  map_add' _ _ _ := Subtype.ext (map_add _ _ _ _)
  map_zero' _ := Subtype.ext (map_zero_apply _ _)
#align flow.restrict Flow.restrict

end Flow

namespace Flow

variable {τ : Type*} [AddCommGroup τ] [TopologicalSpace τ] [TopologicalAddGroup τ]
  {α : Type*} [TopologicalSpace α] (ϕ : Flow τ α)

theorem isInvariant_iff_image_eq (s : Set α) : IsInvariant ϕ s ↔ ∀ t, ϕ t '' s = s :=
  (isInvariant_iff_image _ _).trans
    (Iff.intro
      (fun h t => Subset.antisymm (h t) fun _ hx => ⟨_, h (-t) ⟨_, hx, rfl⟩, by simp [← map_add]⟩)
      fun h t => by rw [h t])
#align flow.is_invariant_iff_image_eq Flow.isInvariant_iff_image_eq

/-- The time-reversal of a flow `ϕ` by a (commutative, additive) group
    is defined `ϕ.reverse t x = ϕ (-t) x`. -/
def reverse : Flow τ α where
  toFun t := ϕ (-t)
  cont' := ϕ.continuous continuous_fst.neg continuous_snd
  map_add' _ _ _ := by dsimp; rw [neg_add, map_add]
  map_zero' _ := by dsimp; rw [neg_zero, map_zero_apply]
#align flow.reverse Flow.reverse

-- Porting note: add @continuity to Flow.toFun so that these works:
-- Porting note: Homeomorphism.continuous_toFun  : Continuous toFun  := by continuity
-- Porting note: Homeomorphism.continuous_invFun : Continuous invFun := by continuity
@[continuity]
theorem continuous_toFun (t : τ) : Continuous (ϕ.toFun t) := by
  rw [← curry_uncurry ϕ.toFun]
  apply continuous_curry
  exact ϕ.cont'

/-- The map `ϕ t` as a homeomorphism. -/
def toHomeomorph (t : τ) : (α ≃ₜ α) where
  toFun := ϕ t
  invFun := ϕ (-t)
  left_inv x := by rw [← map_add, neg_add_self, map_zero_apply]
  right_inv x := by rw [← map_add, add_neg_self, map_zero_apply]
#align flow.to_homeomorph Flow.toHomeomorph

theorem image_eq_preimage (t : τ) (s : Set α) : ϕ t '' s = ϕ (-t) ⁻¹' s :=
  (ϕ.toHomeomorph t).toEquiv.image_eq_preimage s
#align flow.image_eq_preimage Flow.image_eq_preimage

end Flow
