/-
Copyright (c) 2020 Jean Lo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean Lo
-/
import Mathlib.Logic.Function.Iterate
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Algebra.Order.Monoid.Submonoid

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

Additionally, we define such constructions as the (forward) orbit, a
semiconjugacy between flows, a factor of a flow, the restriction of a
flow onto an invariant subset, and the time-reversal of a flow by a group.
-/


open Set Function Filter

/-!
### Invariant sets
-/
section Invariant

variable {τ : Type*} {α : Type*}

/-- A set `s ⊆ α` is invariant under `ϕ : τ → α → α` if `ϕ t s ⊆ s` for all `t` in `τ`. -/
def IsInvariant (ϕ : τ → α → α) (s : Set α) : Prop :=
  ∀ t, MapsTo (ϕ t) s s

variable (ϕ : τ → α → α) (s : Set α)

theorem isInvariant_iff_image : IsInvariant ϕ s ↔ ∀ t, ϕ t '' s ⊆ s := by
  simp_rw [IsInvariant, mapsTo_iff_image_subset]

/-- A set `s ⊆ α` is forward-invariant under `ϕ : τ → α → α` if `ϕ t s ⊆ s` for all `t ≥ 0`. -/
def IsFwInvariant [Preorder τ] [Zero τ] (ϕ : τ → α → α) (s : Set α) : Prop :=
  ∀ ⦃t⦄, 0 ≤ t → MapsTo (ϕ t) s s

theorem IsInvariant.isFwInvariant [Preorder τ] [Zero τ] {ϕ : τ → α → α} {s : Set α}
    (h : IsInvariant ϕ s) : IsFwInvariant ϕ s := fun t _ht => h t

/-- If `τ` is a `CanonicallyOrderedAdd` monoid (e.g., `ℕ` or `ℝ≥0`), then the notions
`IsFwInvariant` and `IsInvariant` are equivalent. -/
theorem IsFwInvariant.isInvariant [AddMonoid τ] [PartialOrder τ] [CanonicallyOrderedAdd τ]
    {ϕ : τ → α → α} {s : Set α}
    (h : IsFwInvariant ϕ s) : IsInvariant ϕ s := fun t => h (zero_le t)

/-- If `τ` is a `CanonicallyOrderedAdd` monoid (e.g., `ℕ` or `ℝ≥0`), then the notions
`IsFwInvariant` and `IsInvariant` are equivalent. -/
theorem isFwInvariant_iff_isInvariant [AddMonoid τ] [PartialOrder τ] [CanonicallyOrderedAdd τ]
    {ϕ : τ → α → α} {s : Set α} :
    IsFwInvariant ϕ s ↔ IsInvariant ϕ s :=
  ⟨IsFwInvariant.isInvariant, IsInvariant.isFwInvariant⟩

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

@[continuity, fun_prop]
protected theorem continuous {β : Type*} [TopologicalSpace β] {t : β → τ} (ht : Continuous t)
    {f : β → α} (hf : Continuous f) : Continuous fun x => ϕ (t x) (f x) :=
  ϕ.cont'.comp (ht.prodMk hf)

alias _root_.Continuous.flow := Flow.continuous

theorem map_add (t₁ t₂ : τ) (x : α) : ϕ (t₁ + t₂) x = ϕ t₁ (ϕ t₂ x) := ϕ.map_add' _ _ _

@[simp]
theorem map_zero : ϕ 0 = id := funext ϕ.map_zero'

theorem map_zero_apply (x : α) : ϕ 0 x = x := ϕ.map_zero' x

/-- Iterations of a continuous function from a topological space `α`
to itself defines a semiflow by `ℕ` on `α`. -/
def fromIter {g : α → α} (h : Continuous g) : Flow ℕ α where
  toFun n x := g^[n] x
  cont' := continuous_prod_of_discrete_left.mpr (Continuous.iterate h)
  map_add' := iterate_add_apply _
  map_zero' _x := rfl

/-- Restriction of a flow onto an invariant set. -/
def restrict {s : Set α} (h : IsInvariant ϕ s) : Flow τ (↥s) where
  toFun t := (h t).restrict _ _ _
  cont' := (ϕ.continuous continuous_fst continuous_subtype_val.snd').subtype_mk _
  map_add' _ _ _ := Subtype.ext (map_add _ _ _ _)
  map_zero' _ := Subtype.ext (map_zero_apply _ _)

@[simp]
theorem coe_restrict_apply {s : Set α} (h : IsInvariant ϕ s) (t : τ) (x : s) :
    restrict ϕ h t x = ϕ t x := rfl

/-- Convert a flow to an additive monoid action. -/
def toAddAction : AddAction τ α where
  vadd      := ϕ
  add_vadd  := ϕ.map_add'
  zero_vadd := ϕ.map_zero'

/-- Convert a flow by `τ` to a flow by an additive submonoid of `τ`. -/
def toAddSubmonoidFlow (S : AddSubmonoid τ) : Flow S α where
  toFun t x := ϕ t x
  cont' := ϕ.continuous (continuous_subtype_val.comp continuous_fst) continuous_snd
  map_add' t₁ t₂ x := ϕ.map_add' t₁ t₂ x
  map_zero' := ϕ.map_zero'

theorem toAddSubmonoidFlow_apply (S : AddSubmonoid τ) (t : S) (x : α) :
    toAddSubmonoidFlow ϕ S t x = ϕ t x := rfl

section Orbit

/-- The orbit of a point under a flow. -/
def orbit (x : α) : Set α := ϕ.toAddAction.orbit _ x

@[simp]
theorem orbit_eq_range (x : α) : ϕ.orbit x = Set.range (fun t => ϕ t x) := rfl

theorem mem_orbit_iff {x₁ x₂ : α} : x₂ ∈ orbit ϕ x₁ ↔ ∃ t : τ, ϕ t x₁ = x₂ :=
  ϕ.toAddAction.mem_orbit_iff

theorem mem_orbit (x : α) {t : τ} : ϕ t x ∈ orbit ϕ x := ϕ.toAddAction.mem_orbit ..

theorem mem_orbit_self (x : α) : x ∈ orbit ϕ x := ϕ.toAddAction.mem_orbit_self x

theorem orbit_nonempty (x : α) : Set.Nonempty (orbit ϕ x) := ϕ.toAddAction.orbit_nonempty x

theorem mem_orbit_of_mem_orbit {x₁ x₂ : α} (t : τ) (h : x₂ ∈ orbit ϕ x₁) : ϕ t x₂ ∈ orbit ϕ x₁ :=
  ϕ.toAddAction.mem_orbit_of_mem_orbit t h

/-- The orbit of a point under a flow `ϕ` is invariant under `ϕ`. -/
theorem isInvariant_orbit (x : α) : IsInvariant ϕ (orbit ϕ x) :=
  fun t _ => ϕ.toAddAction.mem_orbit_of_mem_orbit t

theorem orbit_restrict (s : Set α) (hs : IsInvariant ϕ s) (x : s) :
    orbit (ϕ.restrict hs) x = Subtype.val ⁻¹' orbit ϕ x :=
  Set.ext (fun x => by simp [orbit_eq_range, Subtype.ext_iff])

variable [Preorder τ] [AddLeftMono τ]

/-- Convert a flow by `τ` to a flow by the submonoid of nonnegative elements of `τ`. -/
def fw : Flow (AddSubmonoid.nonneg τ) α := ϕ.toAddSubmonoidFlow (AddSubmonoid.nonneg τ)

/-- The forward orbit of a point under a flow. -/
def fwOrbit (x : α) : Set α := ϕ.fw.orbit x

@[simp]
theorem fwOrbit_eq_nonneg_range (x : α) :
    ϕ.fwOrbit x = Set.range (fun t : {t : τ // 0 ≤ t} => ϕ t x) := rfl

/-- The forward orbit of a point under a flow `ϕ` is forward invariant under `ϕ`. -/
theorem isFwInvariant_fwOrbit (x : α) : IsFwInvariant ϕ (ϕ.fwOrbit x) :=
  fun s hs => IsInvariant.isFwInvariant (isInvariant_orbit ϕ.fw x) (t := ⟨s, hs⟩) hs

/-- The forward orbit of a point `x` is contained in the orbit of `x`. -/
theorem fwOrbit_subset_orbit (x : α) : ϕ.fwOrbit x ⊆ ϕ.orbit x :=
  ϕ.toAddAction.orbit_addSubmonoid_subset (AddSubmonoid.nonneg τ) x

theorem mem_orbit_of_mem_fwOrbit {x y : α} (h : x ∈ (ϕ.fwOrbit y)) : x ∈ ϕ.orbit y :=
  ϕ.fwOrbit_subset_orbit y h

end Orbit

variable {β : Type*} [TopologicalSpace β] (ψ : Flow τ β)
  {γ : Type*} [TopologicalSpace γ] (χ : Flow τ γ)

namespace ContinuousMap

/-- Given flows `ϕ` by `τ` on `α` and `ψ` by `τ` on `β`, a continuous map `π : α → β` is called a
*semiconjugacy* from `ϕ` to `ψ` if `π` is surjective and `π ∘ (ϕ t) = (ψ t) ∘ π` for all `t : τ`. -/
structure IsSemiconjugacy (π : ContinuousMap α β) (ϕ : Flow τ α) (ψ : Flow τ β) : Prop where
  surj : Function.Surjective π
  semiconj : ∀ t, Function.Semiconj π (ϕ t) (ψ t)

/-- The composition of semiconjugacies is a semiconjugacy. -/
theorem IsSemiconjugacy.comp {π₁ : ContinuousMap α β} {π₂ : ContinuousMap β γ}
    (h : IsSemiconjugacy π₁ ϕ ψ) (g : IsSemiconjugacy π₂ ψ χ) : IsSemiconjugacy (π₂.comp π₁) ϕ χ :=
  ⟨by simp [g.surj.comp h.surj], fun t => by simp [(g.semiconj t).comp_left (h.semiconj t)]⟩

/-- The identity is a semiconjugacy from `ϕ` to `ψ` if and only if `ϕ` and `ψ` are equal. -/
theorem isSemiconjugacy_id_iff_eq (ϕ ψ : Flow τ α) : IsSemiconjugacy (ContinuousMap.id α)
    ϕ ψ ↔ ϕ = ψ :=
  ⟨fun h => ϕ.ext h.semiconj, fun h => Eq.recOn h ⟨surjective_id, by simp [Semiconj.id_left]⟩⟩

end ContinuousMap

/-- A flow `ψ` is called a *factor* of `ϕ` if there exists a semiconjugacy from `ϕ` to `ψ`. -/
def IsFactorOf (ψ : Flow τ β) (ϕ : Flow τ α) : Prop :=
  ∃ π : ContinuousMap α β, ContinuousMap.IsSemiconjugacy π ϕ ψ

theorem _root_.ContinuousMap.IsSemiconjugacy.isFactorOf {π : ContinuousMap α β}
    (h : ContinuousMap.IsSemiconjugacy π ϕ ψ) : IsFactorOf ψ ϕ := ⟨π, h⟩

/-- Transitivity of factors of flows. -/
theorem IsFactorOf.trans (h₁ : IsFactorOf ϕ ψ) (h₂ : IsFactorOf ψ χ) : IsFactorOf ϕ χ :=
  h₁.elim fun k hk => h₂.elim fun f hf => ⟨k.comp f, hf.comp χ ψ ϕ hk⟩

/-- Every flow is a factor of itself. -/
theorem IsFactorOf.self : IsFactorOf ϕ ϕ :=
  ⟨ContinuousMap.id α, (ContinuousMap.isSemiconjugacy_id_iff_eq ϕ ϕ).mpr (by rfl)⟩

end Flow

namespace Flow

variable {τ : Type*} [AddCommGroup τ] [TopologicalSpace τ] [IsTopologicalAddGroup τ]
  {α : Type*} [TopologicalSpace α] (ϕ : Flow τ α)

theorem isInvariant_iff_image_eq (s : Set α) : IsInvariant ϕ s ↔ ∀ t, ϕ t '' s = s :=
  (isInvariant_iff_image _ _).trans
    (Iff.intro
      (fun h t => Subset.antisymm (h t) fun _ hx => ⟨_, h (-t) ⟨_, hx, rfl⟩, by simp [← map_add]⟩)
      fun h t => by rw [h t])

/-- The time-reversal of a flow `ϕ` by a (commutative, additive) group
is defined `ϕ.reverse t x = ϕ (-t) x`. -/
def reverse : Flow τ α where
  toFun t := ϕ (-t)
  cont' := ϕ.continuous continuous_fst.neg continuous_snd
  map_add' _ _ _ := by rw [neg_add, map_add]
  map_zero' _ := by rw [neg_zero, map_zero_apply]

@[continuity, fun_prop]
theorem continuous_toFun (t : τ) : Continuous (ϕ.toFun t) := by
  fun_prop

/-- The map `ϕ t` as a homeomorphism. -/
def toHomeomorph (t : τ) : (α ≃ₜ α) where
  toFun := ϕ t
  invFun := ϕ (-t)
  left_inv x := by rw [← map_add, neg_add_cancel, map_zero_apply]
  right_inv x := by rw [← map_add, add_neg_cancel, map_zero_apply]

theorem image_eq_preimage (t : τ) (s : Set α) : ϕ t '' s = ϕ (-t) ⁻¹' s :=
  (ϕ.toHomeomorph t).toEquiv.image_eq_preimage s

end Flow
