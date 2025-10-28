/-
Copyright (c) 2020 Jean Lo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean Lo
-/
import Mathlib.Logic.Function.Iterate
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Group.Defs
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
def IsForwardInvariant [Preorder τ] [Zero τ] (ϕ : τ → α → α) (s : Set α) : Prop :=
  ∀ ⦃t⦄, 0 ≤ t → MapsTo (ϕ t) s s

@[deprecated (since := "2025-09-25")] alias IsFwInvariant := IsForwardInvariant

theorem IsInvariant.isForwardInvariant [Preorder τ] [Zero τ] {ϕ : τ → α → α} {s : Set α}
    (h : IsInvariant ϕ s) : IsForwardInvariant ϕ s := fun t _ht => h t

@[deprecated (since := "2025-09-25")]
alias IsInvariant.isFwInvariant := IsInvariant.isForwardInvariant

/-- If `τ` is a `CanonicallyOrderedAdd` monoid (e.g., `ℕ` or `ℝ≥0`), then the notions
`IsForwardInvariant` and `IsInvariant` are equivalent. -/
theorem IsForwardInvariant.isInvariant [AddMonoid τ] [PartialOrder τ] [CanonicallyOrderedAdd τ]
    {ϕ : τ → α → α} {s : Set α}
    (h : IsForwardInvariant ϕ s) : IsInvariant ϕ s := fun t => h (zero_le t)

@[deprecated (since := "2025-09-25")]
alias IsFwInvariant.isInvariant := IsForwardInvariant.isInvariant

/-- If `τ` is a `CanonicallyOrderedAdd` monoid (e.g., `ℕ` or `ℝ≥0`), then the notions
`IsForwardInvariant` and `IsInvariant` are equivalent. -/
theorem isForwardInvariant_iff_isInvariant [AddMonoid τ] [PartialOrder τ] [CanonicallyOrderedAdd τ]
    {ϕ : τ → α → α} {s : Set α} :
    IsForwardInvariant ϕ s ↔ IsInvariant ϕ s :=
  ⟨IsForwardInvariant.isInvariant, IsInvariant.isForwardInvariant⟩

@[deprecated (since := "2025-09-25")]
alias isFwInvariant_iff_isInvariant := isForwardInvariant_iff_isInvariant

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

/-- Restrict a flow by `τ` to a flow by an additive submonoid of `τ`. -/
def restrictAddSubmonoid (S : AddSubmonoid τ) : Flow S α where
  toFun t x := ϕ t x
  cont' := ϕ.continuous (continuous_subtype_val.comp continuous_fst) continuous_snd
  map_add' t₁ t₂ x := ϕ.map_add' t₁ t₂ x
  map_zero' := ϕ.map_zero'

theorem restrictAddSubmonoid_apply (S : AddSubmonoid τ) (t : S) (x : α) :
    restrictAddSubmonoid ϕ S t x = ϕ t x := rfl

section Orbit

/-- The orbit of a point under a flow. -/
def orbit (x : α) : Set α := @AddAction.orbit _ _ ϕ.toAddAction.toVAdd x

theorem orbit_eq_range (x : α) : orbit ϕ x = Set.range (fun t => ϕ t x) := rfl

theorem mem_orbit_iff {x₁ x₂ : α} : x₂ ∈ orbit ϕ x₁ ↔ ∃ t : τ, ϕ t x₁ = x₂ := Iff.rfl

theorem mem_orbit (x : α) (t : τ) : ϕ t x ∈ orbit ϕ x :=
  @AddAction.mem_orbit _ _ ϕ.toAddAction.toVAdd x t

theorem mem_orbit_self (x : α) : x ∈ orbit ϕ x := ϕ.toAddAction.mem_orbit_self x

theorem nonempty_orbit (x : α) : Set.Nonempty (orbit ϕ x) := ϕ.toAddAction.nonempty_orbit x

theorem mem_orbit_of_mem_orbit {x₁ x₂ : α} (t : τ) (h : x₂ ∈ orbit ϕ x₁) : ϕ t x₂ ∈ orbit ϕ x₁ :=
  ϕ.toAddAction.mem_orbit_of_mem_orbit t h

/-- The orbit of a point under a flow `ϕ` is invariant under `ϕ`. -/
theorem isInvariant_orbit (x : α) : IsInvariant ϕ (orbit ϕ x) :=
  fun t _ => ϕ.toAddAction.mem_orbit_of_mem_orbit t

theorem orbit_restrict (s : Set α) (hs : IsInvariant ϕ s) (x : s) :
    orbit (ϕ.restrict hs) x = Subtype.val ⁻¹' orbit ϕ x :=
  Set.ext (fun x => by simp [orbit_eq_range, Subtype.ext_iff])

variable [Preorder τ] [AddLeftMono τ]

/-- Restrict a flow by `τ` to a flow by the additive submonoid of nonnegative elements of `τ`. -/
def restrictNonneg : Flow (AddSubmonoid.nonneg τ) α := ϕ.restrictAddSubmonoid (.nonneg τ)

/-- The forward orbit of a point under a flow. -/
def forwardOrbit (x : α) : Set α := orbit ϕ.restrictNonneg x

theorem forwardOrbit_eq_range_nonneg (x : α) :
    forwardOrbit ϕ x = Set.range (fun t : {t : τ // 0 ≤ t} => ϕ t x) := rfl

/-- The forward orbit of a point under a flow `ϕ` is forward-invariant under `ϕ`. -/
theorem isForwardInvariant_forwardOrbit (x : α) : IsForwardInvariant ϕ (forwardOrbit ϕ x) :=
  fun t h => IsInvariant.isForwardInvariant (isInvariant_orbit ϕ.restrictNonneg x) (t := ⟨t, h⟩) h

/-- The forward orbit of a point `x` is contained in the orbit of `x`. -/
theorem forwardOrbit_subset_orbit (x : α) : forwardOrbit ϕ x ⊆ orbit ϕ x :=
  ϕ.toAddAction.orbit_addSubmonoid_subset (AddSubmonoid.nonneg τ) x

theorem mem_orbit_of_mem_forwardOrbit {x₁ x₂ : α} (h : x₁ ∈ forwardOrbit ϕ x₂) : x₁ ∈ orbit ϕ x₂ :=
  ϕ.forwardOrbit_subset_orbit x₂ h

end Orbit

variable {β γ : Type*} [TopologicalSpace β] [TopologicalSpace γ] (ψ : Flow τ β) (χ : Flow τ γ)

/-- Given flows `ϕ` by `τ` on `α` and `ψ` by `τ` on `β`, a function `π : α → β` is called a
*semiconjugacy* from `ϕ` to `ψ` if `π` is continuous and surjective, and `π ∘ (ϕ t) = (ψ t) ∘ π` for
all `t : τ`. -/
structure IsSemiconjugacy (π : α → β) (ϕ : Flow τ α) (ψ : Flow τ β) : Prop where
  cont : Continuous π
  surj : Function.Surjective π
  semiconj : ∀ t, Function.Semiconj π (ϕ t) (ψ t)

/-- The composition of semiconjugacies is a semiconjugacy. -/
theorem IsSemiconjugacy.comp {π : α → β} {ρ : β → γ}
    (h₁ : IsSemiconjugacy π ϕ ψ) (h₂ : IsSemiconjugacy ρ ψ χ) : IsSemiconjugacy (ρ ∘ π) ϕ χ :=
  ⟨h₂.cont.comp h₁.cont, h₂.surj.comp h₁.surj, fun t => (h₂.semiconj t).comp_left (h₁.semiconj t)⟩

/-- The identity is a semiconjugacy from `ϕ` to `ψ` if and only if `ϕ` and `ψ` are equal. -/
theorem isSemiconjugacy_id_iff_eq (ϕ ψ : Flow τ α) : IsSemiconjugacy id ϕ ψ ↔ ϕ = ψ :=
  ⟨fun h => ext h.semiconj, fun h => h.recOn ⟨continuous_id, surjective_id, fun _ => .id_left⟩⟩

/-- A flow `ψ` is called a *factor* of `ϕ` if there exists a semiconjugacy from `ϕ` to `ψ`. -/
def IsFactorOf (ψ : Flow τ β) (ϕ : Flow τ α) : Prop := ∃ π : α → β, IsSemiconjugacy π ϕ ψ

theorem IsSemiconjugacy.isFactorOf {π : α → β} (h : IsSemiconjugacy π ϕ ψ) : IsFactorOf ψ ϕ :=
  ⟨π, h⟩

/-- Transitivity of factors of flows. -/
theorem IsFactorOf.trans (h₁ : IsFactorOf ϕ ψ) (h₂ : IsFactorOf ψ χ) : IsFactorOf ϕ χ :=
  h₁.elim fun π hπ => h₂.elim fun ρ hρ => ⟨π ∘ ρ, hρ.comp χ ψ ϕ hπ⟩

/-- Every flow is a factor of itself. -/
theorem IsFactorOf.self : IsFactorOf ϕ ϕ := ⟨id, (isSemiconjugacy_id_iff_eq ϕ ϕ).mpr (by rfl)⟩

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
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem image_eq_preimage (t : τ) (s : Set α) : ϕ t '' s = ϕ (-t) ⁻¹' s :=
  (ϕ.toHomeomorph t).toEquiv.image_eq_preimage s

end Flow
