import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Order.IntermediateValue

/-!
# Equivariant Maps and Antipodal Zero-Node Theorems

This module formalizes zero-node existence for continuous odd fields under domain involutions
along connected paths, and proves quadratic energy density invariance for equivariant vector
fields.

## Main definitions
* `IsInvolution τ`: Predicate that `τ : α → α` satisfies `τ ∘ τ = id`.
* `IsEquivariant τ σ u`: Equivariance condition `u (τ x) = σ (u x)`.
* `IsNormPreserving σ`: An involution on a normed space that preserves the norm.
* `IsOddField τ f`: Anti-invariance condition `f (τ x) = -f x`.

## Main statements
* `equivariant_energy_invariant`: Quadratic energy `(1/2) * ‖u x‖^2` is invariant under `τ`.
* `odd_field_not_everywhere_pos`: An odd field cannot be strictly positive everywhere.
* `odd_field_not_everywhere_neg`: An odd field cannot be strictly negative everywhere.
* `antipodal_path_has_zero`: Any continuous odd field along a path connecting antipodal points
  `γ(b) = τ (γ(a))` has a zero node `f (γ t*) = 0`.
-/

noncomputable section

open Set

/-- An abstract involution on a type `α` is a map `τ` satisfying `τ ∘ τ = id`. -/
def IsInvolution {α : Type*} (τ : α → α) : Prop :=
  Function.Involutive τ

/-- An abstract vector field `u : α → V` is equivariant with respect to
a domain involution `τ` and a codomain reflection `σ` if `u (τ x) = σ (u x)`. -/
def IsEquivariant {α V : Type*} (τ : α → α) (σ : V → V) (u : α → V) : Prop :=
  ∀ x, u (τ x) = σ (u x)

/-- An involution `σ` on a normed space `V` is an isometry if it preserves the norm. -/
def IsNormPreserving {V : Type*} [NormedAddCommGroup V] (σ : V → V) : Prop :=
  ∀ v, ‖σ v‖ = ‖v‖

/-- For ANY base space `α`, ANY normed space `V`, ANY domain involution `τ`, and ANY
norm-preserving reflection `σ`, the quadratic energy density `(1/2) * ‖u x‖^2`
of any equivariant field is strictly invariant under `τ`! -/
theorem equivariant_energy_invariant {α V : Type*} [NormedAddCommGroup V]
    (τ : α → α) (σ : V → V) (h_iso : IsNormPreserving σ)
    (u : α → V) (h_equiv : IsEquivariant τ σ u) (x : α) :
    (1 / 2 : ℝ) * ‖u (τ x)‖ ^ 2 = (1 / 2 : ℝ) * ‖u x‖ ^ 2 := by
  rw [h_equiv x, h_iso (u x)]

/-- A scalar field `f : α → ℝ` is odd (anti-invariant) with respect to `τ`
if `f (τ x) = -f x`. -/
def IsOddField {α : Type*} (τ : α → α) (f : α → ℝ) : Prop :=
  ∀ x, f (τ x) = -f x

/-- On any space equipped with a domain involution `τ`, an odd scalar field
cannot be strictly positive everywhere. -/
theorem odd_field_not_everywhere_pos {α : Type*} [Nonempty α]
    (τ : α → α) (f : α → ℝ) (h_odd : IsOddField τ f) :
    ¬(∀ x, 0 < f x) := fun h_pos => by
  inhabit α
  nlinarith [h_pos default, h_pos (τ default), h_odd default]

/-- An odd scalar field cannot be strictly negative everywhere. -/
theorem odd_field_not_everywhere_neg {α : Type*} [Nonempty α]
    (τ : α → α) (f : α → ℝ) (h_odd : IsOddField τ f) :
    ¬(∀ x, f x < 0) := fun h_neg => by
  inhabit α
  nlinarith [h_neg default, h_neg (τ default), h_odd default]

/-- Let `γ : [a, b] → α` be any continuous path connecting a point `γ(a)` to its
antipodal image `γ(b) = τ(γ(a))`. Then any odd field `f` continuous along the path
must possess a zero node `γ(t*)` where `f(γ(t*)) = 0`. -/
theorem antipodal_path_has_zero {α : Type*} (τ : α → α) (f : α → ℝ)
    (h_odd : IsOddField τ f) {a b : ℝ} (hab : a ≤ b)
    (γ : ℝ → α)
    (h_cont : ContinuousOn (f ∘ γ) (Icc a b))
    (h_endpoints : γ b = τ (γ a)) :
    ∃ t ∈ Icc a b, f (γ t) = 0 := by
  let g := f ∘ γ
  have h_flip : g b = -g a := by dsimp [g]; rw [h_endpoints, h_odd]
  rcases le_total 0 (g a) with h_pos | h_neg
  · have h_mem : (0 : ℝ) ∈ Icc (g b) (g a) := ⟨by linarith, h_pos⟩
    rcases intermediate_value_Icc' hab h_cont h_mem with ⟨t, ht_icc, ht_eq⟩
    exact ⟨t, ht_icc, ht_eq⟩
  · have h_mem : (0 : ℝ) ∈ Icc (g a) (g b) := ⟨h_neg, by linarith⟩
    rcases intermediate_value_Icc hab h_cont h_mem with ⟨t, ht_icc, ht_eq⟩
    exact ⟨t, ht_icc, ht_eq⟩
