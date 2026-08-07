module

public import Mathlib

@[expose] public section

open TopologicalSpace

open scoped unitInterval

/-- Helper lemma: the concatenation of two lifted paths projects to the concatenation
    of the original paths. -/
lemma trans_lift_commutes {X : Type*} [TopologicalSpace X] {U : Set X} {x y z : X}
    (hx : x ∈ U) (hy : y ∈ U) (hz : z ∈ U)
    (γ₁ : Path x y) (γ₂ : Path y z)
    (γ₁_lift : Path (⟨x, hx⟩ : U) (⟨y, hy⟩ : U))
    (γ₂_lift : Path (⟨y, hy⟩ : U) (⟨z, hz⟩ : U))
    (hγ₁ : ∀ (t : unitInterval), (γ₁_lift t : X) = γ₁ t)
    (hγ₂ : ∀ (t : unitInterval), (γ₂_lift t : X) = γ₂ t) :
    ∀ (t : unitInterval), ((γ₁_lift.trans γ₂_lift) t : X) = (γ₁.trans γ₂) t := by
  intro t
  by_cases h : (t : ℝ) ≤ 1 / 2
  · -- Case (t : ℝ) ≤ 1 / 2
    have h_t1 : 2 * (t : ℝ) ∈ I := ⟨by linarith [t.2.1], by linarith [h]⟩
    let t' : unitInterval := ⟨2 * (t : ℝ), h_t1⟩
    have h1 : (γ₁_lift.trans γ₂_lift) t = γ₁_lift t' := by
      have h_trans : (γ₁_lift.trans γ₂_lift) t =
          dite ((t : ℝ) ≤ 1 / 2) (fun h => γ₁_lift ⟨2 * (t : ℝ), _⟩) (fun h => γ₂_lift ⟨2 * (t : ℝ) - 1, _⟩) :=
        Path.trans_apply γ₁_lift γ₂_lift t
      rw [h_trans]
      rw [dif_pos h]
      <;> rfl
    have h2 : (γ₁.trans γ₂) t = γ₁ t' := by
      have h_trans : (γ₁.trans γ₂) t =
          dite ((t : ℝ) ≤ 1 / 2) (fun h => γ₁ ⟨2 * (t : ℝ), _⟩) (fun h => γ₂ ⟨2 * (t : ℝ) - 1, _⟩) :=
        Path.trans_apply γ₁ γ₂ t
      rw [h_trans]
      rw [dif_pos h] <;> rfl
    rw [h1, h2]
    exact hγ₁ t'
  · -- Case (t : ℝ) > 1 / 2
    have h_t2 : 2 * (t : ℝ) - 1 ∈ I := ⟨by linarith [t.2.1, h], by linarith [t.2.2]⟩
    let t' : unitInterval := ⟨2 * (t : ℝ) - 1, h_t2⟩
    have h1 : (γ₁_lift.trans γ₂_lift) t = γ₂_lift t' := by
      have h_trans : (γ₁_lift.trans γ₂_lift) t =
          dite ((t : ℝ) ≤ 1 / 2) (fun h => γ₁_lift ⟨2 * (t : ℝ), _⟩) (fun h => γ₂_lift ⟨2 * (t : ℝ) - 1, _⟩) :=
        Path.trans_apply γ₁_lift γ₂_lift t
      rw [h_trans]
      rw [dif_neg h] <;> rfl
    have h2 : (γ₁.trans γ₂) t = γ₂ t' := by
      have h_trans : (γ₁.trans γ₂) t =
          dite ((t : ℝ) ≤ 1 / 2) (fun h => γ₁ ⟨2 * (t : ℝ), _⟩) (fun h => γ₂ ⟨2 * (t : ℝ) - 1, _⟩) :=
        Path.trans_apply γ₁ γ₂ t
      rw [h_trans]
      rw [dif_neg h] <;> rfl
    rw [h1, h2]
    exact hγ₂ t'

end
