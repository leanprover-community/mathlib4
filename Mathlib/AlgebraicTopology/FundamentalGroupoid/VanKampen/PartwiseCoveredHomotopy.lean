module

public import Mathlib
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen.PathHelpers
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen.HomotopyDecomposition

@[expose] public section

open TopologicalSpace

open scoped unitInterval

universe u

variable {X : Type u} [TopologicalSpace X]
variable (𝒰 : Set (Opens X))

/-- A partwise covered homotopy: a homotopy H together with an n×m grid of subrectangles,
    each subrectangle mapping into some open set from 𝒰. -/
structure PartwiseCoveredHomotopy {x y : X} {γ₁ γ₂ : Path x y} (H : Path.Homotopy γ₁ γ₂) (n m : ℕ) : Type u where
  covers : Fin n → Fin m → Opens X
  hcover_mem : ∀ i j, covers i j ∈ 𝒰
  h_rectangles : ∀ (i : Fin n) (j : Fin m),
    ∀ (p : I × I),
      (i : ℝ) / (n : ℝ) ≤ (p.1 : ℝ) → (p.1 : ℝ) ≤ ((i : ℝ) + 1) / (n : ℝ) →
      (j : ℝ) / (m : ℝ) ≤ (p.2 : ℝ) → (p.2 : ℝ) ≤ ((j : ℝ) + 1) / (m : ℝ) →
      H p ∈ covers i j

/-- Every homotopy admits a partwise covered decomposition (square grid). -/
theorem exists_partwise_covered_homotopy
    (hcover : ∀ x : X, ∃ U : Opens X, U ∈ 𝒰 ∧ x ∈ U)
    {x y : X} {γ₁ γ₂ : Path x y} (H : Path.Homotopy γ₁ γ₂) :
    ∃ (n : ℕ), 0 < n ∧ Nonempty (PartwiseCoveredHomotopy 𝒰 H n n) := by
  classical
  -- Use the homotopy_has_subdivision theorem
  have h_main := homotopy_has_subdivision 𝒰 hcover H
  rcases h_main with ⟨n, hn_pos, h_subdiv⟩
  refine' ⟨n, hn_pos, _⟩

  -- For each (i, j), choose a U ∈ 𝒰 that covers the subrectangle
  let covers : Fin n → Fin n → Opens X := fun i j =>
    Classical.choose (h_subdiv i j)
  let hcover_mem : ∀ i j, covers i j ∈ 𝒰 ∧
    ∀ (p : I × I),
      (i : ℝ) / (n : ℝ) ≤ (p.1 : ℝ) → (p.1 : ℝ) ≤ ((i : ℝ) + 1) / (n : ℝ) →
      (j : ℝ) / (n : ℝ) ≤ (p.2 : ℝ) → (p.2 : ℝ) ≤ ((j : ℝ) + 1) / (n : ℝ) →
      H p ∈ covers i j := fun i j => Classical.choose_spec (h_subdiv i j)

  let hcover_mem1 : ∀ i j, covers i j ∈ 𝒰 := fun i j => (hcover_mem i j).1
  let h_rectangles : ∀ (i : Fin n) (j : Fin n),
    ∀ (p : I × I),
      (i : ℝ) / (n : ℝ) ≤ (p.1 : ℝ) → (p.1 : ℝ) ≤ ((i : ℝ) + 1) / (n : ℝ) →
      (j : ℝ) / (n : ℝ) ≤ (p.2 : ℝ) → (p.2 : ℝ) ≤ ((j : ℝ) + 1) / (n : ℝ) →
      H p ∈ covers i j := fun i j => (hcover_mem i j).2

  exact ⟨⟨covers, hcover_mem1, h_rectangles⟩⟩

end
