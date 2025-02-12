import Mathlib.Algebra.Lie.UniversalEnveloping

open BigOperators TensorProduct DirectSum TensorAlgebra UniversalEnvelopingAlgebra

/-
The work on this file might have to stop for a while, as we're now communicating with the group that's working on graded/filtered objects since most constructions seems to be more generally applicable. They'll probably write something of more general usage, and we'll use those APIs after they've finished.

So the current work will be focusing on the other missing things like symmetric algebra and some specific constructions in the proof.
-/

noncomputable section
variable (R : Type*) [CommRing R]
variable (L : Type*) [LieRing L] [LieAlgebra R L] [Module.Free R L]

local notation "ιₜ" => TensorAlgebra.ι R (M := L)
local notation "𝔘" => UniversalEnvelopingAlgebra R L
local notation "π" => UniversalEnvelopingAlgebra.mkAlgHom R L
local notation "𝔖" => SymmetricAlgebra R L
local notation "ω" => SymmetricAlgebra.mkAlgHom R L
local notation "ιₛ" => SymmetricAlgebra.iota R L

#check LieRing
abbrev 𝔗 := TensorAlgebra

#synth GradedRing ((LinearMap.range (ι R : L →ₗ[R] TensorAlgebra R L) ^ ·))

abbrev graded_T : ℕ → Submodule R (TensorAlgebra R L) := fun (n : ℕ) ↦
  (LinearMap.range (ι R : L →ₗ[R] TensorAlgebra R L) ^ n)

abbrev filter_T := induced_fil' (graded_T R L)

#synth FilteredAlgebra (filter_T R L)

abbrev graded_S := SymmetricAlgebra.gradingSymmetricAlgebra R L

abbrev filter_S := induced_fil' (graded_S R L)

lemma aux_lemma_a : ∃ ρ : L →ₗ⁅R⁆ Module.End R 𝔖, (∀ m : ℕ, ∀ u : L, ∀ x : SymmetricAlgebra R L, x ∈ filter_S R L m → ((ρ u) x) - ((ιₛ u) * x) ∈ filter_S R L m) := sorry

lemma aux_lemma_b : ∃ ρ : 𝔘 →ₐ[R] Module.End R 𝔖, (∀ m n : ℕ, ∀ x : TensorAlgebra R L, ∀ y : SymmetricAlgebra R L, x ∈ filter_T R L (m + 1) → y ∈ filter_S R L n → (ρ (π x)) y - (ω x) * y) ∈ filter_S R L (m + n) := by
  obtain ⟨ρ, hρ⟩ := aux_lemma_a R L
  use UniversalEnvelopingAlgebra.lift R ρ
  -- some kind of induction would finish this step.
  sorry

lemma aux_lemma_c (x : TensorAlgebra R L) (m : ℕ) (h : x ∈ filter_T R L m)
  (heq : π x = 0) : ω (GradedAlgebra.proj (graded_T R L) m x) = 0 := by
    sorry
    -- obtain ⟨ρ, hρ⟩ := aux_lemma_b R L
    -- specialize hρ m 0 x 1 h (by apply FilteredRing.one)
    -- rw [heq, map_zero, add_zero, mul_one, LinearMap.zero_apply, map_zero] at hρ
    -- rw [hρ]
    -- exact SymmetricAlgebra.proj_comm R L x m
