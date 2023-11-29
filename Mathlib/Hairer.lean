/- Hairer's challenge given to Kevin. -/

import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Data.MvPolynomial.Variables

open Metric Set MeasureTheory
open MvPolynomial hiding support
open Function hiding eval

section linear

variable {𝕜 : Type*} [Field 𝕜]
variable {E E' F  : Type*}
  [AddCommGroup E] [Module 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F]

lemma exists_affineSpan_zero {ι'} (s : Submodule 𝕜 F) [FiniteDimensional 𝕜 s] [Infinite ι']
  (L : F →ₗ[𝕜] E →ₗ[𝕜] 𝕜) (x : ι' → E) (hx : LinearIndependent 𝕜 x) :
  ∃ y ∈ affineSpan 𝕜 (range x), ∀ i ∈ s, L i y = 0 := sorry

variable (𝕜) in
def nonConstantTotalDegreeLE (ι : Type*) (N : ℕ) : Submodule 𝕜 (MvPolynomial ι 𝕜) where
  carrier := { p | p.totalDegree ≤ N ∧ constantCoeff p = 0 }
  add_mem' := sorry
  zero_mem' := sorry
  smul_mem' := sorry

instance (ι : Type*) [Finite ι] (N : ℕ) :
  FiniteDimensional 𝕜 (nonConstantTotalDegreeLE 𝕜 ι N) := sorry

lemma affineSpan_subset_span {s : Set E} : (affineSpan 𝕜 s : Set E) ⊆ Submodule.span 𝕜 s := sorry

variable (𝕜) in
lemma support_subset_of_mem_span {α β} [Zero β] {s : Set E} {y : E} [FunLike E α (fun _ ↦ β)]
    (hy : y ∈ Submodule.span 𝕜 s) : support y ⊆ ⋃ i ∈ s, support i := by
  -- rw [← Subtype.range_coe (s := s), mem_affineSpan_iff_eq_affineCombination] at hy
  sorry

variable (𝕜) in
lemma support_subset_of_mem_affineSpan {α β} [Zero β] {s : Set E} {y : E} [FunLike E α (fun _ ↦ β)]
    (hy : y ∈ affineSpan 𝕜 s) : support y ⊆ ⋃ i ∈ s, support i :=
  support_subset_of_mem_span 𝕜 (affineSpan_subset_span hy)



end linear

section normed
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E E' F  : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable (𝕜 E F) in
def SmoothSupportedOn (n : ℕ∞) (s : Set E) : Submodule 𝕜 (E → F) where
  carrier := { f : E → F | tsupport f ⊆ s ∧ ContDiff 𝕜 n f }
  add_mem' hf hg := ⟨sorry, hf.2.add hg.2⟩
  zero_mem' :=
    ⟨(tsupport_eq_empty_iff.mpr rfl).subset.trans (empty_subset _), contDiff_const (c := 0)⟩
  smul_mem' r f hf :=
    ⟨(closure_mono <| support_smul_subset_right r f).trans hf.1, contDiff_const.smul hf.2⟩

variable {n : ℕ∞} {s : Set E}

instance : FunLike (SmoothSupportedOn 𝕜 E F n s) E (fun _ ↦ F) where
  coe := Subtype.val
  coe_injective' := Subtype.coe_injective

lemma SmoothSupportedOn.tsupport_subset (f : SmoothSupportedOn 𝕜 E F n s) : tsupport f ⊆ s := f.2.1

lemma SmoothSupportedOn.support_subset (f : SmoothSupportedOn 𝕜 E F n s) :
  support f ⊆ s := subset_tsupport _ |>.trans (tsupport_subset f)

protected lemma SmoothSupportedOn.contDiff (f : SmoothSupportedOn 𝕜 E F n s) :
    ContDiff 𝕜 n f := f.2.2

variable (𝕜) in
lemma contDiff_of_mem_span {V} {n : ℕ∞} [AddCommGroup V] [Module 𝕜 V] {s : Set V} {y : V}
    [FunLike V E (fun _ ↦ F)] (hy : y ∈ Submodule.span 𝕜 s) (hi : ∀ i ∈ s, ContDiff 𝕜 n i) :
    ContDiff 𝕜 n y := by
  sorry

variable (𝕜) in
lemma contDiff_of_mem_affineSpan {V} {n : ℕ∞} [AddCommGroup V] [Module 𝕜 V] {s : Set V} {y : V}
    [FunLike V E (fun _ ↦ F)] (hy : y ∈ affineSpan 𝕜 s) (hi : ∀ i ∈ s, ContDiff 𝕜 n i) :
    ContDiff 𝕜 n y :=
  contDiff_of_mem_span 𝕜 (affineSpan_subset_span hy) hi

end normed
open SmoothSupportedOn

noncomputable section real

lemma step (ι) [Fintype ι] :
    ∃ f : ℕ → SmoothSupportedOn ℝ (EuclideanSpace ℝ ι) ℝ ⊤ (closedBall 0 1),
    LinearIndependent ℝ f ∧ ∀ n, ∫ x, f n x = 1 := by
  obtain ⟨s, r, hs, hr, h2s⟩ : ∃ (s : ℕ → EuclideanSpace ℝ ι) (r : ℕ → ℝ),
    Pairwise (Disjoint on (fun i ↦ closedBall (s i) (r i))) ∧
    (∀ i, 0 < r i) ∧ (∀ i, ball (s i) (r i) ⊆ closedBall 0 1)
  · sorry
  let f1 n : ContDiffBump (s n) := ⟨r n / 2, r n, half_pos (hr n), half_lt_self (hr n)⟩
  let f2 n : SmoothSupportedOn ℝ (EuclideanSpace ℝ ι) ℝ ⊤ (closedBall 0 1) :=
    ⟨(f1 n).normed volume, sorry⟩
  refine ⟨f2, ?_, fun n ↦ (f1 n).integral_normed⟩
  sorry

def L {ι : Type*} [Fintype ι] :
  MvPolynomial ι ℝ →ₗ[ℝ] SmoothSupportedOn ℝ (EuclideanSpace ℝ ι) ℝ ⊤ (closedBall 0 1) →ₗ[ℝ] ℝ where
    toFun p :=
      { toFun := fun f ↦ ∫ x : EuclideanSpace ℝ ι, eval x p • f x
        map_add' := sorry
        map_smul' := sorry }
    map_add' := sorry
    map_smul' := sorry

lemma hairer (N : ℕ) (ι : Type*) [Fintype ι] :
    ∃ (ρ : EuclideanSpace ℝ ι → ℝ), tsupport ρ ⊆ closedBall 0 1 ∧ ContDiff ℝ ⊤ ρ ∧
    ∀ (p : MvPolynomial ι ℝ), p.totalDegree ≤ N →
    ∫ x : EuclideanSpace ℝ ι, eval x p • ρ x = eval 0 p := by
  classical
  obtain ⟨f, hf, h2f⟩ := step ι
  obtain ⟨ρ, hρ, h2ρ⟩ := exists_affineSpan_zero (nonConstantTotalDegreeLE ℝ ι N) L f hf
  have h3ρ : ∫ x, ρ x = 1
  · sorry
  refine ⟨ρ, ?_, ?_, ?_⟩
  · refine closure_minimal ?_ isClosed_ball
    refine support_subset_of_mem_affineSpan ℝ hρ |>.trans ?_
    simp [-support_subset_iff, SmoothSupportedOn.support_subset]
  · refine contDiff_of_mem_affineSpan ℝ hρ ?_
    simp [SmoothSupportedOn.contDiff]
  · intro p hp
    obtain ⟨q, r, hq, rfl⟩ : ∃ q r, constantCoeff q = 0 ∧ p = q + C r
    · refine ⟨p - C (eval 0 p), eval 0 p, by simp, by ring⟩
    have h2q : totalDegree q ≤ N
    · refine Eq.trans_le ?_ hp
      sorry
    simp [hq, add_mul]
    rw [integral_add]
    · simp [integral_mul_left, h3ρ]
      exact h2ρ q ⟨h2q, hq⟩
    · sorry
    · sorry

end real
