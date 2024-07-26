import Mathlib.Analysis.NormedSpace.AffineIsometry
import Mathlib.Order.Partition.Finpartition


open Function

variable (𝕜 : Type*) {V: Type*}(P: Type*)
  [NormedField 𝕜]
  [SeminormedAddCommGroup V] [NormedSpace 𝕜 V] [PseudoMetricSpace P] [NormedAddTorsor V P]

/-
Two subsets B₁ B₂ of a pseudometric space P are equidecomposable if B₁ and B₂ can be divided into
finitely many affinely isometric parts.
-/
def equidecomposable (B₁ B₂ : Set P) : Prop :=
  ∃ (P_B₁ : Finpartition B₁), ∃ (P_B₂ : Finpartition B₂), ∃ (f : P_B₁.parts → P_B₂.parts),
    P_B₂.parts.val.sizeOf = P_B₁.parts.val.sizeOf ∧
  Bijective f ∧ (∀ p_b₁ : P_B₁.parts, ∃ (a : AffineIsometry 𝕜 P P),
    ∀ x ∈ p_b₁.val, ∃ y ∈ (f p_b₁).val, a.toFun x = y ∧
    ∀ y ∈ (f p_b₁).val, ∃ x ∈ p_b₁.val, a.toFun x = y)
