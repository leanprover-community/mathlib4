import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.Diffeomorph

open Manifold Diffeomorph
open Set Filter Function PartialEquiv ENat

variable {𝕜 E : Type*} (H : Type*)
variable [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [TopologicalSpace H]
variable (M : Type*) [TopologicalSpace M] [ChartedSpace H M]

variable (M' : Type*) [TopologicalSpace M'] [instChartedSpaceM' : ChartedSpace H M']

variable (I : ModelWithCorners 𝕜 E H) (n : WithTop ℕ∞) [IsManifold I n M]

#check IsLocalHomeomorph.chartedSpace

-- Charted Space on M' is the same as pushing the one from M forward along f
-- Compatible ist ein schlechtes wort dafür
def ChartedSpaceCompatible (f : M' ≃ₜ M) : Prop :=
  ∀ x : M', chartAt H x = f.toOpenPartialHomeomorph.trans (chartAt H (f x))

/-
def ChartedSpaceCompatible' (f : M' ≃ₜ M) : Prop :=
  ∀ e ∈ atlas H M', ∀ e' ∈ atlas H M',
    e.symm ≫ₕ e' = f.toOpenPartialHomeomorph
  ∀ x : M', chartAt H x = f.toOpenPartialHomeomorph.trans (chartAt H (f x))-/


def ChartedSpaceInduced (f : M ≃ₜ M') (hf : Surjective f) : Prop :=
  instChartedSpaceM' = f.isLocalHomeomorph.chartedSpace hf

variable (f : Diffeomorph I I M M' ⊤) (hf : Surjective f)

lemma aux (h : ChartedSpaceInduced H M M' f.toHomeomorph hf) : ∀ (e e' : OpenPartialHomeomorph M' H),
    e ∈ atlas H M' →
    e' ∈ atlas H M' → ContDiffOn 𝕜 n (↑I ∘ ↑(e.symm ≫ₕ e') ∘ ↑I.symm) (↑I.symm ⁻¹' (e.symm ≫ₕ e').source ∩ range ↑I) := by
  intro e e' h1 h2
  rw [ChartedSpaceInduced] at h
  simp_all [IsLocalHomeomorph.chartedSpace, IsLocalHomeomorph.chartedSpaceOfRightInverse]
  have h : atlas H M' = {x | ∃ q, (id (Eq.refl ⇑f) ▸ Homeomorph.isLocalHomeomorph f.toHomeomorph ).localInverseAt (Exists.choose hf.hasRightInverse q) ≫ₕ chartAt H (Exists.choose hf.hasRightInverse q) = x} := by
    sorry
  rw [h] at h1 h2
  simp_all
  







instance instTest : IsManifold I n M' := isManifold_of_contDiffOn _ _ _ (by sorry)
