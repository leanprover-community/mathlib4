import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.CategoryTheory.Sites.OneHypercover
import Mathlib.AlgebraicGeometry.Sites.BigZariski

namespace AlgebraicGeometry.Scheme.GlueData

open AlgebraicGeometry CategoryTheory

universe u

variable (D : Scheme.GlueData.{u})

noncomputable def preOneHypercover : PreOneHypercover D.glued where
  I₀ := D.J
  X := D.U
  f := D.ι
  I₁ _ _ := PUnit
  Y i₁ i₂ _ := D.V (i₁, i₂)
  p₁ i₁ i₂ _ := D.f i₁ i₂
  p₂ i₁ i₂ j := D.t i₁ i₂ ≫ D.f i₂ i₁
  w i₁ i₂ _ := by simp only [Category.assoc, Scheme.GlueData.glue_condition]

noncomputable def oneHypercover : Scheme.zariskiTopology.OneHypercover D.glued := by
  apply GrothendieckTopology.OneHypercover.mk' D.preOneHypercover
  sorry
  sorry




end AlgebraicGeometry.Scheme.GlueData
