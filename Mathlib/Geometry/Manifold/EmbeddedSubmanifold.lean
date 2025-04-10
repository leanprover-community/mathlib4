/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
import Mathlib.Geometry.Manifold.IsImmersionEmbedding

/-!
# Embedded submanifolds

TODO: write doc-string when things are clearer

-/

open scoped Manifold Topology ContDiff

open Function Set

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E E' : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H']
  {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'}
  {M M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] {n : WithTop ℕ∞}

variable (I I' F) in
/-- Two models with corners `I` and `I'` form a **slice model** if "I includes into I'".
More precisely, there are an embedding `H → H'` and a continuous linear map `E → E'` so the diagram
  H  -I  → E'
  |        |
  |        |
  H' -I' → E'
commutes. More precisely, we prescribe a linear equivalence `E × F → E`, for some normed space `F`,
which induces the map `E → E'` in the obvious way.
-/
class SliceModel where
  equiv: (E × F) ≃L[𝕜] E'
  map: H → H'
  hmap : Topology.IsEmbedding map
  compatible : I' ∘ map = equiv ∘ ((·, 0) : E → E × F) ∘ I

-- warm-up: I' ∘ map ⊆ im equiv ∘ I: that's basically obvious, nothing to prove

section

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] [Unique G]

-- TODO: this ought to be available already/ what am I missing?
variable (𝕜 E) in
def LinearEquiv.prodSingleton {y : G} : E ≃ₗ[𝕜] (E × G) where
  toFun := (·, y)
  map_add' := sorry
  map_smul' := sorry
  invFun := Prod.fst
  left_inv := sorry
  right_inv := sorry

@[simp]
lemma LinearEquiv.prodSingle_coe {y : G} :
    (LinearEquiv.prodSingleton 𝕜 E (y := y)) = ((·, y) : E → E × G) := rfl

lemma LinearEquiv.prodSingle_apply {y : G} (x : E) :
    (LinearEquiv.prodSingleton 𝕜 E (y := y)) x = (x, y) := by simp

@[simp]
lemma LinearEquiv.prodSingle_symm_apply {y : G} (x : E × G) :
    (LinearEquiv.prodSingleton 𝕜 E (y := y)).symm x = x.1 := rfl

def ContinuousLinearEquiv.prodSingleton {y : G} : E ≃L[𝕜] (E × G) where
  toLinearEquiv := LinearEquiv.prodSingleton 𝕜 E (y := y)
  continuous_toFun := by dsimp; fun_prop
  continuous_invFun := by show Continuous Prod.fst; fun_prop

/-- Every model with corners is a slice model over itself. -/
instance : SliceModel (⊥ : Subspace 𝕜 E) I I where
  equiv := (ContinuousLinearEquiv.prodSingleton (y := 0)).symm
  map := id
  hmap := Topology.IsEmbedding.id
  compatible := by
    ext x
    dsimp
    erw [LinearEquiv.prodSingle_symm_apply] -- TODO: add the appropriate coercions!

end
