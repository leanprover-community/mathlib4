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

namespace PartialHomeomorph

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

noncomputable def _root_.PartialEquiv.pullback (φ : PartialEquiv Y Z) {f : X → Y} (hf : Injective f) [Nonempty X] :
    PartialEquiv X Z where
  toFun := φ ∘ f
  invFun := (Function.extend f id (fun _ ↦ (Classical.arbitrary X))) ∘ φ.invFun
  left_inv' x hx := by
    have : φ.symm (φ (f x)) = f x := φ.left_inv' hx
    simp only [PartialEquiv.invFun_as_coe, comp_apply, this]
    exact hf.extend_apply _ _ _
  right_inv' x hx := by
    simp only [comp_apply]
    set y := φ.invFun x with hy
    have : y ∈ φ.source := φ.map_target' hx
    -- trouble: this is true if y ∈ im f, and maybe VERY false otherwise!!
    have : f (Function.extend f id (fun x ↦ Classical.arbitrary X) y) = y := by
      unfold Function.extend
      by_cases h : ∃ a, f a = y
      · obtain ⟨a, ha⟩ := h
        rw [← ha]
        simp
        sorry -- seems true, but lean is stuck somewhere
      · simp [h]
        sorry -- this is clearly false
    rw [this, hy]
    exact φ.right_inv' hx
  -- trouble: I *could* restrict the target (e.g. by intersecting with im f), but then the target
  -- would generally not be open any more! for pulling back, I really need a better way.
  source := f ⁻¹' φ.source
  target := φ.target
  map_source' := fun x hx ↦ φ.map_source hx
  map_target' x hx := by
    rw [mem_preimage]
    simp only [comp_apply]
    set y := φ.invFun x with hy
    convert φ.map_target' hx
    rw [← hy]
    -- now, we're just at the interesting part of right_inv'
    sorry

/-- Pulling back a partial homeomorphism by an injective continuous map.
XXX: what's the inverse map? not sure! -/
noncomputable  def pullback (φ : PartialHomeomorph Y Z) {f : X → Y}
    (hf : Injective f) (hf' : Continuous f) [Nonempty X] : PartialHomeomorph X Z where
  toPartialEquiv := φ.toPartialEquiv.pullback hf
  continuousOn_toFun := φ.continuousOn_toFun.comp hf'.continuousOn (fun ⦃x⦄ a ↦ a)
  continuousOn_invFun := by
    let finv := Function.extend f id (fun _ ↦ (Classical.arbitrary X))
    sorry
  open_source := IsOpen.preimage hf' φ.open_source
  open_target := φ.open_target

end PartialHomeomorph

variable (I I' M M' n) in
class IsImmersedSubmanifold [TopologicalSpace M] [IsManifold I' n M'] [SliceModel F I I'] where
  emb: M → M'

namespace IsImmersedSubmanifold

variable [TopologicalSpace M] [IsManifold I' n M']

--instance instChartedSpace [IsImmersedSubmanifold I' M M' n] : ChartedSpace H M := sorry
-- IsManifold I n M
-- IsImmersion ...emb

-- conversely, if f: M → M' is an immersion (embedding), we can define the image model I₀ on M',
-- prove that this is a slice model and deduce IsImmersedSubmanifold via f! (same for embedded)
end IsImmersedSubmanifold

#exit



-- XXX: does NontriviallyNormedField also work? Splits seems to require more...
variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {F F' : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H']
  {G : Type*} [TopologicalSpace G] {G' : Type*} [TopologicalSpace G']
  {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'}
  {J : ModelWithCorners 𝕜 F G} {J' : ModelWithCorners 𝕜 F G'}

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {N' : Type*} [TopologicalSpace N'] [ChartedSpace G' N']
  {n : WithTop ℕ∞}
